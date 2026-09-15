

import requests
import json
import threading
import copy
import pickle
import multiprocessing
import os
import time
import sys
import posixpath

from Utilities.unit_IO import processIO, orderHandling
from Utilities import utilities

sys.path.append("") #add betting folder to path

class RequestError(Exception):
    """Raised in case of problems in a request"""
    pass

class LogoutError(Exception):
    """"""
    pass

class KeepAliveError(Exception):
    """"""
    pass

class BetfairBot(orderHandling):
    """Interface to betfairs exchange api. Should be able to both create bets and provide information about current bets, match odds, volume etc.
    
    Game limit 5000 i timmen annars transaktionsavgift

    #max 20 dataförfrågningar per sekund annars avgift?
    Market data request limit for listMarketBook, listRunnerBook, listMarketCatalogue and listMarketProfitandLoss

    Premiumavgifter om mycket profit och för lite komission
    Ingen kommission om förlust
    Kommision på nettovinster
    Marknadstaxa för sverige är 5%
    Avgift för inaktivt konta i 13+ mån, 30kr per månad, upp till 6 mån betalas tillbaka

    Keep-alive header or session will timeout, INVALID_SESSION_TOKEN handler for new login maybe?

    """


    def __init__(self) -> None:
        self.stop_flag = utilities.BetterEvent(multiprocessing)
        self.error_flag = utilities.BetterEvent(multiprocessing)

        self.base_path = "Betfair"

        self.application_name = ""

        self.headers = {
            "Accept": "application/json",
            "X-Application": "", #application key, Delayed
            "Content-Type": "application/x-www-form-urlencoded",
            "Accept-Encoding": "gzip, deflate"
        } #X-authentication comes from login below

        #Login info
        self.cert_login_url = "https://identitysso-cert.betfair.se/api/certlogin"
        self.cert_crt_path = ""
        self.cert_key_path = ""

        self.username = ""
        self.password = ""

        self.sessionToken = self.login()
        self.headers["X-Authentication"] = self.sessionToken

        #Logout info
        self.logout_url = "https://identitysso.betfair.se/api/logout"

        #Keep-alive url
        self.keep_alive_url = "https://identitysso.betfair.se/api/keepAlive"

        #Endpoints (Using JSON-RPC)
        self.betting_endpoint = "https://api.betfair.com/exchange/betting/json-rpc/v1"
        self.account_endpoint = "https://api.betfair.com/exchange/account/json-rpc/v1"

        #Internal input/output path, used to check for already sent orders and to manage any received orders without interfering with other programs
        #self.processed_orders_path = os.path.join(self.base_path,".processed_orders")
        self.sent_orders_path = os.path.join(self.base_path,".sent_orders")
        

        self.input_address_name = "input_betfair"
        self.order_select_query = "SELECT * FROM order_table WHERE model_predictions IS NOT NULL"

        #self.io = None

        self.new_orders_delay = 300 #the delay in seconds between new orders polling

        self.start_process_functions = [self.new_orders_check]
        self.orderhandling_function = self.market_monitoring
        self.p_list = []


        #API method limits, not implemented yet
        #self.api_rate_limit = {"listMarketBook": []}
        #listMarketBook, max 5 times per second to a single marketId


#API interaction
    def post(self, url: str, headers: dict = None, data: dict = None, cert: tuple = None) -> dict:
        """Makes a post request to the provided url with the provided headers, data and certification. If headers is missing, uses self.headers as substitute.
        
        """
        if headers is None:
            headers = self.headers

        #print(url)
        resp = requests.post(url = url, headers=headers, data=data, cert=cert)

        resp_json = resp.json()

        if resp.status_code == 200:

            return resp_json
        
        else:
            raise RequestError(resp.status_code, resp.text)

    def login(self) -> str:
        """Logs in non-interactively and returns the session token to be used in future requests.

        Limited to 100 requests per minute before error (not implemented here)
        
        """

        body = {
            "username": self.username,
            "password": self.password
        }

        resp_json = self.post(url = self.cert_login_url, headers=self.headers, data=body, cert=(self.cert_crt_path, self.cert_key_path))

        return resp_json["sessionToken"]

    def keep_alive(self) -> None:
        """Sends a keep-alive request to the keep-alive url"""
        resp_json = self.post(self.keep_alive_url)
        if resp_json == "SUCCESS":
            return
        else:
            raise KeepAliveError()

    def logout(self) -> None:
        """Logs out, in case of failure raises LogoutError"""
        resp_json = self.post(self.logout_url, headers=self.headers)

        if resp_json["status"] == "SUCCESS":
            print("logged out")
            return
        else:
            raise LogoutError()



    def rpc_dict(self, method_name: str, params_dict: dict) -> dict:
        """Returns the rpc request dict using the provided method name and parameters
        
        """
        rpc_req = {"jsonrpc": "2.0", "method": "SportsAPING/v1.0/" + method_name, "params": params_dict, "id": 1}
        return rpc_req
    
    def rpc_request(self, method_name: str, params: dict):
        """Returns data from a request using the provided method and parameters. If the request weight is too high, splits the market ids
        
        """
        data_list = self.data_split(method_name, params)


        resp_list = []

        for data in data_list:

            jsonrpc_req = json.dumps(data)

            resp = self.post(self.betting_endpoint, data=jsonrpc_req)

            resp_list.extend(resp["result"])

        return resp_list

    def data_split(self, method_name: str, params: dict):
        """Returns a list of data to be sent in separate requests which do not violate the market data request limits"""
        packet_list = []

        #Weight assignment
        packet_weight = 0

        match method_name:
            case w if w in ["listMarketBook", "listRunnerBook"]:
                if "priceProjection" not in params:
                    packet_weight += 2
                else:
                    projections = params["priceProjection"]["priceData"]

                    if "EX_BEST_OFFERS" in projections and "EX_TRADED" in projections and len(projections) == 2:
                        packet_weight += 20
                    elif "EX_ALL_OFFERS" in projections and "EX_TRADED" in projections and len(projections) == 2:
                        packet_weight += 32
                    else:
                        if "SP_AVAILABLE" in projections:
                            packet_weight += 3
                        if "SP_TRADED" in projections:
                            packet_weight += 7
                        if "EX_BEST_OFFERS" in projections:
                            packet_weight += 5
                        if "EX_ALL_OFFERS" in projections:
                            packet_weight += 17
                        if "EX_TRADED" in projections:
                            packet_weight += 17
                
            case w if w == "listMarketCatalogue":
                
                #weight splitting
                if "marketProjection" in params:
                    par_list = params["marketProjection"]

                    if "MARKET_DESCRIPTION" in par_list:
                        packet_weight += 1
                    elif "RUNNER_METADATA" in par_list:
                        packet_weight += 1

                
            case w if w == "listMarketProfitandLoss":
                raise NotImplementedError
            

        #Figuring out which ids and limit to use
        split = False
        ids_per_req = None

        key = None


        if "filter" in params and "marketIds" in params["filter"] and packet_weight*len(params["filter"]["marketIds"]) > 200:
            key = "filter"

            split = True
            ids_name = "marketIds"

            ids_per_req = 200//packet_weight

        elif "marketIds" in params and packet_weight*len(params["marketIds"]) > 200:
            key = "marketIds"
            split = True
            ids_name = "marketIds"

            ids_per_req = 200//packet_weight

            #split instead using maxResults, argument for listMarketCatalogue
        if "maxResults" in params:
            if ids_per_req is None or params["maxResults"] < ids_per_req:

                if "eventIds" in params["filter"] and len(params["filter"]["eventIds"]) > params["maxResults"]:
                    split = True
                    key = "filter"
                    ids_per_req = params["maxResults"]
                    ids_name = "eventIds"

                if "marketIds" in params["filter"] and len(params["filter"]["marketIds"]) > params["maxResults"]:
                    split = True
                    key = "filter"
                    ids_per_req = params["maxResults"]
                    ids_name = "marketIds"


        
        #Package splitting according to limit
        if split:
            if key == "filter":
                ids = copy.deepcopy(params[key][ids_name])
            elif key == "marketIds":
                ids = copy.deepcopy(params[key])
            
            ids_chunk_list = []

            while len(ids) > 0:
                ids_chunk_list.append(ids[:ids_per_req])
                ids = ids[ids_per_req:]

            for ids in ids_chunk_list:
                params_packet = copy.deepcopy(params)
                if key == "filter":
                    params_packet[key][ids_name] = ids
                elif key == "marketIds":
                    params_packet[key] = ids

                packet = self.rpc_dict(method_name, params_packet)
                packet_list.append(packet)
                
        else:
            packet = self.rpc_dict(method_name, params)
            packet_list.append(packet)


        return packet_list




    def api_match_list(self) -> list:
        """Returns a list of matches with a MATCH_ODDS market and the required information entries from the api"""

        market_type_code = "MATCH_ODDS"

        events = self.rpc_request(method_name="listEvents", params={"filter": {"eventTypeIds": ["1"], "marketTypeCodes": [market_type_code]}})
        #hemma, bortalag, land, datum, klockslag

        #print(len(events))
        event_id_list = []

        for e in events:
            event_id_list.append(e["event"]["id"])

        markets = self.rpc_request("listMarketCatalogue", params={"filter": {"eventIds": event_id_list, "marketTypeCodes": [market_type_code]}, "marketProjection": ["COMPETITION","EVENT", "RUNNER_DESCRIPTION"], "maxResults": 1000})

        filtered_markets = []

        expected_keys = ['marketId', 'marketName', 'totalMatched', 'runners', 'event', "competition"]

        for m in markets:
            complete = True
            keys = list(m.keys())

            for ex in expected_keys:
                if ex not in keys:
                    complete = False
            
            if complete:
                filtered_markets.append(m)
        
        order_list = []
        for m in filtered_markets:
            order = {}
            order["team1"] = m["runners"][0]["runnerName"]
            order["team2"] = m["runners"][1]["runnerName"]

            comp_full_name = m["competition"]["name"]
            org, competition = comp_full_name.split(" ",1) #to remove the country prefix, eg Argentinian La Liga 1

            if "countryCode" in m["event"]:
                order["country_code"] = m["event"]["countryCode"]
            else:
                order["country_code"] = org
            order["competition"] = competition
            order["competition_prefix"] = org
            
            full_date_time = m["event"]["openDate"].strip("Z")

            date, time = full_date_time.split("T")
            
            date = int(date.replace("-", ""))

            time,_ = time.split(".") #to remove the milliseconds

            order["date"] = date
            order["time"] = time
            order["market_id"] = m["marketId"]
            order["market_name"] = m["marketName"]

            order_list.append(order)

        return order_list
    
    def new_orders(self) -> list:
        """Gets all matches from the api and checks them against the already sent orders stored in the sent_orders file. Any new market_ids are returned in a list as new orders
        
        """
        all_website_orders = self.api_match_list()

        if os.path.exists(self.sent_orders_path):

            with open(self.sent_orders_path, "rb") as f:
                sent_orders = pickle.load(f)

        else:

            with open(self.sent_orders_path, "wb") as f:
                pickle.dump(list(), f)
            sent_orders = []

        sent_orders = utilities.order_list_cleaning(sent_orders)

        sent_Ids = set()
        for sent in sent_orders:
            sent_Ids.add(sent["market_id"])

        new_unique_orders = []
        for new in all_website_orders:
            if new["market_id"] not in sent_Ids:
                new_unique_orders.append(new)

        #add all unique orders to the sent orders list and save
        with open(self.sent_orders_path, "wb") as f:
            sent_orders.extend(new_unique_orders)
            pickle.dump(sent_orders, f)

        return new_unique_orders

    def new_orders_check(self) -> None:
        """Pings for any new orders and adds them to the io output. Waits self.new_orders_delay before pinging again"""

        while not self.stop_flag.is_set():
            new_orders = self.new_orders()
            
            self.io.append_output(new_orders)

            self.stop_flag.wait(timeout=self.new_orders_delay)

    def market_monitoring(self, order: dict) -> None:
        """Function intended to make use of the received orders to monitor the markets for good odds and invest etc."""
        raise NotImplementedError



    def market_book(self, marketIds: list):
        raise NotImplementedError



    def close(self) -> None:
        for p in self.p_list:
            p.join()

        self.logout()
        
if __name__ == "__main__":
    bot = BetfairBot()
    print("starting betfair")
    bot.start()
