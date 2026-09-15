import sys


sys.path.append("") #add betting folder to path

import requests
import pandas as pd
import time
import os
import posixpath
from functools import wraps
import pathlib
import json
import datetime
import re
import heapq
import pickle
import sys
import pynput.keyboard as kb
from typing import Callable
import subprocess
import shutil
import pytz
import sqlite3 as sq
import timeit
import decimal
import copy

import threading
import concurrent.futures
import multiprocessing

from bs4 import BeautifulSoup as bs
import bs4

from Utilities.unit_IO import processIO
from Utilities.unit_IO import orderHandling
from Utilities import utilities

import logging
import logging.config

from tkinter import *
from tkinter.ttk import Treeview

import matplotlib
matplotlib.use('agg')
import matplotlib.pyplot as plt
from matplotlib.axes import Axes
from matplotlib.figure import Figure
from matplotlib.backends.backend_tkagg import (FigureCanvasTkAgg,  
NavigationToolbar2Tk) 

from stem import Signal
from stem.control import Controller
from stem import process

from selenium import webdriver 
from selenium.common import exceptions 
from selenium.webdriver.firefox.options import Options
from selenium.webdriver.common.proxy import Proxy, ProxyType
from selenium.webdriver.common.by import By
from selenium.webdriver.firefox.firefox_profile import FirefoxProfile


def setup_logging() -> logging.Logger:
    config_file = ".logging_configs/config.json"
    with open(config_file) as f_in:
        config = json.load(f_in)
    logging.config.dictConfig(config)
    return logging.getLogger("RefScraper")

def log(func):
    @wraps(func)
    def wrapper(*args, **kwargs):
        # saved_args = locals()
        logger.info("Running: " + func.__name__)
        try:
            return func(*args, **kwargs)
        except Exception as e:
            logger.exception(e)#"Args: " + str(saved_args))
            raise
    return wrapper

logger = setup_logging()


def timing(func):
    @wraps(func)
    def wrapper(*args, **kwargs):
        start = time.time()
        try:
            return func(*args, **kwargs)
        finally:
            end = time.time()
            print(func.__name__ + " : " + "{:.2e}".format(end-start))

    return wrapper



class FindingError(Exception):
    """Exception raised when relevant tags are not found or found too often on website"""
    pass

class TableUnknownKeyError(Exception):
    """Occurs when a competition/seasons table has an unhandled key"""
    pass

class OrderNotFoundError(Exception):
    """Raised if the order cannot be found for any reason, eg. competition not on website or the website is missing the current season etc."""
    pass

class HttpTimeoutsError(Exception):
    """Occurs when the http request timeouts too many times"""
    pass

class StoppingException(Exception):
    """Exception used to stop operation"""
    pass

class ScrapingServerError(Exception):
    """Raised when site returns an error response"""
    pass





class TorBrowser():
    """A browser object which handles the socks5 tor proxy requests. Multiple instances of this class can coexist without breakage.
    The class has a few attributes relating to the speed and buffer size of the http requests that can be tweaked as necessary in order to respect any bitrate.
    
    """

    #print("tor")
    id_num = 0
    status_dict = {} #maps id_num -> dict where dict contains keys for name, url status, tries and renews
    change_flag = threading.Event() #change_flag is used to alert a listening program to any changes

    TB_DIR = "" #path to tor-browser
    TB_PROFILE_DIR = posixpath.join(TB_DIR, "Browser/TorBrowser/Data/Browser/profile.default")
    TB_BINARY = posixpath.join(TB_DIR, 'Browser/firefox')

    curr_socks_port = 9052 #start ports, stör ej de vanliga portsen
    curr_ctrl_port = 9053

    HTTP_TIMEOUT = 120 #in seconds
    TRIES = 2
    RENEWTRIES = 1
    
    REQUESTS_PER_MIN = 10 #keep this low, saw my life flash before my eyes when 403 showed once
    DELAY = 60/REQUESTS_PER_MIN #delay between timer calls in seconds
    MAX_REQUESTS_STORED = 5

    history_path = "Scraper/.history"
    history_time_start = None
    history_lastpos = 0
    history_length = 120
    history_requests_list = [0]*history_length #history length in minutes

    tokens = 0
    tokens_space = threading.Event()
    tokens_space.set()
    tokens_has = threading.Event()
    tokens_lock = threading.Lock()
    tokens_consume_lock = threading.Lock()

    timer_started = False

    @classmethod
    def add_token(cls): #Token bucket implementation
        
        cls.tokens_space.wait()
        with cls.tokens_lock:
            cls.tokens += 1
            cls.tokens_has.set()

        if cls.tokens == cls.MAX_REQUESTS_STORED:
            cls.tokens_space.clear()

        timer = threading.Timer(cls.DELAY, cls.add_token)
        timer.daemon = True
        timer.start()
        TorBrowser.change_flag.set()

    @classmethod
    def readd_token(cls):
        with cls.tokens_lock:
            if cls.tokens < cls.MAX_REQUESTS_STORED:
                cls.tokens += 1
                cls.tokens_has.set()
            if cls.tokens == cls.MAX_REQUESTS_STORED:
                cls.tokens_space.clear()

    @classmethod
    def http_history_add(cls):
        now = time.time()

        #spara listan som en förflyttande punkt, måste ha en variabel för vad positionen var förra anropet
        currpos = round(((now-cls.history_time_start)%(cls.history_length*60))//60)

        if currpos != cls.history_lastpos:
            cls.history_requests_list[currpos] = 0
            cls.history_lastpos = currpos

        cls.history_requests_list[currpos] += 1


    @log
    def __init__(self, stop_flag: utilities.BetterEvent):
        
        self.id_num = TorBrowser.id_num
        self.sdict = {"name": "driver_" + str(self.id_num), "url": "", "status": "ready", "tries": "", "renews": ""} #values must be strings
        TorBrowser.status_dict[self.sdict["name"]] = self.sdict

        self.socks_port = TorBrowser.curr_socks_port
        self.ctrl_port = TorBrowser.curr_ctrl_port

        self.parser = "html.parser"
        self.stop_flag = stop_flag

        self.http_stat_path = "Scraper/.http_stat"
        
        self.tor_process = self.start_tor_process()
        self.driver = self.driver_setup()

        TorBrowser.curr_socks_port += 2
        TorBrowser.curr_ctrl_port += 2

        TorBrowser.id_num += 1

        if not TorBrowser.timer_started:
            self.add_token()
            TorBrowser.timer_started = True
        
        if TorBrowser.history_time_start is None:
            TorBrowser.history_time_start = time.time()

    @log
    def driver_setup(self):
        """Sets up the selenium driver with the tor settings and socks proxy
        
        """
        profile = FirefoxProfile(self.TB_PROFILE_DIR)
        profile.set_preference('network.proxy.type', 1) #these preferences seem to be correct already in the browser, except the port
        profile.set_preference('network.proxy.socks', '127.0.0.1')
        profile.set_preference('network.proxy.socks_port', self.socks_port)
        profile.set_preference("network.proxy.socks_remote_dns", True)

        options = Options()
        options.binary_location = self.TB_BINARY
        options.profile = profile

        options.page_load_strategy = "normal"
        options.add_argument("--headless")

        driver = webdriver.Firefox(options=options)
        driver.set_page_load_timeout(self.HTTP_TIMEOUT)

        return driver

    @log
    def start_tor_process(self) -> subprocess.Popen:
        """Returns a tor subprocess using the instance socks and control ports"""
        return process.launch_tor_with_config(
            config = {
                "ControlPort": str(self.ctrl_port),
                "SocksPort": str(self.socks_port),
                "HashedControlPassword": "",
                "SafeSocks": "1",
                "DataDirectory": "" + #path to .tor/custom
                                    str(self.socks_port) 
            }, timeout=None #No idea why setting no timeout fixed the timeout error when starting the process
        )




    @log
    def http_get(self, url: str, tries: int = 0, ip_renews: int = 0) -> bs4.BeautifulSoup:
        """Returns html string from http get with corresponding headers and data
        
        Raises: HTTP error, if http method returns error
        """
        if ip_renews > self.RENEWTRIES:
            utilities.email_msg("Browser has renewed ip > renewtries times")
            raise HttpTimeoutsError("ip renews > renewtries")

        if tries == self.TRIES:
            #print("renewing ip", self.id_num, datetime.datetime.now())
            self.renewIP()
            return self.http_get(url, tries=0, ip_renews=ip_renews+1)

        self.sdict["status"] = "waiting"
        self.sdict["url"] = url

        tries_list = []

        self.sdict["renews"] = str(ip_renews)
        self.sdict["tries"] = str(tries)
        logger.info("http_get for url: " + url)

        TorBrowser.change_flag.set()
        with TorBrowser.tokens_consume_lock:
            TorBrowser.tokens_has.wait()
            with TorBrowser.tokens_lock:
                TorBrowser.tokens -= 1
                TorBrowser.tokens_space.set()
                if TorBrowser.tokens == 0:
                    TorBrowser.tokens_has.clear()

        self.sdict["status"] = "getting"

        if self.stop_flag.is_set():
            raise StoppingException("Stopping, browser")

        start = time.time()
        try:
            self.driver.get(url)
            response = self.driver.page_source
            html = bs(response, self.parser)
            h1 = html.find("h1")
            try:
                title = h1.text
            except AttributeError as e:
                if "Just a moment..." in html.find("title"):
                    print(html.find("title"), type(html.find("title")))
                    raise ScrapingServerError("Just a moment")
                print(len(html.find_all("title")))
                print(html.find_all("title"))
                with open("html", "wb") as f:
                    pickle.dump(html, f)
                print("nonetype") #cloudflare problem?
                raise e
            
            logger.info("Title name for " + url + " : " + title + ", " + str(type(title)))
            #500 internal server error, 502 cloudflare bad gateway, 522 cloudflare connection to origin server timed out,
            #504 gateway timeout, 403 forbidden, 404 not found, 524 timeout occurred, Error/1018 cloudflare error
            errors = ["403", "404" "500", "502", "504" "522", "524", "Forbidden", "Error", "error"] #403 not working? 404 not working?
            for error in errors:
                if error in title:
                    #print(h1.text)
                    print(time.localtime(time.time()), error, url)
                    raise ScrapingServerError(error)

            status = "success"
            self.http_history_add()

        except exceptions.TimeoutException as e:
            status = "timeout"
            self.readd_token()
        except exceptions.WebDriverException as e:
            #print("exception", self.id_num, datetime.datetime.now(), e)
            status = "webdriverexception"
            self.readd_token()
        except ScrapingServerError as e:
            status = "servererror"
            self.readd_token()

        time_taken = time.time() - start
        tries_list.append(time.asctime(time.gmtime(start)) + "," + str(time_taken) + "," + status + "\n")
        

        with open(self.http_stat_path,"a+") as f:
            for line in tries_list: #Document the time taken for a request, for statistics purposes
                f.write(line)
        
        if status == "success":
            self.sdict["url"] = ""
            self.sdict["status"] = "ready"
            self.sdict["tries"] = ""
            self.sdict["renews"] = ""
            TorBrowser.change_flag.set()


            logger.info("responded for url: " + url)
            return html
        else:
            return self.http_get(url, tries=tries+1, ip_renews=ip_renews)

    @log
    def renewIP(self) -> None:
        """Renews the tor_browser attribute with a new ip"""
        self.driver.close()

        with Controller.from_port(port = self.ctrl_port) as controller:
            controller.authenticate(password="")
            controller.signal(Signal.NEWNYM)
        
        self.driver = self.driver_setup()



    @log
    def http_stat_avg(self) -> float:
        """Returns an average of the time taken for http_get requests, including timeouts

        """
        stat_list = []

        with open(self.http_stat_path,"r") as f:
            for line in f:
                stat_list.append(float(line.strip("\n").split(",")[1]))
        
        stat_sum = sum(stat_list)
        avg = stat_sum/len(stat_list)

        return avg
    
    @log
    def http_stat_numrequests_dict(self) -> dict[int: int]:
        """Sums the number of successful requests for every minute and returns a dict, 0 is the most recent request showing the past at higher minutes on the x-axis
        Currently also brings up a plot with minutes on the x-axis and counts on the y-axis
        """
        counts_dict = {}
        min_dict = {}
        far_back = 40 #number of minutes to go back
        
        with open(self.http_stat_path,"r") as f:
            most_recent = 0
            lines = []
            for line in f:
                lines.append(line)
                entry_list = line.strip("\n").split(",")
                date = time.strptime(entry_list[0])
                challenger = time.mktime(date)
                if challenger > most_recent:
                    most_recent = challenger

            for j in range(far_back+1):
                counts_dict[j] = 0
                min_dict[j] = j

            for line in lines:
                entry_list = line.strip("\n").split(",")
                date = time.strptime(entry_list[0])
                dateint = time.mktime(date)

                if most_recent-dateint < far_back*60 and entry_list[2] == "success": #inom området
                    index = round((most_recent-dateint)/60, ndigits=None)
                    counts_dict[index] +=1

        df = pd.DataFrame.from_dict(data={"minute": min_dict, "counts": counts_dict})
        df.plot(x="minute",y="counts")
        plt.show(block=True)
        plt.close("all")

        return counts_dict




    @log
    def close(self) -> None:
        """Exits the webdriver and kills the tor subprocess 
        
        """

        self.driver.quit()
        self.tor_process.terminate()



class RefScraper(orderHandling):
    """Uppgift för denna klass:
    Få ut strukturerad och konsekvent data som kan både användas till modellen och kopplas till bettingskrapares matcher senare.
    Fokusera på att bara få ut användbar information här.

    """

    def __init__(self):
        self.stop_flag = utilities.BetterEvent(multiprocessing) #set if the process should exit
        self.error_flag = utilities.BetterEvent(multiprocessing) #set if an error occurred in the process which triggered the stop flag, otherwise should be unset

        self.base_path = "Scraper"
        self.version = "1.1"

        self.base_url = "https://fbref.com"
        self.comps_url = "https://fbref.com/en/comps/"

        self.parser = "html.parser" #to stop beautiful soup from bitching
        self.encoding = "utf-8"

        self.db_path = "scraper.db"
        self.db_conn, self.db_cur = utilities.db_access_init(self.db_path)



        self.input_address_name = "input_scraper"
        self.order_select_query = "SELECT * FROM order_table WHERE scraped_match_id IS NULL"

        
        self.orderhandling_function = self.order_competitions

        self.base_expiration_time = 60*60*24 #time in seconds before a cache is considered expired, -1 to never expire
        self.competitions_expiration_time = 60*60*24
        self.seasons_expiration_time = -1 #still scrapes again if the season is not found in the cache
        self.season_expiration_time = -1
        self.fixtures_expiration_time = -1 #still always scrapes the newest season
        self.match_expiration_time = -1



        self.drivers = []
        for i in range(4):
            self.drivers.append(TorBrowser(self.stop_flag))

        self.change_flag = threading.Event()
        self.status_dict = {"curr_country_str": "", "curr_gender_str": "", "curr_comp_str": "", "curr_season_str": "", "comps_left_str": "", "seasons_left_str": "", "matches_left_str": "", "order_country_code": "", "order_comp_str": "", "order_home_team": "", "order_away_team": "", "order_date": "", 
                            "order_prefix_str": "", "order_time_str": "", "curr_comps_unfinished": [], "curr_comps_finished": [], "orders_left": ""
                            }
        self.window_thread = threading.Thread(target=StatusWindow, args=(self,), daemon=True)
        self.window_thread.start()


        """Varningsfilosofi: För att undvika att saknad information ger upphov till upprepade errors då informationen aldrig är tillgänglig, implementerar vi ett system med varningar där 
        filväg samt varningskod sparas i en fil. Varningskoderna är associerade med specifika fel och bör därför enkelt kunna redogöra ifall något har förändrats på sidan eller inte. Detta ger en 
        möjlighet för att eventuellt i framtiden kolla igenom varningarna för att få tillgång till nyfunnen information som tidigare saknats. För att undvika att alldeles för mycket information sparas i onödan
        , exempelvis är det osannolikt att en gammal match får nyfunnen detaljerad speldata såsom shots osv, så sparas endast varningar för de mest allvarliga avsaknaderna. Anledningen till att varning
        inte sparas för mindre information är alltså låg relevans samt lång väntetid i förhållande till de fel som varningar sparas för som har hög relevans. 

        Varningsraden i warnings är kopplad till en match genom match_id med värden för varje varning i respektive kolonn

        #start_index (inclusive) - (to) end_index (inclusive)
        #0-3 dataframe_from_team_table
        #4-5 team_tables_on_page
        #6 shots_on_pag
        #7 data_for_all_matches
        #8, 10,11 formations_on_page
        #9 timeline_on_page

        season_warnings
        #0 

        info_dict warning_codes:
                            0: "No rows found in tbody for Home_Players", 1: "No rows found in tbody for Home_Goalkeeper",
                            2: "No rows found in tbody for Away_Players", 3: "No rows found in tbody for Away_Goalkeepers",

                            4: "No match tables found", 5: "Unexpected number of keeper or player tables"

                            6: "No shots table"

                            7: "Fixtures link tag not found"

                            8: Wrong number of formation fields found, 10: Home formation missing, 11: Away formation missing

                            9: No timeline on page
                            
        season_warnings:    
                            0: "Fixtures link tag not found"
                            """
        
        




#Scraping functions
    @log
    def all_competitions(self, comps_html: bs4.Tag) -> list: #hitta alla länkar med data-stat="league_name"
        """Finds relevant competition tables on page and returns a list with dict for each competition

        Currently skips table 3 corresponding to the "Big 5 European Leagues" table
        """

        tables = comps_html.find_all(class_ = "table_container")
        tables.pop(2) #remove big 5 european leagues table, it's just redundant information
        
        #tables_list = []
        all_rows = []

        for t in tables:
            table_html = t.find("tbody")

            rows_html = table_html.find_all("tr")

            rows_list = []

            for r in rows_html:

                if r["class"] == ["thead"]: #To skip separatingrows inside a table
                    continue

                datas = r.find_all(attrs = {"data-stat": True})
                row_dict = {}

                for d in datas:
                    key = str(d["data-stat"])
                    value = None

                    match key:
                        case "league_name":
                            key_name = "competition_name"
                            value = d.string
                            row_dict["seasons_link"] = self.base_url + d.find("a")["href"]

                        case "country":
                            key_name = "country_code"
                            try:
                                value = d.find_all("a")[0].string
                                value = value.upper()
                            except IndexError:
                                value = None

                        case "governing_body":
                            key_name = "country_code"
                            value = d.string

                        case "gender":
                            key_name = "gender"
                            value = d.string
                        
                        case "minseason":
                            key_name = "min_season"
                            value = d.string

                        case "maxseason":
                            key_name = "max_season"
                            value = d.string

                        case "tier":
                            key_name = "tier"
                            value = d.string

                        case "awards":
                            key_name = "awards"
                            value = d.string
                        
                        case _:
                            raise TableUnknownKeyError("Unknown table key for competition")

                    value = str(value)
                    row_dict[key_name] = value
                
                rows_list.append(row_dict)

            all_rows.extend(rows_list)
            #tables_list.append(rows_list)

        return all_rows

    @log
    def all_seasons(self, seasons_html: bs4.Tag) -> list:
        """Returns a list of dictionaries with entries from table
        Most importantly the "season_link" entry gives the season link
        And "season_name" gives the season year string
        """
        tables = seasons_html.find_all(class_ = "table_container")
        
        try:
            t = tables[0] #funkar inte ifall competitionen är seasonen
        except IndexError as e:
            raise OrderNotFoundError("Competition page is the season")
        table_html = t.find("tbody")
        rows_html = table_html.find_all("tr", attrs={"class": False})

        rows_list = []

        for r in rows_html:
            datas = r.find_all(attrs = {"data-stat": True})
            row_dict = {}

            for d in datas:
                key = d["data-stat"]
                key = str(key)
                value = None
                value = str(d.string)
                if key == "league_name" or key == "comp_name":
                    url_addition = d.find("a")["href"]
                    row_dict["season_link"] = self.base_url + url_addition
                    continue
                
                elif key == "year_id" or key == "year":
                    row_dict["season_name"] = value
                    continue


                row_dict[key] = value
            
            rows_list.append(row_dict)
        return rows_list

    @log
    def scores_and_fixtures_link(self, pre_fixtures_html: bs4.Tag) -> str:
        """
        Finds the a-tag with the "Scores and Fixtures" text and returns the link/part of the link
        """
        soup = pre_fixtures_html
        
        def has_fixtures_text(tag):
            return tag.has_attr("class") and tag["class"] == ["full"] and tag.contents[0].string == "Scores & Fixtures"
        
        tags = soup.find_all(has_fixtures_text)

        if len(tags) == 0:
            raise OrderNotFoundError("Link tag not found")
        elif len(tags) != 1:
            raise OrderNotFoundError("Too many link tags found")
        else:
            link = tags[0].contents[0]["href"]
            return self.base_url + link

    @log
    def match_rows_from_fixtures(self, fixtures_html: bs4.Tag) -> list:
        """
        Returns all match rows from a fixtures page in the form of info_dicts using the summary tables id="div_sched_all" and "table_container" class
        """

            
        table_dict = {}
        tables = fixtures_html.find_all("table")

        if len(tables) != 1: #try to narrow the search down to one table at a time
            switchers = fixtures_html.find_all(class_="sr_preset")
            for s in switchers: #get the matches from each switcher and do a sanity test later
                # if s.text not in ["Qualifying rounds", "Group stage", "All Rounds", "Knockout phase", "Regular season", "Championship round", "Relegation round"]:
                #     raise NotImplementedError("Switcher tab not accounted for")
                schedule_name = s.attrs["data-show"].replace(".assoc_", "")
                tables = fixtures_html.find_all("table", id=schedule_name)

                if len(tables) > 1:
                    raise NotImplementedError("Several fixtures tables with same schedule name")
                elif len(tables) == 0:
                    raise NotImplementedError("No fixtures tables with schedule name")
                else:
                    table = tables[0]

                table_dict[s.text] = table
        else:
            table_dict["All Rounds"] = tables[0]
        
        match_rows_dict = {}
        for key in table_dict: #process each table found
            table = table_dict[key]
        
            tbodys = table.find_all("tbody")
            if len(tbodys) != 1:
                raise FindingError("wrong number of tbodys")
            
            tbody = tbodys[0]
            rows = tbody.find_all("tr", class_=False)
            if len(rows) == 0:
                raise FindingError("didn't find any rows")
        
            match_rows = []
            for r in rows:
                info = self.info_dict(r)
                match_rows.append(info)
                
            match_rows_dict[key] = match_rows

        final_match_rows = []
        if len(match_rows_dict) > 1: #determine which tabs go into the final output
            num = 0
            for key in match_rows_dict:
                if key == "All Rounds":
                    continue
                else:
                    num += len(match_rows_dict[key])
            

            if num != len(match_rows_dict["All Rounds"]): #some tabs contain extra matches, likely qualifying tab
                if "Qualifying rounds" in match_rows_dict and num-len(match_rows_dict["Qualifying rounds"]) == len(match_rows_dict["All Rounds"]):
                    final_match_rows = match_rows_dict["Qualifying rounds"]
                    final_match_rows.extend(match_rows_dict["All Rounds"])
                elif "Qualifying stages" in match_rows_dict and num-len(match_rows_dict["Qualifying stages"]) == len(match_rows_dict["All Rounds"]):
                    final_match_rows = match_rows_dict["Qualifying stages"]
                    final_match_rows.extend(match_rows_dict["All Rounds"])
                elif "Qualifying round" in match_rows_dict and num-len(match_rows_dict["Qualifying round"]) == len(match_rows_dict["All Rounds"]):
                    final_match_rows = match_rows_dict["Qualifying round"]
                    final_match_rows.extend(match_rows_dict["All Rounds"])
                else:
                    with open("fixtures", "wb") as f:
                        pickle.dump([fixtures_html], f)
                    raise NotImplementedError("Each tabs matches minus qualifying does not equal all rounds matches, dumped fixtures") #https://fbref.com/en/comps/8/1996-1997/schedule/1996-1997-Champions-League-Scores-and-Fixtures
            else:
                final_match_rows.extend(match_rows_dict["All Rounds"])
        else:
            final_match_rows.extend(match_rows_dict["All Rounds"])
        
        return final_match_rows




#Team dataframes and tables in match

    @log
    def team_tables_on_page(self, match_html: bs4.BeautifulSoup, warning_dict: dict = None) -> tuple:
        """Returns dictionary for keys: (using id=all_player_stats_... or id=all_keeper_stats_...)
        "Home_Players": h_player_table
        "Home_Goalkeeper": h_goalkeeper_table
        "Away_Players": a_player_table
        "Away_Goalkeeper": a_goalkeeper_table

        Every table contains subtables (table_container with id=... misc/passing etc) which contain tr tags for every row. In case of recognized problems 
        sets warning_dict WARNING to 1 and appends an warning code to warning_triggers. Manages the following warning codes:
        4: "No match tables found", 5: "Unexpected number of keeper or player tables". For 5 the number of tables is always 0<=x<=2 but not for both keepers and players
        """

        if warning_dict is None: #för självständig användning av funktionen, warning_triggers finns annars sedan warning_dicts skapelse
            warning_dict = {}
        
        player_tables = match_html.find_all(lambda t: t.has_attr("id") and re.match('all_player_stats_.*',t["id"]))
        goalkeeper_tables = match_html.find_all(lambda t: t.has_attr("id") and re.match('all_keeper_stats_.*',t["id"]))

        tables = {}

        if len(player_tables) > 2 or len(goalkeeper_tables) > 2: #har inte sett något sådant än
            raise FindingError("Major problem with right number of keeper or player tables, player, keeper: " + str(len(player_tables)) + ", " + str(len(goalkeeper_tables)))
        
        elif len(player_tables) == 0 and len(goalkeeper_tables) == 0:
            #logger.warning("No keeper or player tables found, player, keeper: " + str(len(player_tables)) + ", " + str(len(goalkeeper_tables)))
            #tables["Warning"] = True
            warning_dict["four"] = 1 #"No match tables found"

        elif len(player_tables) != 2 or len(goalkeeper_tables) != 2: # >2 tas hand om tidigare
            #logger.warning("Didn't find expected number of keeper or player tables, player, keeper: " + str(len(player_tables)) + ", " + str(len(goalkeeper_tables)))
            warning_dict["five"] = 1#"Unexpected number of keeper or player tables: " + str(len(player_tables)) + ", " + str(len(goalkeeper_tables)))
            # tables["Warning"] = True

            if len(goalkeeper_tables) == 1 and len(player_tables) == 2: #Borde gå att göra på andra hållet också
                found_team_id = goalkeeper_tables[0]["id"].split("_")[-1]
                home_team_id = player_tables[0]["id"].split("_")[-1]
                away_team_id = player_tables[1]["id"].split("_")[-1]

                tables["Home_Players"] = player_tables[0]
                tables["Away_Players"] = player_tables[1]

                if found_team_id == home_team_id:
                    tables["Home_Goalkeepers"] = goalkeeper_tables[0]
                elif found_team_id == away_team_id:
                    tables["Away_Goalkeepers"] = goalkeeper_tables[0]
                else:
                    raise FindingError("No matching team id for found goalkeeper table")
                
            elif len(player_tables) == 2 and len(goalkeeper_tables) == 0:
                tables["Home_Players"] = player_tables[0]
                tables["Away_Players"] = player_tables[1] #troligen tomma tables
            
            elif len(goalkeeper_tables) == 2 and len(player_tables) == 1:
                raise NotImplementedError("The impossible has happened")
        else:
            tables["Home_Players"] = player_tables[0]
            tables["Away_Players"] = player_tables[1]
            tables["Home_Goalkeepers"] = goalkeeper_tables[0]
            tables["Away_Goalkeepers"] = goalkeeper_tables[1]

        return tables, warning_dict

    @log
    def player_dict_from_team_tables(self, tables: dict, warning_dict: dict = None) -> dict:
        """Returns a dict with the keys "Home_Players", "Home_Goalkeepers", "Away_Players", "Away_Goalkeepers" giving a list for each player's dict from a table.
        Raises FindingError if wrong number of tbody elements are found. In case of managed exception issues a warning and appends the code to warning_dicts warning_triggers set. 
        Manages the following warning codes: 0, 1, 2, 3

        """

        if warning_dict is None: #för självständig användning av funktionen, warning_triggers finns annars sedan warning_dicts skapelse
            warning_dict = {}

        #table_types = ["Home_Players", "Home_Goalkeepers", "Away_Players", "Away_Goalkeepers"]
        warning_code_num = {"Home_Players": "zero", "Home_Goalkeepers": "one", "Away_Players": "two", "Away_Goalkeepers": "three"}

        team_dict = {}

        for t in tables:
            table_html = tables[t]


            subtables = table_html.find_all(class_="table_container")
            player_list = []
            skip = False

            for sub in subtables:
                rows = []
                tbodies = sub.find_all("tbody")
                
                if len(tbodies) != 1:
                    raise FindingError("Wrong number of tbodies found in table_container")
                
                tbody = tbodies[0]

                rows = tbody.find_all("tr")

                if len(rows) == 0:
                    warning_dict[warning_code_num[t]] = 1
                    skip = True
                    continue

                    #raise FindingError("No rows found in tbody")

                for i, player in enumerate(rows):

                    datas = player.find_all(lambda t: t.has_attr("data-stat"))
                    row_dict = {}

                    if "Home" in t:
                        row_dict["ground"] = "home"
                    elif "Away" in t:
                        row_dict["ground"] = "away"
                    
                    for d in datas:
                        data_stat = d["data-stat"]
                        text = None
                        match data_stat:
                            case "player":
                                text = d.text #to get in the order first name, last name
                                text = text.replace("\xa0", "")

                                row_dict.update({"player_name": text})
                                continue

                            case "nationality":
                                try:
                                    text = list(d.find(class_="f-i").parent.stripped_strings)[1] #sometimes date of birth and/or nationality are missing
                                except AttributeError:
                                    text = None #Insignificant, don't issue a warning for this

                            case _:
                                text = d.string
                        
                        if text == None: #to prevent None strings in database
                            continue
                        text = str(text)
                        row_dict[data_stat] = text

                    #found = False #assuming that the players are all in the same order regardless of subtable, subtable example: https://fbref.com/en/matches/26cacbb5/Lille-Montpellier-September-3-2023-Ligue-1
                    if len(player_list) > i:
                        player_list[i].update(row_dict)
                    else:
                        player_list.append(row_dict) #removed check for subtables since player's with same name are otherwise just updated over each other. Example of 2 michels: https://fbref.com/en/matches/b3efacd0/Sevilla-Getafe-September-14-2014-La-Liga
                    # for p in player_list: #updates if the previous player is found again, this is to account for subtables and then just update the player stats
                    #     if row_dict["player_name"] == p["player_name"]:
                    #         p.update(row_dict)
                    #         found = True
                    #         break
                    
                    # if found == False:
                    #     player_list.append(row_dict)
            
            if not skip:
                team_dict[t] = player_list

        return team_dict, warning_dict

    @log
    def formations_on_page(self, match_html: bs4.BeautifulSoup, warning_dict: dict = None) -> tuple:
        """"Returns a tuple with the first index being a dict of the home and away team's formation string, starters and benched players. The second index is the returned warning_dict, although the original warning_dict dictionary is changed as well.
        In case of warning code 8 the first index list will be empty. Has the structure: dict["Home", "Away"] -> dict["Starters", "Benched", "Formation"], formation is string and starter and benched are lists with a tuple of 
        (player_num, player_name)
        WARNING CODES:
        8: Wrong number of formation fields found
        10,11
        
        """

        def lineup_processing(lineup_rows: list, warning_dict: dict, team_str: str) -> list:
            """Returns the formation string, starter players and benched players in a list"""
            bench_players = False

            starters = []
            benched = []

            res_dict = {}

            for row in lineup_rows:

                if len(row.contents) == 1:
                    tag = row.contents[0]

                    if tag.name == "th" and tag.text != "Bench": #Team header and formation string
                        if "(" not in tag.text:
                            if team_str == "HOME_TEAM":
                                warning_dict["ten"] = 1
                            elif team_str == "AWAY_TEAM":
                                warning_dict["eleven"] = 1
                            else:
                                raise NotImplementedError("Wtf?")

                        else:    
                            formation = tag.text.split("(")[1].strip(")")
                            res_dict["Formation"] = formation
                    elif tag.name == "th" and tag.text == "Bench":
                        bench_players = True
                
                else:

                    tags = row.find_all("td")

                    player_num = tags[0].text
                    player_name = tags[1].find("a").text

                    if bench_players:
                        benched.append((player_num, player_name)) #not using player_num
                    else:
                        starters.append((player_num, player_name))

                    res_dict["Starters"] = starters
                    res_dict["Benched"] = benched

            return res_dict


        if warning_dict is None: #för självständig användning av funktionen, warning_triggers finns annars sedan warning_dicts skapelse
            warning_dict = {}

        fields = match_html.find_all(id = "field_wrap")

        if len(fields) != 1:
            warning_dict["eight"] = 1

            return (None, warning_dict)
        else:
            field = fields[0]

            home_rows = field.find(id = "a").find_all("tr")
            away_rows = field.find(id = "b").find_all("tr")

            home_lineup = lineup_processing(home_rows, warning_dict, "HOME_TEAM")
            away_lineup = lineup_processing(away_rows, warning_dict, "AWAY_TEAM")

            return ({"Home": home_lineup, "Away": away_lineup}, warning_dict)

    @log
    def timeline_on_page(self, match_html: bs4.BeautifulSoup, warning_dict: dict = None) -> tuple:
        """Returns a tuple with the first index being a list of dictionaries containing the event types, affected players and the event timestamp.
        The second index is the returned warning_dict, although the original warning_dict dictionary is changed as well"""

        if warning_dict is None: #för självständig användning av funktionen, warning_triggers finns annars sedan warning_dicts skapelse
            warning_dict = {}

        events_divs = match_html.find_all(id = "events_wrap")

        if len(events_divs) > 1:
            raise NotImplementedError("Too many events divs")
        elif len(events_divs) == 0:
            warning_dict["nine"] = 1
            return None, warning_dict

        event_rows = events_divs[0].find_all(class_=["event", "event_header"])

        events_list = []

        for e in event_rows:

            if "event_header" in e.attrs["class"]:
                section = e.text

            else: #Find which team the row belongs to
                if "a" in e.attrs["class"]:
                    team = "home"

                elif "b" in e.attrs["class"]:
                    team = "away"
                else:
                    raise NotImplementedError("No team indicator")

                divs = e.find_all("div")

                timestamp = list(divs[0].children)[0].get_text(strip=True).strip("’")

                event_dict = {}
                event_dict["timestamp"] = timestamp
                event_dict["ground"] = team
                event_dict["time_section"] = section

                event_type = divs[1].find(class_="event_icon").attrs["class"][1]

                player_divs = divs[1].find_all("div")[1]
                player = player_divs.find("div").get_text(strip=True)


                extra = player_divs.find_all("small")
                if len(extra) > 0:
                    if len(list(extra[0].children)) == 1: #plain comment text
                        pass
                    else: #anything else, like an extra player tag
                        text = list(extra[0].children)[1].text

                        if event_type == "substitute_in":
                            event_dict["player_in"] = text
                        elif event_type == "goal":
                            event_dict["assisting_player"] = text
                        # elif event_type == "own_goal":
                        #     pass
                        elif event_type == "penalty_miss":
                            event_dict["saved_by"] = text
                        # elif event_type == "penalty_goal":
                        #     pass
                        else:
                            raise NotImplementedError("extra not implemented")

                event_dict["event"] = event_type
                event_dict["player_name"] = player
                events_list.append(event_dict)

        return events_list, warning_dict

    @log
    def shots_on_page(self, match_html: bs4.BeautifulSoup, warning_dict: dict = None) -> tuple:
        """Returns a tuple with the first index being a list of rows of the shots table. The second index is the returned warning_dict, although the original warning_dict dictionary is changed as well
        
        Manages warning 6
        """

        def row_processing(row_html) -> dict:
            row_dict = {}

            for tag in row_html.children:
                key = tag["data-stat"]

                match key:
                    case "player":
                        value = tag.find("a").text
                        row_dict["player_name"] = value
                        continue

                    case "team":
                        value = tag.find("a").text

                    case _:
                        value = tag.text

                row_dict[key] = value

            return row_dict


        if warning_dict is None or "warning_triggers" not in warning_dict: #för självständig användning av funktionen, warning_triggers finns annars sedan warning_dicts skapelse
            warning_dict = {}



        shots_divs = match_html.find_all(id="div_shots_all")

        if len(shots_divs) > 1:
            raise NotImplementedError("more than 1 shots table")
        elif len(shots_divs) == 0:
            warning_dict["six"] = 1
            return None, warning_dict
        
        tbody = shots_divs[0].find("tbody")
        shots_html_rows = tbody.find_all(class_ = re.compile("shots_.+"))
        shots_rows = []

        for r in shots_html_rows:
            shots_rows.append(row_processing(r))

        return shots_rows, warning_dict

    @log
    def overview_text_on_page(self, match_html: bs4.BeautifulSoup, warning_dict: dict = None) -> tuple:
        """Gets manager, captain, officals, venuetext, aggregate and penaltyscore. Has structure dict[Attendance -> number, Venue -> text, Officials -> dict[job] -> name]"""

        if warning_dict is None: #för självständig användning av funktionen, warning_triggers finns annars sedan warning_dicts skapelse
            warning_dict = {}

        scoreboxes = match_html.find_all(name = "div", class_="scorebox")
        if len(scoreboxes) == 0:
            # first https://fbref.com/en/matches/a7f152e2/Hannover-96-Kaiserslautern-November-26-2005-Bundesliga
            # second https://fbref.com/en/matches/f49163bf/Paris-Saint-Germain-Strasbourg-August-14-2021-Ligue-1
            # 404 scoreboxes 3
            # 524 scoreboxes 4, overwritten now cloudflare error
            # 404 scoreboxes 5
            with open("scoreboxes6", "wb") as f: 
                pickle.dump([match_html], f)
            raise NotImplementedError("No scoreboxes, dumped")
        elif len(scoreboxes) > 1:
            raise NotImplementedError("Several scoreboxes")
        scorebox = scoreboxes[0]

        #get the small text below teams with attendance, venue, officials
        scorebox_metas = scorebox.find_all(class_ = "scorebox_meta")
        results_dict = {}
        if len(scorebox_metas) == 0:
            raise NotImplementedError("No scorebox meta")
        elif len(scorebox_metas) > 1:
            raise NotImplementedError("Several scorebox meta tags")
        else:
            divs = scorebox_metas[0].find_all("div")
            start = False
            for d in divs:
                text = d.get_text(strip=True)
                if text == "":
                    start = True
                elif start:
                    key, value = text.split(":")

                    if key not in ["Attendance", "Venue", "Officials"]:
                        raise NotImplementedError("Scorebox category not accounted for")

                    elif key == "Officials":
                        job_dict = {}
                        if value != "":
                            value = value.replace("\xa0", " ")
                            parts = value.split("·") #symbolen wtf?
                            for person in parts:
                                name, job = person.split("(")
                                name = name.strip(" ")
                                job = job.strip(")")
                                if job not in ["Referee", "AR1", "AR2", "4th", "VAR"]:
                                    raise NotImplementedError("Offical's job not accounted for")
                                job_dict[job] = name

                        results_dict[key] = job_dict
                    else:
                        results_dict[key] = value
        
        #get the manager, captain and scores
        divs = list(scorebox.children)
        divs_processed = []
        for d in divs:
            if d != "\n":
                divs_processed.append(d)

        if len(divs_processed) < 2:
            raise NotImplementedError("Number of scorebox divs < 2")
        team_divs = [divs_processed[0], divs_processed[1]] #home, away

        team_dicts = []
        for div in team_divs:
            team_dict = {}

            scores_dict = {}
            scores = div.find(class_="scores")
            score_children = scores.find_all("div")
            for s in score_children:
                keys = s.attrs["class"]
                #score double https://fbref.com/en/matches/213132ff/Real-Madrid-Rayo-Vallecano-December-20-2015-La-Liga
                key = keys[0]
                if key not in ["score", "score_xg", "score_aggr", "score_pen"]:
                    raise NotImplementedError("Score tag class not accounted for")

                value = s.text
                scores_dict[key] = value
            team_dict["SCORES"] = scores_dict

            datapoints = div.find_all(class_="datapoint")

            for d in datapoints:
                text = d.text

                title, name = text.split(":")

                title = title.replace("\xa0", " ").strip(" ")
                name = name.replace("\xa0", " ").strip(" ")

                if title not in ["Manager", "Captain"]:
                    raise NotImplementedError("Title not accounted for")

                team_dict[title] = name


            team_dicts.append(team_dict)

        results_dict["HOME_TEAM"] = team_dicts[0]
        results_dict["AWAY_TEAM"] = team_dicts[1]

        return results_dict, warning_dict
        







#Internal functions
    @log
    def info_dict(self, fixtures_row_html: bs4.Tag) -> dict:
        """Returns a dict with information regarding
        Date, Venue, Time, Home team, Away team osv from a fixtures match row from a html fixtures summary table. Adds these keys: LINK, FINISHED, WARNING, warning_triggers.

        """
        row = fixtures_row_html
        datas = row.find_all(name=["td", "th"], attrs={"data-stat": True})

        info_dict = {}

        for d in datas:
                key = str(d["data-stat"])
                value = None

                match key:
                    case "home_team":
                        value = d.find("a").string
                        info_dict["home_name"] = str(value)
                        value = d.find("a")["href"].split("/")[3]
                        info_dict["home_fbref_id"] = str(value)
                        continue

                    case "away_team":
                        value = d.find("a").string
                        info_dict["away_name"] = str(value)
                        value = d.find("a")["href"].split("/")[3]
                        info_dict["away_fbref_id"] = str(value)
                        continue

                    case "match_report":
                        if d.string == "Match Report":
                            info_dict["match_link"] = self.base_url + d.find("a")["href"]
                            value = d.string

                        elif d.string == "Head-to-Head":
                            value = d.string
                        else:
                            value = d.string

                        info_dict["match_report"] = str(value)
                        continue

                    case "start_time":
                        try:
                            value = str(d["csk"])
                        except KeyError:
                            value = None

                        tags = d.find_all(attrs={"data-venue-epoch": True})
                        if len(tags) != 0:
                            info_dict["epoch"] = int(tags[0]["data-venue-epoch"]) #epoch is a float according to database specification

                    case "date": #specifying the keys here allows us to control them later in case the website changes. Date should always be in the format YYYYMMDD
                        date = str(d.string)
                        info_dict["date"] = int("".join(date.split("-"))) #date is an integer according to database specification
                        continue

                    case "score":
                        value = d.text #don't know why string is used everywhere else, just use text here instead
                        if value != "":
                            scores = value.split("–") #konstigt mellanstreck

                            info_dict["home_score"] = scores[0]
                            info_dict["away_score"] = scores[1]
                        else:
                            continue

                    case _:
                        value = d.string

                value = str(value)
                info_dict[key] = value


        if info_dict["match_report"] == "Head-to-Head":
            info_dict["finished"] = 0
        elif info_dict["match_report"] == "Match Report":
            info_dict["finished"] = 1
        elif info_dict["notes"] == "Match Postponed":
            info_dict["finished"] = 0
        else:
            raise OrderNotFoundError("Can't decide if finished, necessary information missing for infodict")
        #Får kanske titta mer här ifall en match exempelvis är uppskjuten/saknar datum/inte är schemalagd alls

        return info_dict

    @log
    def source(self, cache_table: str, cache_name: str, scratch_source: Callable[[],list], expiration_time: int,  primary_key_name: str = None, primary_key_id: int = None, brute_renew: bool = False, brute_load: bool = False,
                db_conn: sq.Connection = None, db_cur: sq.Cursor = None) -> list:
        """Normally gets the data through the cache if it is not expired, otherwise get a new list from create_cache and replace the cache. Brute_renew renews no matter what while brute_load only loads and never renews the cache.
        Expiration_time determines how much older the old cache has to be than current time to be replaced. Primary_key_name and id are used to find the right cache and should be provided if the table uses them.
        db_conn and db_cur should be provided if used in a multithreading context, otherwise defaults to the class instance attributes.
        
        """
        if db_conn is None or db_cur is None:
            db_conn = self.db_conn
            db_cur = self.db_cur

        html_str = cache_name + "_html"
        scraped_epoch_str = cache_name + "_scraped_epoch"
        version_str = cache_name + "_version"

        need_new = False
        if brute_renew and brute_load:
            raise ValueError("Only one brute parameter can be true")
        
        sql_cache_str = "SELECT " + html_str + ", " + scraped_epoch_str + " FROM " + cache_table
        if primary_key_name is not None and primary_key_id is not None:
            sql_cache_str = sql_cache_str + " WHERE " + primary_key_name + "=:primary_key"
        
        found_rows = db_cur.execute(sql_cache_str, {"primary_key": primary_key_id}).fetchall()
        if len(found_rows) > 1:
            raise ValueError("Found several rows to source")
        elif len(found_rows) == 0:
            found_row = None
            #raise ValueError("No rows found")
        else:
            found_row = dict(found_rows[0])
        
        if found_row is not None and html_str in found_row and found_row[html_str] is not None:
            cache = found_row

            if expiration_time != -1:
                if cache[scraped_epoch_str] + expiration_time > time.time() or brute_load: #not expired
                    html = pickle.loads(cache[html_str]) #tror loads funkar här
                else:
                    need_new = True
            else:
                html = pickle.loads(cache[html_str])

        else:
            if brute_load:
                raise ValueError("Cannot bruteload, html data does not exist", primary_key_id, cache_table)
            need_new = True

        if need_new or brute_renew:
            html = scratch_source() #self.create_cache(cache_table, cache_name, primary_key_name, primary_key_id, scratch_source=scratch_source)
            row = {}
            row[html_str] = pickle.dumps(html)
            row[version_str] = None #delete version data, the html needs to be rescanned
            row[scraped_epoch_str] = time.time()
            if primary_key_name is not None:
                row[primary_key_name] = primary_key_id #competitions_html kommer bli problem
            else: #bör bara finnas en rad i tabeln här, därför ok att wipa
                with db_conn:
                    db_cur.execute("DELETE FROM " + cache_table)
            utilities.db_insert(row, cache_table, db_conn=db_conn, db_cur=db_cur)

        return html

    @log
    def cache_check(self, cache_table: str, cache_name: str, primary_key_name: str = None, primary_key_id: int = None) -> bool:
        """Returns true if the cache version is up to date, otherwise returns false"""
        version_name = cache_name + "_version"
        if primary_key_name is None or primary_key_id is None:
            rows = self.db_cur.execute("SELECT " + version_name + " FROM " + cache_table).fetchall()
        else:
            rows = self.db_cur.execute("SELECT " + version_name + " FROM " + cache_table + " WHERE " + primary_key_name + "=" + str(primary_key_id)).fetchall()

        if len(rows) > 1:
            raise ValueError("Too many rows")
        elif len(rows) == 0:
            return False
        else:
            row = dict(rows[0])
            if version_name in row and row[version_name] == self.version:
                return True
            else:
                return False



    @staticmethod
    @log
    def competition_tree(comp_rows: list) -> dict:
        """Constructs a dictionary tree from a comp_rows list with the country codes/governing bodies as the roots and the competitions as branches from each root"""
        tree_dict = {}

        for row in comp_rows:

            if row["COUNTRY_CODE"] not in tree_dict:
                tree_dict[row["COUNTRY_CODE"]] = []
            
            tree_dict[row["COUNTRY_CODE"]].append(row)

        return tree_dict

    @staticmethod
    @log
    def name_similar(name1: str, name2: str) -> bool:
        """Splits each name by the spaces and checks if the other name contains any of the separate words, 
        if so returns true otherwise returns false"""

        parts1 = name1.split(" ")
        parts2 = name2.split(" ")

        for p in parts1:
            if p in name2:
                return True
        
        for p in parts2:
            if p in name1:
                return True
        
        return False

    @staticmethod
    @log
    def string_normalizer(string: str) -> str:
        """Replaces any characters with dots and other extremeties with their normal counterparts"""

        normal_string = string.replace("ũ","u")
        normal_string = normal_string.replace("ö","o")
        normal_string = normal_string.replace("ä","a")
        normal_string = normal_string.replace("é","e")

        return normal_string





#Order scraping
    @log
    def order_competitions(self, order: dict) -> None: #big fucking loop no more, POG
        """Finds the order's competition from the competitions on the fbref website and continues scraping the seasons, stores any scraped information in the sql database 
        which can be reused by this scraper whenever anything needs rescraping or reprocessing. As long as OrderNotFoundError is used in child functions, is able to keep scraping the next competitions.
        Any other thrown exceptions halts the order.

        """

        self.db_conn.execute("PRAGMA wal_checkpoint(FULL)") 
        #checkpoint in case there are any problems below which would not be visible otherwise when viewing the database from external program

        def clear_status_dict():
            self.update_status_entry("order_country_code", "")
            self.update_status_entry("order_comp_str", "")
            self.update_status_entry("order_home_team", "")
            self.update_status_entry("order_away_team", "")
            self.update_status_entry("order_date", "")
            if "prefix" in order:
                self.update_status_entry("order_prefix_str", "")
            self.update_status_entry("order_time_str", "")
            self.update_status_entry("curr_comps_unfinished", [])
            self.update_status_entry("curr_comps_finished", [])
            self.update_status_entry("curr_comp_str", "")
            self.update_status_entry("curr_country_str", "")
            self.update_status_entry("curr_gender_str", "")



        self.update_status_entry("order_country_code", order["country_code"])
        self.update_status_entry("order_comp_str", order["competition"])
        self.update_status_entry("order_home_team", order["team1"])
        self.update_status_entry("order_away_team", order["team2"])
        self.update_status_entry("order_date", str(order["date"]))
        if "prefix" in order:
            self.update_status_entry("order_prefix_str", order["prefix"])
        self.update_status_entry("order_time_str", order["time"])
        self.update_status_entry("orders_left", str(self.num_orders_left()))




        def scratch_source() -> list:
            address = self.base_url + "/en/comps/"
            comps_html = self.drivers[0].http_get(address)
            
            #comps = self.all_competitions(comps_html)
            return comps_html
        




        if not self.cache_check("competitions_html", "competitions"):
            comps_html = self.source(cache_table="competitions_html", cache_name="competitions", scratch_source=scratch_source, expiration_time=self.competitions_expiration_time)
            comps = self.all_competitions(comps_html)
            self.db_update(comps, "competition", ["competition_name", "country_code", "gender"], primary_key_name="competition_id")
            #update competitions_html version
            row = dict(self.db_cur.execute("SELECT * FROM competitions_html").fetchone())
            row["competitions_version"] = self.version
            with self.db_conn:
                self.db_cur.execute("DELETE FROM competitions_html")
            utilities.db_insert(row, "competitions_html", db_conn=self.db_conn, db_cur=self.db_cur)



        match order["competition_prefix"]:
            case "Scottish":
                web_country_code = "SCT"
            case "English":
                web_country_code = "ENG"
            case _:
                web_country_code = order["country_code"]
        
        name_parts = order["competition"].split(" ")
        glob_str = ""
        for i, part in enumerate(name_parts):
            if i == 0:
                glob_str = glob_str + "competition_name GLOB " + '"*' + part + '*" ' #använder " inuti som stränggrej för att undvika problem med exempelvis 'women's'
            else: 
                glob_str = glob_str + "OR competition_name GLOB " + '"*' + part + '*" '

        rows = self.db_cur.execute("SELECT competition_id, competition_name, country_code, gender FROM competition WHERE country_code=:country_code AND " + glob_str, {"country_code": web_country_code})

        multiples = [dict(r) for r in rows]


            
        if len(multiples) == 0: #add as failed order
            clear_status_dict()
            raise OrderNotFoundError("No competitions match order competition", order)
        else:
            found_competitions = []
            unfinished_competitions = multiples.copy()
            finished_competitions = []

            self.update_status_entry("curr_comps_unfinished", unfinished_competitions)
            self.update_status_entry("curr_comps_finished", finished_competitions)

            for competition in multiples:
                self.update_status_entry("comps_left_str", str(len(unfinished_competitions)))
                self.update_status_entry("curr_comp_str", competition["competition_name"])
                self.update_status_entry("curr_country_str", competition["country_code"])
                self.update_status_entry("curr_gender_str", competition["gender"])
                try:

                    if self.stop_flag.is_set():
                        raise StoppingException("Stopping, order_competitions")
                        
                    self.order_seasons(order, competition_id=competition["competition_id"])
                    found_competitions.append(competition)
                except OrderNotFoundError as e:
                    if "Stopping" not in e.args:
                        logger.exception("Something happened")
                    pass
                unfinished_competitions.remove(competition)
                finished_competitions.append(competition)

                self.update_status_entry("curr_comps_unfinished", unfinished_competitions)
                self.update_status_entry("curr_comps_finished", finished_competitions)
            
            self.update_status_entry("comps_left_str", "")

            if len(found_competitions) == 0:
                clear_status_dict()
                raise OrderNotFoundError("No matches match order's match")
            elif len(found_competitions) > 1:
                clear_status_dict()
                raise OrderNotFoundError("Several matches found for order")
        print("finished order", order["country_code"], order["competition"])

    @log
    def order_seasons(self, order: dict, competition_id: int) -> None:
        """Looks through the seasons, makes sure the latest season contains the order's year and begins scraping the matches below. In case of problems with season table format raises an exception. """

        row = dict(self.db_cur.execute("SELECT seasons_link FROM competition WHERE competition_id=?", (competition_id,)).fetchone())

        address = row["seasons_link"]
        

        def scratch_source() -> list:
            seasons_html = self.drivers[0].http_get(address)

            #seasons = self.all_seasons(seasons_html)

            return seasons_html

        def season_match_finder(seasons: list) -> list:
            """Finds the season that corresponds to the order date"""
            order_date = order["date"]
            order_year = str(order_date)[:4]
            
            season_matches = []
            for s in seasons:
                if "-" in s["season_name"]:
                    years = s["season_name"].split("-")
                    if len(years) != 2:
                        raise OrderNotFoundError("Unexpected season year format") #assuming that seasons don't span more than 2 different years
                else:
                    years = s["season_name"]

                if order_year in years:
                    year_sum = 0
                    for year in years:
                        year_sum += int(year)
                    season_matches.append([s, year_sum])

            if len(season_matches) > 1: #compare the year sums to get the most recent/highest one

                sums = []
                for s in season_matches:
                    sums.append(s[1])

                highest_sum = max(sums)
                season_matches_final = []
                for s in season_matches:
                    if s[1] == highest_sum:
                        season_matches_final.append(s[0])

                if len(season_matches_final) != 1:
                    raise NotImplementedError("Two season periods are the same, somehow")
                season_matches = season_matches_final[0]
                    
            elif len(season_matches) == 0:
                raise OrderNotFoundError("No season years match")
            else:
                season_matches = season_matches[0][0]
            
            #print(season_matches)
            return season_matches

        if not self.cache_check(cache_table="competition", cache_name="seasons", primary_key_id=competition_id, primary_key_name="competition_id"):
            seasons_html = self.source(cache_table="competition", cache_name="seasons", scratch_source=scratch_source, expiration_time=self.seasons_expiration_time, primary_key_id=competition_id, primary_key_name="competition_id")
            try:
                seasons = self.all_seasons(seasons_html)
            except OrderNotFoundError as e: #problem with all seasons, skipping, I can't be bothered to fix this
                self.update_status_entry("seasons_left_str", "")
                self.update_status_entry("curr_season_str", "")
                raise e

            for s in seasons:
                s["competition_id"] = competition_id
            self.db_update(row_list=seasons, table_name="season", deciding_columns=["season_name", "competition_id"], primary_key_name="season_id")
            with self.db_conn:
                self.db_cur.execute("UPDATE competition SET seasons_version=? WHERE competition_id=?", (self.version, competition_id))
        
        season_rows = self.db_cur.execute("SELECT * FROM season WHERE competition_id=:competition_id", {"competition_id": competition_id})
        seasons = [dict(r) for r in season_rows]

        #if the season doesn't exist from the timeless seasons, try with an actual expiration time, this should lessen the seasons scraping
        try:
            season_matches = season_match_finder(seasons)
        except OrderNotFoundError:
            seasons_html = self.source(cache_table="competition", cache_name="seasons", scratch_source=scratch_source, expiration_time=self.base_expiration_time, primary_key_id=competition_id, primary_key_name="competition_id")
            try:
                seasons = self.all_seasons(seasons_html)
            except OrderNotFoundError as e: #problem with all seasons, skipping, I can't be bothered to fix this
                self.update_status_entry("seasons_left_str", "")
                self.update_status_entry("curr_season_str", "")
                raise e
            
            for s in seasons:
                s["competition_id"] = competition_id
            self.db_update(seasons, "season", ["season_name", "competition_id"], "season_id")

            season_rows = self.db_cur.execute("SELECT * FROM season WHERE competition_id=:competition_id", {"competition_id": competition_id})
            seasons = [dict(r) for r in season_rows]
            season_matches = season_match_finder(seasons)
        
        #kolla först om matchen existerar, dvs kolla nyaste säsongen först, gäller dock inte vid kvalificeringstävlingar, får hantera dessa separat
        seasons_left = seasons.copy()
        for s in seasons: #scrape matches in every season
            self.update_status_entry("seasons_left_str", str(len(seasons_left)))
            self.update_status_entry("curr_season_str", s["season_name"])

            #season_path = posixpath.join(competition_path, s["SEASON"])
            match_in_season = False

            if s == season_matches:
                match_in_season = True


            if self.stop_flag.is_set():
                raise StoppingException("Stopping, order_seasons")

            self.order_matches(order=order, competition_id=competition_id, season_id=s["season_id"], match_in_season=match_in_season)
            seasons_left.remove(s)

        self.update_status_entry("seasons_left_str", "")
        self.update_status_entry("curr_season_str", "")

    @log
    def order_matches(self, order: dict, competition_id: str, season_id: str, match_in_season: bool) -> None:
        """Iterates through all match rows on a season fixtures page and saves them, in case of problems will save current state and 
        load it next time function runs. Uses multithreading with . Also adds a few rows to info.csv: PATH, ID, COUNTRY, COMPETITION, SEASON, FIXTURES_ADDRESS. Has a stopper in the exception check function
        Returns bool from final touches depending on length of error_list. Manages the following warning codes: 7: "Link tag not found"
        """
        the_match = None

        #decide source
        def scratch_source_season() -> bs4.BeautifulSoup:
            """Returns a season html page that can be used to get the fixtures link"""
            season_link = dict(self.db_cur.execute("SELECT season_link FROM season WHERE season_id=?", (season_id,)).fetchone())["season_link"]
            season_html = self.drivers[0].http_get(season_link) #pre_fixtures_address
            return season_html


        rows = self.db_cur.execute("SELECT * FROM warning WHERE season_id=?", (season_id,)).fetchall()
        if len(rows) > 0: #to skip seasons with warnings
            return
        
        if not self.cache_check(cache_table="season", cache_name="season", primary_key_name="season_id", primary_key_id=season_id):
            self.source(cache_table="season", cache_name="season", scratch_source=scratch_source_season, expiration_time=self.season_expiration_time, primary_key_id=season_id, primary_key_name="season_id")
        
        if match_in_season:
            expiration = self.fixtures_expiration_time
        else:
            expiration = self.base_expiration_time
        

        def scratch_source_fixtures() -> bs4.BeautifulSoup:
            """Returns a fixtures html page"""
            fixtures_link = self.db_cur.execute("SELECT fixtures_link FROM season WHERE season_id=?", (season_id,)).fetchone()["fixtures_link"]
            fixtures_html = self.drivers[0].http_get(fixtures_link)
            return fixtures_html

        if not self.cache_check(cache_table="season", cache_name="fixtures", primary_key_name="season_id", primary_key_id=season_id):
            season_html = pickle.loads(self.db_cur.execute("SELECT season_html FROM season WHERE season_id=?", (season_id,)).fetchone()["season_html"])
            fixtures_link = self.scores_and_fixtures_link(season_html)
            with self.db_conn:
                self.db_cur.execute("UPDATE season SET fixtures_link=? WHERE season_id=?", (fixtures_link, season_id))
                self.db_cur.execute("UPDATE season SET season_version=? WHERE season_id=?", (self.version, season_id))
            self.source(cache_table="season", cache_name="fixtures", scratch_source=scratch_source_fixtures, expiration_time=expiration, primary_key_id=season_id, primary_key_name="season_id")

        fixtures_html = pickle.loads(self.db_cur.execute("SELECT fixtures_html FROM season WHERE season_id=?", (season_id,)).fetchone()["fixtures_html"])

        match_rows = self.match_rows_from_fixtures(fixtures_html) #need to match matches here according to update

        #make sure the match exists in the season
        def match_in_season_check() -> dict:
            """Checks if the order match can be found in the match_rows variable. If not, raises OrderNotFoundError. Returns the matched match"""
            order_date_list = [int(str(order["date"])[:4]), int(str(order["date"])[4:6]), int(str(order["date"])[6:])] #year, month, day
            order_time = list(map(int, order["time"].split(":")))

            dt = datetime.datetime(*order_date_list, *order_time, tzinfo=pytz.timezone("UTC"))
            order_epoch = float(round(dt.timestamp())) #float according to specification
            order_dates = [datetime.date(*order_date_list), datetime.date(*order_date_list) - datetime.timedelta(days=1), datetime.date(*order_date_list) + datetime.timedelta(days=1)]# +- 1  dag eftersom tiderna på hemsidan är relativt till sina egna tidszoner

            order_dates = list(map(lambda x: int(str(x).replace("-", "")), order_dates)) #int in specification

            matches = []
            for m in match_rows:

                team_strs = ["home_name", "away_name"]
                teams = {}

                for t in team_strs:
                
                    if m[t] == "Türkiye":
                        team_var = "Turkey"
                    elif m[t] == "Czechia":
                        team_var = "Czech Republic"
                    else:
                        team_var = self.string_normalizer(m[t])

                    teams[t] = team_var

                home_team = teams["home_name"]
                away_team = teams["away_name"]

                if "epoch" in m:
                    if order_epoch == m["epoch"]:
                        if order["team1"] == home_team and order["team2"] == away_team:
                            matches.append(m)

                elif "date" in m:
                    if m["date"] in order_dates:
                        if order["team1"] == home_team and order["team2"] == away_team:
                            matches.append(m)
                else:
                    raise NotImplementedError("No date or epoch in match")
            
            if len(matches) > 1:
                raise OrderNotFoundError("Order matches more than 1 match")
            elif len(matches) == 0:
                raise OrderNotFoundError("Order matches 0 matches")
            else:
                the_match = matches[0]
                print("order's match found")
            
            return the_match

        if match_in_season:
            the_match = match_in_season_check()

        #get the old match rows
        old_rows = self.db_cur.execute("SELECT match_id, home_fbref_id, away_fbref_id, epoch, date, finished FROM match WHERE season_id=?", (season_id,)).fetchall() #self.db_cur.execute("SELECT home_fbref_id FROM match WHERE season_id=?", (season_id,)) #home_fbref_id, away_fbref_id, epoch, date
        old_match_rows = [dict(r) for r in old_rows]

        #construct mapping for old match rows, anything not mapped will be deleted and scraped
        mapping = [] #new_match, old_match
        for o in old_match_rows:
            matches = []
            for m in match_rows:
                mapped = False
                if "epoch" in o and "epoch" in m:
                    if m["home_fbref_id"] == o["home_fbref_id"] and m["away_fbref_id"] == o["away_fbref_id"] and m["epoch"] == o["epoch"]: #nothing relevant has changed
                        mapped = True
                elif "date" in o and "date" in m:
                    if m["home_fbref_id"] == o["home_fbref_id"] and m["away_fbref_id"] == o["away_fbref_id"] and m["date"] == o["date"]:
                        mapped = True
                else:
                    raise NotImplementedError("Varken epoch eller date i gammal eller ny match")
                
                if mapped:
                    matches.append((m, o))
                    
            if len(matches) > 1: #to prevent any weird issues of several matches, look into it if it occurs
                raise NotImplementedError("Several matches match an old match")
            elif len(matches) == 1:
                mapping.append(matches[0])

        #delete old unmapped matches, scrape new unmapped matches, reprocess matches whose versions are not up to date
        old_matches_to_delete = [] #old matches to be thrown in the trash
        
        mapped_new_matches = [] #old matches to look through
        unmapped_new_matches = [] #completely new matches

        temp_unmapped_new_matches = match_rows.copy()
        temp_unmapped_old_matches = old_match_rows.copy()
        for m_tuple in mapping:
            m, m_old = m_tuple
            temp_unmapped_new_matches.remove(m) #remove match before adding match_id

            m["match_id"] = m_old["match_id"]
            mapped_new_matches.append(m)

            temp_unmapped_old_matches.remove(m_old)


        unmapped_new_matches.extend(temp_unmapped_new_matches)
        old_matches_to_delete.extend(temp_unmapped_old_matches)

        
        #set actions for the matches
        matches_to_reprocess = [] #reprocess because version not up to date
        matches_to_add = [] #add new unmapped matches

        for r in unmapped_new_matches: #unmapped matches
            matches_to_add.append(r)
        
        for r in mapped_new_matches: #mapped matches
            if r["finished"] == 1 and not self.cache_check("match", "match", primary_key_name="match_id", primary_key_id=r["match_id"]): #if match is finished and version is not up to date, then reprocess
                matches_to_reprocess.append(r)

        
        with self.db_conn:
            for m_old in old_matches_to_delete: #delete every trace of match
                self.db_cur.execute("DELETE FROM warning WHERE match_id=?", (m_old["match_id"],))
                self.db_cur.execute("DELETE FROM player WHERE match_id=?", (m_old["match_id"],))
                self.db_cur.execute("DELETE FROM goalkeeper WHERE match_id=?", (m_old["match_id"],))
                self.db_cur.execute("DELETE FROM shot WHERE match_id=?", (m_old["match_id"],))
                self.db_cur.execute("DELETE FROM timeline WHERE match_id=?", (m_old["match_id"],))
                self.db_cur.execute("DELETE FROM match WHERE match_id=?", (m_old["match_id"],))
                

        
        print("add", len(matches_to_add), "reprocess", len(matches_to_reprocess), "delete", len(old_matches_to_delete), "mapped", len(mapping), "match_rows", len(match_rows),
               "competition_id", competition_id, "season_id", season_id)

        match_rows_unfinished = matches_to_add.copy()
        match_rows_unfinished.extend(matches_to_reprocess.copy())
        match_rows_available = matches_to_add.copy()
        match_rows_available.extend(matches_to_reprocess.copy())
        
        driver_available = threading.Event()
        drivers_copy = self.drivers
        driver_available.set()

        def exception_check(futures: list[concurrent.futures.Future, dict]) -> list[concurrent.futures.Future, dict]:
            """ Checks for an exception and returns a new list of the unfinished futures if no exception, 
            otherwise sets the self.stop_flag to True. The futures list contains tuples of a future and 
            the corresponding match_row argument.
            
            """

            futures_copy = futures.copy()

            for f, match_row in futures: #just checks the finished futures for exceptions
                if f.done():
                    try:
                        f.result()
                        futures_copy.remove((f, match_row))

                    except Exception as e:
                        self.error_flag.set()
                        self.stop_flag.set()
                        logger.exception(e)
                        print("exception for match: ", competition_id, season_id, match_row, e.__repr__())


            return futures_copy.copy()

        def match_saver(match_row: dict[str: str], driver: TorBrowser):
            """
            Processes the match_row supplied and inserts it into the database as well as inserting additional data using save_match_data if the match is finished. 
            If the match_id is already provided in the match_row then the insertion updates the existing match_id entry.
            
            """
            db_conn, db_cur = utilities.db_access_init(self.db_path)

            try:
                match_row_here = match_row.copy() #using match_row_here to be able to remove the match easily from match_rows_unfinished later

                match_row_here["competition_id"] = competition_id
                match_row_here["season_id"] = season_id

                if match_row_here["finished"]:
                    def scratch_source():
                        match_html = driver.http_get(match_row["match_link"])
                        return match_html
                    
                    match_id = utilities.db_insert(match_row_here, "match", db_conn=db_conn, db_cur=db_cur)  #to make sure that match_html has somewhere to go
                    match_row_here["match_id"] = match_id

                    #delete references to match in other tables
                    with db_conn:
                        db_cur.execute("DELETE FROM warning WHERE match_id=?", (match_row_here["match_id"],))
                        db_cur.execute("DELETE FROM player WHERE match_id=?", (match_row_here["match_id"],))
                        db_cur.execute("DELETE FROM goalkeeper WHERE match_id=?", (match_row_here["match_id"],))
                        db_cur.execute("DELETE FROM shot WHERE match_id=?", (match_row_here["match_id"],))
                        db_cur.execute("DELETE FROM timeline WHERE match_id=?", (match_row_here["match_id"],))

                    match_html = self.source(cache_table="match", cache_name="match", primary_key_name="match_id", primary_key_id=match_row_here["match_id"], scratch_source=scratch_source, expiration_time=self.match_expiration_time,
                                            db_conn=db_conn, db_cur=db_cur)

                    self.save_match_data(match_html=match_html, match_row=match_row_here, db_conn=db_conn, db_cur=db_cur) #adds entries to match_row dict by reference
                    match_row_here["match_version"] = self.version
                
                match_id = utilities.db_insert(match_row_here, "match", db_conn=db_conn, db_cur=db_cur) #just to update the version
                match_row_here["match_id"] = match_id #in case the match is not finished and didn't acquire the match_id previously

                #add the match_id to the order, if the order has failed for any reason the path will simply be updated later before being forwarded
                if the_match is not None:
                    if (match_row_here["home_fbref_id"] == the_match["home_fbref_id"] and match_row_here["away_fbref_id"] == the_match["away_fbref_id"] and 
                        ("epoch" in the_match and "epoch" in match_row_here and match_row_here["epoch"] == the_match["epoch"]) or 
                        ("date" in the_match and "date" in match_row_here and match_row_here["date"] == the_match["date"])):
                        order["scraped_match_id"] = match_row_here["match_id"]

            finally:
                drivers_copy.append(driver)
                driver_available.set()

                match_rows_unfinished.remove(match_row)
        
        #main match processing loop
        pool = concurrent.futures.ThreadPoolExecutor(max_workers=len(self.drivers))
        futures = []

        while len(match_rows_available) > 0:
            self.update_status_entry("matches_left_str", str(len(match_rows_unfinished)))
                
            futures = exception_check(futures)
            if self.stop_flag.is_set():
                break

            match_row = match_rows_available.pop()

            if len(drivers_copy) == 0:
                driver_available.clear()
            driver_available.wait()
            driver = drivers_copy.pop()

            future = pool.submit(match_saver, match_row=match_row, driver=driver)
            futures.append((future, match_row))

        pool.shutdown(wait=True)
        with self.db_conn:
            self.db_cur.execute("UPDATE season SET fixtures_version=? WHERE season_id=?", (self.version, season_id))
        
        self.db_conn.execute("PRAGMA wal_checkpoint(FULL)")

        self.update_status_entry("matches_left_str", "")

    @log
    def save_match_data(self, match_html: bs4.Tag, match_row: dict, db_conn: sq.Connection, db_cur: sq.Cursor) -> None:
        """
        Saves available match data consisting of team tables, formations, timeline, shots, overview and any eventual warnings into their respective tables in the database.
        Also uses the match_row to add a formation key, official names and venue.
        Requires that the match_id key exists in match_row. Since the method is usually used in a multithreading context it requires it's own sql cursor object from to the thread
        """

        match_id = match_row["match_id"]

        #data
        tables, warning_dict = self.team_tables_on_page(match_html=match_html)
        player_dict, __ = self.player_dict_from_team_tables(tables, warning_dict)

        player_list = []
        gk_list = []
        for key, value in player_dict.items():
            if "Players" in key:
                player_list.extend(value)
            elif "Goalkeepers" in key:
                gk_list.extend(value)
        
        formations, __ = self.formations_on_page(match_html, warning_dict)
        if formations is not None:
            for key, value in formations.items(): #key is Home/Away
                if "Formation" in value:
                    match_row[key.lower() + "_formation"] = value["Formation"]
                
                if "Starters" in value: #going through the player_list to check which players need starter=1
                    starter_list = value["Starters"].copy()
                    temp = list(map(list, zip(*starter_list)))

                    if len(temp) != 2:
                        print(temp, "starters", match_row["match_id"]) #debug
                    
                    starter_nums, starter_names = temp[0], temp[1] #ignores the starter num here
                    for p in player_list:
                        p_name = p["player_name"]
                        if p_name in starter_names:
                            p["starter"] = 1
                            starter_names.remove(p_name)

                    if len(starter_names) > 0: #try to detect mismatches/spell errors in starter_list
                        with open("players2", "wb") as f:
                            pickle.dump([value, player_list, player_dict, match_html], f)
                        raise NotImplementedError("starter_names still has p_names", starter_names)

                if "Benched" in value and len(value["Benched"]) > 0: #if player in player_list already exists, set starter=1, otherwise add the player as a leftover into the player_list
                    benched_list = value["Benched"].copy()
                    temp = list(map(list, zip(*benched_list))) #len(benched) > 0 to avoid empty benched lists

                    if len(temp) != 2:
                        with open("players_benched", "wb") as f:
                            pickle.dump([value, match_html], f)
                        print(temp, "benched", match_row["match_id"]) #debug
                    
                    benched_nums, benched_names = temp[0], temp[1]
                    for p in player_list:
                        p_name = p["player_name"]
                        if p_name in benched_names:
                            p["starter"] = 0
                            i = benched_names.index(p_name)
                            benched_names.pop(i)
                            benched_nums.pop(i)

                    
                    for i, leftover_name in enumerate(benched_names):
                        player = {"player_name": leftover_name, "shirtnumber": benched_nums[i], "ground": key.lower(), "starter": 0} #kanske går att få med mer data här ifall vi vill
                        player_list.append(player)
                elif "Benched" in value:
                    print(value["Benched"], "Benched skipped")

        #timeline
        timeline_list, __ = self.timeline_on_page(match_html, warning_dict)
        if timeline_list is not None:
            for e in timeline_list:
                e["match_id"] = match_id
                utilities.db_insert(e, "timeline", db_conn=db_conn, db_cur=db_cur)

        #shots
        shots_list, __ =  self.shots_on_page(match_html, warning_dict)
        if shots_list is not None:
            for s in shots_list:
                s["match_id"] = match_id
                utilities.db_insert(s, "shot", db_conn=db_conn, db_cur=db_cur)

        #overview
        overview_dict, __ = self.overview_text_on_page(match_html, warning_dict)
        if overview_dict is not None:
            if "Officials" in overview_dict:
                job_dict = overview_dict["Officials"]
                for job, name in job_dict.items():
                    match_row[job] = name
            elif "Venue" in overview_dict:
                match_row["overview_venue"] = overview_dict["Venue"]

        #finish up the player and gk lists
        for p in player_list:
            p["match_id"] = match_id
            utilities.db_insert(p, "player", db_conn=db_conn, db_cur=db_cur)
        
        for gk in gk_list:
            gk["match_id"] = match_id
            utilities.db_insert(gk, "goalkeeper", db_conn=db_conn, db_cur=db_cur)

        #save any warning
        if len(warning_dict) > 0:
            warning_dict["match_id"] = match_id
            utilities.db_insert(warning_dict, "warning", db_conn=db_conn, db_cur=db_cur)


        







#Database
    @log
    def database_setup(self):
        """Sets up the basic database structure without removing anything. The version stated is the one used on the specified html file in the same table.
        
        
        """

        with self.db_conn:
            self.db_cur.execute("""
                        CREATE TABLE competitions_html(
                        
                        competitions_version TEXT,
                        competitions_scraped_epoch REAL,
                        competitions_html BLOB
                        )""")

            self.db_cur.execute("""
                        CREATE TABLE competition(
                        competition_id INTEGER PRIMARY KEY,
                                
                        competition_name TEXT,
                        country_code TEXT,
                        gender TEXT,
                                
                        seasons_link TEXT,
                        seasons_version TEXT,
                        seasons_scraped_epoch REAL,
                        seasons_html BLOB
                        )""")
            
            self.db_cur.execute("""
                        CREATE TABLE season(
                        competition_id INTEGER,
                        season_id INTEGER PRIMARY KEY,
                                
                        season_name TEXT,
                        warning INTEGER,
                            
                        season_link TEXT,
                        season_html BLOB,
                        season_version TEXT,
                        season_scraped_epoch REAL,
                                
                        fixtures_link TEXT,
                        fixtures_html BLOB,
                        fixtures_version TEXT,
                        fixtures_scraped_epoch REAL,
                                
                        FOREIGN KEY(competition_id) REFERENCES competition(competition_id)
                        )""")
            
            self.db_cur.execute("""CREATE INDEX competition_id_idx ON season (competition_id)""")
            
            self.db_cur.execute("""
                        CREATE TABLE match(
                        competition_id INTEGER,
                        season_id INTEGER,
                        match_id INTEGER PRIMARY KEY,
                                
                        finished INTEGER,
                        epoch REAL,
                        date INTEGER,
            
                        home_formation TEXT,
                        away_formation TEXT,
                        home_fbref_id TEXT,
                        away_fbref_id TEXT,
                        home_name TEXT,
                        away_name TEXT,
                        home_score TEXT,
                        away_score TEXT,
                                
                        match_link TEXT,
                        match_html BLOB,
                        match_version TEXT,
                        match_scraped_epoch REAL,
                                    
                        )""")
            
            self.db_cur.execute("""CREATE INDEX match_team_idx ON match(home_fbref_id, away_fbref_id, epoch, date)""")
            
            self.db_cur.execute("""
                        CREATE TABLE player(
                        match_id INTEGER,
                                
                        player_name TEXT,
                        starter INTEGER,
                        minutes TEXT,
                        age TEXT,
                        position TEXT,
                        cards_yellow TEXT,
                        cards_red TEXT,
                        own_goals TEXT,
                        goals TEXT,
                        assists TEXT,
                        shots TEXT,
                        ground TEXT,
                                    
                        )""")
            self.db_cur.execute("""CREATE INDEX match_id_player_idx ON player(match_id)""")
            
            self.db_cur.execute("""
                        CREATE TABLE goalkeeper(
                        match_id INTEGER,
                                
                        player_name TEXT,
                        nationality TEXT,
                        age TEXT,
                        gk_saves TEXT,
                        gk_saves_pct TEXT,
                        gk_crosses TEXT,
                                    
                        )""")
            self.db_cur.execute("""CREATE INDEX match_id_goalkeeper_idx ON goalkeeper(match_id)""")
            
            self.db_cur.execute("""
                        CREATE TABLE timeline(
                        match_id INTEGER,
                                
                        time_section TEXT,
                        timestamp TEXT,
                        player_name TEXT,
                        event TEXT,
                        ground TEXT,
                        assisting_player TEXT,
                        player_in TEXT,
                        saved_by TEXT,
                                    
                        )""")
            self.db_cur.execute("""CREATE INDEX match_id_timeline_idx ON timeline(match_id)""")
            
            self.db_cur.execute("""
                        CREATE TABLE shot(
                        match_id INTEGER,
                                
                        player_name TEXT,
                        body_part TEXT,
                        distance TEXT,
                        team TEXT,
                        xg_shot TEXT,
                        notes TEXT,
                        outcome TEXT,
                        minute TEXT,
                                    
                        )""")
            self.db_cur.execute("""CREATE INDEX match_id_shot_idx ON shot(match_id)""")
            
            self.db_cur.execute("""
                        CREATE TABLE warning(
                        match_id INTEGER,
                        season_id INTEGER,
                                    
                        )""")

            self.db_cur.execute("""CREATE INDEX match_id_warning_idx ON warning(match_id)""")
     
    @log
    def db_update(self, row_list: list, table_name: str, deciding_columns: list, primary_key_name: str) -> None:
        """
        Updates the specified database with the provided list. Either inserts new entries or updates old/slightly changed entries using db_insert. The entries will still use deciding columns to determine which entry matches.
        Primary_key_name is used to identify and access the rows found.
        """

        column_str = primary_key_name
        for i, d in enumerate(deciding_columns):
            # if i == 0:
            #     column_str = column_str + d
            # else:
            column_str = column_str + ", " + d

        db_rows = self.db_cur.execute("SELECT " + column_str + " FROM " + table_name).fetchall()
        db_rows = [dict(r) for r in db_rows]

        for new in row_list:
            found = False
            for old in db_rows:
                this_one = True
                for d in deciding_columns:
                    if new[d] != old[d]:
                        this_one = False
                        break
                
                if this_one:
                    found = True
                    break

            if not found:
                utilities.db_insert(new, table_name, db_conn=self.db_conn, db_cur=self.db_cur)
            else:
                new[primary_key_name] = old[primary_key_name]
                if not new == old:
                    utilities.db_insert(new, table_name, db_conn=self.db_conn, db_cur=self.db_cur)




#Utilities
    @log
    def cleanup(self, data: bool):
        """Cleans up (deletes) relevant directories according to the passed argument booleans
        
        """


        clean_paths = []

        for f in clean_paths:
            try:
                os.remove(f)
            except FileNotFoundError:
                pass

        if data:
            self.__rec_cleanup(self.data_path)
            os.mkdir(self.data_path)

    @log
    def __rec_cleanup(self, file_path: str) -> None:
        """Recursive helper for the cleanup function"""
        if posixpath.isfile(file_path):
            os.remove(file_path)
        elif posixpath.isdir(file_path):
            for f in os.listdir(file_path):
                self.__rec_cleanup(posixpath.join(file_path,f))
            os.rmdir(file_path)
        else:
            raise Exception("cleanup path is not file or dir", file_path)

    @log
    def find_unoccupied_id(self, relative_path: str, name: str):
        """Returns a number from a selected name pattern with suffix _id that does not occur in relative_path
        Using the forms (Statistik/Data) and (name)
        """
        i = 0
        while True:
            if posixpath.exists(relative_path + "/" + name + "_" + str(i)):
                i+=1
            else:
                break
        return i

    @log
    def update_status_entry(self, key: str, value: str) -> None:
        """Updates the status_dict key entry to the value provided and sets the change flag to True
        
        """
        self.status_dict[key] = value
        self.change_flag.set()

    @log
    def close(self) -> None:
        """Closes the tor drivers and cleans up the unfinished match folders"""
        #utilities.email_msg("Scraper has exited")
        self.stop_flag.set()

        for d in self.drivers:
            print("closing scraper")
            d.close()

        self.db_cur.close()
        self.db_conn.close()



class StatusWindow():
    """A window displaying status variables from the scraper,
    should be used in a separate thread

    """
    

    def __init__(self, refscraper: RefScraper):
        self.scraper = refscraper
        self.update_delay = 500 #time between updates in milliseconds

        self.background = "white"

        self.text_bg = "white"
        self.text_fg = "black"
        
        self.entry_font = "none 10"
        self.value_font = "none 10"

        self.window = Tk()

        self.data_labels = []
        self.update_functions = []
        

        self.setup()

    def setup(self):
        """Sets up the window structure and starts an update timer according to the update_delay attribute
        Updates the labels specified in the update helper according to the scraper dict entries if the scraper change flag is True
        """
        self.window.title("Status monitor")
        self.window.configure(background=self.background)
        self.window.geometry("1400x1000")

        status_frame = self.StatusFrame()
        tor_info_frame = self.TorFrame()

        #Frame structure
        status_frame.grid(row=0, column=0, rowspan=1, columnspan=1, sticky=NW, padx=20)
        tor_info_frame.grid(row=0, column=1, rowspan=1, columnspan=1, sticky=NW, padx=20)



        def update_values():

            if self.scraper.change_flag.is_set() or TorBrowser.change_flag.is_set():

                for l in self.data_labels:
                    l.update()

                for f in self.update_functions:
                    f()

                self.scraper.change_flag.clear()
                TorBrowser.change_flag.clear()

            self.window.after(self.update_delay, update_values)

        self.window.after(self.update_delay,update_values)
        self.window.mainloop()

    def func_maker(self, fn: Callable[..., None], *args: ...):
        """Returns a callable function intended to be called later
        
        """
        def fn_callable():
            fn(*args)
        
        return fn_callable

    def StatusFrame(self) -> Frame:

        frame = Frame(master=self.window)
        frame.configure(background=self.background)

        #Base status frame
        base_info_frame = Frame(master=frame)
        base_info_frame.configure(background=self.background, pady=5)
        local_master = base_info_frame

        row = 0

        # label_widget = Label(local_master, text="Current governing body: ", bg=self.text_bg, fg=self.text_fg, font=self.entry_font)
        # label_widget.grid(row=row, column=0, sticky=W)
        # self.data_labels.append(DataLabel(label_widget,"curr_gov_str", self.scraper))
        # row+=1

        label_widget = Label(local_master, text="Current governing body: ", bg=self.text_bg, fg=self.text_fg, font=self.entry_font)
        label_widget.grid(row=row, column=0, sticky=W)
        self.data_labels.append(DataLabel(label_widget,"curr_country_str", self.scraper))
        row+=1
        
        label_widget = Label(local_master, text="Current competition: ", bg=self.text_bg, fg=self.text_fg, font=self.entry_font)
        label_widget.grid(row=row, column=0, sticky=W)
        self.data_labels.append(DataLabel(label_widget,"curr_comp_str", self.scraper))
        row+=1

        label_widget = Label(local_master, text="Current gender: ", bg=self.text_bg, fg=self.text_fg, font=self.entry_font)
        label_widget.grid(row=row, column=0, sticky=W)
        self.data_labels.append(DataLabel(label_widget,"curr_gender_str", self.scraper))
        row+=1

        label_widget = Label(local_master, text="Current season: ", bg=self.text_bg, fg=self.text_fg, font=self.entry_font)
        label_widget.grid(row=row, column=0, sticky=W)
        self.data_labels.append(DataLabel(label_widget,"curr_season_str", self.scraper))
        row+=1

        #Curr frame
        left_info_frame = Frame(master=frame)
        left_info_frame.configure(background=self.background, pady=5)
        local_master = left_info_frame
        row = 0

        label_widget = Label(local_master, text="Competitions left: ", bg=self.text_bg, fg=self.text_fg, font=self.entry_font)
        label_widget.grid(row=row, column=0, sticky=W)
        self.data_labels.append(DataLabel(label_widget,"comps_left_str", self.scraper))
        row+=1

        label_widget = Label(local_master, text="Seasons left on current competition: ", bg=self.text_bg, fg=self.text_fg, font=self.entry_font)
        label_widget.grid(row=row, column=0, sticky=W)
        self.data_labels.append(DataLabel(label_widget,"seasons_left_str", self.scraper))
        row+=1

        label_widget = Label(local_master, text="Matches left on current season: ", bg=self.text_bg, fg=self.text_fg, font=self.entry_font)
        label_widget.grid(row=row, column=0, sticky=W)
        self.data_labels.append(DataLabel(label_widget,"matches_left_str", self.scraper))
        row+=1


        #Order frame
        order_frame = Frame(master=frame)
        order_frame.configure(background=self.background, pady=5)
        local_master = order_frame
        row = 0

        label_widget = Label(local_master, text="Orders left: ", bg=self.text_bg, fg=self.text_fg, font=self.entry_font)
        label_widget.grid(row=row, column=0, sticky=W)
        self.data_labels.append(DataLabel(label_widget,"orders_left", self.scraper))
        row+=1

        label_widget = Label(local_master, text="Country code: ", bg=self.text_bg, fg=self.text_fg, font=self.entry_font)
        label_widget.grid(row=row, column=0, sticky=W)
        self.data_labels.append(DataLabel(label_widget,"order_country_code", self.scraper))
        row+=1

        label_widget = Label(local_master, text="Competition prefix: ", bg=self.text_bg, fg=self.text_fg, font=self.entry_font)
        label_widget.grid(row=row, column=0, sticky=W)
        self.data_labels.append(DataLabel(label_widget,"order_prefix_str", self.scraper))
        row+=1

        label_widget = Label(local_master, text="Competition: ", bg=self.text_bg, fg=self.text_fg, font=self.entry_font)
        label_widget.grid(row=row, column=0, sticky=W)
        self.data_labels.append(DataLabel(label_widget,"order_comp_str", self.scraper))
        row+=1

        label_widget = Label(local_master, text="Home team: ", bg=self.text_bg, fg=self.text_fg, font=self.entry_font)
        label_widget.grid(row=row, column=0, sticky=W)
        self.data_labels.append(DataLabel(label_widget,"order_home_team", self.scraper))
        row+=1

        label_widget = Label(local_master, text="Away team: ", bg=self.text_bg, fg=self.text_fg, font=self.entry_font)
        label_widget.grid(row=row, column=0, sticky=W)
        self.data_labels.append(DataLabel(label_widget,"order_away_team", self.scraper))
        row+=1

        label_widget = Label(local_master, text="Date: ", bg=self.text_bg, fg=self.text_fg, font=self.entry_font)
        label_widget.grid(row=row, column=0, sticky=W)
        self.data_labels.append(DataLabel(label_widget,"order_date", self.scraper))
        row+=1

        label_widget = Label(local_master, text="Time (GMT): ", bg=self.text_bg, fg=self.text_fg, font=self.entry_font)
        label_widget.grid(row=row, column=0, sticky=W)
        self.data_labels.append(DataLabel(label_widget,"order_time_str", self.scraper))
        row+=1


        #Unfinished/Finished
        list_font = "none 8"

        list_frame = Frame(master=frame)
        list_frame.configure(background=self.background, pady=5)
        local_master = list_frame
        row = 0

        t = Label(local_master, text="Unfinished", bg=self.text_bg, fg=self.text_fg, font="none 8 bold").grid(row=row,column=0,sticky=NW, rowspan=1, columnspan=1)
        row += 1

        list_unfinished = Listbox(local_master, font=list_font)
        list_unfinished.configure(width=33)
        list_unfinished.grid(row=row, column=0, sticky=W)
        row+=1

        t = Label(local_master, text="Finished", bg=self.text_bg, fg=self.text_fg, font="none 8 bold").grid(row=row,column=0,sticky=NW, rowspan=1, columnspan=1)
        row += 1

        list_finished = Listbox(local_master, font=list_font)
        list_finished.configure(width=33)
        list_finished.grid(row=row, column=0, sticky=W)
        row+=1

        list_dict = {"curr_comps_unfinished": list_unfinished, "curr_comps_finished": list_finished}

        def lists_updater():

            for key in list_dict:
                lbox = list_dict[key]

                lbox.delete(0, lbox.size())

                comps = self.scraper.status_dict[key]
                largest = len(comps)
                for i in range(len(comps)):
                    j = largest - i - 1
                    c = comps[j]
                    lbox.insert(0, c["country_code"] + "_" + c["competition_name"] + "_" + c["gender"])



        self.update_functions.append(lists_updater)


        row = 0
        t1 = Label(frame, text="Status", bg=self.text_bg, fg=self.text_fg, font="none 12 bold").grid(row=row,column=0,sticky=NW, rowspan=1, columnspan=1)
        row += 1
        t2 = Label(frame, text="Order", bg=self.text_bg, fg=self.text_fg, font="none 9 bold").grid(row=row,column=0,sticky=NW, rowspan=1, columnspan=1)
        row += 1
        order_frame.grid(row=row, column=0, rowspan=1, columnspan=1, sticky=NW)
        row += 1
        t3 = Label(frame, text="Scraping", bg=self.text_bg, fg=self.text_fg, font="none 9 bold").grid(row=row,column=0,sticky=NW, rowspan=1, columnspan=1)
        row += 1
        base_info_frame.grid(row=row, column=0, rowspan=1, columnspan=1, sticky=NW)
        row += 1
        left_info_frame.grid(row=row, column=0, rowspan=1, columnspan=1, sticky=NW)
        row += 1
        list_frame.grid(row=row, column=0, rowspan=1, columnspan=1, sticky=NW)
        row += 1

        return frame

    def TorFrame(self) -> Frame:
        """
        
        """
        #Tor frame
        frame = Frame(master=self.window)
        frame.configure(background=self.background, pady=5)


        #Driver table frame
        driver_table_frame = Frame(master=frame)
        driver_table_frame.configure(background=self.background)

        treeview = Treeview(master = driver_table_frame, columns=["Status", "Tries", "Ip renewals", "URL"], height=4)
        treeview.heading("#0", text = "Name")
        treeview.column("#0", minwidth=0, width=100, stretch=NO)
        treeview.heading("URL", text = "URL")
        treeview.column("URL", minwidth=0, width=500, stretch=NO)
        treeview.heading("Status", text = "Status")
        treeview.column("Status", minwidth=0, width=100, stretch=NO)
        treeview.heading("Tries", text = "Tries")
        treeview.column("Tries", minwidth=0, width=100, stretch=NO)
        treeview.heading("Ip renewals", text = "Ip renewals")
        treeview.column("Ip renewals", minwidth=0, width=100, stretch=NO)
        treeview.pack()

        def handle_click(event): #to prevent resizing of the treeview columns
            if treeview.identify_region(event.x, event.y) == "separator":
                return "break"

        treeview.bind('<Button-1>', handle_click)

        def update_item_fn(item_id: str, pre_url: str): #item id should be the same as the name of the driver in the status dict, eg driver_0 ... etc
            sdict = TorBrowser.status_dict[item_id]
            treeview.item(item_id, values=(sdict["status"], sdict["tries"], sdict["renews"], sdict["url"][len(pre_url):]))

        for driver_dict_key in TorBrowser.status_dict:
            driver_dict = TorBrowser.status_dict[driver_dict_key]

            treeview.insert("", END, iid = driver_dict_key, text = driver_dict_key)

            self.update_functions.append(self.func_maker(update_item_fn, driver_dict_key, self.scraper.base_url))




        #Bar plot frame
        fig, ax = plt.subplots()

        fig.set_dpi(80)
        fig.set_size_inches(h=4,w=10)

        t = []
        t_length = TorBrowser.history_length
        for i in range(t_length):
            t.append(i)

        canvas = FigureCanvasTkAgg(fig, master = frame)
        #canvas.draw()

        def axes_settings(axes: Axes, rates_visible_max: int = 30):
            axes.set_title("Rate history") #ax.clear also clears axes settings

            axes.set_xlim(-1, t_length)
            axes.set_xlabel("Time in minutes")

            axes.set_ylim(0, rates_visible_max)
            axes.set_ylabel("Number of requests")

        axes_settings(ax)

        def rotate(l: list, n: int):
            """Rotates the list l BACKWARDS by n steps"""

            return l[n:] + l[:n]

        def bar_updater():
            """Updates the figure using the Tor requests history list"""
            ax.clear()

            rates = TorBrowser.history_requests_list.copy()
            
            rates_visible_max = 30
            if max(rates) > rates_visible_max: #in case the rates exceed the visible max per min
                rates_visible_max = max(rates)

            reversed_rates = rates.copy()
            reversed_rates.reverse()

            rotated_rates = rotate(reversed_rates, TorBrowser.history_length - TorBrowser.history_lastpos - 1)

            ax.axhline(y=20, color = "lightgray")
            ax.axhline(y=10, color = "lightgray")
            ax.axhline(y=TorBrowser.REQUESTS_PER_MIN, color = "green")
            ax.bar(t, rotated_rates)
            #print(t, rates, rotated_rates)

            axes_settings(ax, rates_visible_max=rates_visible_max)

            canvas.draw()

        self.update_functions.append(bar_updater)

        #Frame structure
        row = 0

        t2 = Label (frame, text="TorBrowser", bg=self.text_bg, fg=self.text_fg, font="none 12 bold").grid(row=row,column=0,sticky=W)
        row+=1

        label_widget = Label(frame, text="Tokens in bucket: ", bg=self.text_bg, fg=self.text_fg, font=self.entry_font)
        label_widget.grid(row=row, column=0, sticky=W)
        self.data_labels.append(DataLabel(label_widget, value_function=lambda: str(TorBrowser.tokens))) #scraper argument is not necessary here and therefore is removed
        row+=1

        driver_table_frame.grid(row=row, column=0)
        row+=1

        canvas.get_tk_widget().grid(row=row, column=0, sticky=W, pady=3)


        return frame

class DataLabel():
    """Used to simplify the updating of label texts by keeping track of the base text (specified upon creation) as well as the refscraper 
    key str for the value that should be appended to the label text 
    
    A number of these could be kept in a list and updated continously
    """

    def __init__(self, label: Label, key_str: str = None, refscraper: RefScraper = None, value_function: Callable[[], None] = None):
        self.label = label
        self.base_text = label["text"]
        self.key_str = key_str
        self.refscraper = refscraper
        self.value_function = value_function

    def update(self):
        """Updates label text to base text + the status value. If key_str is None and value_function exists use the function instead to determine value to be appended.
        This allows arbitrary functions for monitoring
        
        """
        if self.key_str != None and self.refscraper != None:
            value_text = self.refscraper.status_dict[self.key_str]

        elif self.key_str != None and self.value_function != None:
            value_text = self.value_function(self.key_str)

        elif self.key_str == None and self.value_function != None:
            value_text = self.value_function()
        else:
            raise NotImplementedError("don't know what to do here")
        
        self.label.configure(text=self.base_text + value_text)


if __name__ == "__main__":

    r = RefScraper()
    print("starting refscraper")
    r.start(restart=True)
















