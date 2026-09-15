import multiprocessing.process
import sys

sys.path.append("") #add betting folder to path

import pickle
import os
from Utilities import utilities
import threading
import inotify.adapters
import multiprocessing
from multiprocessing.connection import Listener, Client
import time
import socket
from types import UnionType
import posixpath
from Utilities.utilities import ProtocolError



ENCODING = "utf-8"

class processIO():
    """Will manage input and output through various methods to separate it from the other processes. 
    
    """

    def __init__(self, input_address_name: str, stop_flag: utilities.BetterEvent, order_select_query: str):
        """The input and output address names are used for the socket file names. The stop flag is necessary for the poison signal to propagate into the above class. Input file path is a file which 
        will contain any received orders which have not been processed yet"""

        self.socket_folder = "Sockets"

        self.stop_flag = stop_flag

        self.input_address = os.path.join(self.socket_folder, input_address_name)
        # self.output_address = os.path.join(self.socket_folder, output_address_name)

        if os.path.exists(self.input_address):
            raise NotImplementedError("Input socket file already exists, cannot start")

        self.db_path = "orders.db"
        self.table_name = "order_table"
        self.order_ping_delay = 60
        self.order_select_query = order_select_query
        self.input_event = utilities.BetterEvent(multiprocessing)

        self.db_conn, self.db_cur = utilities.db_access_init(self.db_path)



        self.server_thread = threading.Thread(target = self.server)
        self.order_ping_thread = threading.Thread(target = self.order_ping)

        self.t_list = [self.server_thread]
        for t in self.t_list:
            t.start()


    def server(self) -> None:

        with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as s:
            s.bind(self.input_address)

            s.listen(0) 
            while not self.stop_flag.is_set():
                conn, addr = s.accept()


                try:

                    decoded_msg = utilities.receive_protocol(conn)

                except ProtocolError as e:
                    print("protocol exception", e)
                    pass

                finally:
                    conn.shutdown(socket.SHUT_RDWR)
                    conn.close()

                if decoded_msg == "STOP":
                    self.stop_flag.set()


                if isinstance(decoded_msg, str) and decoded_msg == "STOP":
                    self.stop_flag.set()

                elif isinstance(decoded_msg, list): #Nothing will happen to other message types
                    self.append_input(decoded_msg)

            print("server stopping")
            s.shutdown(socket.SHUT_RDWR)

        try:
            os.remove(self.input_address) #to prevent socket binding error later
        except FileNotFoundError:
            pass

    def server_exit(self) -> None:
        """Connects to the server socket and sends the stopping string to let it exit"""
        try:
            utilities.send_protocol("STOP", self.input_address)
        except FileNotFoundError:
            pass


    
    def order_ping(self) -> None:
        """Pings the order database and checks for length"""

        db_conn, db_cur = utilities.db_access_init(self.db_path)

        while self.stop_flag.is_unset():
            res = db_cur.execute(self.order_select_query).fetchall()
            orders = [dict(row) for row in res]

            if len(orders) > 0:
                self.input_event.set()
            else:
                self.input_event.clear()

            self.stop_flag.wait(self.order_ping_delay)


    def get_all_input(self) -> list:
        """Gets all input orders"""
        res = self.db_cur.execute(self.order_select_query).fetchall()
        orders = [dict(row) for row in res]

        return orders


    def append_output(self, order_list: list) -> None:
        """Inserts/updates the order provided into the database"""
        for order in order_list:
            utilities.db_insert(row_dict=order, table_name=self.table_name, db_conn=self.db_conn, db_cur=self.db_cur)
        self.db_conn.execute("PRAGMA wal_checkpoint(FULL)") 

    def clean_input(self) -> None:
        """Deletes orders with date less than today"""
        today = time.gmtime()

        month = str(today[1])
        if len(month) == 1:
            month = "0" + month

        day = str(today[2])
        if len(day) == 1:
            day = "0" + day

        today_int = int(str(today[0]) + month + day) #as int eg. 20240411

        with self.db_conn:
            self.db_cur.execute("DELETE FROM " + self.table_name + " WHERE date < " + str(today_int))



    def num_orders_left(self) -> int:
        """Gets the number of relevant orders in the database"""

        orders = self.get_all_input()
        num = len(orders)

        return num
    
    def order_table_setup(self) -> None:
        with self.db_conn:
            self.db_cur.execute("""
                    CREATE TABLE order_table(
                    order_id INTEGER PRIMARY KEY,
                            
                    team1 TEXT,
                    team2 TEXT,
                    
                    country_code TEXT,         
                    competition TEXT,
                    competition_prefix TEXT,
                    date INTEGER,
                    time TEXT,
                    
                    marketId TEXT,
                    marketName TEXT,
                   
                    scraped_match_id INTEGER,
                    model_predictions BLOB
                        )""")






class orderHandling():
    """Class implementing basic start and orderhandling functionality which should be used in subclasses for inheritance"""


    def start(self, restart: bool = False):
        """Starts the orderHandling structure. If restart is set to True then tries handling orders again after a timeout period in case of unhandled exceptions which would otherwise lead to shutdown, this is intended to make the processes more reliable for longer periods."""
        restart_timeout = 60*30 #in seconds

        
        self.io = processIO(input_address_name=self.input_address_name, stop_flag=self.stop_flag, order_select_query=self.order_select_query)
        self.num_orders = self.io.num_orders_left()
        
        
        if hasattr(self, "start_process_functions"):

            for p in self.start_process_functions:
                process = multiprocessing.Process(target=p)
                process.start()
                self.p_list.append(process)

        #self.retry_failed_orders()
        self.io.clean_input()
        
        input_event = self.io.input_event
        stop_flag = self.stop_flag

        or_event = utilities.events_any(stop_flag, input_event)

        if self.io.num_orders_left() > 0: #orders in input file
            input_event.set()


        while not stop_flag.is_set():
            or_event.wait() #if orders exist in input file or stop_flag

            if input_event.is_set() and not stop_flag.is_set():
                
                orders = self.io.get_all_input()

                num = len(orders)
                for order in orders:

                    self.handle_order(order)
                    num = num-1
                    self.num_orders = num
                    
                    #restart orderhandling if necessary
                    if self.stop_flag.is_set() and self.error_flag.is_set() and restart:
                        self.error_flag.clear()
                        self.stop_flag.clear() #only stopped due to error, so clear here

                        alarm_event = utilities.BetterEvent(threading)
                        alarm_thread = threading.Thread(target=utilities.alarm, args=(restart_timeout, alarm_event), daemon=True)
                        restart_event = utilities.events_any(alarm_event, stop_flag)
                        alarm_thread.start()
                        print(time.localtime(time.time()), "Started restart timer")
                        restart_event.wait()
                        break

                    elif self.stop_flag.is_set():
                        break



        self.io.server_exit()
        self.close()

    def handle_order(self, order: dict) -> None:
        """Sends one order to the orderhandling_function and if succesful, meaning no exception was thrown out, moves it to the output file and returns True. Otherwise adds it to the failed_orders file and returns False"""

        failed = False
        try:

            self.orderhandling_function(order)

        except Exception as e: #order failed
            print("exception", e)
            failed = True
        
        if not failed:
            self.io.append_output([order])
        


    def num_orders_left(self):
        """Gets the number of orders in the input file"""
        return self.num_orders
