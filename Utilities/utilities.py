import threading
import multiprocessing
from typing import Union
import time
import pickle
import socket
import os
import sqlite3 as sq

import ssl
import smtplib
from email.mime.text import MIMEText
from email.mime.multipart import MIMEMultipart

class ProtocolError(Exception):
    pass

class BetterEvent():
    """
    A better form of the python thread and process events which allow to also wait for the event to be unset, wait_for_false. BetterEvents update_functions attribute can also be used to create meshed events which allow for AND and OR gates for example.  
    
    """
    def __init__(self, module) -> None:
        self.b_event = module.Event()
        self.opp_b_event = module.Event()

        self.update_functions = []

        if not self.b_event.is_set(): #false
            self.opp_b_event.set()

    def set(self) -> None:
        """Sets the flag to true"""
        self.b_event.set()
        self.opp_b_event.clear()

        for f in self.update_functions:
            f()

    def clear(self) -> None:
        """Clears the flag"""
        self.b_event.clear()
        self.opp_b_event.set()

        for f in self.update_functions:
            f()

    def is_set(self) -> bool:
        """Returns true if the flag is set, otherwise returns false."""
        return self.b_event.is_set()
    
    def is_unset(self) -> bool:
        """Returns true if the flag is not set, otherwise returns false."""
        return self.opp_b_event.is_set()

    def wait(self, timeout=None) -> None:
        """Waits for the flag to be set to true"""
        self.b_event.wait(timeout=timeout)

    def wait_for_false(self, timeout=None) -> None:
        """Waits for the flag to be set to false"""
        self.opp_b_event.wait(timeout=timeout)





@staticmethod
def events_any(*events: BetterEvent) -> BetterEvent:
    """Returns a meshed event that is true when any of the provided events are set. This can be used to be able to wait for any number of events. Currently returns a threading BetterEvent and only works in the same process
    """
    #thread_list = []
    all_events = list(events)
    event_lock = threading.Lock()
    meshed_event = BetterEvent(threading)

    def or_update():
        with event_lock:

            one_true = False #det här kanske ger upphov till buggar, vi får se
            for e in all_events:
                if e.is_set():
                    one_true = True
                    break

            if one_true:
                meshed_event.set()
            else:
                meshed_event.clear()

    for e in events:
        e.update_functions.append(or_update)

    return meshed_event

@staticmethod
def events_all(*events: BetterEvent) -> BetterEvent:
    """Returns a new betterevent which will be set whenever all events comprising it are true. Logically an AND gate"""

    all_events = list(events)
    event_lock = threading.Lock()
    meshed_event =  BetterEvent(threading)

    def and_update():
        with event_lock:
            
            all_true = True
            for e in all_events:
                
                if not e.is_set():
                    all_true = False
                    break

            if all_true:
                meshed_event.set()
            else:
                meshed_event.clear()

    for e in events:
        e.update_functions.append(and_update)

    return meshed_event

@staticmethod
def alarm(t: float, event: BetterEvent) -> None:
    """Waits t seconds, then sets event"""

    time.sleep(t)
    event.set()





@staticmethod
def order_list_cleaning(order_list: list):
    """Cleans an order list by removing orders whose date is past today.
    
    """

    cleaned_order_list = []

    for o in order_list:
        today = time.gmtime()
        order_date = o["date"]

        month = str(today[1])
        if len(month) == 1:
            month = "0" + month

        day = str(today[2])
        if len(day) == 1:
            day = "0" + day

        today_int = int(str(today[0]) + month + day) #as int eg. 20240411


        if today_int <= order_date:
            cleaned_order_list.append(o)

    return cleaned_order_list

@staticmethod
def add_orders(base_order_list: list, orders_to_be_added: list) -> list:
    """Adds orders not present in the base_order_list to it, uses a set to speed up uniqueness checking"""

    marketIds = set()

    for o in base_order_list:

        marketIds.add(o["marketId"]) #Får titta mer här sen !!!, vet inte varför string kommer här ibland

    for o in orders_to_be_added:
            
        if o["marketId"] not in marketIds:
            base_order_list.append(o)

    return base_order_list

@staticmethod
def file_list_not_empty(file_list: list) -> bool:
    """Checks a file list if the file in question exists and contains a list with len > 0, if so returns True. Otherwise returns False"""
    if os.path.exists(file_list[0]):

        with file_list[2]:
            order_list = p_load(file_list[0])

            if isinstance(order_list, list) and len(order_list) > 0:
                return True
    
    return False



@staticmethod
def _socket_receive(socket) -> bytes:
    full_msg = None
    while True: #reading message
        data = socket.recv(1024)
        if not data:
            break

        if full_msg is not None: #since data is only a part of the message
            full_msg = b"".join([full_msg, data])
        else:
            full_msg = data

    return full_msg

@staticmethod
def _socket_send(socket: socket.socket, msg_bytes: bytes) -> None:
    total_sent = 0
    while total_sent < len(msg_bytes):
        sent = socket.send(msg_bytes[total_sent:])
        total_sent += sent

@staticmethod
def send_protocol(msg: object, address: str) -> None:
    """Connects to a socket address, sends the bytes message and waits for the message to be returned which guarantees that the message was received in full. If any error occurs or the message wasn't 
    received back from the address socket, returns the message passed."""

    s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)


    msg_pickled = pickle.dumps(msg)
    try:
        s.connect(address)

        _socket_send(s, msg_pickled)
        s.shutdown(socket.SHUT_WR)

        received_msg = _socket_receive(s)
        s.shutdown(socket.SHUT_RD)

        if received_msg != msg_pickled:
            raise ProtocolError

    except (BrokenPipeError, ConnectionRefusedError, ConnectionResetError) as e:
        raise ProtocolError
    finally:
        s.shutdown(socket.SHUT_RDWR)
        s.close()

@staticmethod
def receive_protocol(connected_socket: socket.socket) -> object:
    """Takes a connection socket and returns the received object using the made up protocol which also sends back the same message as an acknowledgement"""
    try:
        conn = connected_socket

        pickled_msg = _socket_receive(conn)
        conn.shutdown(socket.SHUT_RD)

        _socket_send(conn, pickled_msg)
        conn.shutdown(socket.SHUT_WR)

        msg = pickle.loads(pickled_msg)

    except (BrokenPipeError, ConnectionRefusedError, ConnectionResetError) as e:
        raise ProtocolError
    
    return msg




@staticmethod
def p_load(path: str):
    """Loads a file using pickle and returns the contents"""
    with open(path, "rb") as f:
        data = pickle.load(f)

    return data

@staticmethod
def p_dump(path: str, data) -> None:
    """Dumps the data into the file provided, overwriting the file in the process"""

    with open(path, "wb") as f:
        pickle.dump(data, f)




@staticmethod
def email_msg(text: str) -> None:
    """Sends an email to the reciever_email containing text string"""

    port = 465
    smtp_server = "smtp.gmail.com"
    password = ""
    sender_email = ""
    receiver_email = ""

    context = ssl.create_default_context()

    msg = MIMEMultipart("alternative")
    msg["Subject"] = "Program status"
    msg["From"] = sender_email
    msg["To"] = receiver_email

    part1 = MIMEText(text, "plain")
    msg.attach(part1)

    with smtplib.SMTP_SSL(smtp_server, port, context=context) as server:
        server.login(sender_email, password)

        server.sendmail(sender_email, receiver_email, msg.as_string())



@staticmethod
def db_access_init(db_path: str) -> tuple:
    """
    Returns a new database connection and cursor as a tuple. Useful for multithreading and possibly also multiprocessing since every thread needs their own sql objects.
    Also uses a few useful settings like foreign keys and row_factory=sq.Row. Runs in wal mode to prevent "database is locked" exceptions
    """
    db_conn = sq.connect(db_path)
    #db_conn.execute("PRAGMA foreign_keys = OFF")

    res = db_conn.execute("PRAGMA journal_mode = WAL").fetchone()[0] #returns a cursor object which points to a tuple of (wal,)
    if res != "wal":
        raise NotImplementedError("Couldn't enable wal mode for db connection")

    db_conn.row_factory = sq.Row
    db_cur = db_conn.cursor()
    return db_conn, db_cur

@staticmethod
def db_insert(row_dict: dict, table_name: str, db_conn: sq.Connection = None, db_cur: sq.Cursor = None) -> int:
    """Inserts the row_dict into the table given by table_name, any entries in row_dict which do not correspond to any column in table_name are added to table_name.
    If the primary key for the table is specified the function will update the existing entry instead. Always returns the primary key id for the insertion.
    
    If the db_cur or db_conn argument is None then uses the class instance connection and cursor. Otherwise it should be provided if used in a multithreading/multiprocessing context.
    """

    def is_float(string: str) -> bool:
        """Determines if the string passed is a definite float"""
        string = string.replace(".", "1", 1)
        if string.isnumeric():
            return True
        else:
            return False

    row_dict = row_dict.copy() #to prevent pk_value later being present, since row_dict is modified later

    if db_conn is None or db_cur is None:
        raise ValueError("db_conn or db_cur is None")
    
    if "table" in row_dict or "pk_name" in row_dict:
        raise ValueError("row_dict has key named table")

    #add new columns not in table
    res = db_cur.execute("PRAGMA table_info(" + table_name + ")")
    table_cols = res.fetchall()
    table_col_names = set([col[1] for col in table_cols])
    cols_to_add = set()
    for r in row_dict:
        if str(r).lower() not in table_col_names:
            cols_to_add.add(r)


    col_dicts = {}
    for col_name in cols_to_add:

        row_val = row_dict[col_name]

        if isinstance(row_val, int) or (isinstance(row_val, str) and row_val.isnumeric()):
            col_type = "INTEGER"
        elif isinstance(row_val, float) or (isinstance(row_val, str) and is_float(row_val)):
            col_type = "REAL"
        elif isinstance(row_val, str):
            col_type = "TEXT"
        else:
            print(row_dict)
            raise NotImplementedError("db type not implemented", type(row_val), row_val, col_name)

        col_dicts["table_name"] = table_name
        if isinstance(col_name, int) or col_name[0].isnumeric(): #ready col_dicts values to alter the table
            col_dicts["col_name"] = "'" + str(col_name) + "'" #if the name is an int/float, use the string representation
        else:
            col_dicts["col_name"] = col_name.lower()

        col_dicts["col_type"] = col_type

        sql_str = "ALTER TABLE {table_name} ADD COLUMN {col_name} {col_type}".format(**col_dicts)
        with db_conn:
            try:
                db_cur.execute(sql_str) #or here
            except sq.OperationalError as e:
                print(sql_str)
                raise e

    #get primary key name and check if it is in row_dict
    pk_info = db_cur.execute("SELECT * FROM pragma_table_info('" + table_name + "') WHERE pk").fetchone()
    existing_entry = None
    if pk_info is not None and pk_info["name"] in row_dict:
        pk_name = pk_info["name"]
        check_dict = {"pk_value": row_dict[pk_info["name"]]}
        existing_entry = db_cur.execute("SELECT * FROM " + table_name + " WHERE " + pk_name + "=:pk_value", check_dict).fetchone()

    if existing_entry is not None: #the row already exist, update
        set_str = " SET"
        for i, key in enumerate(row_dict):
            col_key = key
            val_key = key
            if isinstance(key, int) or key[0].isnumeric(): #escaping, fucking annoying
                col_key = "'" + str(key) + "'"

            if i == 0:
                set_str = set_str + " " + col_key + " =:" + val_key +  ""
            else:
                set_str = set_str + ", " + col_key + "=:" + val_key +  " "

        row_dict["pk_value"] = row_dict[pk_name] #huh? Tror bara denna bara används temporärt för att ge värde till sql_str nedanför
        with db_conn:
            try:
                sql_str = "UPDATE " + table_name + set_str + "WHERE " + pk_name + "=:pk_value"
                db_cur.execute(sql_str, row_dict) #and here
            except sq.OperationalError as e:
                print(sql_str)
                raise e

        return row_dict[pk_name]
    else:
        #add the values for each row_dict
        cols_str = ""
        vals_str = ""
        for key in row_dict:

            if key[0].isnumeric():
                key = "'" + key + "'"

            if cols_str == "":
                cols_str = cols_str + key
                vals_str = vals_str + ":" + key
            else:
                cols_str = cols_str + ", " + key
                vals_str = vals_str + ", :" + key

            sql_str = "INSERT INTO " + table_name +  " (" + cols_str + ") VALUES (" + vals_str + ")"
        with db_conn:
            try:

                db_cur.execute(sql_str, row_dict) #here
                insert_id = dict(db_cur.execute("SELECT last_insert_rowid()").fetchone())["last_insert_rowid()"]
            except (sq.OperationalError, sq.ProgrammingError) as e:
                print(sql_str)
                raise e

        return insert_id