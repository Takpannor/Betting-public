
import sys

sys.path.append("") #add betting folder to path

import posixpath
import socket
import pickle
import Utilities.utilities as ut

if __name__ == "__main__": #'team1': 'Remo', 'team2': 'Floresta EC', 'country_code': 'BR', 'competition': 'Serie C', 'competition_prefix': 'Brazilian', 'date': '2024-05-12', 'time': '22:00:00', 'marketId': '1.228741538', 'marketName': 'Match Odds'}
    socket_folder = "Sockets"

    # input_address_path = posixpath.join(socket_folder, "input_betfair")
    # ut.send_protocol("STOP", input_address_path)

    input_address_path = posixpath.join(socket_folder, "input_scraper")
    ut.send_protocol("STOP", input_address_path)

"""
{'team1': 'Criciuma', 'team2': 'SE Palmeiras', 'country_code': 'BR', 'competition': 'Serie A', 'competition_prefix': 'Brazilian', 'date': '2024-05-19', 'time': '14:00:00', 'marketId': '1.228589980', 'marketName': 'Match Odds'} 1716127200 1716127200
{'team1': 'Fluminense', 'team2': 'Juventude', 'country_code': 'BR', 'competition': 'Serie A', 'competition_prefix': 'Brazilian', 'date': '2024-05-19', 'time': '19:00:00', 'marketId': '1.228590243', 'marketName': 'Match Odds'} 1716145200 1716145200
{'team1': 'Atletico MG', 'team2': 'Bahia', 'country_code': 'BR', 'competition': 'Serie A', 'competition_prefix': 'Brazilian', 'date': '2024-05-19', 'time': '19:00:00', 'marketId': '1.228590118', 'marketName': 'Match Odds'} 
{'team1': 'Cuiaba', 'team2': 'Internacional', 'country_code': 'BR', 'competition': 'Serie A', 'competition_prefix': 'Brazilian', 'date': '2024-05-19', 'time': '21:30:00', 'marketId': '1.228589739', 'marketName': 'Match Odds'}
{'team1': 'Gremio', 'team2': 'Bragantino SP', 'country_code': 'BR', 'competition': 'Serie A', 'competition_prefix': 'Brazilian', 'date': '2024-05-19', 'time': '21:30:00', 'marketId': '1.228589860', 'marketName': 'Match Odds'}

"""