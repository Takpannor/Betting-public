import matplotlib
from sklearn import linear_model
import copy

import matplotlib.pyplot as plt
import numpy as np
import os
import pandas as pd
import math
from typing import Callable
import pynput.keyboard as kb
import threading
import pickle
import re
import posixpath
import random


from sklearn.pipeline import Pipeline
from sklearn.feature_selection import SelectFromModel
from sklearn.preprocessing import StandardScaler
from sklearn.datasets import make_circles, make_moons
from sklearn.metrics import accuracy_score, balanced_accuracy_score

from sklearn.feature_selection import RFECV
from sklearn.model_selection import TimeSeriesSplit

from sklearn.ensemble import RandomForestClassifier
from sklearn.neural_network import MLPClassifier
from sklearn.svm import SVC
from sklearn.neighbors import KNeighborsClassifier

#Kommer behöva funktion som går igenom alla matcher och hämtar samples för visst lag ifall det är deltagande i en match
#(inom ett visst antal seasons)



class BallModel():
    """Uses different statistical models including machine learning and data cleaning methods in order to effectively 
    predict certain features such as match wins
    
    """

    def __init__(self):

        self.base_path = "Model/"
        self.data_path = "Data/"

        #refers to unfinished work if not explicitly finished in variable name
        self.starter_memory_path = posixpath.join(self.base_path, ".starter")
        self.unique_memory_path = posixpath.join(self.base_path, ".unique")
        self.unique_finished_memory_path = posixpath.join(self.base_path, ".unique_finished")
        self.intersection_memory_path = posixpath.join(self.base_path, ".intersection")
        self.intersection_finished_memory_path = posixpath.join(self.base_path, ".intersection_finished")

        #contains extra keys and completed seasons/competitions/govs
        self.ccl_final_memory_path = posixpath.join(self.base_path, ".final_finished")
        self.pre_dataset_memory_path = posixpath.join(self.base_path, ".pre_dataset")
        self.dataset_memory_path = posixpath.join(self.base_path, ".dataset")

        self.failed_orders_path = posixpath.join(self.base_path,".failed_orders")

        self.input_file_path = posixpath.join(self.base_path, ".input")
        self.output_file_path = posixpath.join(self.base_path, ".output")

        self.input_address_name = "input_model"
        self.output_address_name = "input_betfair"
        
        self.orderhandling_function = self.prediction



        self.stop_flag = False
        self.listener = kb.Listener(on_press=self.keyboard_on_press)
        self.listener.start()


    #Common column construction parts
    def ucl_starter(self, path: str, overwrite_unfinished: bool = False, save_result: bool = True) -> list[dict]:
        """Returns one or several dictionaries containing paths that match the unique columns also listed in the dictionary. The dictionary has values for the following keys:
        "match_paths", "common_columns", "total_num_matches", "dropped_columns"
        
        For a column to be valid it must contain some values other than Nan regardless of type: str, float etc. This is to ensure the possibility of imputation and later also
        summations per match later. Percentages are also ignored as they can be calculated later.
        Also adds a (H,A) prefix to columns gotten from team csv files to separate the different team stats.
        
        """
        #tries to load unfinished list from memory
        try:
            with open(self.unique_memory_path, "rb") as f:
                common_list, num_matches, path_last= pickle.load(f)

            if path_last != path and not overwrite_unfinished:
                raise ValueError("Memory path does not match argument path")
            elif overwrite_unfinished:
                try:
                    os.remove(self.unique_memory_path)
                except FileNotFoundError:
                    pass

                try:
                    os.remove(self.starter_memory_path)
                except FileNotFoundError:
                    pass
            
                raise FileNotFoundError #to start from the beginning using the except handler

            
                
        except FileNotFoundError:
            common_list = []
            num_matches = [0]

        #creates a list of unique column configurations
        self.__rec_ucl_starter(curr_path=path, common_list=common_list, num_matches=num_matches, layer=0)

        if self.stop_flag: #saves to memory
            with open(self.unique_memory_path, "wb") as f:
                pickle.dump((common_list, num_matches, path), f)
            self.shutdown()
            return
        else: #meaning the function has finished succesfully
            try:
                os.remove(self.unique_memory_path)
            except FileNotFoundError:
                pass

        for common_block in common_list: #to make use of the num matches
            common_block["total_num_matches"] = num_matches[0]

        if save_result: #overwrites automatically
            with open(self.unique_finished_memory_path, "wb") as f:
                pickle.dump(common_list, f)

        return common_list
    
    def __rec_ucl_starter(self, curr_path: str, common_list: list[dict], num_matches: list, column_dict: dict = {}, layer: int=0) -> None:
        """Recursive function for column_compiler to add match paths to set, uses a dictionary to store unique column configurations 
        with the cc block which is also added to the common list. Uses the .starter memory file to load any unfinished progress. Layer is used to keep 
        track of the depth that the current iteration is running on

        """

        def memory_save(unfinished_names: list) -> None:
            """Saves or appends the unfinished names to be loaded on the next run. Column_compiler saves the unique list itself"""
            try:
                with open(self.starter_memory_path, "rb") as f:
                    l = pickle.load(f)
            except FileNotFoundError:
                l = []

            l.append(unfinished_names)

            with open(self.starter_memory_path, "wb") as f:
                pickle.dump(l, f)

        def memory_load() -> list:
            """Loads and returns the first item in the saved list before removing it and resaving the list.
            If the list is empty after a load, it also deletes the file. If the memory_file does not exist raises FileNotFoundError
            """

            with open(self.starter_memory_path, "rb") as f:
                l = pickle.load(f)
            
            #print(l, len(l))
            first = l.pop()

            if len(l) == 0:
                try:
                    os.remove(self.starter_memory_path)
                except FileNotFoundError:
                    pass
            else:
                with open(self.starter_memory_path, "wb") as f:
                    pickle.dump(l, f)

            return first


        if "match_" in curr_path:
            usable_columns = set()
            dropped_columns = set()

            file_list = os.listdir(curr_path)
            for file_name in file_list:
                if "info.csv" == file_name:
                    df = pd.read_csv(posixpath.join(curr_path, file_name))
                    if not df["FINISHED"][0]:
                        return
                    else:
                        num_matches[0] += 1

            for file_name in file_list:
                if file_name not in ["info.csv", "Away_Goalkeepers.csv", "Away_Players.csv", "Home_Goalkeepers.csv","Home_players.csv"]: #to skip over shots and overview etc.
                    continue

                prefix = ""
                if "Away" in file_name:
                    prefix = "A_"
                elif "Home" in file_name:
                    prefix = "H_"
                if "Goalkeepers" in file_name:
                    prefix+="GK_"

                df = pd.read_csv(posixpath.join(curr_path,file_name))
                df.drop(labels="Unnamed: 0", axis=1, inplace=True)

                if file_name == "info.csv":
                    for cols in df.columns.values:
                        if cols.isupper():
                            df.drop(labels=cols, axis=1, inplace=True)

                for c in df.columns.values:
                    if "pct" in c: #skippar alla procent kolonner, beräknas bäst senare
                        continue

                    usable = False
                    for i in range(len(df[c])):
                        v = df[c][i]
                        #vi använder inte denna procentkollaren: and not ("pct" in c and df[c.replace("_pct","")][i] == 0):
                        if not pd.isnull(v):

                            usable = True
                            break
                    if usable:
                        usable_columns.add(prefix + c)
                    else:
                        dropped_columns.add(prefix + c)
            
            key = str(usable_columns)

            if key in column_dict:
                column_dict[key]["match_paths"].add(curr_path)
            else:
                cc_block = {"common_columns": usable_columns, "match_paths": {curr_path}, "dropped_columns": dropped_columns}#, "dropped_columns": dropped_columns}
                column_dict[key] = cc_block
                common_list.append(cc_block)

        elif "cache" in curr_path or "warnings" in curr_path:
            return
        else:
            try: 
                names = memory_load()
            except FileNotFoundError:
                names = os.listdir(curr_path)
            unfinished = copy.deepcopy(names)

            for n in names:
                if layer == 0:
                    print(n)
                self.__rec_ucl_starter(posixpath.join(curr_path,n), common_list=common_list, num_matches=num_matches, column_dict=column_dict, layer=layer+1)
                if layer == 0:
                    print(n, len(unfinished))

                if self.stop_flag:
                    memory_save(unfinished)
                    return
                else:
                    unfinished.remove(n)

    def ccl_load_unique(self) -> list[dict]:
        """Loads and returns the saved finished unique columns list"""

        with open(self.unique_finished_memory_path, "rb") as f:
            ucl = pickle.load(f)
        return ucl



    def ccl_intersection_constructor(self, unique_list: list[dict], overwrite_unfinished: bool = False, save_result: bool = True) -> None:
        """Goes through a simple cc list and updates the common_columns list with super or subset paths added and additional sets constructed.
        overwrites unfinished result if bool is True
        """

        def subset_parent_child_adjuster(common_list: list, common_block: dict):
            """Updates the super/subsets matches according to the usable columns. Returns the additional paths
            
            """
            curr_paths = common_block["match_paths"]
            usable_columns = common_block["common_columns"]
            dropped_columns = common_block["dropped_columns"]
            additional_paths = curr_paths

            for cb in common_list:
                if usable_columns.issubset(cb["common_columns"]):
                    additional_paths.update(cb["match_paths"])
                
                if cb["common_columns"].issubset(usable_columns):
                    cb["match_paths"].update(curr_paths)

            return additional_paths

        def equality(common_list: list, common_block: dict) -> bool:
            """Find match and/or create new in common_list here using usable_columns
            
            """
            curr_paths = common_block["match_paths"]
            usable_columns = common_block["common_columns"]
            dropped_columns = common_block["dropped_columns"]

            for cb in common_list:
                if usable_columns == cb["common_columns"]:
                    cb["match_paths"].update(curr_paths)

                    subset_parent_child_adjuster(common_list=common_list, common_block=common_block)

                    return True #ingen anledning att fortsätta
            return False
        
        def subsets(common_list: list, common_block: dict) -> None:
            """Finds the blocks which contain the common columns subset and add their paths to the paths return variable, also adds current path to any supersets.
            Creates a new block from the usable_columns
            """
            curr_paths = common_block["match_paths"]
            usable_columns = common_block["common_columns"]
            dropped_columns = common_block["dropped_columns"]

            path_adjusted = subset_parent_child_adjuster(common_list=common_list, common_block=common_block)

            final_add(common_list=common_list, common_block=common_block, pre_paths=path_adjusted)
        
        def common_columns(common_list: list, common_block: dict) -> list[list, list]:
            """Find list of common columns between column argument and columns in list
            
            """
            curr_paths = common_block["match_paths"]
            usable_columns = common_block["common_columns"]
            dropped_columns = common_block["dropped_columns"]
            total_num_matches = common_block["total_num_matches"]

            common_columns_list = []
            for common_block in common_list:
                
                diff1 = usable_columns-common_block["common_columns"]
                diff2 = common_block["common_columns"]-usable_columns #to amke sure subsets are not included

                common_columns = usable_columns-diff1

                if len(diff1) > 0 and len(diff2) > 0 and common_columns not in common_columns_list:

                    d_columns = copy.deepcopy(dropped_columns)
                    d_columns.update(diff1)
                    common_columns_list.append({"common_columns": common_columns, "dropped_columns": d_columns, "match_paths": set(), "total_num_matches": total_num_matches})


            return common_columns_list
        
        def final_add(common_list: list, common_block: dict, pre_paths: set = None):
            curr_paths = common_block["match_paths"]
            usable_columns = common_block["common_columns"]
            dropped_columns = common_block["dropped_columns"]
            total_num_matches = common_block["total_num_matches"]

            if pre_paths is None:
                new_common_block = {"match_paths": {curr_paths}, "common_columns": usable_columns, "dropped_columns": dropped_columns,
                                    "total_num_matches": total_num_matches}
            else:
                new_common_block = {"match_paths": pre_paths, "common_columns": usable_columns, "dropped_columns": dropped_columns,
                                    "total_num_matches": total_num_matches}
            #print(dropped_columns)
            common_list.append(new_common_block)



        def routine(common_list: list, common_block: dict) -> None:

            if equality(common_list=common_list, common_block=common_block):
                return
            
            subsets(common_list=common_list, common_block=common_block) #this adds the columns as a block

            l = common_columns(common_list=common_list, common_block=common_block)
            for block in l:
                routine(common_list=common_list, common_block=block)

        if os.path.exists(self.intersection_memory_path) and not overwrite_unfinished:

            with open(self.intersection_memory_path, "rb") as f:
                unique_list, common_list = pickle.load(f)

        else:

            common_list = []
            unfinished = copy.copy(unique_list) #a shallow copy should suffice



        for block in unique_list: #adds the blocks one by one

            routine(common_list=common_list, common_block=block)

            if self.stop_flag:
                with open(self.intersection_memory_path, "wb") as f:
                    pickle.dump((unfinished, common_list), f)
                self.shutdown()
                return
            else:
                unfinished.remove(block)
        
        if save_result: #save finished list
            with open(self.intersection_finished_memory_path, "wb") as f:
                pickle.dump(common_list, f)

        try: #remove any old memory file
            os.remove(self.intersection_memory_path)
        except FileNotFoundError:
            pass
        
        unique_list.clear()
        unique_list.extend(common_list)

    def ccl_load_intersection(self) -> list[dict]:
        """Loads the finished intersection file and returns it
        
        """
        with open(self.intersection_finished_memory_path, "rb") as f:
            ccl = pickle.load(f)
        return ccl


    def ccl_final(self, ccl: list, save_result: bool = True) -> None:
        """Adds a few final keys to the block dictionary and sorts the list in percentage contained order, highest first, 
        before saving the list if save_result is True. The keys added are the ones given by 
        ccl_extra_keys and complete_column_folders functions.
        
        """

        self.complete_column_folders(ccl)
        self.ccl_extra_keys(ccl)
        self.ccl_sort(ccl, sort_key="contained_pct")
        if save_result:
            with open(self.ccl_final_memory_path, "wb") as f:
                pickle.dump(ccl, f)

    def ccl_load_final(self) -> list[dict]:
        with open(self.ccl_final_memory_path, "rb") as f:
            ccl = pickle.load(f)
        return ccl



    #Column utility
    def complete_column_folders(self, ccl: list[dict]) -> None:
        """Adds entries for complete governing bodies, competitions and seasons as path strings. The complete parent entry is only for complete subfolders.
        Adds the following keys: "complete_governing_bodies", "complete_competitions", "complete_seasons". FUNGERAR EJ
        """

        #uses a tree dictionary structure with "comp: seasonslist[dict]" and "season: matchnameslist" 
        
        def tree_maker(ccl: list[dict]) -> dict:
            tree_struct = {}

            for block in ccl:

                #constructs the tree structure, check it later against the actual folders
                for path in block["match_paths"]:
                    rest_path = path[len(self.data_path):]
                    # difference between windows \ and unix path / separators
                    # not relevant anymore though
                    parts = re.split("[/]", rest_path)
                    gov_body = parts[0]
                    comp = parts[1]
                    season = parts[2]
                    match_num = parts[3]

                    try:
                        comp_dict = tree_struct[gov_body]
                    except KeyError:
                        comp_dict = {}
                        tree_struct[gov_body] = comp_dict
                        
                    try:
                        seasons_dict = comp_dict[comp]
                    except KeyError:
                        seasons_dict = {}
                        comp_dict[comp] = seasons_dict
                    
                    try:
                        seasons_dict[season].add(match_num)
                    except KeyError:
                        match_set = set()
                        seasons_dict[season] = match_set

            return tree_struct

        #check each block if it is equal to the tree structures matches etc
        def test_ccl_blocks_against_tree(ccl: list[dict], tree_struct: dict):
            """Tests ccl list against tree and adds complete section keys to each block"""

            def matches_in_sections(gov_body: str, comp: str, season: str, block: dict):
                """Returns match paths from block that match the provided sections"""

                test_path = posixpath.join(self.data_path, gov_body, comp, season)
                section_paths = set()
                full_paths = set()

                for match_path in block["match_paths"]:
                    if test_path in match_path:
                        section_paths.add(match_path[len(test_path + "/"):]) # extra slash since test_path lacks "/" at the end
                        full_paths.add(match_path)

                return section_paths, full_paths



            for block in ccl:
                block["complete_seasons"] = {}
                block["complete_competitions"] = {}
                block["complete_governing_bodies"] = {}

                gov_complete_list = {}

                for gov_body in tree_struct:
                    comps = tree_struct[gov_body]
                    comps_complete_list = {}

                    for comp in comps:
                        seasons = comps[comp]
                        seasons_complete_list = {}

                        for season in seasons:

                            #Season match paths test
                            tree_matches = seasons[season]
                            section_matches, full_match_paths = matches_in_sections(gov_body=gov_body, comp=comp, season=season, block=block)


                            if tree_matches == section_matches:
                                seasons_complete_list[season] = full_match_paths

                        #Seasons match, indicating complete competition
                        if list(seasons_complete_list.keys()) == list(tree_struct[gov_body][comp].keys()):

                            match_paths = set()
                            for p_set in seasons_complete_list.values():
                                match_paths.update(p_set)
                            
                            comps_complete_list[comp] = match_paths

                        else: #Incomplete competition, add individual season paths to a dict
                            full_path_dict = {}
                            for c in seasons_complete_list.keys():
                                full_path_dict[posixpath.join(self.data_path,gov_body,comp,c)] = seasons_complete_list[c]
                            block["complete_seasons"].update(full_path_dict)


                    #Complete competitions match, complete gov_body
                    if list(comps_complete_list.keys()) == list(tree_struct[gov_body].keys()):
                        match_paths = set()
                        for p_set in comps_complete_list.values():
                            match_paths.update(p_set)
                        
                        gov_complete_list[gov_body] = match_paths

                    else:
                        full_path_dict = {}
                        for c in comps_complete_list.keys():
                            full_path_dict[posixpath.join(self.data_path,gov_body,c)] = comps_complete_list[c]

                        block["complete_competitions"].update(full_path_dict)


                if list(gov_complete_list.keys()) == list(tree_struct.keys()):
                    full_path_dict = {}
                    for c in gov_complete_list.keys():
                        full_path_dict[posixpath.join(self.data_path,c)] = gov_complete_list[c]

                    block["complete_governing_bodies"].update(full_path_dict)


        tree = tree_maker(ccl=ccl)
        test_ccl_blocks_against_tree(ccl=ccl, tree_struct=tree)

    def ccl_extra_keys(self, ccl: list) -> None:
        """Adds a few extra keys to the ccl such as: 
        "len_common_columns", "len_match_paths", "contained_pct"
        
        """
        for common_block in ccl:
            common_block["len_match_paths"] = len(common_block["match_paths"])
            common_block["contained_pct"] = len(common_block["match_paths"])/common_block["total_num_matches"]
            common_block["len_common_columns"] = len(common_block["common_columns"])

    def ccl_sort(self, cc_block_list: list, sort_key: str) -> None:
        """Sorts the cc_block_list according to key in descending order according to any of the following keys:
        "len_match_paths", "contained_pct", "len_common_columns"
        
        """
        possible_sorts = ["len_match_paths", "contained_pct", "len_common_columns"] #only meaningful sorts, what would match_paths sort mean?
        #pct and len match paths give same result
        if sort_key not in possible_sorts:
            raise ValueError("Sorting key not valid")

        cc_block_list.sort(key=lambda cdict: cdict[sort_key], reverse=True)

        #s = sorted(cc_block_list, key=lambda cdict: cdict[sort_key], reverse=True)

        #return s

    def ccl_validity_check(self, cc_block_list: list) -> bool:
        """Checks if any blocks contain identical common_columns which should not occur if the list is valid.
        
        """

        for l1 in cc_block_list:
            for l2 in cc_block_list:
                if l1 is l2:
                    continue
                if l1["common_columns"] == l2["common_columns"]:
                    return "Invalid"
        return "Valid"

    def ccl_print(self, cc_block_list: list, dropped_columns: bool = False, sort_key: str = None) -> None:
        """Prints a ccl with a few keys, sort_key can be the following: "len_match_paths", "contained_pct", "len_common_columns"""

        if sort_key is not None:
            self.ccl_sort(cc_block_list, sort_key)

        if dropped_columns:
            print("len_match_paths", "total_num_matches", "contained_pct", "len_common_columns", "dropped_columns", "number of complete seasons", "number of complete competitions", "number of complete gov bodies")
        else:
            print("len_match_paths", "total_num_matches", "contained_pct", "len_common_columns", "number of complete seasons", "number of complete competitions", "number of complete gov bodies")

        all_inclusive_bool = False
        i = 0
        if dropped_columns:
            for l in cc_block_list:
                if "score" not in l["common_columns"]:
                    i += 1
                    continue

                if l["contained_pct"] == 1:
                    all_inclusive = l["common_columns"]
                print(i, l["len_match_paths"], l["total_num_matches"], l["contained_pct"], l["len_common_columns"], l["dropped_columns"], 
                      len(l["complete_seasons"]), len(l["complete_competitions"]), len(l["complete_governing_bodies"]))
                i += 1
        else:
            for l in cc_block_list:
                if "score" not in l["common_columns"]:
                    i += 1
                    continue

                if l["contained_pct"] == 1:
                    all_inclusive_bool = True
                    all_inclusive = l["common_columns"]
                print(i, l["len_match_paths"], l["total_num_matches"], l["contained_pct"], l["len_common_columns"],
                      len(l["complete_seasons"]), len(l["complete_competitions"]), len(l["complete_governing_bodies"]))
                i += 1

        print("All inclusive:")
        if all_inclusive_bool:
            print(all_inclusive)
        else:
            print("No all inclusive")
        print("Validity check:")
        print(self.ccl_validity_check(cc_block_list))





    #Pre-dataset
    def imputation(self, df: pd.DataFrame, csv_name: str, common_columns: set) -> None:
        """Imputes values into the provided dataframe using various methods depending on the column dtype and name. Currently only imputes nationality.
        
        """

        def median_imputation(col: pd.Series) -> pd.Series: #Vet ej om denna funkar
            """Returns a column where every nan value is replaced with the median"""
            counts = col.value_counts()
            print(counts)
            return counts.index[counts//2]
        
        def highest_count_imputation(col: pd.Series) -> pd.Series:
            """Returns a column whose nan values have been filled by the most common value"""
            return col.fillna(col.value_counts().idxmax())
        
        def zeroing_imputation(col: pd.Series) -> pd.Series:
            """Returns a column with every nan value replaced with 0"""
            return col.fillna(0)
        
        imp_highest = ["nationality"]

        for c_name in imp_highest:
            if c_name in df and c_name in common_columns:
                #try:
                df[c_name] = highest_count_imputation(df[c_name])
                # except ValueError as e:
                #     print(c_name, csv_name)
                #     raise e

    def match_pre_feature_sum(self, df: pd.DataFrame, csv_name: str, match_dict: dict, common_columns: set) -> None:
        """Adds a few pre feature numbers to the match_dict dictionary. Actual features (numbers from previous matches) 
        will need to be added later.
        
        """

        #These are for object dtype columns
        def team_names() -> None:
            if "home_team" in common_columns and "away_team" in common_columns:
                match_dict["HOME_TEAM"] = df["home_team"][0]
                match_dict["AWAY_TEAM"] = df["away_team"][0]

        def  team_scores() -> None:
            if "score" in common_columns:
                score_list = df["score"][0].split("\u2013")# – <- denna konstiga karaktären

                match_dict["H_goals"] = int(score_list[0])
                match_dict["A_goals"] = int(score_list[1])

                match_dict["H_win"] = 0
                match_dict["H_loss"] = 0
                match_dict["H_draw"] = 0

                match_dict["A_win"] = 0
                match_dict["A_loss"] = 0
                match_dict["A_draw"] = 0


                if match_dict["H_goals"] > match_dict["A_goals"]:
                    match_dict["H_win"] = 1
                    match_dict["A_loss"] = 1

                elif match_dict["H_goals"] < match_dict["A_goals"]:
                    match_dict["A_win"] = 1
                    match_dict["H_loss"] = 1

                elif match_dict["H_goals"] == match_dict["A_goals"]:
                    match_dict["H_draw"] = 1
                    match_dict["A_draw"] = 1
            else:
                raise ValueError("score not in common columns, can't distinguish victories")
        
        def match_date() -> None:
            d = "date"
            if d in common_columns:
                d_string = df[d][0]
                date_int = int(d_string.replace("-", ""))
                match_dict["DATE"] = date_int

        def venue() -> None:
            d = "venue"
            if d in common_columns:
                match_dict["VENUE"] = df[d][0]

        if csv_name == "info.csv":
            team_names()
            team_scores()
            venue()
            match_date() #used to sort timeseries

        prefix = ""


        if "Away" in csv_name:
            prefix += "A_"
        elif "Home" in csv_name:
            prefix += "H_"

        if "Goalkeepers" in csv_name:
            prefix += "GK_"

        for prefixed_col_name in common_columns: #time independent features
            if prefix == prefixed_col_name[:len(prefix)]: #to make sure the correct prefixes are prefixed in the column name
                col_name = prefixed_col_name[len(prefix):]
            else:
                continue
            
            #to not have duplicate goals from here and scores. Scores seems more reliable
            #Shirtnumber is just useless
            skip_cols = ["goals", "shirtnumber"]
            if col_name in skip_cols:
                continue

            if col_name in df and (df[col_name].dtype == np.int64 or df[col_name].dtype == np.float64):

                match_dict[prefixed_col_name + "_sum"] = df[col_name].sum()
                #match_dict[prefixed_col_name + "_avg"] = df[col_name].sum()/df.shape[0]

    def pre_dataset(self, cc_block: dict, save_result: bool = True) -> pd.DataFrame:
        """Uses paths list of csvs to construct a basic dataframe containing sum of columns for every match which additional features can be added onto/concatenated later.
        The function uses different imputation techniques depending on the column to accomplish this. Takes a single cc_block as argument.
        Will return a massive dataframe with a match on every row with corresponding features. Might need to be filtered somehow.
        """

        main_dict_list = []
        cc = cc_block["common_columns"]
        #path = cc_block["match_paths"][4]
        
        for path in cc_block["match_paths"]:
            match_dict = dict()

            for csv in os.listdir(path):
                df = pd.read_csv(posixpath.join(path,csv))
                df.drop(labels="Unnamed: 0", axis=1, inplace=True)

                if csv == "info.csv":
                    match_dict["ID"] = df["ID"][0]
                    match_dict["SEASON"] = df["SEASON"][0]
                    custom = []
                    for c in df.columns:
                        if c.isupper():
                            custom.append(c)

                    df.drop(labels=custom, axis=1, inplace=True)


                self.imputation(df=df, csv_name=csv, common_columns=cc)
                self.match_pre_feature_sum(df=df, csv_name=csv, match_dict=match_dict,
                                    common_columns=cc)
                
            
            main_dict_list.append(match_dict)

        main_df = pd.DataFrame.from_dict(main_dict_list)
        main_df.sort_values(axis=0, inplace=True, by="DATE", ascending=False)

        if save_result:
            with open(self.pre_dataset_memory_path, "wb") as f:
                pickle.dump(main_df, f)
            main_df.to_csv(self.pre_dataset_memory_path + ".csv")

        return main_df

    def load_pre_dataset(self) -> pd.DataFrame:
        with open(self.pre_dataset_memory_path, "rb") as f:
            df = pickle.load(f)
        df.to_csv(self.pre_dataset_memory_path + ".csv")
        return df

    def pre_dataset_scratchload(self, path: str, overwrite: bool = False):
        """Creates, saves and returns a pre_dataset using the path specified, overwriting unfinished work based on passed arguments
        
        """
        if overwrite:
            paths = [self.starter_memory_path,
            self.unique_memory_path,
            self.unique_finished_memory_path,
            self.intersection_memory_path,
            self.intersection_finished_memory_path,
            self.ccl_final_memory_path,
            self.pre_dataset_memory_path]

            for p in paths:
                try:
                    os.remove(p)
                except FileNotFoundError:
                    pass
        
        try:
            ccl = self.ccl_load_unique()
        except FileNotFoundError:
            ccl = self.ucl_starter(path=path)
            if self.stop_flag:
                return
        print("finished unique")

        try:
            ccl = self.ccl_load_intersection()
        except FileNotFoundError:
            self.ccl_intersection_constructor(ccl)
            if self.stop_flag:
                return
        print("finished intersections")

        try:
            self.ccl_load_final()
        except FileNotFoundError:
            self.ccl_final(ccl)
            if self.stop_flag:
                return
        print("finished final")

        try:
            df = self.load_pre_dataset()
        except FileNotFoundError:
            df = self.pre_dataset(ccl[0])
            if self.stop_flag:
                return
        print("finished pre_dataset")

        

        return df


    #Dataset
    def dataset_constructor(self, pre_dataset: pd.DataFrame, history_len_limit: int = 5) -> pd.DataFrame:
        """Uses a pre_dataset dataframe to construct a dataset using features according to allowed and filtered feature words which reflect column names from pre_dataset.
        Accomplishes the feature construction by continuously adding and keeping track of column history.

        Might need to implement a season simulation/ordering for additional features
        

        Difference for stat
        num stat for [away team]/[home team] [away from home]/[home] last x games
        won/loss last x games
        total avg
        dummy variables for won/loss straight last x games or for red card last game eg.

        #Ex. Goals scored/conceded, fouls, shots, yellow cards, red cards, crosses, interceptions, offside calls, 
        
        """

        def lexicographic_order(team1: str, team2: str) -> tuple[str,str]: #Unused
            """Used to order the team Vs keys"""
            if team1 == team2:
                raise ValueError("Input teams are the same")
            if team1 < team2:
                return (team1, team2)
            else:
                return (team2, team1)

        def process_row(row_series: pd.Series, features_dict: dict, history_dict: dict, skip_flag: list[bool], allowed_features: set = None, filter_features: list = None) -> None:
            """Keeps track of some match features based on history and also adds the feature, if enough history exists,
            to the features_dict. Skip flag is used to signal if any history is missing.
            
            """
            #row_series is just like a dict for the row

            """Ha en löpande historia bara för varje datakolonn och bygg historiefeatures utifrån dessa. Ifall en feature saknar tillräcklig historia aktivera skip_flag.
            Delar: Kategorikolonner (Vinst, förlust, draw utifrån hemmalagets perspektiv), features för match utifrån historik(hemma/bortalag vid hemma/bortamatcher, senaste 1,2,3,x matcherna) (summa räcker nog, avg blir samma sak bara), 
            Historia för hemma/bortalag vid @H/@A och en gemensam
            """

            def history_row_adder(row_series: pd.Series, history_dict: list) -> None:
                """Adds relevant history data to each team history list
                
                """
                teams_general_list = ["HOME_TEAM", "AWAY_TEAM"]

                for team_general in teams_general_list:

                    team = row_series[team_general]
                    if team not in history_dict:
                        history_dict[team] = {} #team_history_dict

                    team_history_dict = history_dict[team]


                    for col_name in row_series.keys():
                        # print(row_series["A_sca_sum"], row_series.iloc[0], row_series[0])

                        if col_name.isupper(): #artificial/string column
                            continue

                        location_prefix = "@" + team_general[0] + "_"

                        if team_general[0] == col_name[0]:
                            UO_prefix = "U_" #us
                        else:
                            UO_prefix = "O_" #opponent

                        history_individual_adder(row_series=row_series, team_history_dict=team_history_dict, col_name=col_name, location_prefix=location_prefix, UO_prefix=UO_prefix)

            def history_individual_adder(row_series: pd.Series, team_history_dict: dict, col_name: str, location_prefix: str = None, UO_prefix: str = None) -> None:
                """Adds a column value to the team_history_dict with the column name and prefixes 
                
                """

                def history_add(processed_col_name: str, team_history_dict: dict, value: int | float) -> None:
                    if processed_col_name not in team_history_dict:
                        team_history_dict[processed_col_name] = []
                    
                    team_history_dict[processed_col_name].insert(0,value)

                stat_col_name = col_name[2:]
                value = row_series[col_name]

                if location_prefix is not None and UO_prefix is not None:
                    processed_col_name = UO_prefix + location_prefix + stat_col_name
                    history_add(processed_col_name=processed_col_name, team_history_dict=team_history_dict, value=value)

                if UO_prefix is not None:
                    processed_col_name = UO_prefix + stat_col_name
                    history_add(processed_col_name=processed_col_name, team_history_dict=team_history_dict, value=value)

            def feature_adder(row_series: pd.Series, features_dict: dict, history_dict: dict, skip_flag: list[bool], filter_features: list):
                """Adds features using history_dict in several ways: Difference for stat, num stat for [away team]/[home team] [away from home]/[home] last history_len games, won/loss last x games
        #total avg, dummy variables for won/loss straight last x games or for red card last game eg.
                
                """
                def total_stat_history_len(history_feature_key: str, history_list: list, features_dict: dict, history_len: int) -> None:
                    """Adds a total stat counter features for the length of history_len"""
                    feature_name = history_feature_key + "_" + str(history_len)

                    feature_val = 0
                    i = 0
                    while i < 5:
                        feature_val += history_list[i]
                        i += 1

                    features_dict[feature_name] = feature_val

                def difference_stat_history_len(history_feature_key: str, team1_history: dict, team2_history: dict, features_dict: dict, history_len: int) -> None:
                    """Adds the difference between the """
                    feature_name = history_feature_key[2:] + "_diff_" + str(history_len)

                    team1_val = 0
                    team2_val = 0

                    feature1_history = team1_history[history_feature_key]
                    feature2_history = team2_history[history_feature_key]

                    i = 0
                    while i < 5:
                        team1_val += feature1_history[i]
                        team2_val += feature2_history[i]
                        i += 1

                    feature_val = team1_val - team2_val

                    features_dict[feature_name] = feature_val

                def dummy_event_variables(team_history: list, features_dict: dict, history_len: int) -> None:
                    """Adds a few event variables (0 or 1 if the event occured) such as win/loss/draw last x rounds in a row from 1 to 3, both location dependent and independent.
                    Looks for history entries containing win/loss/draw words (when written denoted only actual win/loss/draw history)
                    
                    
                    """
                    
                    dummy_history_len = history_len
                    i = 0

                    triggers = ["win", "loss", "draw"]
                    for feature_key in team_history.keys():
                        for word in triggers:
                            if word in feature_key:
                                
                                j = 0
                                feature_history = team_history[feature_key]
                                #print(len(feature_history), history_len)

                                if len(feature_history) < history_len:
                                    skip_flag[0] = 1
                                    return

                                while j < dummy_history_len:

                                    if feature_history[j]:
                                        feature_name = feature_key + "_streak_" + str(j)
                                        #print(feature_name)
                                        features_dict[feature_name] = 1
                                    else:
                                        break

                                    j += 1
                                i += 1

                    if i != 18: #3 for every win/loss/draw = 9*2 for both U and O
                        skip_flag[0] = 1
                        return

                teams_general_list = ["HOME_TEAM", "AWAY_TEAM"]

                #Useful info
                features_dict["SEASON"] = row_series["SEASON"]

                #Feature adding
                for team_general in teams_general_list:
                    team = row_series[team_general]

                    #Team dummy
                    if team_general == "HOME_TEAM":
                        features_dict[team] = 1
                    else:
                        features_dict[team] = -1

                    if team in history_dict:
                        team_history = history_dict[team]
                    else:
                        skip_flag[0] = 1
                        return
                    
                    dummy_event_variables(team_history=team_history, features_dict=features_dict, history_len=history_len_limit)

                    for history_feature_key in team_history:
                        
                        history_list = team_history[history_feature_key]

                        #filter/skip
                        if len(history_list) < history_len_limit:
                            skip_flag[0] = 1
                            return
                        
                        if filter_features is not None:
                            use = True
                            for filter_word in filter_features:
                                if filter_word in history_feature_key:
                                    use = False
                                    break

                            if not use:
                                continue

                        #start of feature adding
                        history_len = history_len_limit
                        total_stat_history_len(history_feature_key=history_feature_key, history_list=history_list, history_len=history_len, features_dict=features_dict)

                #need to go key by key for both teams to determine stat difference, to have gotten this far historyskipping must not be necessary
                H_team = row_series[teams_general_list[0]]
                A_team = row_series[teams_general_list[1]]

                H_team_history = history_dict[H_team]
                A_team_history = history_dict[A_team]

                history_len = history_len_limit

                for history_feature_key in H_team_history: #the team used here is not relevant, only used for the history key list
                        
                    if filter_features is not None: #still needs to be filtered of course
                        use = True
                        for filter_word in filter_features:
                            if filter_word in history_feature_key:
                                use = False
                                break

                        if not use:
                            continue

                    difference_stat_history_len(history_feature_key=history_feature_key, team1_history=H_team_history, team2_history=A_team_history, history_len=history_len, features_dict=features_dict)
                    
        
                        
                        


                
            
            def result_category(row_series: pd.Series) -> dict:
                """Returns a win/loss/draw -> 0 | 1 dict from the home teams perspective, used as classes for training
                
                """

                category_dict = {}
                if row_series["H_win"]:
                    value = "WIN"
                elif row_series["H_loss"]:
                    value = "LOSS"
                elif row_series["H_draw"]:
                    value = "DRAW"

                category_dict["RESULT"] = value
                
                return category_dict
            
            category_dict = result_category(row_series=row_series)
            features_dict.update(category_dict)

            feature_adder(row_series=row_series, features_dict=features_dict, history_dict=history_dict, skip_flag=skip_flag, filter_features=filter_features)
            
            history_row_adder(row_series=row_series, history_dict=history_dict)
        


        features_dict_list = []
        history_dict = {}
        allowed_features = set(["win", "loss", "draw", "goals", "gk_crosses_stopped_sum", "goal_kicks_sum", "crosses_sum", "shots_sum", "own_goals_sum", "ball_recoveries_sum", "assists_sum", "cards_red_sum",
                                "passes_sum", "challenges_sum", "offsides_sum", "cards_yellow_sum"])
        
        filter_features = ["minutes"]

        for row_series in pre_dataset.iloc:
            skip_flag = [0]
            features_dict = {}
            process_row(row_series=row_series, features_dict=features_dict, skip_flag=skip_flag, history_dict=history_dict, filter_features=filter_features)#, allowed_features=allowed_features) add allowed features later maybe?

            if not skip_flag[0]:
                features_dict_list.append(features_dict)

        dataset = pd.DataFrame.from_dict(features_dict_list)
        dataset.fillna(value=0, inplace=True)

        #Save the dataset
        dataset.to_csv(self.dataset_memory_path + ".csv")

        return dataset

    def load_dataset(self) -> pd.DataFrame:
        """Loads the dataset csv file and returns the dataframe
        
        """
        return pd.read_csv(self.dataset_memory_path + ".csv")


    #Model related
    def random_forest(self, dataset: pd.DataFrame):


        x_train, x_test, y_train, y_test, train_df = self.last_percentage_test_split(dataset, 0.25)
        # print('Training Features Shape:', x_train.shape)
        # print('Training Labels Shape:', y_train.shape)
        # print('Testing Features Shape:', x_test.shape)
        # print('Testing Labels Shape:', y_test.shape)

        sel = SelectFromModel(estimator=RandomForestClassifier(n_estimators = 100, random_state=42, min_samples_leaf=1), max_features=10)
        sel.fit(x_train, y_train)
        selected_feat = train_df.columns[(sel.get_support())]
        print(selected_feat)

        #print((sel.get_support()))
        #print(sel.feature_names_in_[sel.get_support()])

        #hist = pd.Series(sel.estimator_.feature_importances_[sel.get_support()].ravel()).hist()
        
        #plt.show()
        #print(dataset.shape)
        #rf = RandomForestClassifier(n_estimators = 1000, random_state = 42)

        #rf.fit(x_train, y_train)

        rf = RandomForestClassifier(n_estimators = 100, random_state=42, min_samples_leaf=1)
        rf.fit(sel.transform(x_train), y_train)
        #print(rf.feature_importances_)
        predictions = rf.predict(sel.transform(x_test))

        accuracy = self.prediction_accuracy(predictions, y_test)

        return accuracy
        #print(predictions)

    def svm(self, dataset: pd.DataFrame):
        x_train, x_test, y_train, y_test = self.last_percentage_test_split(dataset, 0.25)
        y_train=np.ravel(y_train)
        y_test=np.ravel(y_test)

        #print(y_test)
        """RFECV gav typ max 50% utan balanserad accuracy score
        testar univariate selection istället, måste även testa ridge regression/lasso som jag tror uppsatsen använde.

        Känns lite bajs att välja features utifrån nån arbitrary modell, bättre då att använda något statistiskt test även om modellen uppenbarligen ger ett mått på vilka features som är avgörande
        
        
        """
        pipe = Pipeline(steps=[
            ("scaling", StandardScaler()),
            ("feature_selection", RFECV(estimator=KNeighborsClassifier, step=1, cv=TimeSeriesSplit(), scoring="accuracy", min_features_to_select=1, n_jobs=2)),
            ("clf", KNeighborsClassifier())])
        

        print("patrick swayze")
        
        pipe.fit(x_train, y_train)
        print(pipe["feature_selection"].n_features_)
        preds = pipe.predict(x_test)

        print("lahey, you are fucked")
        
        print(balanced_accuracy_score(y_test, preds))

        return
        

    def neural_network(self, dataset: pd.DataFrame):
        x_train, x_test, y_train, y_test, train_df = self.last_percentage_test_split(dataset, 0.25)

        scaler = StandardScaler()
        scaler.fit(x_train)
        x_train = scaler.transform(x_train)
        x_test = scaler.transform(x_test)

        #print(x_train)

        clf = MLPClassifier(solver="lbfgs", alpha=1e-5, hidden_layer_sizes=(10,10), random_state=1, max_iter=2000)
        clf.fit(x_train, y_train)

        sel = SelectFromModel(clf, max_features=10, prefit=True)
        #print(clf.coefs_)

        # clf2 = MLPClassifier(solver="lbfgs", alpha=1e-5, hidden_layer_sizes=(5,2), random_state=1, max_iter=2000)
        # clf2.fit(sel.transform(x_train), y_train)

        preds = clf.predict(x_test)
        #print(preds)

        accuracy = self.prediction_accuracy(preds, y_test)

        return accuracy



    # def prediction_accuracy(self, predictions, y_test):
    #     """Determines the prediction accuracy from multiclass predictions"""

    #     #print(type(predictions), type(y_test))

    #     print(predictions)

    #     print()

    #     print(y_test)
        
    #     correct_answers = 0
    #     for i in range(len(predictions)):
    #         if y_test[i] == predictions[i]:
    #             correct_answers += 1

    #     accuracy = correct_answers/len(predictions)
    #     return accuracy

    # def class_distribution(self, y) -> dict:
    #     """Returns the distribution of """
    #     res = {}
    #     total = 0

    #     for val in y:
    #         total += 1
    #         if val in res:
    #             res[val] += 1
    #         else:
    #             res[val] = 1
        
    #     for key in res:
    #         res[key] = res[key]/total
        
    #     return res
        

    def dataset_baseline(self, dataset: pd.DataFrame) -> np.ndarray:
        """Calculates a baseline of the distribution of wins/losses/draws in the dataset"""
        labels = np.array([dataset["WIN"], dataset["LOSS"], dataset["DRAW"]]).transpose()
        observations = len(labels)

        column_sum = np.sum(labels, axis=0)
        chance = column_sum/observations
        return chance




    #Dataset split
    def last_percentage_test_split(self, dataset: pd.DataFrame, percentage: float) -> tuple:
        """Splits the dataset provided into training/test parts using the percentage provided, rounding to whole numbers. Assumes that the dataset is sorted by date, most recent highest.
        The 
        
        """
        dataset.drop("SEASON", axis=1, inplace=True)

        num_observations = len(dataset)
        x_test_len = round(num_observations*percentage)
        x_test = dataset.iloc[:x_test_len]
        x_train = dataset.iloc[x_test_len:]

        #print(x_train["RESULT"])

        y_train = np.array([x_train["RESULT"]]).transpose()
        x_train = x_train.drop(["RESULT"], axis=1, inplace=False)
        #train_df = x_train.copy()
        x_train = np.array(x_train)

        y_test = np.array([x_test["RESULT"]]).transpose()
        x_test = x_test.drop(["RESULT"], axis=1, inplace=False)
        x_test = np.array(x_test)


        return (x_train, x_test, y_train, y_test)#, train_df)
        
    def last_season_test_split(self, dataset: pd.DataFrame) -> tuple:
        """Separates the dataset into training and testing parts using the latest season for testing and the rest for training. Also removes the SEASON column from the dataset
        
        """
        #Will need some extra work in case of seasons over several years, might just be able to use the upmost season
        latest_season_int = max(dataset["SEASON"])

        latest_season_bool_list = dataset["SEASON"].apply(lambda x: x == latest_season_int)

        dataset.drop("SEASON", axis=1, inplace=True)

        x_test = dataset.iloc[list(latest_season_bool_list)]
        x_train = dataset.iloc[list(latest_season_bool_list.apply(lambda x: not x))]



        y_train = np.array([x_train["WIN"], x_train["LOSS"], x_train["DRAW"]]).transpose()
        x_train = x_train.drop(["WIN", "LOSS", "DRAW"], axis=1, inplace=False)
        x_train = np.array(x_train)

        y_test = np.array([x_test["WIN"], x_test["LOSS"], x_test["DRAW"]]).transpose()
        x_test = x_test.drop(["WIN", "LOSS", "DRAW"], axis=1, inplace=False)
        x_test = np.array(x_test)



        return (x_train, x_test, y_train, y_test)


    #Orders
    def prediction(self, order):
        """Adds prediction probabilities to the order depending on the orders marketName."""
        #If finished add odds to order silently, otherwise raise some kind of exception which adds it to the failed orders

        if order["marketName"] == "Match Odds":
            self.match_odds_prediction(order)

        raise NotImplementedError

    def match_odds_prediction(self, order):
        """"""

        raise NotImplementedError



    #Utility
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

    def keyboard_on_press(self, key) -> None:
        """For stopping the program when the "end" key is pressed"""
        try:
            if key == kb.Key.end:
                print("detected keypress, stopping program...")
                self.stop_flag = True
        except:
            pass

    def shutdown(self) -> None:
        self.listener.stop()