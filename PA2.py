#!/usr/bin/env python3
""" 
PA2.py

Requirements:
    Python 3.7.3 and up

PySimpleGUI Square Mapping
board = [
    56, 57, ... 63
    ...
    8, 9, ...
    0, 1, 2, ...
]

row = [
    0, 0, ...
    1, 1, ...
    ...
    7, 7 ...
]

col = [
    0, 1, 2, ... 7
    0, 1, 2, ...
    ...
    0, 1, 2, ... 7
]


Python-Chess Square Mapping
board is the same as in PySimpleGUI
row is reversed
col is the same as in PySimpleGUI

"""

import PySimpleGUI as sg
import os
import sys
import queue
import copy
from datetime import datetime
import chess.pgn
import random
import logging
import time


log_format = '%(asctime)s :: %(funcName)s :: line: %(lineno)d :: %(' \
                 'levelname)s :: %(message)s'



APP_NAME = 'Python Easy Chess GUI'
APP_VERSION = 'v1.11'
BOX_TITLE = '{} {}'.format(APP_NAME, APP_VERSION)


platform = sys.platform
    

ico_path = {'win32': {'pecg': 'Icon/pecg.ico', 'enemy': 'Icon/enemy.ico',
                      'adviser': 'Icon/adviser.ico'}, 
            'linux': {'pecg': 'Icon/pecg.png', 'enemy': 'Icon/enemy.png',
                      'adviser': 'Icon/adviser.png'},
            'darwin': {'pecg': 'Icon/pecg.png', 'enemy': 'Icon/enemy.png',
                      'adviser': 'Icon/adviser.png'}}


MIN_DEPTH = 1
MAX_DEPTH = 1000
MANAGED_UCI_OPTIONS = ['ponder', 'uci_chess960', 'multipv', 'uci_analysemode',
                       'ownbook']
GUI_THEME = ['Green', 'GreenTan', 'LightGreen', 'BluePurple', 'Purple',
             'BlueMono', 'GreenMono', 'BrownBlue', 'BrightColors',
             'NeutralBlue', 'Kayak', 'SandyBeach', 'TealMono', 'Topanga',
             'Dark', 'Black', 'DarkAmber']
IMAGE_PATH = 'Images/60'  # path to the chess pieces


BLANK = 0  # piece names
QUEENB = 6



# Absolute rank based on real chess board, white at bottom, black at the top.
# This is also the rank mapping used by python-chess modules.
RANK_8 = 7
RANK_7 = 6
RANK_6 = 5
RANK_5 = 4
RANK_4 = 3
RANK_3 = 2
RANK_2 = 1
RANK_1 = 0



white_init_promote_board = [[]]

black_init_promote_board = [[QUEENB]]


blank = os.path.join(IMAGE_PATH, 'blank.png')
queenB = os.path.join(IMAGE_PATH, 'bQ.png')

images = {QUEENB: queenB, BLANK: blank}


promote_psg_to_pyc = {QUEENB: chess.QUEEN}


INIT_PGN_TAG = {
        'Event': 'Human vs computer',
        'White': 'sjkldmff',
        'Black': 'Computer',
}


menu_def_neutral = [['&Mode', ['Backtracking']]]


def initial_board (self,window):
    global steps
    global ld
    global rd
    global cl

    ld = [0] * 30
    rd = [0] * 30
    cl = [0] * 30
    board = [[0, 0, 0, 0, 0, 0, 0, 0],
             [0, 0, 0, 0, 0, 0, 0, 0],
             [0, 0, 0, 0, 0, 0, 0, 0],
             [0, 0, 0, 0, 0, 0, 0, 0],
             [0, 0, 0, 0, 0, 0, 0, 0],
             [0, 0, 0, 0, 0, 0, 0, 0],
             [0, 0, 0, 0, 0, 0, 0, 0],
             [0, 0, 0, 0, 0, 0, 0, 0]
             ]

    fitnessNum = 1
    list=[]
    global best
    global best_atack
    global steps
    steps = 0
    for i in range(0,generations):
        steps = steps +1
        list = generate_genetic_algorithm_board()
        fitnessNum = fitness(list)
        if fitnessNum < best_atack:
            best_atack = fitnessNum
            best = list
        savedSteps.append(list)


    return best

def randonm_number():
    return random.randrange(8)


def generate_genetic_algorithm_board():
    list =[]
    for i in range(0,8):
        x = random.randrange(8)
        while x in list:
            x = randonm_number()
        list.append(x)
    return list


class EasyChessGui:
    queue = queue.Queue()
    is_user_white = True  # White is at the bottom in board layout

    def __init__(self, theme):
        self.theme = theme
        self.opp_path_and_file = None
        self.opp_file = None
        self.opp_id_name = None

        self.pecg_auto_save_game = 'pecg_auto_save_games.pgn'
        self.my_games = 'pecg_my_games.pgn'
        self.repertoire_file = {'white': 'pecg_white_repertoire.pgn', 'black': 'pecg_black_repertoire.pgn'}
        self.init_game()
        self.fen = None
        self.psg_board = None
        self.menu_elem = None
        self.engine_id_name_list = []
        self.engine_file_list = []
        self.username = INIT_PGN_TAG["White"]


        # Default board color is brown
        self.sq_light_color = '#F0D9B5'
        self.sq_dark_color = '#B58863'

        # Move highlight, for brown board
        self.move_sq_light_color = '#E8E18E'
        self.move_sq_dark_color = '#B8AF4E'

        self.gui_theme = 'Reddit'


    def update_game(self, mc, user_move, time_left, user_comment):


        if self.is_save_user_comment:
            # If comment is empty
            if not (user_comment and user_comment.strip()):
                if mc == 1:
                    self.node = self.game.add_variation(user_move)
                else:
                    self.node = self.node.add_variation(user_move)

                # Save clock (time left after a move) as move comment
                if self.is_save_time_left:
                    rem_time = self.get_time_h_mm_ss(time_left, False)
                    self.node.comment = '[%clk {}]'.format(rem_time)
            else:
                if mc == 1:
                    self.node = self.game.add_variation(user_move)
                else:
                    self.node = self.node.add_variation(user_move)

                # Save clock, add clock as comment after a move
                if self.is_save_time_left:
                    rem_time = self.get_time_h_mm_ss(time_left, False)
                    self.node.comment = '[%clk {}] {}'.format(rem_time,
                                                         user_comment)
                else:
                    self.node.comment = user_comment
        # Do not save user comment
        else:
            if mc == 1:
                self.node = self.game.add_variation(user_move)
            else:
                self.node = self.node.add_variation(user_move)

            # Save clock, add clock as comment after a move
            if self.is_save_time_left:
                rem_time = self.get_time_h_mm_ss(time_left, False)
                self.node.comment = '[%clk {}]'.format(rem_time)

    def create_new_window(self, window, flip=False):
        """ Close the window param just before turning the new window """

        loc = window.CurrentLocation()
        window.Disable()
        if flip:
            self.is_user_white = not self.is_user_white

        layout = self.build_main_layout(self.is_user_white)

        w = sg.Window('{} {}'.format(APP_NAME, APP_VERSION),
            layout,
            default_button_element_size=(12, 1),
            auto_size_buttons=False,
            location=(loc[0], loc[1]),
            icon=ico_path[platform]['pecg'])

        # Initialize White and black boxes
        while True:
            self.update_labels_and_game_tags(w, human=self.username)
            break

        window.Close()
        return w



    def get_tag_date(self):
        """ Return date in pgn tag date format """
        return datetime.today().strftime('%Y.%m.%d')

    def init_game(self):
        """ Initialize game with initial pgn tag values """
        self.game = chess.pgn.Game()
        self.node = None
        self.game.headers['Event'] = INIT_PGN_TAG['Event']
        self.game.headers['Date'] = self.get_tag_date()
        self.game.headers['White'] = "ythfgd"
        self.game.headers['Black'] = INIT_PGN_TAG['Black']

    def set_new_game(self, name="gf"):
        """ Initialize new game but save old pgn tag values"""
        old_event = self.game.headers['Event']
        self.game.headers['White'] = name
        old_black = self.game.headers['Black']

        # Define a game object for saving game in pgn format
        self.game = chess.pgn.Game()

        self.game.headers['Event'] = old_event
        self.game.headers['Date'] = self.get_tag_date()
        self.game.headers['White'] = name
        self.game.headers['Black'] = old_black


    def update_labels_and_game_tags(self, window, human='Human'):
        engine_id = self.opp_id_name

    def relative_row(self, s, stm):
        return 7 - self.get_row(s) if stm else self.get_row(s)

    def get_row(self, s):
        return 7 - chess.square_rank(s)

    def get_col(self, s):
        return chess.square_file(s)

    def redraw_board(self, window):
        for i in range(8):
            for j in range(8):
                color = self.sq_dark_color if (i + j) % 2 else \
                        self.sq_light_color
                piece_image = images[self.psg_board[i][j]]
                elem = window.FindElement(key=(i, j))
                elem.Update(button_color=('white', color),
                            image_filename=piece_image, )

    def render_square(self, image, key, location):
        """ Returns an RButton (Read Button) with image image """
        if (location[0] + location[1]) % 2:
            color = self.sq_dark_color  # Dark square
        else:
            color = self.sq_light_color
        return sg.RButton('', image_filename=image, size=(1, 1),
                          border_width=0, button_color=('white', color),
                          pad=(0, 0), key=key)



    def create_board(self, is_user_white=True,list=[]):

        board = [[0, 0, 0, 0, 0, 0, 0, 0],
                 [0, 0, 0, 0, 0, 0, 0, 0],
                 [0, 0, 0, 0, 0, 0, 0, 0],
                 [0, 0, 0, 0, 0, 0, 0, 0],
                 [0, 0, 0, 0, 0, 0, 0, 0],
                 [0, 0, 0, 0, 0, 0, 0, 0],
                 [0, 0, 0, 0, 0, 0, 0, 0],
                 [0, 0, 0, 0, 0, 0, 0, 0]
                 ]
        for i in range(0, 8):
            board[i][list[i]] = 6
        self.psg_board = copy.deepcopy(board)

        board_layout = []

        if is_user_white:
            start = 0
            end = 8
            step = 1
        else:
            start = 7
            end = -1
            step = -1

        for i in range(start, end, step):
            row = []
            for j in range(start, end, step):
                piece_image = images[self.psg_board[i][j]]
                row.append(self.render_square(piece_image, key=(i, j), location=(i, j)))
            board_layout.append(row)
        return board_layout

    def build_main_layout(self, is_user_white=True,name="gfhc",list=[0, 0, 0, 0, 0, 0, 0, 0]):
        sg.ChangeLookAndFeel(self.gui_theme)
        sg.SetOptions(margins=(0, 3), border_width=1)
        global savedIndex
        global savedSteps


        # Define board
        board_layout = self.create_board(is_user_white, list)
        board_controls = [
            [sg.Button("Start", key="Start")],
            [sg.Text("you can run pure backtracking")],
            [sg.Radio('pure', 1, key='pure', default=True), sg.Radio('MRV', 1, key='MRV'),
             sg.Radio('LCV', 1, key='LCV')],

        ]

        board_tab = [[sg.Column(board_layout, key="board"), sg.Column(board_controls)]]

        self.menu_elem = sg.Menu(menu_def_neutral, tearoff=False)

        # White board layout, mode: Neutral
        layout = [
                [self.menu_elem],
                [sg.Column(board_tab)]
        ]

        return layout



    def main_loop(self):
        layout = self.build_main_layout(True)
        # Use white layout as default window
        window = sg.Window('{} {}'.format(APP_NAME, APP_VERSION),
                           layout, default_button_element_size=(12, 1),
                           auto_size_buttons=False,
                           icon=ico_path[platform]['pecg'])
        self.init_game()
        savedIndex = len(savedSteps)- 1
        while True:
            self.update_labels_and_game_tags(window, human=self.username)
            break

        # Mode: Neutral, main loop starts here
        while True:
            button, values= window.Read(timeout=50)
            global generations

            if button == "previous":

                if(savedIndex > 0):
                    savedIndex = savedIndex - 1
                    print(savedSteps[savedIndex])
                    window.FindElement("board").update(self.create_board(self, savedSteps[savedIndex]))
                    self.redraw_board(window)

            if button == "Start":

                initial_board(self, window)

                vector = backtracking(MRV=values['MRV'], LCV=values['LCV'])
                window.FindElement("board").update(self.create_board(self, vector))
                self.redraw_board(window)

            if button == "next":
                last_index = len(savedSteps)
                if(savedIndex < last_index -1):
                    savedIndex = savedIndex + 1
                    last_index = len(savedSteps) - savedIndex
                    window.FindElement("board").update(self.create_board(self, savedSteps[last_index]))
                    self.redraw_board(window)

            if button is None:
                logging.info('Quit app from main loop, X is pressed.')
                break


N = 8

ld = [0] * 30

rd = [0] * 30

cl = [0] * 30



def fitness (chromosome):

    t1 = 0
    """number of repetitive queens in one diagonal while seen from left corner""";
    t2 = 0
    """number of repetitive queens in one diagonal while seen from right corner""";
    size = len(chromosome)
    f1=[]
    f2=[]

    for i in range(0,size):
        f1.append(chromosome[i]-i)
        f2.append(( 1+size)- chromosome[i] - i)

    f1= sorted(f1);
    f2= sorted(f2);
    for i in range(2, size):

        if f1[i] == f1[i-1]:
            t1 = t1+1

        if f2[i] == f2[i-1]:
            t2 = t2+1;


    fitness_value = t1 + t2;
    return fitness_value


steps=0
best=[]
generations = 500
best_atack=10
savedSteps=[]
savedIndex=0


def is_solution (vector):
    length = len(vector)
    for i in range(0, length):
        if is_partial(vector):
            return False
        for j in range(i+1, length):
            if vector[i] == vector[j]:
                return False
            if vector[i]-vector[j]== i-j or vector[i]-vector[j]==j-i:
                return False
    return True

def is_partial(vector):
    length = len(vector)
    for i in range(0, length):
        if vector[i] == 0:
            return True
    return False

def is_p_and_L(vector):
    if is_partial(vector):
        length = len(vector)
        for i in range(0, length):
            for j in range(i + 1, length):
                if vector[i] !=0 and vector[j]!=0:
                    if vector[i] == vector[j]:
                        return False
                    if vector[i] - vector[j] == i - j or vector[i] - vector[j] == j - i:
                        return False
        return True
    return False



def is_legal(x, vector):
    length = len(vector)
    for i in range(0, length):
        if x != i and vector[i] != 0:
            if vector[i] == vector[x]:
                return False
            elif vector[i] - vector[x] == (i - x) or vector[i] - vector[x] == (x - i):
                return False
    return True


def lcv(x, vector, stack):
    length = len(vector)
    myValue = 0
    lest = 0
    for i in range(1, length+1):
        temp = 0
        vector[x] = i
        if is_legal(x, vector) and i not in stack:
            for j in range(0, length):
                if x != j and vector[j] == 0:
                    for k in range(1, length+1):
                        vector[j] = k
                        if is_legal(j, vector):
                            temp = temp + 1
                    vector[j] = 0
            if temp > lest:
                lest = temp
                myValue = i
    vector[x] = 0
    if myValue not in stack:
        return myValue
    else:
        return 0




def mrv(vector):
    length = len(vector)
    myk = 10
    min = 10

    for i in range(0, length):
        temp = 0
        if vector[i] == 0:
            for j in range(1, length+1):
                vector[i] = j
                if is_legal(i, vector):
                    temp = temp + 1
            vector[i] = 0
            if min > temp:
                min = temp
                myk = i
    return myk



def backtracking (MRV= False, LCV=False):
    vector = [0, 0, 0, 0, 0, 0, 0, 0]
    noSolution = False
    MRV_stack = []
    k = 0
    LCV_stack = [[], [], [], [], [], [], [], []]
    while k >= 0 and noSolution == False:
        savedSteps.append(list)
        while vector[k] <= 7:
            if LCV:
                temp = lcv(k, vector, LCV_stack[k])
                if temp != 0:
                    vector[k] = temp
                    LCV_stack[k].append(temp)
                else:
                    vector[k] = 0
                    LCV_stack[k] = []
                    break
            else:
                vector[k] = vector[k] + 1
            if is_solution(vector):
                for i in range(0, len(vector)):
                    vector[i] -= 1
                return vector
            elif is_p_and_L(vector):
                if MRV:
                    MRV_stack.append(k)
                    k = mrv(vector)
                else:
                    k += 1
        vector[k] = 0
        if MRV:
            if MRV_stack:
                k = MRV_stack.pop()
                print("k with MRV", k)
            else:
                break
        else:
            k -= 1
    if noSolution:
        return "no Solution"



def main():
    theme = 'Reddit'
    pecg = EasyChessGui(theme)
    pecg.main_loop()


if __name__ == "__main__":
    main()