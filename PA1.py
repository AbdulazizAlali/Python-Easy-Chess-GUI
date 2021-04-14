#!/usr/bin/env python3
""" 
PA1.py

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
PAWNB = 1
KNIGHTB = 2
BISHOPB = 3
ROOKB = 4
KINGB = 5
QUEENB = 6
PAWNW = 7
KNIGHTW = 8
BISHOPW = 9
ROOKW = 10
KINGW = 11
QUEENW = 12


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



white_init_promote_board = [[QUEENW, ROOKW, BISHOPW, KNIGHTW]]

black_init_promote_board = [[QUEENB, ROOKB, BISHOPB, KNIGHTB]]


HELP_MSG = """(A) To play a game
You should be in Play mode.
1. Mode->Play
2. Make move on the board

(B) To play as black
You should be in Neutral mode
1. Board->Flip
2. Mode->Play
3. Engine->Go
If you are already in Play mode, go back to 
Neutral mode via Mode->Neutral

(C) To flip board
You should be in Neutral mode
1. Board->Flip
  
(D) To paste FEN
You should be in Play mode
1. Mode->Play
2. FEN->Paste

(E) To show engine search info after the move                
1. Right-click on the Opponent Search Info and press Show

(F) To Show book 1 and 2
1. Right-click on Book 1 or 2 press Show
"""


# Images/60
blank = os.path.join(IMAGE_PATH, 'blank.png')
bishopB = os.path.join(IMAGE_PATH, 'bB.png')
bishopW = os.path.join(IMAGE_PATH, 'wB.png')
pawnB = os.path.join(IMAGE_PATH, 'bP.png')
pawnW = os.path.join(IMAGE_PATH, 'wP.png')
knightB = os.path.join(IMAGE_PATH, 'bN.png')
knightW = os.path.join(IMAGE_PATH, 'wN.png')
rookB = os.path.join(IMAGE_PATH, 'bR.png')
rookW = os.path.join(IMAGE_PATH, 'wR.png')
queenB = os.path.join(IMAGE_PATH, 'bQ.png')
queenW = os.path.join(IMAGE_PATH, 'wQ.png')
kingB = os.path.join(IMAGE_PATH, 'bK.png')
kingW = os.path.join(IMAGE_PATH, 'wK.png')


images = {BISHOPB: bishopB, BISHOPW: bishopW, PAWNB: pawnB, PAWNW: pawnW,
          KNIGHTB: knightB, KNIGHTW: knightW,
          ROOKB: rookB, ROOKW: rookW, KINGB: kingB, KINGW: kingW,
          QUEENB: queenB, QUEENW: queenW, BLANK: blank}


# Promote piece from psg (pysimplegui) to pyc (python-chess)
promote_psg_to_pyc = {KNIGHTB: chess.KNIGHT, BISHOPB: chess.BISHOP,
                      ROOKB: chess.ROOK, QUEENB: chess.QUEEN,
                      KNIGHTW: chess.KNIGHT, BISHOPW: chess.BISHOP,
                      ROOKW: chess.ROOK, QUEENW: chess.QUEEN,}


INIT_PGN_TAG = {
        'Event': 'Human vs computer',
        'White': 'sjkldmff',
        'Black': 'Computer',
}


# (1) Mode: Neutral
menu_def_neutral = [
        ['&Mode', ['Genetic Run',"A* Run"]],

]

# (2) Mode: Play, info: hide
menu_def_play = [
        ['&Mode', ['Neutral']],
        ['&Game', ['&New::new_game_k',
                   'Save to My Games::save_game_k',
                   'Save to White Repertoire',
                   'Save to Black Repertoire',
                   'Resign::resign_game_k',
                   'User Wins::user_wins_k',
                   'User Draws::user_draws_k']],
        ['FEN', ['Paste']],
        ['&Engine', ['Go', 'Move Now']],
        ['&Help', ['About']],
]



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
    # solveNQUtil(board, 0)
    # printSolution(board)
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
        print(fitnessNum)
        print(list)
        savedSteps.append(list)
# time.sleep(2)


    print(steps)


    print("====")

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
        """
        Used for saving moves in the game.

        :param mc: move count
        :param user_move:
        :param time_left:
        :param user_comment: Can be a 'book' from the engine
        :return:
        """
        # Save user comment
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
        """ Update player names """
        engine_id = self.opp_id_name
        # if self.is_user_white:
        #     window.FindElement('_White_').Update(human)
        #     window.FindElement('_Black_').Update(engine_id)

        # else:
        #     window.FindElement('_White_').Update(engine_id)
        #     window.FindElement('_Black_').Update(human)
        #     self.game.headers['White'] = engine_id
        #     self.game.headers['Black'] = human



    def relative_row(self, s, stm):
        """
        The board can be viewed, as white at the bottom and black at the
        top. If stm is white the row 0 is at the bottom. If stm is black
        row 0 is at the top.
        :param s: square
        :param stm: side to move
        :return: relative row
        """
        return 7 - self.get_row(s) if stm else self.get_row(s)

    def get_row(self, s):
        """
        This row is based on PySimpleGUI square mapping that is 0 at the
        top and 7 at the bottom.
        In contrast Python-chess square mapping is 0 at the bottom and 7
        at the top. chess.square_rank() is a method from Python-chess that
        returns row given square s.

        :param s: square
        :return: row
        """
        return 7 - chess.square_rank(s)

    def get_col(self, s):
        """ Returns col given square s """
        return chess.square_file(s)

    def redraw_board(self, window):
        """
        Redraw board at start and afte a move.

        :param window:
        :return:
        """
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
        """
        Returns board layout based on color of user. If user is white,
        the white pieces will be at the bottom, otherwise at the top.

        :param is_user_white: user has handling the white pieces
        :return: board layout
        """
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
            # Save the board with black at the top
            start = 0
            end = 8
            step = 1
        else:
            start = 7
            end = -1
            step = -1

        # Loop through the board and create buttons with images
        for i in range(start, end, step):
            # Row numbers at left of board is blank
            row = []
            for j in range(start, end, step):
                piece_image = images[self.psg_board[i][j]]
                row.append(self.render_square(piece_image, key=(i, j), location=(i, j)))
            board_layout.append(row)

        return board_layout

    def build_main_layout(self, is_user_white=True,name="gfhc",list=[0,0,0,0,0,0,0,0]):

        sg.ChangeLookAndFeel(self.gui_theme)
        sg.SetOptions(margins=(0, 3), border_width=1)
        global savedIndex
        global savedSteps
        print(savedSteps)
        print("******")

        # Define board
        board_layout = self.create_board(is_user_white,list)
        board_controls = [
            [sg.Button("previous", key="previous"),sg.Button("next", key="next")],
            [sg.Text('generations'),sg.InputText(generations),],
            [sg.Text('steps:'), sg.InputText(str(savedIndex) +" / "+str(len(savedSteps)) ,key="index"), ],


        ]

        board_tab = [[sg.Column(board_layout,key="board"),sg.Column(board_controls)]]

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

        while True:
            self.update_labels_and_game_tags(window, human=self.username)
            break

        # Mode: Neutral, main loop starts here
        while True:
            button, value = window.Read(timeout=50)
            global generations
            try:
                generations = int(list(value.values())[1])
                temp = str(savedIndex + 1) + " out of " + str(len(savedSteps))
                window.FindElement("index").update(temp)

            except:
                m =1;
            # print(generations)
            # generations = int(value)
            # Mode: Neutral
            if button == "previous":

                if(savedIndex > 0):
                    savedIndex = savedIndex - 1
                    window.FindElement("board").update(self.create_board(self, savedSteps[savedIndex]))
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

            if button == 'Genetic Run':

                    global best_atack
                    best_atack = 10
                    # run(layout)
                    savedSteps.clear()
                    initial_board(self,window)
                    # print(len(savedSteps))
                    savedIndex = len(savedSteps) - 1
                    savedSteps.sort(key=fitness, reverse = True)
                    window.FindElement("board").update(self.create_board(self, savedSteps[savedIndex]))


                    self.redraw_board(window)

            if button == 'A* Run':

                    initial_board(self, window)
                    window.FindElement("board").update(self.create_board(True, backtracking()))
                    self.redraw_board(window)
                    # best_atack = 10
                    # # run(layout)
                    # savedSteps.clear()
                    # initial_board(self,window)
                    # print(len(savedSteps))
                    # savedIndex = len(savedSteps) - 1
                    # savedSteps.sort(key=fitness, reverse = True)
                    # window.FindElement("board").update(self.create_board(self, savedSteps[savedIndex]))
                    #
                    #
                    # self.redraw_board(window)





# def run(hi):

        # time.sleep(5)


N = 8

""" ld is an array where its indices indicate row-col+N-1  
(N-1) is for shifting the difference to store negative  
indices """
ld = [0] * 30

""" rd is an array where its indices indicate row+col  
and used to check whether a queen can be placed on  
right diagonal or not"""
rd = [0] * 30

"""column array where its indices indicates column and  
used to check whether a queen can be placed in that  
    row or not"""
cl = [0] * 30

""" A utility function to print solution """

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



def printSolution(board):
    for i in range(N):
        for j in range(N):
            print(board[i][j], end = " ")
        print()
    print(steps)

""" A recursive utility function to solve N  
Queen problem """

steps=0
best=[]
generations = 500
best_atack=10
savedSteps=[]
savedIndex=0
def solveNQUtil(board, col):
    """ base case: If all queens are placed
        then return True """
    if (col >= N):
        print("solved")
        return True
    global steps

    steps=0
    for i in range(N):
        steps = steps+1

        if ((ld[i - col + N - 1] != 1 and
             rd[i + col] != 1) and cl[i] != 1):

            board[i][col] = QUEENB
            ld[i - col + N - 1] = rd[i + col] = cl[i] = 1

            if (solveNQUtil(board, col + 1)):
                return True

            board[i][col] = 0  # BACKTRACK
            ld[i - col + N - 1] = rd[i + col] = cl[i] = 0

    return False


""" This function solves the N Queen problem using  
Backtracking. It mainly uses solveNQUtil() to  
solve the problem. It returns False if queens  
cannot be placed, otherwise, return True and  
prints placement of queens in the form of 1s.  
Please note that there may be more than one  
solutions, this function prints one of the  
feasible solutions."""

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
        # print("isL i ",i)
        if x != i and vector[i] != 0:
            # print("isL i ", i)
            if vector[i] == vector[x]:

                return False
            elif vector[i] - vector[x] == (i - x) or vector[i] - vector[x] == (x - i):
                return False

    return True




def mrv(vector):
    length = len(vector)
    myk = 10
    min = 10

    for i in range(0, length):
        temp = 0
        if vector[i] == 0:
            # print("i is", i)
            for j in range(1, length+1):
                vector[i] = j
                if is_legal(i, vector):
                    temp = temp + 1
                    # print("temp", temp)
            vector[i] = 0

            if min > temp:
                min = temp
                myk = i
                # print("k is", myk, "\n")

    # print(vector)
    return myk


def backtracking():
    vector = [0, 0, 0, 0, 0, 0, 0, 0]
    k = 0
    while k >= 0:
        while vector[k] <= 7:
            vector[k] = vector[k]+1
            if is_solution(vector):
                print("done")
                print(vector)
                for i in range(0, len(vector)):
                    vector[i] -= 1
                print(vector)
                return vector
            elif is_p_and_L(vector):
                k += 1
        vector[k] = 0
        k -= 1


def backtraking_with_mrv (MRV):
    vector = [0, 0, 0, 0, 0, 0, 0, 0]
    stack = []
    k = 0
    if MRV:
        stack.append(k)
    while k >= 0:
        print('k with mrv', k ,vector)
        while vector[k] <= 7:
            vector[k] = vector[k]+1
            if is_solution(vector):
                print(vector)
                for i in range(0, len(vector)):
                    vector[i] -= 1
                print(vector)
                return vector
            elif is_p_and_L(vector):
                if MRV:
                    k = mrv(vector)
                    stack.append(k)
                else:
                    k += 1
        vector[k] = 0

        if MRV:
            if stack:
                k = stack.pop()
            else:
                break
        else:
            k -= 1








def main():
    theme = 'Reddit'

    pecg = EasyChessGui(theme)

    pecg.main_loop()



if __name__ == "__main__":
    main()