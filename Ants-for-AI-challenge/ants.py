#!/usr/bin/env python
import sys
import traceback
import time
import random
from collections import deque
from collections import defaultdict
from math import sqrt
from operator import itemgetter
from optparse import OptionParser

maxint = 32767 
#32767
#2147483647

MY_ANT = 0
ANTS = 0
DEAD = -1
LAND = -2
FOOD = -3
WATER = -4
UNSEEN = -5

FIGHT_WIN = 1
FIGHT_DIE = 2
FIGHT_TIE = 3
FIGHT_FRE = 4

AIM = {'n': (-1, 0),
       'e': (0, 1),
       's': (1, 0),
       'w': (0, -1)}
RIGHT = {'n': 'e',
         'e': 's',
         's': 'w',
         'w': 'n'}
LEFT = {'n': 'w',
        'e': 'n',
        's': 'e',
        'w': 's'}
BEHIND = {'n': 's',
          's': 'n',
          'e': 'w',
          'w': 'e'}

PLAYER_ANT = 'abcdefghij'
HILL_ANT = string = 'ABCDEFGHIJ'
PLAYER_HILL = string = '0123456789'
MAP_OBJECT = '?%*.!'
MAP_RENDER = PLAYER_ANT + HILL_ANT + PLAYER_HILL + MAP_OBJECT

class Ants():
    def __init__(self):
        self.cols = 0
        self.rows = 0
        self.viewradius2 = 0
        self.attackradius2 = 0
        self.spawnradius2 = 0
        self.turns = 0
        self.turn = -1
        self.turntime = 0
        self.loadtime = 0

        self.map = []
        self.hill_list = {}
        self.ant_list = {}
        self.food_list = []
        self.visible_food_list = []
        self.turn_start_time = 0
        self.unseen_cells = []

        self.combat_offset = []
        self.hill_guard_offset = {}
        self.least_seen_offset = []
        self.vision_disc = []

        self.visible = []
        self.food_influence = []
        self.food_map = []
        self.food_stop = []
        self.explore_influence = []
        self.distance_map = []
        self.hill_influence = []
        self.visited_map = []
        self.spread_food = deque()
        self.spread_hill = deque()
        self.spread_explore = deque()
        
        self.attack_influence = []
        self.total_attack = []
        self.fight_influence = []

    def setup(self, data):
        "Parse initial input and setup starting game state"
        for line in data.split('\n'):
            line = line.strip().lower()
            if len(line) > 0:
                tokens = line.split()
                key = tokens[0]
                if key == 'cols':
                    self.cols = int(tokens[1])
                elif key == 'rows':
                    self.rows = int(tokens[1])
                elif key == 'player_seed':
                    random.seed(int(tokens[1]))
                elif key == 'turntime':
                    self.turntime = int(tokens[1])
                elif key == 'loadtime':
                    self.loadtime = int(tokens[1])
                elif key == 'viewradius2':
                    self.viewradius2 = int(tokens[1])
                elif key == 'attackradius2':
                    self.attackradius2 = int(tokens[1])
                elif key == 'spawnradius2':
                    self.spawnradius2 = int(tokens[1])
                elif key == 'turns':
                    self.turns = int(tokens[1])

        self.map = [[LAND for col in range(self.cols)] for row in range(self.rows)]
        self.visited_map = [[0 for col in range(self.cols)] for row in range(self.rows)]
        self.unseen_cells = []

        self.find_radius_offset()
        self.spread_food = deque()
        self.spread_explore = deque()
        self.spread_hill = deque()
        self.food_influence = [[0 for col in range(self.cols)] for row in range(self.rows)]
        self.food_map = [[(0,0) for col in range(self.cols)] for row in range(self.rows)]
        self.food_stop = []
        self.explore_influence = [[0 for col in range(self.cols)] for row in range(self.rows)]
        self.hill_influence = [[0 for col in range(self.cols)] for row in range(self.rows)]

        self.attack_influence = [[[0 for col in range(self.cols)] for row in range(self.rows)] for player in range(10)]
        self.total_attack = [[0 for col in range(self.cols)] for row in range(self.rows)]
        self.fight_influence = [[[0 for col in range(self.cols)] for row in range(self.rows)] for player in range(10)]

    def update(self, data):
        "Parse engine input and update the game state"
        self.turn_start_time = time.time()
        
        for row, col in self.ant_list.keys():
            self.map[row][col] = LAND

        self.ant_list = {}
        self.hill_list = {}
        self.visible_food_list = []
        visible_hill_list = {}
        
        # update map and create new ant and food lists
        for line in data.split('\n'):
            line = line.strip().lower()
            if len(line) > 0:
                tokens = line.split()
                if len(tokens) == 2:
                    if tokens[0] == 'turn':
                        self.turn = int(tokens[1])
                elif len(tokens) >= 3:
                    row = int(tokens[1])
                    col = int(tokens[2])
                    if tokens[0] == 'w':
                        self.map[row][col] = WATER
                    elif tokens[0] == 'f':
                        self.map[row][col] = FOOD
                        self.visible_food_list.append((row, col))
                    else:
                        owner = int(tokens[3])
                        if tokens[0] == 'a':
                            self.map[row][col] = owner
                            self.ant_list[(row, col)] = owner
                        elif tokens[0] == 'd':
                            self.map[row][col] = LAND
                        elif tokens[0] == 'h':
                            self.map[row][col] = owner + 25
                            visible_hill_list[(row, col)] = owner
        self._update_visible()

        # Update food
        new_food = []
        for r,c in self.food_list:
            if self.visible[r][c] == 1:
                self.map[r][c] = LAND
            else:
                new_food.append((r,c))

        for r,c in self.visible_food_list:
            self.map[r][c] = FOOD
        self.food_list = new_food + self.visible_food_list

        # Update hills
        for pos, owner in self.hill_list.items():
            if self.visible[pos[0]][pos[1]] == 1 and pos not in visible_hill_list:
                del self.hill_list[pos]
        self.hill_list.update(visible_hill_list)
        self.fill_diffusion_map()

    def refine_orders(self):
        self.attack_influence = [[[0 for col in range(self.cols)] for row in range(self.rows)] for player in range(10)]
        self.total_attack = [[0 for col in range(self.cols)] for row in range(self.rows)]
        self.weakness_map = [[99 for col in range(self.cols)] for row in range(self.rows)]

        singleton_move = []
        for aloc, p in self.ant_list.items():
            singleton_spread = []
            nei = self.possibility(aloc)
            for nr,nc,d in nei:
                if self.passable((nr,nc)) and (nr,nc,p) not in singleton_move:
                    singleton_move.append((nr,nc,p))
                    for (ofr, ofc) in self.combat_offset:
                        xr = (nr+ofr)%self.rows
                        xc = (nc+ofc)%self.cols
                        if (xr,xc) not in singleton_spread:
                            singleton_spread.append((xr,xc))
                            self.attack_influence[p][xr][xc] += 1
                            self.total_attack[xr][xc] += 1

        for aloc, p in self.enemy_ants():
            nei = self.possibility(aloc)
            for nr,nc,d in nei:
                if self.passable((nr,nc)):
                    weakness = self.total_attack[nr][nc] - self.attack_influence[p][nr][nc]
                    for (ofr, ofc) in self.combat_offset:
                        if self.weakness_map[(nr+ofr)%self.rows][(nc+ofc)%self.cols] > weakness:
                            self.weakness_map[(nr+ofr)%self.rows][(nc+ofc)%self.cols] = weakness

        new_orders = {}
        dests = []
        for aloc in self.my_ants():
            best_dir = defaultdict(int)
            dirs = self.goal_direction(aloc, dests)
            for d in dirs:
                best_dir[d] = 2
            nei = self.possibility(aloc)
            random.shuffle(nei)
            for r,c,d in nei:
                if self.passable((r,c)) and (r,c) not in dests:
                    if self.weakness_map[r][c] > self.total_attack[r][c] - self.attack_influence[0][r][c]:
                        best_dir[d] += 6
                    elif self.weakness_map[r][c] < self.total_attack[r][c] - self.attack_influence[0][r][c]:
                        best_dir[d] -= 6
                    elif self.weakness_map[r][c] == 99:
                        best_dir[d] += 3
                    elif self.weakness_map[r][c] == self.total_attack[r][c] - self.attack_influence[0][r][c]:
                        nhill_dist = self.nearest_hill_dist((r,c))
                        if nhill_dist < 14:
                            best_dir[d] += 8            # R.I.P You lived like a Spartan

                        best_dir[d] -= 3
                else:
                    best_dir[d] -= 10
    
            best_dlist = best_dir.items()
            best_dlist.sort(key=itemgetter(1), reverse=True)
            (bestd,dump) = best_dlist[0]
            new_orders[aloc] = bestd
            nl = self.destination(aloc, bestd)
            dests.append(nl)

        return new_orders

    def fill_diffusion_map(self):
        self.spread_food = deque()
        self.spread_explore = deque()
        self.spread_hill = deque()
        self.food_influence = [[0 for col in range(self.cols)] for row in range(self.rows)]
        self.food_map = [[(0,0) for col in range(self.cols)] for row in range(self.rows)]
        self.food_stop = []
        self.explore_influence = [[0 for col in range(self.cols)] for row in range(self.rows)]
        self.hill_influence = [[0 for col in range(self.cols)] for row in range(self.rows)]

        myhillcount = len(self.my_hills())
        myantscount = len(self.my_ants())
        #self.calculate_distances()
        #(nearest_enemy, dist) = self.find_nearest_enemy()
            #if nearest_enemy != None and dist < 20:
            #(r,c) = nearest_enemy
            #self.explore_influence[r][c] = maxint
        #self.add_explore_seed(nearest_enemy)

        if myhillcount > 0:
            for r,c in self.food():
                self.food_influence[r][c] = maxint
                self.food_map[r][c] = (r,c)
                self.add_food_seed((r,c))
        
        for (r,c),p in self.enemy_hills():
            self.food_influence[r][c] = maxint
            self.food_map[r][c] = (r,c)
            self.add_food_seed((r,c))

        for (ar,ac) in self.my_ants():
            for (vr,vc) in self.least_seen_offset:
                nr = (ar+vr)%self.rows
                nc = (ac+vc)%self.cols
                if self.visited_map[nr][nc] == 0:
                    self.unseen_cells.append((nr,nc))
                elif self.map[nr][nc] != WATER and self.turn-self.visited_map[nr][nc] > 6:
                    self.food_influence[nr][nc] = maxint
                    self.food_map[nr][nc] = (nr,nc)
                    self.add_food_seed((nr,nc))

        for (r,c) in self.unseen_cells:
            if self.visited_map[r][c] == 0:
                self.add_explore_seed((r,c))
                self.explore_influence[r][c] = maxint
            else:
                self.unseen_cells.remove((r,c))

        if len(self.unseen_cells) == 0:
            for (r,c), owner in self.enemy_hills():
                self.explore_influence[r][c] = maxint
                self.add_explore_seed((r,c))
            for r,c in self.food():
                self.explore_influence[r][c] = maxint
                self.add_explore_seed((r,c))

        if myantscount > myhillcount*10 or self.turn >= 24:
            for (r,c),p in self.enemy_hills():
                self.hill_influence[r][c] = (self.rows+self.cols)/6
                self.add_hill_seed((r,c))

        for (r,c),p in self.enemy_ants():
            nhill_dist = self.nearest_hill_dist((r,c))
            if nhill_dist < 10:
                self.hill_influence[r][c] = 12
                self.add_hill_seed((r,c))
            elif nhill_dist < 16:
                self.hill_influence[r][c] = 8
                self.add_hill_seed((r,c))

        self.calculate_diffusion()

    def find_nearest_enemy(self):
        enemy = None
        enemy_dist = maxint
        for (r,c),p in self.enemy_ants():
            dist = maxint - self.distance_map[r][c]
            if enemy_dist < dist:
                enemy_dist = dist
                enemy = (r,c)
        return (enemy, enemy_dist)
            
    def calculate_distances(self):
        spread_distance = deque()
        self.distance_map = [[0 for col in range(self.cols)] for row in range(self.rows)]
        
        for (r,c) in self.my_hills():
            self.distance_map[r][c] = maxint
            nei = self.neighbours((r,c))
            random.shuffle(nei)
            for sr,sc in nei:
                if self.distance_map[sr][sc] == 0 and self.visited_map[sr][sc] > 0 and self.map[sr][sc] != WATER:
                    spread_distance.append((sr,sc))

        while spread_distance:
            (r,c) = spread_distance.popleft()
            if self.distance_map[r][c] == 0:
                diffusion = self.get_distance_value((r,c))
                if diffusion > 0:
                    self.distance_map[r][c] = diffusion
                    nei = self.neighbours((r,c))
                    random.shuffle(nei)
                    for sr,sc in nei:
                        if self.distance_map[sr][sc] == 0 and self.visited_map[sr][sc] > 0 and self.map[sr][sc] != WATER:
                            spread_distance.append((sr,sc))

    def nearest_hill_dist(self, loc):
        nhill_dist = 9999
        for hill in self.my_hills():
            dist = self.distance(hill, loc)
            if dist < nhill_dist:
                nhill_dist = dist
        return nhill_dist

    def nearest_enemy_hill(self, loc):
        nhill_dist = 9999
        hill_loc = None
        for hill,p in self.enemy_hills():
            dist = self.distance(hill, loc)
            if dist < nhill_dist:
                nhill_dist = dist
                hill_loc = hill
        return (hill_loc, nhill_dist)

    def evaluate_sacrifice(self, loc):
        (r,c) = loc
        enemycount = 1
        allycount = 0
        for (ofr,ofc) in self.vision_disc:
            if self.map[(r+ofr)%self.rows][(c+ofc)%self.cols] == MY_ANT:
                allycount += 1
            elif 0 < self.map[(r+ofr)%self.rows][(c+ofc)%self.cols] < 25:
                enemycount += 1
        
        if enemycount >= allycount:
            return 0
        else:
            return 1

    def add_food_seed(self, loc):
        nei = self.neighbours(loc)
        random.shuffle(nei)
        for r,c in nei:
            if self.map[r][c] == MY_ANT:
                self.food_stop.append(self.food_map[loc[0]][loc[1]])
            elif self.food_influence[r][c] == 0 and self.map[r][c] == LAND and self.visited_map[r][c] > 0:
                self.food_map[r][c] = self.food_map[loc[0]][loc[1]]
                self.spread_food.append((r,c))

    def add_explore_seed(self, loc):
        nei = self.neighbours(loc)
        random.shuffle(nei)
        for r,c in nei:
            if self.explore_influence[r][c] == 0 and self.map[r][c] == LAND and self.visited_map[r][c] > 0:
                self.spread_explore.append((r,c))

    def add_hill_seed(self, loc):
        nei = self.neighbours(loc)
        random.shuffle(nei)
        for r,c in nei:
            if self.hill_influence[r][c] == 0 and self.map[r][c] == LAND and self.visited_map[r][c] > 0:
                self.spread_hill.append((r,c))

    def get_distance_value(self, loc):
        diffusion = 0
        nei = self.neighbours(loc)
        for r,c in nei:
            if diffusion < self.distance_map[r][c]:
                diffusion = self.distance_map[r][c]
        return diffusion-1

    def get_explore_diffusion(self, loc):
        diffusion = 0
        nei = self.neighbours(loc)
        for r,c in nei:
            if diffusion < self.explore_influence[r][c]:
                diffusion = self.explore_influence[r][c]
        return diffusion-1
    
    def get_hill_diffusion(self, loc):
        diffusion = 0
        nei = self.neighbours(loc)
        for r,c in nei:
            if diffusion < self.hill_influence[r][c]:
                diffusion = self.hill_influence[r][c]
        return diffusion-1

    def calculate_diffusion(self):
        while self.spread_food:
            (r,c) = self.spread_food.popleft()
            if self.food_influence[r][c] == 0:
                if self.food_map[r][c] not in self.food_stop:
                    diffusion = 0
                    nei = self.neighbours((r,c))
                    for nr,nc in nei:
                        if diffusion < self.food_influence[nr][nc]:
                            diffusion = self.food_influence[nr][nc]
                            self.food_map[r][c] = self.food_map[nr][nc]
                    diffusion = diffusion-1
                    if diffusion > 0:
                        self.food_influence[r][c] = diffusion
                        self.add_food_seed((r,c))
                    else:
                        self.food_map[r][c] = (0,0)

        while self.spread_explore:
            (r,c) = self.spread_explore.popleft()
            if self.explore_influence[r][c] == 0:
                diffusion = self.get_explore_diffusion((r,c))
                if diffusion > 0:
                    self.explore_influence[r][c] = diffusion
                    self.add_explore_seed((r,c))

        while self.spread_hill:
            (r,c) = self.spread_hill.popleft()
            if self.hill_influence[r][c] == 0:
                diffusion = self.get_hill_diffusion((r,c))
                if diffusion > 0:
                    self.hill_influence[r][c] = diffusion
                    self.add_hill_seed((r,c))

    def goal_direction(self, loc, dests):
        food_dir = []
        hill_dir = []
        explore_dir = []

        total_food = 0
        total_hill = 0
        total_explore = 0
        
        nei = self.neighbours_and_dirs(loc)
        for r,c,d in nei:
            if self.map[r][c] != WATER and (r,c) not in dests:
                total_food += self.food_influence[r][c]
                food_dir.append((d,self.food_influence[r][c]))
                total_hill += self.hill_influence[r][c]
                hill_dir.append((d,self.hill_influence[r][c]))
                total_explore += self.explore_influence[r][c]
                explore_dir.append((d,self.explore_influence[r][c]))

        dir_output = []
        if total_hill != 0:
            hill_dir.sort(key=itemgetter(1), reverse=True)
            (dirx, dump) = hill_dir[0]
            high_inf = dump
            for dirx, dump in hill_dir:
                if dump == high_inf:
                    dir_output.append(dirx)
            return dir_output
        
        if total_food != 0:
            food_dir.sort(key=itemgetter(1), reverse=True)
            (dirx, dump) = food_dir[0]
            high_inf = dump
            for dirx, dump in food_dir:
                if dump == high_inf:
                    dir_output.append(dirx)
            return dir_output
        
        if total_explore != 0:
            explore_dir.sort(key=itemgetter(1), reverse=True)
            (dirx, dump) = explore_dir[0]
            high_inf = dump
            for dirx, dump in explore_dir:
                if dump == high_inf:
                    dir_output.append(dirx)
            return dir_output

        dir_output.append('0')
        return dir_output

    def find_radius_offset(self):
        self.hill_guard_offset = {}
        offset = []
        offset.append((+1,+1))
        offset.append((-1,-1))
        self.hill_guard_offset[1] = offset
        
        offset = []
        offset.append((+1,+1))
        offset.append((-1,-1))
        offset.append((-1,+1))
        offset.append((+1,-1))
        self.hill_guard_offset[2] = offset
        
        offset = []
        offset.append((+1,+1))
        offset.append((-1,-1))
        offset.append((-1,+1))
        offset.append((+1,-1))
        offset.append((+1,+2))
        offset.append((+2,+1))
        offset.append((-1,-2))
        offset.append((-2,-1))
        offset.append((-1,+2))
        offset.append((-2,+1))
        offset.append((+1,-2))
        offset.append((+2,-1))
        self.hill_guard_offset[3] = offset

        self.combat_offset = []
        max_dist = self.attackradius2
        mx = int(sqrt(max_dist))
        for d_row in range(-mx,mx+1):
            for d_col in range(-mx,mx+1):
                d = d_row**2 + d_col**2
                if 0 < d <= max_dist:
                    self.combat_offset.append((d_row, d_col))

        self.vision_disc = []
        max_dist = self.viewradius2
        mx = int(sqrt(max_dist))
        for d_row in range(-mx,mx+1):
            for d_col in range(-mx,mx+1):
                d = d_row**2 + d_col**2
                if 0 < d <= max_dist:
                    self.vision_disc.append((d_row, d_col))

        self.least_seen_offset = []
        max_dist = self.viewradius2+12
        mx = int(sqrt(max_dist))
        for d_row in range(-mx,mx+1):
            for d_col in range(-mx,mx+1):
                d = d_row**2 + d_col**2
                if 0 < d <= max_dist:
                    self.least_seen_offset.append((d_row, d_col))
        max_dist = self.viewradius2
        mx = int(sqrt(max_dist))
        for d_row in range(-mx,mx+1):
            for d_col in range(-mx,mx+1):
                d = d_row**2 + d_col**2
                if 0 < d <= max_dist:
                    self.least_seen_offset.remove((d_row, d_col))

    def time_remaining(self):
        return self.turntime - int(1000 * (time.time() - self.turn_start_time))
    
    def issue_order(self, ant_loc, dir):
        "Issue an order by either (ant_loc, dir) or (ant_loc, dest) pair"
        sys.stdout.write('o %s %s %s\n' % (ant_loc[0], ant_loc[1], dir))
        sys.stdout.flush()
        
    def finish_turn(self):
        "Finish the turn by writing the go line"
        sys.stdout.write('go\n')
        sys.stdout.flush()
    
    def my_hills(self):
        return [loc for loc, owner in self.hill_list.items()
                    if owner == MY_ANT]

    def enemy_hills(self):
        return [(loc, owner) for loc, owner in self.hill_list.items()
                    if owner != MY_ANT]
        
    def my_ants(self):
        'return a list of all my ants'
        return [(row, col) for (row, col), owner in self.ant_list.items()
                    if owner == MY_ANT]

    def enemy_ants(self):
        'return a list of all visible enemy ants'
        return [((row, col), owner)
                    for (row, col), owner in self.ant_list.items()
                    if owner != MY_ANT]

    def food(self):
        "Return a list of all known food locations (visible or not)"
        return self.food_list[:]

    def passable(self, loc):
        "True if seen and not water"
        row, col = loc
        return self.map[row][col] != WATER
    
    def possibility(self, pos):
        return [((pos[0]-1)%self.rows, pos[1], 'n'), (pos[0], (pos[1]+1)%self.cols, 'e'), ((pos[0]+1)%self.rows, pos[1], 's'), (pos[0], (pos[1]-1)%self.cols, 'w'), (pos[0], pos[1], '0')]

    def neighbours(self, pos):
        return [((pos[0]-1)%self.rows, pos[1]), (pos[0], (pos[1]+1)%self.cols), ((pos[0]+1)%self.rows, pos[1]), (pos[0], (pos[1]-1)%self.cols)]

    def neighbours_and_dirs(self, pos):
        return [((pos[0]-1)%self.rows, pos[1], 'n'), (pos[0], (pos[1]+1)%self.cols, 'e'), ((pos[0]+1)%self.rows, pos[1], 's'), (pos[0], (pos[1]-1)%self.cols, 'w')]

    def destination(self, loc, direction):
        if direction == '0':
            return loc
        else:
            row, col = loc
            d_row, d_col = AIM[direction]
            return ((row + d_row) % self.rows, (col + d_col) % self.cols)        

    def distance(self, loc1, loc2):
        "Calculate the closest distance between two locations"
        row1, col1 = loc1
        row2, col2 = loc2
        d_col = min(abs(col1 - col2), self.cols - abs(col1 - col2))
        d_row = min(abs(row1 - row2), self.rows - abs(row1 - row2))
        return d_row + d_col

    def direction(self, loc1, loc2):
        "Return a list of the 1 or 2 fastest (closest) directions to reach a location"
        row1, col1 = loc1
        row2, col2 = loc2
        height2 = self.rows//2
        width2 = self.cols//2
        d = []
        if row1 < row2:
            if row2 - row1 >= height2:
                d.append('n')
            if row2 - row1 <= height2:
                d.append('s')
        if row2 < row1:
            if row1 - row2 >= height2:
                d.append('s')
            if row1 - row2 <= height2:
                d.append('n')
        if col1 < col2:
            if col2 - col1 >= width2:
                d.append('w')
            if col2 - col1 <= width2:
                d.append('e')
        if col2 < col1:
            if col1 - col2 >= width2:
                d.append('e')
            if col1 - col2 <= width2:
                d.append('w')
        return d

    def _update_visible(self):
        self.visible = [[0 for col in range(self.cols)] for row in range(self.rows)]
        for ar, ac in self.my_ants():
            for nr,nc in self.vision_disc:
                xr = (ar+nr)%self.rows
                xc = (ac+nc)%self.cols
                self.visible[xr][xc] = 1
                self.visited_map[xr][xc] = self.turn
    
    def render_text_map(self):
        """Return a pretty text representation of the map"""
        tmp = ''
        for row in self.map:
            tmp += '# %s\n' % ''.join([MAP_RENDER[col] for col in row])
        return tmp

    # static methods are not tied to a class and don't have self passed in
    # this is a python decorator
    @staticmethod
    def run(bot):
        "Parse input, update game state and call the bot classes do_turn method"
        ants = Ants()
        map_data = ''
        while(True):
            try:
                current_line = sys.stdin.readline().rstrip('\r\n') # string new line char
                if current_line.lower() == 'ready':
                    ants.setup(map_data)
                    bot.do_setup(ants)
                    ants.finish_turn()
                    map_data = ''
                elif current_line.lower() == 'go':
                    ants.update(map_data)
                    # call the do_turn method of the class passed in
                    bot.do_turn(ants)
                    ants.finish_turn()
                    map_data = ''
                else:
                    map_data += current_line + '\n'
            except EOFError:
                break
            except KeyboardInterrupt:
                raise
            except:
                # don't raise error or return so that bot attempts to stay alive
                traceback.print_exc(file=sys.stderr)
                sys.stderr.flush()
