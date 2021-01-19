import model
from model.entity_type import EntityType as et
import pandas as pd
from sklearn.cluster import KMeans
from math import hypot
import random
import numpy as np

import datetime  # DEBUG
# import pickle  # DEBUG


class MyStrategy:

    def __init__(self):
        self.debug = False
        self.time_spent = 0
        self.log = []
        self.current_tick = 0
        self.map_size = 80
        self.entities = []
        self.resources = []
        self.my_factories = {}
        self.bases = {}
        self.busy_field = np.zeros([80,80]).astype(int)
        self.fog_field = np.ones([80,80]).astype(int)
        self.entity_counter = {
            et.BUILDER_UNIT:0,
            et.RANGED_UNIT:0,
            et.MELEE_UNIT:0,
            et.HOUSE:0,
            et.BUILDER_BASE: 0,
            et.MELEE_BASE: 0,
            et.RANGED_BASE: 0,
            et.TURRET: 0,
            et.WALL: 0,
        }
        self.damaged_counter = {
            et.BUILDER_UNIT: 0,
            et.RANGED_UNIT: 0,
            et.MELEE_UNIT: 0,
            et.HOUSE: 0,
            et.BUILDER_BASE: 0,
            et.MELEE_BASE: 0,
            et.RANGED_BASE: 0,
            et.TURRET: 0,
            et.WALL: 0,
        }
        self.inicialization = True
        self.factory_start_treshold = 20
        self.melee_ranged_half_distance = 1
        self.spy_distance = 4
        self.retreat_distance = 11
        self.retreaters = {}
        self.entity_actions = {}
        self.house_builders_batch_size = 4
        self.silent_period = 10
        self.dynamic_period = 1
        self.repairers_per_target = 2
        self.house_side_switch = 150
        self.max_builder_distance = 0
        self.population_use = 0
        self.population_provide = 0
        self.ranged_base_count = 0
        self.melee_base_count = 0
        self.my_attacker_factories = []
        self.my_attackers = 0
        self.my_builders = 0
        #self.near_enemy_attackers = 0
        self.builder_base_id = 0
        self.enemy_centroids = pd.DataFrame([[6,  22], [ 19, 19], [22, 6]], columns=['x', 'y'])
        self.centroids_builders_range = 10
        self.complete_x = {}
        self.complete_y = {}
        self.busy_builders = []
        self.resource_wall_x = {}
        self.resource_wall_y = {}

        self.sizes = {
            et.RANGED_UNIT: 1,
            et.MELEE_UNIT: 1,
            et.BUILDER_UNIT: 0,
            et.HOUSE: 3,
            et.TURRET: 4,
            et.WALL: 1,
            et.RANGED_BASE: 5,
            et.MELEE_BASE: 5,
            et.BUILDER_BASE: 5,
        }

        self.build_spec = {
            et.RANGED_UNIT: et.RANGED_BASE,
            et.MELEE_UNIT: et.MELEE_BASE,
            et.BUILDER_UNIT: et.BUILDER_BASE,
            et.HOUSE: et.BUILDER_UNIT,
            et.TURRET: et.BUILDER_UNIT,
            et.WALL: et.BUILDER_UNIT,
            et.RANGED_BASE: et.BUILDER_UNIT,
            et.MELEE_BASE: et.BUILDER_UNIT,
            et.BUILDER_BASE: et.BUILDER_UNIT,
        }
        self.history = {}
        self.tick = {
            'resource':0,
            'builders':pd.DataFrame(columns = ['entity_id', 'entity_type', 'x', 'y', 'h']),
            'build_tasks':{},
            'build_targets': {},
            'build_plan':[],
            'busy_builders':[]
        }

        self.build_plan = []

        # default unit action ++
        self.citizens = {}
        default_target = model.vec2_int.Vec2Int(50, 50)
        self.default_action = {}
        m, b, a, r = None, None, None, None
        self.default_action['do_nothing'] = model.EntityAction(m, b, a, r)
        self.default_action[et.HOUSE] = model.EntityAction(m, b, a, r)
        m = model.move_action.MoveAction(default_target, True, True)
        a = model.attack_action.AttackAction(
            target=None,
            auto_attack=model.auto_attack.AutoAttack(
                pathfind_range=10,
                valid_targets=[et.RESOURCE]
            )
        )
        self.default_action[et.BUILDER_UNIT] = model.EntityAction(m, b, a, r)
        a = model.attack_action.AttackAction(
            target=None,
            auto_attack=model.auto_attack.AutoAttack(
                pathfind_range=10,
                valid_targets=[]
            )
        )
        b = None
        self.default_action[et.RANGED_UNIT] = model.EntityAction(m, b, a, r)
        self.default_action[et.MELEE_UNIT] = model.EntityAction(m, b, a, r)
        m = None
        self.default_action[et.TURRET] = model.EntityAction(m, b, a, r)
        b = model.build_action.BuildAction(et.BUILDER_UNIT, model.vec2_int.Vec2Int(5, 4))
        self.default_action[et.BUILDER_BASE] = model.EntityAction(m, b, a, r)
        b = model.build_action.BuildAction(et.RANGED_UNIT, model.vec2_int.Vec2Int(20, 9))
        self.default_action[et.RANGED_BASE] = model.EntityAction(m, b, a, r)
        b = model.build_action.BuildAction(et.MELEE_UNIT, model.vec2_int.Vec2Int(10, 19))
        self.default_action[et.MELEE_BASE] = model.EntityAction(m, b, a, r)
        # default unit action --

        self.time_report = {
            'tick': []
        }

    def init_entities(self, timer_start, timer_end, player_view):

        if self.inicialization:
            self.map_size = player_view.map_size
            self.inicialization = False

        self.my_factories = {}
        self.log = []
        self.current_tick = player_view.current_tick
        self.busy_field = np.zeros([player_view.map_size, player_view.map_size]).astype(int)
        self.fog_field = np.ones([player_view.map_size, player_view.map_size]).astype(int)
        self.tick['build_tasks'] = {}
        self.tick['build_targets'] = {}
        self.tick['resource'] = player_view.players[player_view.my_id - 1].resource
        self.tick['busy_builders'] = []
        #self.tick['build_plan_v2'] = []
        tick_builders = []
        self.history[player_view.current_tick] = {'entity_counter':{}}
        for key in self.entity_counter.keys():
            self.entity_counter[key] = 0
            self.history[player_view.current_tick]['entity_counter'][key] = 0
        for key in self.damaged_counter.keys():
            self.damaged_counter[key] = 0
        entity_storage = []
        resource_storage = []
        self.population_use = 0
        self.population_provide = 0
        """prev_ranged_base_count = self.ranged_base_count
        prev_melee_base_count = self.melee_base_count"""
        self.ranged_base_count = 0
        self.melee_base_count = 0
        self.my_attacker_factories = []
        self.my_attackers = 0
        self.my_builders = 0
        #self.near_enemy_attackers = 0
        self.busy_builders = []
        self.resource_wall_x = [0 for _ in range(0, player_view.map_size)]
        self.resource_wall_y = [0 for _ in range(0, player_view.map_size)]
        for entity in player_view.entities:
            # busy field ++
            entity_size = player_view.entity_properties[entity.entity_type].size
            if not (entity.entity_type == et.BUILDER_UNIT and entity.player_id == player_view.my_id):
                for x in range(entity_size):
                    for y in range(entity_size):
                        self.busy_field[entity.position.x + x, entity.position.y + y] += 1 # = entity.id #+= 1
            sight_range = player_view.entity_properties[entity.entity_type].sight_range
            self.fog_field[
            entity.position.x - sight_range: entity.position.x + entity_size + sight_range,
            entity.position.y - sight_range: entity.position.y + entity_size + sight_range
            ] = 0
            # busy field --
            if entity.entity_type == et.RESOURCE:
                if entity.position.x < 3:
                    self.resource_wall_y[entity.position.y] += 1
                if entity.position.y < 3:
                    self.resource_wall_x[entity.position.x] += 1
                resource_storage.append([
                    entity.position.x,
                    entity.position.y,
                    hypot(entity.position.x, entity.position.y)
                    #entity.position.x + entity.position.y
                ])
            else:
                e_type = player_view.entity_properties[entity.entity_type]
                entity_storage.append([
                    entity.player_id,
                    entity.id,
                    entity.entity_type,
                    entity.position.x,
                    entity.position.y,
                    hypot(entity.position.x, entity.position.y),
                    #entity.position.x + entity.position.y,
                    e_type.max_health-entity.health
                ])
                if entity.player_id == player_view.my_id:
                    if entity.entity_type in [
                        et.BUILDER_BASE,
                        et.MELEE_BASE,
                        et.RANGED_BASE
                    ]:
                        self.my_factories[entity.id] = entity.entity_type
                    if entity.entity_type in [
                        et.BUILDER_UNIT,
                        # et.RANGED_UNIT,
                        # et.MELEE_UNIT,
                        et.BUILDER_BASE,
                        et.MELEE_BASE,
                        et.RANGED_BASE
                    ]:
                        tick_builders.append([
                            entity.id,
                            entity.entity_type,
                            entity.position.x,
                            entity.position.y
                        ])
                    self.history[player_view.current_tick]['entity_counter'][entity.entity_type] += 1
                    if entity.entity_type in [et.HOUSE, et.TURRET, et.BUILDER_BASE, et.RANGED_BASE, et.MELEE_BASE]:
                        if entity.health == e_type.max_health:
                            self.entity_counter[entity.entity_type] += 1
                        else:
                            self.damaged_counter[entity.entity_type] += 1

                    else:
                        self.entity_counter[entity.entity_type] += 1
                    if entity.entity_type == et.RANGED_BASE or entity.entity_type == et.MELEE_BASE:
                        factory = {
                                      'entity_id':entity.id,
                                      'entity_type':entity.entity_type,
                                      'x': entity.position.x,
                                      'y': entity.position.y
                        }
                        self.my_attacker_factories.append(factory)
                    if entity.entity_type == et.RANGED_BASE:
                        self.ranged_base_count += 1
                    if entity.entity_type == et.MELEE_BASE:
                        self.melee_base_count += 1
                    if entity.entity_type == et.HOUSE:
                        if entity.position.y == 0:
                            self.complete_x[entity.position.x] = True
                        elif entity.position.x == 0:
                            self.complete_y[entity.position.y] = True
                    self.population_use += e_type.population_use
                    if entity.health == e_type.max_health:
                        self.population_provide += e_type.population_provide
                    if entity.entity_type == et.RANGED_UNIT or entity.entity_type == et.MELEE_UNIT:
                        self.my_attackers += 1
                    elif entity.entity_type == et.BUILDER_UNIT:
                        self.my_builders += 1
                        current_builder_distance = int(hypot(entity.position.x, entity.position.y))
                        if current_builder_distance > self.max_builder_distance:
                            self.max_builder_distance = current_builder_distance
                    if entity.entity_type == et.BUILDER_BASE:
                        #builder base init
                        if entity.id not in self.entity_actions.keys():
                            self.entity_actions[entity.id] = True
                        self.builder_base_id = entity.id

        self.tick['builders'] = pd.DataFrame(tick_builders, columns = ['entity_id', 'entity_type', 'x', 'y'])
        #self.tick['builders']['h'] = np.hypot(self.tick['builders'].x,self.tick['builders'].y).astype(int)
        #self.tick['builders'].sort_values(['h', 'entity_id'], ascending=True, inplace=True)

        entities = pd.DataFrame(entity_storage, columns=[
            'player_id',
            'entity_id',
            'entity_type',
            'x',
            'y',
            'zero_distance',
            'health_gap'
        ])

        resources = pd.DataFrame(resource_storage, columns=[
            'x',
            'y',
            'zero_distance'
        ])

        self.busy_field += self.fog_field
        if self.debug:
            for key in self.damaged_counter.keys():
                self.log.append(str(key) + 'damaged_counter' + str(self.damaged_counter[key]))
        return entities, resources

    def enemy_clusters(self, timer_start, timer_end, my_id, tick, entities):
        if self.my_attackers == 0:
            return
        # get max builder distance
        """mask = (entities.player_id == my_id) & (entities.entity_type == et.BUILDER_UNIT)
        builders = pd.DataFrame(entities[mask], columns = ['entity_id', 'x', 'y', 'zero_distance'])
        builders.sort_values(['zero_distance', 'entity_id'], ascending = False, inplace = True)
        if len(builders):
            self.max_builder_distance = int(builders['zero_distance'].head(1).values)
        else:
            self.max_builder_distance = 25"""

        if self.max_builder_distance < 25 or self.my_attackers < 10:
            self.max_builder_distance = 25

        new_centroids = pd.DataFrame([], columns=['x', 'y'])
        # near base enemy
        mask = (entities.player_id != my_id) & \
               (entities.zero_distance < 30) & ( \
                           (entities.entity_type == et.RANGED_UNIT) |
                           (entities.entity_type == et.MELEE_UNIT))
        enemy = entities[mask]
        if len(enemy):
            enemy = pd.DataFrame(enemy, columns=['x', 'y'])
            kmeans = KMeans(n_clusters=min([len(enemy), 1])).fit(enemy)
            new_centroids = pd.concat([
                new_centroids,
                pd.DataFrame(kmeans.cluster_centers_.astype(int), columns=['x', 'y'])
            ],
                axis=0)

        # enemy builders
        if self.my_attackers > 9:
            mask = (entities.player_id != my_id) & (entities.entity_type == et.BUILDER_UNIT)
            enemy = entities[mask]
            if len(enemy):
                enemy = pd.DataFrame(enemy, columns=['x', 'y'])
                kmeans = KMeans(n_clusters=min([len(enemy), 2])).fit(enemy)
                new_centroids = pd.concat([
                    new_centroids,
                    pd.DataFrame(kmeans.cluster_centers_.astype(int), columns = ['x','y'])
                ],
                    axis = 0)

        # enemy attackers
        mask = (entities.player_id != my_id) &\
               (entities.zero_distance < self.max_builder_distance + self.centroids_builders_range) & (\
               (entities.entity_type == et.RANGED_UNIT) |
               (entities.entity_type == et.MELEE_UNIT))

        enemy = entities[mask]
        if len(enemy):
            enemy = pd.DataFrame(enemy, columns=['x', 'y'])
            kmeans = KMeans(n_clusters=min([len(enemy), 2])).fit(enemy)
            new_centroids = pd.concat([
                new_centroids,
                pd.DataFrame(kmeans.cluster_centers_.astype(int), columns = ['x','y'])
            ],
                axis=0)


        if len(new_centroids):
            self.enemy_centroids = pd.DataFrame(new_centroids)

    def enemy_builder_clusters(self, my_id, entities):
        mask = (entities.player_id != my_id) & (entities.entity_type == et.BUILDER_UNIT)
        enemy = entities[mask]
        if len(enemy):
            enemy = pd.DataFrame(enemy, columns=['x', 'y'])
            kmeans = KMeans(n_clusters=min([len(enemy),10])).fit(enemy)
            enemy_builder_centroids = pd.DataFrame(kmeans.cluster_centers_.astype(int), columns = ['x','y'])



    def attack_action_v2(self, timer_start, timer_end, my_id, sight_range, entities, actions, map_size):
        if self.my_attackers == 0:
            return actions
        # get attackers
        mask = (entities['player_id'] == my_id) & \
               (
                       (entities['entity_type'] == et.MELEE_UNIT) |
                       (entities['entity_type'] == et.RANGED_UNIT)
               )
        units = pd.DataFrame(entities[mask], columns=['entity_id', 'x', 'y', 'entity_type'])
        units.columns = ['entity_id', 'ux', 'uy', 'entity_type']

        # enemy reclaimers spy++
        spy = pd.DataFrame(units)
        mask = (entities['player_id'] != my_id) & (entities['entity_type'] == et.BUILDER_UNIT)
        enemy_builders = pd.DataFrame(entities[mask], columns=['entity_id', 'x', 'y'])
        enemy_builders.columns = ['enemy_builder_id', 'ux', 'uy']
        enemy_builders.ux = (enemy_builders.ux / self.spy_distance).astype(int)
        enemy_builders.uy = (enemy_builders.uy / self.spy_distance).astype(int)
        spy.ux = (spy.ux / self.spy_distance).astype(int)
        spy.uy = (spy.uy / self.spy_distance).astype(int)
        spy = pd.merge(spy, enemy_builders, how='inner', on=['ux', 'uy'])
        # enemy reclaimers spy--

        i = 0
        for cx, cy in self.enemy_centroids.values:
            units['d' + str(i)] = np.hypot(units.ux - cx, units.uy - cy)
            i += 1

        busy = []
        unit_len = len(units)
        counter_len = len(self.enemy_centroids)
        unit_counter = 0
        current_centroid = 0
        units.sort_values(['d' + str(current_centroid),'entity_id'], ascending=True, inplace=True)
        for ex, ey in self.enemy_centroids.values:
            m, b, a, r = None, None, None, None

            a = model.attack_action.AttackAction(
                target=None,
                auto_attack=model.auto_attack.AutoAttack(
                    pathfind_range=sight_range,
                    valid_targets=[]
                )
            )
            a_spy = model.attack_action.AttackAction(
                target=None,
                auto_attack=model.auto_attack.AutoAttack(
                    pathfind_range=sight_range,
                    valid_targets=[et.BUILDER_UNIT]
                )
            )
            for index, row in units.iterrows():
                if not row.entity_id in busy:
                    if row.entity_id in spy.entity_id.values:
                        # spy
                        target = model.vec2_int.Vec2Int(ex, ey)
                        m = model.move_action.MoveAction(target, True, True)
                        actions[int(row.entity_id)] = model.EntityAction(m, b, a_spy, r)
                    else:
                        if row.entity_type == et.RANGED_UNIT:
                            new_ex = int(ex - self.melee_ranged_half_distance
                                         if ex - self.melee_ranged_half_distance > 0 else ex)
                            new_ey = int(ey - self.melee_ranged_half_distance
                                         if ey - self.melee_ranged_half_distance > 0 else ey)
                        else:
                            new_ex = int(ex + self.melee_ranged_half_distance
                                         if ex + self.melee_ranged_half_distance < map_size else ex)
                            new_ey = int(ey + self.melee_ranged_half_distance
                                         if ey + self.melee_ranged_half_distance < map_size else ey)
                        target = model.vec2_int.Vec2Int(new_ex, new_ey)
                        m = model.move_action.MoveAction(target, True, True)
                        #actions[int(row.entity_id)] = model.EntityAction(m, b, a, r)
                        actions[int(row.entity_id)] = model.EntityAction(m, b, a, r)

                    busy.append(row.entity_id)
                    unit_counter += 1
                    if unit_counter >= unit_len / counter_len:
                        unit_counter = 0
                        current_centroid += 1
                        units.sort_values(['d' + str(current_centroid - 1), 'entity_id'], ascending=True, inplace=True)
                        break

        return actions

    def reclaim_action(self, timer_start, timer_end, my_id, sight_range, map_size, entities, actions):
        mask = (entities['entity_type'] == et.BUILDER_UNIT) & \
               (entities['player_id'] == my_id)
        units = pd.DataFrame(entities[mask], columns=['entity_id'])
        if len(units):
            m, b, a, r = None, None, None, None
            a = model.attack_action.AttackAction(
                target=None,
                auto_attack=model.auto_attack.AutoAttack(
                    pathfind_range=sight_range,
                    valid_targets=[et.RESOURCE]
                )
            )
            for entity_id in units['entity_id']:
                if not entity_id in self.retreaters:
                    if random.randint(0, 1) == 0:
                        mx = random.randint(0, map_size - 1)
                        my = map_size - 1
                    else:
                        mx = map_size - 1
                        my = random.randint(0, map_size - 1)
                    target = model.vec2_int.Vec2Int(mx, my)
                    m = model.move_action.MoveAction(target, True, True)
                    actions[entity_id] = model.EntityAction(m, b, a, r)

        return actions

    def retreat_action(self, timer_start, timer_end, my_id, entities, actions):
        self.retreaters = {}
        mask = (entities['entity_type'] == et.BUILDER_UNIT) & \
               (entities['player_id'] == my_id)
        my_units = pd.DataFrame(entities[mask], columns=['entity_id', 'x', 'y'])
        my_units.columns = ['entity_id', 'ux', 'uy']
        my_units.ux = (my_units.ux / self.retreat_distance).astype(int)
        my_units.uy = (my_units.uy / self.retreat_distance).astype(int)
        mask = (entities['player_id'] != my_id) & ( \
                    (entities['entity_type'] == et.MELEE_UNIT) | \
                    (entities['entity_type'] == et.RANGED_UNIT) | \
                    (entities['entity_type'] == et.TURRET))
        enemy_attackers = pd.DataFrame(entities[mask], columns=['entity_id', 'x', 'y'])
        enemy_attackers.columns = ['enemy_attacker_id', 'ux', 'uy']
        enemy_attackers.ux = (enemy_attackers.ux / self.retreat_distance).astype(int)
        enemy_attackers.uy = (enemy_attackers.uy / self.retreat_distance).astype(int)
        my_units = pd.merge(my_units, enemy_attackers, how='inner', on=['ux', 'uy'])
        if len(my_units):
            m, b, a, r = None, None, None, None
            target = model.vec2_int.Vec2Int(13, 13)
            m = model.move_action.MoveAction(target, True, True)
            for entity_id in my_units['entity_id']:
                self.retreaters[entity_id] = True
                actions[entity_id] = model.EntityAction(m, b, a, r)

        return actions

    def repairers_action(self, timer_start, timer_end, my_id, entities, actions):
        mask = (entities['player_id'] == my_id) & ( \
                    (entities['entity_type'] == et.BUILDER_BASE) | \
                    (entities['entity_type'] == et.MELEE_BASE) | \
                    (entities['entity_type'] == et.RANGED_BASE) | \
                    (entities['entity_type'] == et.TURRET) | \
                    (entities['entity_type'] == et.HOUSE)) & \
               (entities['health_gap'] > 0)
        damaged = pd.DataFrame(entities[mask], columns=['entity_id', 'x', 'y', 'health_gap', 'entity_type'])
        damaged.columns = ['entity_id', 'dx', 'dy', 'health_gap', 'entity_type']
        damaged.sort_values(['health_gap', 'entity_id'], ascending=False, inplace=True)
        if len(damaged):
            # busy = []
            # self.tick['busy_builders'].append(int(entity_id))
            mask = (entities['player_id'] == my_id) & (entities['entity_type'] == et.BUILDER_UNIT)
            for building_id, dx, dy, health_gap, entity_type in damaged.values:
                repairers = pd.DataFrame(entities[mask], columns=['entity_id', 'x', 'y'])
                repairers.columns = ['entity_id', 'rx', 'ry']
                repairers['distance'] = np.hypot(repairers.rx - dx, repairers.ry - dy)
                #repairers['distance'] = (repairers.rx - dx) + (repairers.ry - dy)
                repairers.sort_values(['distance', 'entity_id'], ascending=True, inplace=True)
                repairers_count = 0
                for repairer_id, rx, ry, distance in repairers.values:
                    repairer_id = int(repairer_id)
                    #if not repairer_id in busy:
                    if not repairer_id in self.tick['busy_builders']:
                        m, b, a, r = None, None, None, None
                        target = model.vec2_int.Vec2Int(dx, dy)
                        r = model.repair_action.RepairAction(target=building_id)
                        m = model.move_action.MoveAction(target, True, True)
                        actions[repairer_id] = model.EntityAction(m, b, a, r)
                        # busy.append(repairer_id)
                        self.tick['busy_builders'].append(repairer_id)
                        repairers_count += 1
                        if entity_type in [et.RANGED_BASE, et.MELEE_BASE, et.BUILDER_BASE]:
                            if repairers_count >= 7:
                                break
                        elif entity_type in [et.HOUSE, et.TURRET]:
                            if repairers_count >= 4:
                                break
                        elif repairers_count >= 2:
                            break

        return actions

    def is_empty(self, x, y, size, entities, resources):

        mask = (entities['x'] >= x ) &\
               (entities['x'] < x + size) &\
               (entities['y'] >= y) &\
               (entities['y'] < y + size)
        entities_in_area = pd.DataFrame(entities[mask])
        if len(entities_in_area):
            return False

        mask = (resources['x'] >= x) & \
               (resources['x'] < x + size) & \
               (resources['y'] >= y) & \
               (resources['y'] < y + size)
        resources_in_area = pd.DataFrame(resources[mask])
        if len(resources_in_area):
            return False

        return True

    def new_citizen_fast_action(self, player_view, actions):

        for entity in player_view.entities:
            if entity.player_id == player_view.my_id and not entity.id in self.citizens:
                self.citizens[entity.id] = True
                if (entity.entity_type == et.RANGED_BASE or \
                        entity.entity_type == et.MELEE_BASE or \
                        entity.entity_type == et.BUILDER_BASE):
                    new_centroids = []
                    for centroid in self.enemy_centroids.values:
                        new_centroids.append([
                            centroid[0] + 10 if centroid[0] < entity.position.x + 10 else centroid[0],
                            centroid[1] + 10 if centroid[1] < entity.position.y + 10 else centroid[1]
                        ])
                    self.enemy_centroids = pd.DataFrame(new_centroids, columns=['x', 'y'])
                    self.bases[entity.entity_type] = {'x':entity.position.x, 'y':entity.position.y}
                elif not entity.id in self.retreaters:
                    actions[int(entity.id)] = self.default_action[entity.entity_type]
        return actions

    def reserve_place(self, entity_type):
        field = np.array(self.busy_field)
        place_size = self.sizes[entity_type] + 2
        rx, ry = -1, -1
        # numpy indexes comparing
        i, j = np.where(field == 0)
        if len(i) > 0 and len(j) > 0:
            mx = max(i)
            my = max(j)
            target_hypot = self.map_size * self.map_size
            for tx in range(0, mx - place_size):
                for ty in range(0, my - place_size):
                    if field[tx:tx + place_size, ty:ty + place_size].sum() == 0:
                        hp = hypot(tx, ty)
                        if hp < target_hypot:
                            target_hypot = hp
                            rx = int(tx)
                            ry = int(ty)
            for x in range(rx, place_size):
                for y in range(rx, place_size):
                    self.busy_field[x, y] = 1
        return rx, ry

    def add_to_plan(self, builder_type, target_type, initial_cost):
        if self.plan_addiction_available(target_type):
            x, y = -1, -1
            if builder_type in [et.BUILDER_BASE, et.MELEE_BASE, et.RANGED_BASE]:
                x = self.bases[builder_type]['x']
                y = self.bases[builder_type]['y']
            else:
                x, y = self.reserve_place(target_type)
            if x > -1 and y > -1:
                if target_type in [et.BUILDER_UNIT, et.RANGED_UNIT, et.MELEE_UNIT]:
                    population = 1
                else:
                    population = 0
                self.build_plan.append({
                    'entity_type': target_type,
                    'init_type': builder_type,
                    'initial_cost': initial_cost,
                    'x': x,
                    'y': y,
                    'population': population,
                    'tick': self.current_tick
                })
                return initial_cost
        return 0

    def count_in_plan(self, entity_type):
        count = 0
        for task in self.build_plan:
            if task['entity_type'] == entity_type:
                count += 1
        return count

    def plan_addiction_available(self, entity_type):
        current_tick = max(self.history.keys()) if len(self.history) else 0
        if current_tick == 0:
            return True
        if entity_type in [et.RANGED_BASE, et.MELEE_BASE, et.BUILDER_BASE] and \
                self.damaged_counter[entity_type] > 0:
            return False
        if entity_type in [et.HOUSE, et.TURRET] and \
            self.damaged_counter[entity_type] > 2:
            return False
        if self.count_in_plan(entity_type) == 0:
            return True
        if not entity_type in self.history[list(self.history.keys())[-2]]['entity_counter']:
            return True
        if self.history[list(self.history.keys())[-2]]['entity_counter'][entity_type] < \
                self.history[current_tick]['entity_counter'][entity_type]:
            return True
        return False


    def make_build_plan(self, current_tick):
        # pop builded
        if len(self.history) > 1:
            current_tick = max(self.history.keys())
            for entity_type in self.history[current_tick]['entity_counter'].keys():
                current_count = self.history[current_tick]['entity_counter'][entity_type]
                prev_count = self.history[list(self.history.keys())[-2]]['entity_counter'][entity_type]
                if current_count - prev_count:
                    self.build_plan_pop(entity_type)
        # pop old
        # 'tick': self.current_tick
        for task in self.build_plan:
            if self.current_tick > task['tick'] + 20:
                self.build_plan_pop(task['entity_type'])

        population_plan = 0
        for task in self.build_plan:
            population_plan += task['population']
        resource = self.tick['resource']
        population = self.population_provide - self.population_use - population_plan
        counter = 0

        if self.entity_counter[et.RANGED_BASE] == 0 and \
                resource >= 500 and \
                self.count_in_plan(et.RANGED_BASE) == 0:
            resource -= self.add_to_plan(et.BUILDER_UNIT, et.RANGED_BASE, 500)

        if self.entity_counter[et.MELEE_BASE] == 0 and \
                resource >= 500 and \
                self.entity_counter[et.RANGED_BASE] > 0 and \
                self.count_in_plan(et.MELEE_BASE) == 0:
            resource -= self.add_to_plan(et.BUILDER_UNIT, et.MELEE_BASE, 500)

        if self.entity_counter[et.BUILDER_BASE] == 0 and \
                resource >= 500 and \
                self.count_in_plan(et.BUILDER_BASE) == 0:
            resource -= self.add_to_plan(et.BUILDER_UNIT, et.BUILDER_BASE, 500)

        if not (self.entity_counter[et.HOUSE] > 3 and self.entity_counter[et.RANGED_BASE] == 0):
            while resource >= 50:
                if self.population_use > self.population_provide - 10 and \
                    self.count_in_plan(et.HOUSE) == 0:
                    resource -= self.add_to_plan(et.BUILDER_UNIT, et.HOUSE, 50)
                counter += 1
                if counter >= 3:
                    break

        if self.population_use < self.population_provide:

            if resource >= 30 + self.entity_counter[et.RANGED_UNIT] and \
                    self.entity_counter[et.RANGED_BASE] > 0 and \
                    population > 0 and \
                    self.count_in_plan(et.RANGED_UNIT) == 0:
                resource -= self.add_to_plan(
                    et.RANGED_BASE,
                    et.RANGED_UNIT,
                    30 + self.entity_counter[et.RANGED_UNIT]
                )
                population -= 1

            if resource >= 20 + self.entity_counter[et.MELEE_UNIT] and \
                    self.entity_counter[et.MELEE_BASE] > 0 and \
                    population > 0 and \
                    self.count_in_plan(et.MELEE_UNIT) == 0:
                resource -= self.add_to_plan(
                    et.MELEE_BASE,
                    et.MELEE_UNIT,
                    20 + self.entity_counter[et.MELEE_UNIT]
                )
                population -= 1

            if resource >= 10 + self.entity_counter[et.BUILDER_UNIT] and \
                    self.entity_counter[et.BUILDER_BASE] > 0 and \
                    population > 0 and \
                    self.entity_counter[et.BUILDER_UNIT] < 61 and \
                    self.count_in_plan(et.BUILDER_UNIT) == 0:
                resource -= self.add_to_plan(
                    et.BUILDER_BASE,
                    et.BUILDER_UNIT,
                    10 + self.entity_counter[et.BUILDER_UNIT]
                )
                population -= 1
            """elif self.debug:
                self.log.append('resource: '+str(resource))
                self.log.append('self.entity_counter[et.BUILDER_UNIT]: ' + str(self.entity_counter[et.BUILDER_UNIT]))
                self.log.append('self.entity_counter[et.BUILDER_BASE]: ' + str(self.entity_counter[et.BUILDER_BASE]))
                self.log.append('population: ' + str(population))
                self.log.append('self.entity_counter[et.BUILDER_UNIT]: ' + str(self.entity_counter[et.BUILDER_UNIT]))
                self.log.append('self.count_in_plan(et.BUILDER_UNIT): ' + str(self.count_in_plan(et.BUILDER_UNIT)))"""

        if self.entity_counter[et.HOUSE] > 4 and self.entity_counter[et.RANGED_BASE] > 0:
            counter = 0
            while resource >= 50:
                if self.entity_counter[et.TURRET] < self.entity_counter[et.HOUSE] * 0.5 and \
                        resource >= 50 and \
                        self.count_in_plan(et.TURRET) == 0:
                    resource -= self.add_to_plan(et.BUILDER_UNIT, et.TURRET, 50)
                counter += 1
                if counter > 2:
                    break

        if self.debug:
            self.tick['build_plan'] = []
            for task in self.build_plan:
                self.tick['build_plan'].append({
                    'entity_type': task['entity_type'],
                    'x': task['x'],
                    'y': task['y']
                })

    def dozer_v2(self, actions):

        if len(self.build_plan) == 0:
            return actions

        # disable factories
        """mask = (self.tick['builders'].entity_type == et.BUILDER_BASE) | \
               (self.tick['builders'].entity_type == et.RANGED_BASE) | \
               (self.tick['builders'].entity_type == et.MELEE_BASE)
        for entity_id, entity_type, x, y in self.tick['builders'][mask].values:
            actions[int(entity_id)] = self.default_action['do_nothing']
            pass"""
        for entity_id in self.my_factories:
            actions[int(entity_id)] = self.default_action['do_nothing']
            #self.tick['busy_builders'].append(int(entity_id))

        # serve tasks
        #busy_builders = {}
        for task in self.build_plan:
            df = pd.DataFrame(self.tick['builders'][self.tick['builders'].entity_type == task['init_type']])
            df['h'] = np.hypot(task['x'] - df.x, task['y'] - df.y)
            df.sort_values(['h', 'entity_id'], ascending=True, inplace=True)
            for entity_id, entity_type, x, y , h in df.values:
                #if not entity_id in busy_builders:
                if not entity_id in self.tick['busy_builders']:
                    m, b, a, r = None, None, None, None
                    if task['entity_type'] in [et.BUILDER_UNIT, et.MELEE_UNIT, et.RANGED_UNIT]:
                        b = model.build_action.BuildAction(
                            task['entity_type'],
                            model.vec2_int.Vec2Int(
                                int(x + self.sizes[entity_type]),
                                int(y + self.sizes[entity_type] - 1),
                            )
                        )
                    else:
                        x = task['x']
                        y = task['y']
                        m = model.move_action.MoveAction(
                            model.vec2_int.Vec2Int(x + 1, y),
                            True,
                            True
                        )
                        b = model.build_action.BuildAction(
                            task['entity_type'],
                            model.vec2_int.Vec2Int(
                                int(x + 1),
                                int(y + 1)
                            )
                        )

                    actions[int(entity_id)] = model.EntityAction(m, b, a, r)
                    self.tick['busy_builders'].append(int(entity_id))
                    if self.debug:
                        self.tick['build_tasks'][int(entity_id)] = task
                        self.tick['build_targets'][int(entity_id)] = [x + 1, y]

                    # busy_builders[int(entity_id)] = True
                    # self.build_plan_pop(task)
                    break
        return actions

    def build_plan_pop(self, entity_type):
        # print(self.current_tick, 'pop', entity_type)
        for i in range(0,len(self.build_plan)):
            if self.build_plan[i]['entity_type'] == entity_type:
                self.build_plan.pop(i)
                break

    def get_action(self, player_view, debug_interface):
        tick_timer_start = datetime.datetime.now()
        timer_start = {}
        timer_end = {}
        actions = {}

        # new citizen fast action
        if self.debug:
            timer_start['new_citizen_fast_action'] = datetime.datetime.now()
        actions = self.new_citizen_fast_action(player_view, actions)
        if self.debug:
            timer_end['new_citizen_fast_action'] = datetime.datetime.now()

        # init: parse player_view
        if self.debug:
            timer_start['init_entities'] = datetime.datetime.now()
        my_id = player_view.my_id
        if player_view.current_tick % self.dynamic_period == 0 or \
                player_view.current_tick % self.silent_period == 0:
            self.entities, self.resources = self.init_entities(timer_start, timer_end, player_view)
            entities, resources = self.entities, self.resources
        if self.debug:
            timer_end['init_entities'] = datetime.datetime.now()

        # define near enemy clusters
        if self.debug:
            timer_start['enemy_clusters'] = datetime.datetime.now()
        if player_view.current_tick % self.silent_period == 0:
            self.enemy_clusters(timer_start, timer_end, my_id, player_view.current_tick, entities)
        if self.debug:
            timer_end['enemy_clusters'] = datetime.datetime.now()

        # attack actions
        if self.debug:
            timer_start['attack_action_v2'] = datetime.datetime.now()
        if player_view.current_tick % self.silent_period == 0:
            properties = player_view.entity_properties[et.MELEE_UNIT]
            sight_range= properties.sight_range
            actions = self.attack_action_v2(
                timer_start,
                timer_end,
                my_id,
                sight_range,
                entities,
                actions,
                player_view.map_size
            )
        if self.debug:
            timer_end['attack_action_v2'] = datetime.datetime.now()

        # reclaim
        if self.debug:
            timer_start['reclaim_action'] = datetime.datetime.now()
        if player_view.current_tick % self.silent_period == 0:
            properties = player_view.entity_properties[et.BUILDER_UNIT]
            sight_range = properties.sight_range
            actions = self.reclaim_action(
                timer_start,
                timer_end,
                my_id,
                sight_range,
                player_view.map_size,
                entities,
                actions
            )
        if self.debug:
            timer_end['reclaim_action'] = datetime.datetime.now()

        # retreat
        if self.debug:
            timer_start['retreat_action'] = datetime.datetime.now()
        if player_view.current_tick % self.silent_period == 0:
            actions = self.retreat_action(timer_start,timer_end,my_id, entities, actions)
        if self.debug:
            timer_end['retreat_action'] = datetime.datetime.now()

        # make build plan
        if self.debug:
            timer_start['make_build_plan'] = datetime.datetime.now()
        if player_view.current_tick % self.dynamic_period == 0 or \
                player_view.current_tick % self.silent_period == 0:
            self.make_build_plan(player_view.current_tick)
        if self.debug:
            timer_end['make_build_plan'] = datetime.datetime.now()

        # dozer_v2
        if self.debug:
            timer_start['dozer_v2'] = datetime.datetime.now()
        if player_view.current_tick % self.dynamic_period == 0 or \
                player_view.current_tick % self.silent_period == 0:
            actions = self.dozer_v2(actions)
        if self.debug:
            timer_end['dozer_v2'] = datetime.datetime.now()

        # repair actions
        if self.debug:
            timer_start['repairers_action'] = datetime.datetime.now()
        if (self.current_tick <500 and player_view.current_tick % self.dynamic_period == 0) or \
                player_view.current_tick % self.silent_period == 0:
            actions = self.repairers_action(timer_start, timer_end, my_id, entities, actions)
        if self.debug:
            timer_end['repairers_action'] = datetime.datetime.now()

        # debug area
        """ if self.debug:
            # if player_view.current_tick % self.silent_period == 0:
            self.time_report['tick'].append(player_view.current_tick)
            for key in timer_start.keys():
                if not key in self.time_report.keys():
                    self.time_report[key] = []
                self.time_report[key].append((timer_end[key] - timer_start[key]).microseconds / 1000)
        
            if player_view.current_tick == 500:
                pickle.dump(self.time_report, file=open('time_report_' + str(player_view.my_id) + '.dat', 'wb'))
                print('log saved')"""
        self.time_spent += (datetime.datetime.now() - tick_timer_start).microseconds / 1000
        mid_tick_time = 0
        if self.current_tick > 10:
            mid_tick_time = self.time_spent / self.current_tick
            if self.time_spent + ((1000-self.current_tick) * mid_tick_time / self.dynamic_period) > 39000:
                self.dynamic_period += 1
            elif self.time_spent + ((1000 - self.current_tick) * mid_tick_time / self.dynamic_period) < \
                    38000 and self.dynamic_period > 1:
                self.dynamic_period -= 1
            if self.dynamic_period > self.silent_period:
                self.silent_period = self.dynamic_period
        """if self.debug:
            self.log.append('timer ' + str(self.time_spent))
            self.log.append('dynamic_period ' + str(self.dynamic_period))
            self.log.append('mid_tick_time ' + str(mid_tick_time))"""
        return model.Action(actions)

    def debug_triangle(self, debug_interface, color, x, y):
        screen_offset = model.Vec2Float(0, 0)
        debug_interface.send(
            model.DebugCommand.Add(
                model.DebugData.Primitives(
                    [
                        model.ColoredVertex(model.Vec2Float(x, y), screen_offset, color),
                        model.ColoredVertex(model.Vec2Float(x + 1, y), screen_offset, color),
                        model.ColoredVertex(model.Vec2Float(x + 1, y + 1), screen_offset, color),
                    ],
                    model.PrimitiveType.TRIANGLES
                )
            )
        )

    def debug_log(self, debug_interface, text):
        debug_interface.send(
            model.DebugCommand.Add(
                model.DebugData.Log(text)
            )
        )

    def debug_update(self, player_view, debug_interface):
        debug_interface.send(model.DebugCommand.Clear())
        debug_interface.get_state()
        if self.debug:
            for entity in player_view.entities:
                if int(entity.id) in self.tick['build_tasks'].keys():
                    x = entity.position.x
                    y = entity.position.y
                    #color = None
                    if self.tick['build_tasks'][entity.id] == et.BUILDER_UNIT:
                        color = model.Color(0, 255, 0, 0.5)
                    elif self.tick['build_tasks'][entity.id] == et.RANGED_UNIT:
                        color = model.Color(255, 0, 0, 0.5)
                    elif self.tick['build_tasks'][entity.id] == et.MELEE_UNIT:
                        color = model.Color(0, 0, 255, 0.5)
                    else:
                        color = model.Color(255, 255, 255, 0.5)
                    self.debug_triangle(debug_interface, color, x, y)
                    self.debug_triangle(
                        debug_interface,
                        color,
                        self.tick['build_targets'][int(entity.id)][0],
                        self.tick['build_targets'][int(entity.id)][1]
                    )
            for x, y in self.enemy_centroids.values:
                color = model.Color(255, 255, 255, 0.5)
                self.debug_triangle(debug_interface, color, x, y)
            for task in self.tick['build_plan']:
                self.debug_log(
                    debug_interface,
                    str(task['entity_type']) + ' x:' + str(task['x']) + ' y:' + str(task['y'])
                )
            for log_record in self.log:
                self.debug_log(debug_interface, log_record)
