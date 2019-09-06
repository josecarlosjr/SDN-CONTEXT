#-*- coding: utf-8 -*-

from ryu.base import app_manager
from ryu.controller import mac_to_port, ofp_event
from ryu.controller.handler import CONFIG_DISPATCHER, MAIN_DISPATCHER, DEAD_DISPATCHER, set_ev_cls
from ryu.ofproto import ofproto_v1_4
from ryu.ofproto import ofproto_v1_4_parser
from ryu.lib.mac import haddr_to_bin
from ryu.lib.packet import packet, arp, ethernet, ipv4, ipv6, ether_types, icmp
from ryu.lib import mac, ip, hub
from ryu.topology.api import get_switch, get_link, get_all_link, get_all_switch
from ryu.app.wsgi import ControllerBase
from ryu.topology import event, switches
from termcolor import colored
from collections import defaultdict
from operator import itemgetter
from operator import attrgetter
import os
import random
import time, copy


from datetime import datetime
import pandas as pd


#MAX_PATHS = 2

IP_1 = '192.168.1.1'
IP_2 = '192.168.2.2'
IP_3 = '192.168.3.3'
IP_4 = '192.168.4.4'

IP = ['192.168.1.1','192.168.2.2','192.168.3.3','192.168.4.4']

MAX_BAND = 800 #Mbps

adjacency = defaultdict(lambda: defaultdict(lambda: None))

####################################
class ProjectController(app_manager.RyuApp):    
    OFP_VERSIONS = [ofproto_v1_4.OFP_VERSION]
    
    #ADICIONADO 26/09/2018 variavel global
    ################################
    global dp, C, c, b, src, dst, first_port, last_port, out_ports, PL, PL1_3#, ipDFrame_src, arpDFrame_src, ipDFrame_dst, arpDFrame_dst 

    #######################################################################################################################
    #Variaveis globais para calculo de banda
    #DP 1
    global band_1_1, result_1_1, band_rx_1_1, result_rx_1_1, tx_ini_1_1, tx_fin_1_1, rx_ini_1_1, rx_fin_1_1 #dp 1 port 1
    global band_1_2, result_1_2, band_rx_1_2, result_rx_1_2, tx_ini_1_2, tx_fin_1_2, rx_ini_1_2, rx_fin_1_2 #dp 1 port 2
    global band_1_3, result_1_3, band_rx_1_3, result_rx_1_3, tx_ini_1_3, tx_fin_1_3, rx_ini_1_3, rx_fin_1_3 #dp 1 port 3
    global tx_1_2_packet, tx_1_3_packet, rx_1_2_packet, rx_1_3_packet, L1_2, L1_3
    #DP 2
    global band_2_1, result_2_1, band_rx_2_1, result_rx_2_1, tx_ini_2_1, tx_fin_2_1, rx_ini_2_1, rx_fin_2_1 #dp 2 port 1
    global band_2_2, result_2_2, band_rx_2_2, result_rx_2_2, tx_ini_2_2, tx_fin_2_2, rx_ini_2_2, rx_fin_2_2 #dp 2 port 2
    global band_2_3, result_2_3, band_rx_2_3, result_rx_2_3, tx_ini_2_3, tx_fin_2_3, rx_ini_2_3, rx_fin_2_3 #dp 2 port 3
    global tx_2_2_packet, tx_2_3_packet, rx_2_2_packet, rx_2_3_packet, L2_2, L2_3
    #DP 3
    global band_3_1, result_3_1, band_rx_3_1, result_rx_3_1, tx_ini_3_1, tx_fin_3_1, rx_ini_3_1, rx_fin_3_1 #dp 3 port 1
    global band_3_2, result_3_2, band_rx_3_2, result_rx_3_2, tx_ini_3_2, tx_fin_3_2, rx_ini_3_2, rx_fin_3_2 #dp 3 port 2
    global band_3_3, result_3_3, band_rx_3_3, result_rx_3_3, tx_ini_3_3, tx_fin_3_3, rx_ini_3_3, rx_fin_3_3 #dp 3 port 3
    global tx_3_2_packet, tx_3_3_packet, rx_3_2_packet, rx_3_3_packet, L3_2, L3_3
    #DP 4
    global band_4_1, result_4_1, band_rx_4_1, result_rx_4_1, tx_ini_4_1, tx_fin_4_1, rx_ini_4_1, rx_fin_4_1 #dp 4 port 1
    global band_4_2, result_4_2, band_rx_4_2, result_rx_4_2, tx_ini_4_2, tx_fin_4_2, rx_ini_4_2, rx_fin_4_2 #dp 4 port 2
    global band_4_3, result_4_3, band_rx_4_3, result_rx_4_3, tx_ini_4_3, tx_fin_4_3, rx_ini_4_3, rx_fin_4_3 #dp 4 port 3
    global tx_4_2_packet, tx_4_3_packet, rx_4_2_packet, rx_4_3_packet, L4_2, L4_3
    ########################################################################################################################
    
    #inicializando variáveis globais
    C = c = b = out_ports = PL = PL1_3 = 0
    #ipDFrame_src = pd.DataFrame([]) 
    #DP 1
    band_1_1 = result_1_1 = band_rx_1_1 = result_rx_1_1 = tx_ini_1_1 = tx_fin_1_1 = rx_ini_1_1 = rx_fin_1_1 = 0 #dp 1 port 1
    band_1_2 = result_1_2 = band_rx_1_2 = result_rx_1_2 = tx_ini_1_2 = tx_fin_1_2 = rx_ini_1_2 = rx_fin_1_2 = 0 #dp 1 port 2
    band_1_3 = result_1_3 = band_rx_1_3 = result_rx_1_3 = tx_ini_1_3 = tx_fin_1_3 = rx_ini_1_3 = rx_fin_1_3 = 0 #dp 1 port 3
    tx_1_2_packet = tx_1_3_packet = rx_1_2_packet = rx_1_3_packet = L1_2 = L1_3 = 0
    #DP 2
    band_2_1 = result_2_1 = band_rx_2_1 = result_rx_2_1 = tx_ini_2_1 = tx_fin_2_1 = rx_ini_2_1 = rx_fin_2_1 = 0 #dp 2 port 1
    band_2_2 = result_2_2 = band_rx_2_2 = result_rx_2_2 = tx_ini_2_2 = tx_fin_2_2 = rx_ini_2_2 = rx_fin_2_2 = 0 #dp 2 port 2
    band_2_3 = result_2_3 = band_rx_2_3 = result_rx_2_3 = tx_ini_2_3 = tx_fin_2_3 = rx_ini_2_3 = rx_fin_2_3 = 0 #dp 2 port 2
    tx_2_2_packet = tx_2_3_packet = rx_2_2_packet = rx_2_3_packet = L2_2 = L2_3 = 0
    #DP3
    band_3_1 = result_3_1 = band_rx_3_1 = result_rx_3_1 = tx_ini_3_1 = tx_fin_3_1 = rx_ini_3_1 = rx_fin_3_1 = 0 #dp 3 port 1
    band_3_2 = result_3_2 = band_rx_3_2 = result_rx_3_2 = tx_ini_3_2 = tx_fin_3_2 = rx_ini_3_2 = rx_fin_3_2 = 0 #dp 3 port 2
    band_3_3 = result_3_3 = band_rx_3_3 = result_rx_3_3 = tx_ini_3_3 = tx_fin_3_3 = rx_ini_3_3 = rx_fin_3_3 = 0 #dp 3 port 3
    tx_3_2_packet = tx_3_3_packet = rx_3_2_packet = rx_3_3_packet = L3_2 = L3_3 = 0
    #DP4
    band_4_1 = result_4_1 = band_rx_4_1 = result_rx_4_1 = tx_ini_4_1 = tx_fin_4_1 = rx_ini_4_1 = rx_fin_4_1 = 0 #dp 4 port 1
    band_4_2 = result_4_2 = band_rx_4_2 = result_rx_4_2 = tx_ini_4_2 = tx_fin_4_2 = rx_ini_4_2 = rx_fin_4_2 = 0 #dp 4 port 2
    band_4_3 = result_4_3 = band_rx_4_3 = result_rx_4_3 = tx_ini_4_3 = tx_fin_4_3 = rx_ini_4_3 = rx_fin_4_3 = 0 #dp 4 port 3
    tx_4_2_packet = tx_4_3_packet = rx_4_2_packet = rx_4_3_packet = L4_2 = L4_3 = 0
    

    def __init__(self, *args, **kwargs):
        super(ProjectController, self).__init__(*args, **kwargs)
        #self.mac_to_port = {}
        self.ipDFrame_src = self.arpDFrame_src = self.ipDFrame_dst = self.arpDFrame_dst = pd.DataFrame([])
        self.topology_api_app = self
        self.datapath_list = {}
        self.arp_table = {}
        self.switches = []
        self.hosts = {}
        self.multipath_group_ids = {}
        self.group_ids = []
        self.adjacency = defaultdict(dict)
        #ADICIONADO 22/09/2018
        ##################################################
        self.monitor_thread = hub.spawn(self._monitor)
        self.eventos = []
        ##################################################
        
    ######################################################
    #Algoritmo Depth First Search
    def get_paths(self, src, dst):
        '''
        Get all paths from src to dst using DFS (Depth First Search) algorithm    
        '''
        
        if src == dst:
            # host target is on the same switch
            return [[src]]
        paths = []
        stack = [(src, [src])]
        while stack:
            (node, path) = stack.pop()
            for next in set(self.adjacency[node].keys()) - set(path):
                if next is dst:
                    paths.append(path + [next])
                else:
                    stack.append((next, path + [next]))
        return paths
    #####################################################
    

    def add_ports_to_paths(self, paths, first_port, last_port):
        '''
        Add the ports that connects the switches for all paths
        '''
        #print ("add port to path is called")
        paths_p = []
        for path in paths:
            p = {}
            in_port = first_port
            for s1, s2 in zip(path[:-1], path[1:]):
                out_port = self.adjacency[s1][s2]
                p[s1] = (in_port, out_port)
                in_port = self.adjacency[s2][s1]
            p[path[-1]] = (in_port, last_port)
            paths_p.append(p)
        #print "add_port_to_path", paths_p
        return paths_p

    ##########################################################
    def install_paths(self, src, first_port, dst, last_port, ip_src, eth_src, ip_dst, eth_dst):
        computation_start = time.time()
        #paths = self.get_optimal_paths(src, dst)
         
        paths = self.get_paths(src, dst)
        
        paths_with_ports = self.add_ports_to_paths(paths, first_port, last_port)
        switches_in_paths = set().union(*paths)

        for node in switches_in_paths:

            dp = self.datapath_list[node]
            ofp = dp.ofproto
            ofp_parser = dp.ofproto_parser

            ports = defaultdict(list)
            actions = []
            i = 0

            for path in paths_with_ports:
                if node in path:
                    in_port = path[node][0]
                    out_port = path[node][1]
                    if (out_port) not in ports[in_port]:
                        ports[in_port].append((out_port))
                i += 1

            for in_port in ports:
                match_ip = ofp_parser.OFPMatch(
                        eth_type=0x0800, 
                        ipv4_src=ip_src,
                        ipv4_dst=ip_dst
                #        eth_dst=eth_dst
                        )
                match_arp = ofp_parser.OFPMatch(
                        eth_type=0x0806, 
                        arp_spa=ip_src,
                        arp_tpa=ip_dst
                #        eth_dst=eth_dst
                        )

                out_ports = ports[in_port]

                #elif len(out_ports) == 1:
                #print "datapath tive apenas 1 caminho:"
                
                actions = [ofp_parser.OFPActionOutput(out_ports[0])]
                self.add_flow(dp, 32766, match_ip, actions)
                self.add_flow(dp, 1, match_arp, actions)

        return paths_with_ports[0][src][1]
    ############################################################

    def add_flow(self, datapath, priority, match, actions, buffer_id=None):
        # print "Adding flow ", match, actions
        ofproto = datapath.ofproto
        parser = datapath.ofproto_parser

        inst = [parser.OFPInstructionActions(ofproto.OFPIT_APPLY_ACTIONS,
                                             actions)]
        if buffer_id:
            mod = parser.OFPFlowMod(datapath=datapath, buffer_id=buffer_id,
                                    priority=priority, match=match,
                                    instructions=inst)
        else:
            mod = parser.OFPFlowMod(datapath=datapath, priority=priority,
                                    match=match, instructions=inst)
        datapath.send_msg(mod)

    @set_ev_cls(ofp_event.EventOFPSwitchFeatures, CONFIG_DISPATCHER)
    def _switch_features_handler(self, ev):
        global dp

        #print "switch_features_handler is called"
        datapath = ev.msg.datapath
        #dp = ev.msg.datapath
        
        ofproto = datapath.ofproto
        parser = datapath.ofproto_parser

        match = parser.OFPMatch()
        actions = [parser.OFPActionOutput(ofproto.OFPP_CONTROLLER,
                                          ofproto.OFPCML_NO_BUFFER)]
        self.add_flow(datapath, 0, match, actions)

    #@set_ev_cls(ofp_event.EventOFPPortDescStatsReply, MAIN_DISPATCHER)
    #def port_desc_stats_reply_handler(self, ev):
    #    switch = ev.msg.datapath
    #    for p in ev.msg.body:
    #        self.bandwidths[switch.id][p.port_no] = p.curr_speed
    
    
    
