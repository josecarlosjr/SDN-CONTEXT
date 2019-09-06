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
    
    @set_ev_cls(ofp_event.EventOFPPacketIn, MAIN_DISPATCHER)
    def _packet_in_handler(self, ev):
        msg = ev.msg 
        datapath = msg.datapath
        ofproto = datapath.ofproto
        parser = datapath.ofproto_parser
        in_port = msg.match['in_port']
        pkt = packet.Packet(data=msg.data)
        eth = pkt.get_protocol(ethernet.ethernet)
        arp_pkt = pkt.get_protocol(arp.arp)
        pkt_icmp = pkt.get_protocol(icmp.icmp)
        
        #evita broadcast from LLDP
        if eth.ethertype == 35020:
            return

        if pkt.get_protocol(ipv6.ipv6):  # Drop the IPV6 Packets.
            match = parser.OFPMatch(eth_type=eth.ethertype)
            actions = []
            self.add_flow(datapath, 1, match, actions)
            return None

        dst = eth.dst
        src = eth.src
        dpid = datapath.id

        if src not in self.hosts:
            self.hosts[src] = (dpid, in_port)
        #print src
        #print dst

        out_port = ofproto.OFPP_FLOOD
        
        if arp_pkt:
            src_ip = arp_pkt.src_ip
            dst_ip = arp_pkt.dst_ip
            if arp_pkt.opcode == arp.ARP_REPLY:
                self.arp_table[src_ip] = src
                print colored('ARP_REPLY','blue')
                h1 = self.hosts[src]
                h2 = self.hosts[dst]
                #chama o self.install_path primeiro
                out_port = self.install_paths(h1[0], h1[1], h2[0], h2[1], src_ip, src, dst_ip, dst)
                self.install_paths(h2[0], h2[1], h1[0], h1[1], dst_ip, dst, src_ip, src) # reverse
            elif arp_pkt.opcode == arp.ARP_REQUEST:
                print colored('ARP_REQUEST','blue')
                if dst_ip in self.arp_table:
                    self.arp_table[src_ip] = src
                    dst_mac = self.arp_table[dst_ip]
                    h1 = self.hosts[src]
                    h2 = self.hosts[dst_mac]
                    out_port = self.install_paths(h1[0], h1[1], h2[0], h2[1], src_ip, src, dst_ip, dst)
                    self.install_paths(h2[0], h2[1], h1[0], h1[1], dst_ip, dst, src_ip, src) # reverse
        
        actions = [parser.OFPActionOutput(out_port)]

        data = None
        if msg.buffer_id == ofproto.OFP_NO_BUFFER:
            data = msg.data

        out = parser.OFPPacketOut(
            datapath=datapath, buffer_id=msg.buffer_id, in_port=in_port,
            actions=actions, data=data)
        datapath.send_msg(out)
        
        @set_ev_cls(event.EventSwitchEnter)
    def switch_enter_handler(self, ev):
       #print "switch enter handler"
        switch = ev.switch.dp
        ofp_parser = switch.ofproto_parser

        if switch.id not in self.switches:
            self.switches.append(switch.id)
            self.datapath_list[switch.id] = switch

            # Request port/link descriptions, useful for obtaining bandwidth
            req = ofp_parser.OFPPortDescStatsRequest(switch)
            #print req
            switch.send_msg(req)

    @set_ev_cls(event.EventSwitchLeave, MAIN_DISPATCHER)
    def switch_leave_handler(self, ev):
        #print ("Switch leave handler", ev)
        switch = ev.switch.dp.id
        if switch in self.switches:
            self.switches.remove(switch)
            del self.datapath_list[switch]
            del self.adjacency[switch]

    @set_ev_cls(event.EventLinkAdd, MAIN_DISPATCHER)
    def link_add_handler(self, ev):
        global src, dst, ipDFrame_src, arpDFrame_src, ipDFrame_dst, arpDFrame_dst
        s1 = ev.link.src
        s2 = ev.link.dst
        
        print '\033[1;34;47m Link Switch', s1.dpid, 'Porta', s1.port_no, 'Up\033[1;m'
        self.adjacency[s1.dpid][s2.dpid] = s1.port_no
        self.adjacency[s2.dpid][s1.dpid] = s2.port_no
        
        #Variaveis globais sem valores try/except para tratar o erro de NameError or KeyError
        #pq ao iniciar o experimento  é acionada o evento de adicao de link entre switches event.EventLinkAdd
        #
        ##########################################################
        try:
            #SRC
            ofp_src = src.ofproto
            ofp_parser_src = src.ofproto_parser
            buffer_id_src = ofp_src.OFP_NO_BUFFER
            #DST
            ofp_dst = dst.ofproto
            ofp_parser_dst = dst.ofproto_parser
            buffer_id_dst = ofp_dst.OFP_NO_BUFFER
            
            #print self.ipDFrame_src.at[i,'DST']
            #print
            #print self.ipDFrame_src.loc[1], '\n'
            #print self.ipDFrame_src
            #print
            #DST = self.ipDFrame_src.loc["DST"]
            #print self.ipDFrame_src.iloc[[0],[0]]
            if s1.dpid == src.id:
                i=0 
                for row in self.ipDFrame_src.iterrows():               
                    match = ofp_parser_src.OFPMatch(eth_type=0x800, ipv4_dst=str(self.ipDFrame_src.at[i,'DST']),
                            ipv4_src=str(self.ipDFrame_src.at[i,'SRC']))
                    actions = [ofp_parser_src.OFPActionOutput(self.ipDFrame_src.at[i,'PORT'])]
                    self.add_flow(src, 32768, match, actions)
                    i += 1
                i=0
                for row in self.arpDFrame_src.iterrows():
                    match = ofp_parser_src.OFPMatch(eth_type=0x806, arp_tpa=str(self.arpDFrame_src.at[i,'TPA']),
                            arp_spa=str(self.arpDFrame_src.at[i,'SPA']))
                    actions = [ofp_parser_src.OFPActionOutput(self.arpDFrame_src.at[i,'PORT'])]
                    self.add_flow(src, 1, match, actions)
                    i += 1
                self.ipDFrame_src = self.arpDFrame_src = pd.DataFrame([]) 
                
            elif s1.dpid == dst.id:
                i=0
                for row in self.ipDFrame_dst.iterrows():
                    #print colored('Second FOR','red')
                    match = ofp_parser_dst.OFPMatch(eth_type=0x800, ipv4_dst=str(self.ipDFrame_dst.at[i,'DST']),
                            ipv4_src=str(self.ipDFrame_dst.at[i,'SRC']))
                    actions = [ofp_parser_dst.OFPActionOutput(self.ipDFrame_dst.at[i,'PORT'])]
                    self.add_flow(dst, 32768, match, actions)
                    i += 1
                i=0
                for row in self.arpDFrame_dst.iterrows():
                    match = ofp_parser_dst.OFPMatch(eth_type=0x806, arp_tpa=str(self.arpDFrame_dst.at[i,'TPA']),
                            arp_spa=str(self.arpDFrame_dst.at[i,'SPA']))
                    actions = [ofp_parser_dst.OFPActionOutput(self.arpDFrame_dst.at[i,'PORT'])]
                    self.add_flow(dst, 1, match, actions)
                    i += 1
                self.ipDFrame_dst = self.arpDFrame_dst = pd.DataFrame([])                
            else: pass            
        except NameError, KeyError:
            pass

    @set_ev_cls(event.EventLinkDelete, MAIN_DISPATCHER)
    def link_delete_handler(self, ev):
        global c, adjacency, src, dst
         
        s1 = ev.link.src
        s2 = ev.link.dst
        adjacency[s1.dpid][s2.dpid] = None
        adjacency[s2.dpid][s1.dpid] = None
        
        ##########################################################        
        #Exception handling if switch already deleted
        try:
            del self.adjacency[s1.dpid][s2.dpid]
            del self.adjacency[s2.dpid][s1.dpid]
        except KeyError:
            pass
    
    #ADICIONADO 14/10/2018
    #######################################################################
    def install_controller(self, datapath):
        ofproto = datapath.ofproto
        parser = datapath.ofproto_parser
        match = parser.OFPMatch()
        
        actions = [parser.OFPActionOutput(ofproto.OFPP_CONTROLLER,
            ofproto.OFPCML_NO_BUFFER)]
        inst = [parser.OFPInstructionActions(ofproto.OFPIT_APPLY_ACTIONS,
            actions)]        
        mod = datapath.ofproto_parser.OFPFlowMod(
                datapath=datapath, match=match, cookie=0,
                command=ofproto.OFPFC_ADD, idle_timeout=0, hard_timeout=0,
                priority=0, instructions=inst)
        
        datapath.send_msg(mod)
     ######################################################################                   

    #===============================================================================================

    #ADICIONADO 22/09/2018
    #Monitoramento para exibicao de estatisticas imprime na tela
    ###########################################################
    def _monitor(self):
        while True:
            for dp in self.datapath_list.values():
                #print
                #print self.datapath_list.values()
                #print
                self._request_stats(dp)
            hub.sleep(1)#Valor ajustavel (1) = 1 segundo
    
    ###########################################################
    
    #ADICIONADO 22/09/2018
    ###########################################################
    @set_ev_cls(ofp_event.EventOFPStateChange, [MAIN_DISPATCHER, DEAD_DISPATCHER])
    def _state_change_handler(self, ev):
        datapath = ev.datapath

        if ev.state == MAIN_DISPATCHER:
            if not datapath.id in self.datapath_list:
                # self.logger.debug('register datapath: %016x', datapath.id)
                #print 'register datapath:', datapath.id
                self.datapath_list[datapath.id] = datapath
            elif ev.state == DEAD_DISPATCHER:
                if datapath.id in self.datapath_list:
                    # self.logger.debug('unregister datapath: %016x', datapath.id)
                    #print 'unregister datapath:', datapath.id
                    del self.datapath_list[datapath.id]
    ############################################################

    #ADICIONADO 23/09/2018
    ############################################################
    def _request_stats(self, datapath):
        ofproto = datapath.ofproto
        parser = datapath.ofproto_parser

        #req = parser.OFPFlowStatsRequest(datapath)
        #datapath.send_msg(req)

        req = parser.OFPPortStatsRequest(datapath, 0, ofproto.OFPP_ANY)
        datapath.send_msg(req)

        ofp = ofproto
        _parser_ = parser
        dp = datapath
        #print colored('dp _request_stats','blue')  #exibe os 4 switchs na tela
        #print (dp.id)
    #############################################################

    @set_ev_cls(ofp_event.EventOFPPortStatsReply, MAIN_DISPATCHER)
    def _port_stats_reply_handler(self, ev):
        start_time = time.time()
        global c, b, PL, PL1_3
        ####dp1
        global band_1_1, result_1_1, band_rx_1_1, result_rx_1_1, tx_ini_1_1, tx_fin_1_1, rx_ini_1_1, rx_fin_1_1 #dp 1 port 1
        global band_1_2, result_1_2, band_rx_1_2, result_rx_1_2, tx_ini_1_2, tx_fin_1_2, rx_ini_1_2, rx_fin_1_2 #dp 1 port 2
        global band_1_3, result_1_3, band_rx_1_3, result_rx_1_3, tx_ini_1_3, tx_fin_1_3, rx_ini_1_3, rx_fin_1_3 #dp 1 port 3
        global tx_1_2_packet, tx_1_3_packet, rx_1_2_packet, rx_1_3_packet, L1_2, L1_3
        ####dp2
        global band_2_1, result_2_1, band_rx_2_1, result_rx_2_1, tx_ini_2_1, tx_fin_2_1, rx_ini_2_1, rx_fin_2_1 #dp 2 port 1
        global band_2_2, result_2_2, band_rx_2_2, result_rx_2_2, tx_ini_2_2, tx_fin_2_2, rx_ini_2_2, rx_fin_2_2 #dp 2 port 2
        global band_2_3, result_2_3, band_rx_2_3, result_rx_2_3, tx_ini_2_3, tx_fin_2_3, rx_ini_2_3, rx_fin_2_3 #dp 2 port 3
        global tx_2_2_packet, tx_2_3_packet, rx_2_2_packet, rx_2_3_packet, L2_2, L2_3
        ####dp3
        global band_3_1, result_3_1, band_rx_3_1, result_rx_3_1, tx_ini_3_1, tx_fin_3_1, rx_ini_3_1, rx_fin_3_1 #dp 3 port 1 
        global band_3_2, result_3_2, band_rx_3_2, result_rx_3_2, tx_ini_3_2, tx_fin_3_2, rx_ini_3_2, rx_fin_3_2 #dp 3 port 2
        global band_3_3, result_3_3, band_rx_3_3, result_rx_3_3, tx_ini_3_3, tx_fin_3_3, rx_ini_3_3, rx_fin_3_3 #dp 3 port 3
        global tx_3_2_packet, tx_3_3_packet, rx_3_2_packet, rx_3_3_packet, L3_2, L3_3
        ####dp4
        global band_4_1, result_4_1, band_rx_4_1, result_rx_4_1, tx_ini_4_1, tx_fin_4_1, rx_ini_4_1, rx_fin_4_1 #dp 4 port 1
        global band_4_2, result_4_2, band_rx_4_2, result_rx_4_2, tx_ini_4_2, tx_fin_4_2, rx_ini_4_2, rx_fin_4_2 #dp 4 port 2
        global band_4_3, result_4_3, band_rx_4_3, result_rx_4_3, tx_ini_4_3, tx_fin_4_3, rx_ini_4_3, rx_fin_4_3 #dp 4 port 3
        global tx_4_2_packet, tx_4_3_packet, rx_4_2_packet, rx_4_3_packet, L4_2, L4_3
        #######
        #######
        body = ev.msg.body
        dpid = ev.msg.datapath.id
        datapath = ev.msg.datapath        
        #contador de segundos
        #t = time.localtime().tm_sec
        #print colored(t,'green')
        ################################################################################################
        ################################################################################################
        #seleciona o dp 1
        #SELECIONA PORTA 1
        if dpid == 1:
            for stat in sorted(body, key=attrgetter('port_no')):
                if stat.port_no == 1:
                    self.logger.info('switch             '
                            'Port_no         '
                            'Rec_bytes          Rec_Banda       '
                            'Trans_bytes         Trans_banda       ')
                            #'Rx_packets         Tx_packets       ')                            
                    self.logger.info('%04x              %8x         '
                            '%8d       %8d Mbps          %8d       %8d Mbps',
                            #'%8d              %8d         ', 
                            ev.msg.datapath.id, stat.port_no,
                            stat.rx_bytes, result_rx_1_1, stat.tx_bytes, result_1_1)
                            #stat.rx_packets, stat.tx_packets)                            
                    print
                    # Calculo de banda para bytes transmitidos (tx_bytes)
                    # Se o valor bytes transmitidos iniciais forem 0
                    if tx_ini_1_1 == 0: tx_ini_1_1 = stat.tx_bytes  # valor inicial bytes armazenado

                    tx_fin_1_1 = stat.tx_bytes
                    band_1_1 = (tx_fin_1_1-tx_ini_1_1)*8
                    result_1_1 = int(band_1_1/1048576)
                    tx_ini_1_1 = tx_fin_1_1

                    #Calculo de banda para bytes recebidos (rx_bytes)
                    if rx_ini_1_1 == 0: rx_ini_1_1 = stat.rx_bytes
                    rx_fin_1_1 = stat.rx_bytes
                    band_rx_1_1 = (rx_fin_1_1-rx_ini_1_1)*8
                    result_rx_1_1 = int(band_rx_1_1/1048576)
                    rx_ini_1_1 = rx_fin_1_1

                ###############################################################################
                #SELECIONA A PORTA 2
                if stat.port_no == 2:
                    self.logger.info('switch             '
                            'Port_no         '
                            'Rec_bytes          Rec_Banda       '
                            'Trans_bytes         Trans_banda       ')
                            #'Packet_loss         ')
                            #'Rx_packets         Tx_packets        Packet_loss')                            
                    self.logger.info('%04x              %8x         '
                            '%8d       %8d Mbps          %8d       %8d Mbps',
                            #'%8d        ',
                            #'%8d              %8d         %8d',
                            ev.msg.datapath.id, stat.port_no,
                            stat.rx_bytes, result_rx_1_2, stat.tx_bytes, result_1_2)
                            #stat.rx_packets, stat.tx_packets, L1_2)
                            #stat.rx_packets, stat.tx_packets)
                            #stat.rx_dropped, stat.rx_errors, stat.tx_dropped, stat.tx_errors,
                            #stat.properties[0].collisions, stat.properties[0].rx_crc_err, stat.properties[0].rx_frame_err,
                            #stat.properties[0].rx_over_err)
                    print
                    #pacote transmitido(dp1) - pacote recebido(dp2) dividido pelos pacotes transmitidos 
                    #resultado é a % de pacotes perdidos
                    #if stat.tx_packets == 0: tx_1_2_packet = stat.tx_packets
                                        
                    #PL = rx_2_2_packet-tx_1_2_packet
                    #tx_1_2_packet = rx_2_2_packet
                    
                    #L1_2 = (tx_1_2_packet - rx_2_2_packet)/stat.tx_packets
                    
                    # Calculo de banda para bytes transmitidos (tx_bytes)
                    # Se o valor bytes transmitidos iniciais forem 0
                    if tx_ini_1_2 == 0: tx_ini_1_2 = stat.tx_bytes  # valor inicial bytes armazenado
                    
                    tx_fin_1_2 = stat.tx_bytes
                    band_1_2 = (tx_fin_1_2-tx_ini_1_2)*8
                    result_1_2 = int(band_1_2/1048576)
                    tx_ini_1_2 = tx_fin_1_2
                    
                    #Calculo de banda para bytes recebidos (rx_bytes)
                    if rx_ini_1_2 == 0: rx_ini_1_2 = stat.rx_bytes
                   
                    rx_fin_1_2 = stat.rx_bytes
                    band_rx_1_2 = (rx_fin_1_2-rx_ini_1_2)*8
                    result_rx_1_2 = int(band_rx_1_2/1048576)
                    rx_ini_1_2 = rx_fin_1_2

                ###############################################################################
                #SELECIONA A PORTA 3
                if stat.port_no == 3:
                    self.logger.info('switch             '
                            'Port_no         '
                            'Rec_bytes          Rec_Banda       '
                            'Trans_bytes         Trans_banda       ')
                            #'Packet_Loss       ')
                    self.logger.info('%04x              %8x         '
                            '%8d       %8d Mbps          %8d       %8d Mbps',
                            #'%8d     ',
                            ev.msg.datapath.id, stat.port_no,
                            stat.rx_bytes, result_rx_1_3, stat.tx_bytes, result_1_3)
                            #L1_3)
                            
                            #stat.rx_dropped, stat.rx_errors, stat.tx_dropped, stat.tx_errors,
                            #stat.properties[0].collisions, stat.properties[0].rx_crc_err, stat.properties[0].rx_frame_err,
                            #stat.properties[0].rx_over_err)
                    print
                    #if stat.tx_packets == 0: tx_1_3_packet = stat.tx_packets

                    #PL1_3 = rx_4_2_packet-tx_1_3_packet
                    #tx_1_3_packet = rx_4_2_packet

                    # Calculo de banda para bytes transmitidos (tx_bytes)
                    # Se o valor bytes transmitidos iniciais forem 0
                    if tx_ini_1_3 == 0: tx_ini_1_3 = stat.tx_bytes  # valor inicial bytes armazenado
                    
                    tx_fin_1_3 = stat.tx_bytes
                    band_1_3 = (tx_fin_1_3-tx_ini_1_3)*8
                    result_1_3 = int(band_1_3/1048576)
                    tx_ini_1_3 = tx_fin_1_3

                    #Calculo de banda para bytes recebidos (rx_bytes)
                    if rx_ini_1_3 == 0: rx_ini_1_3 = stat.rx_bytes
                    rx_fin_1_3 = stat.rx_bytes
                    band_rx_1_3 = (rx_fin_1_3-rx_ini_1_3)*8
                    result_rx_1_3 = int(band_rx_1_3/1048576)
                    rx_ini_1_3 = rx_fin_1_3

        ################################################################################################
        #seleciona o dp 2
        if dpid == 2:
            for stat in sorted(body, key=attrgetter('port_no')):
                #SELECIONA PORTA 1
                if stat.port_no == 1:
                    self.logger.info('switch             '
                            'Port_no         '
                            'Rec_bytes          Rec_Banda       '
                            'Trans_bytes         Trans_banda       ')
                            #'Rx_packets         Tx_packets       ')
                    self.logger.info('%04x              %8x         '
                            '%8d       %8d Mbps          %8d       %8d Mbps',
                            #'%8d              %8d         ',
                            ev.msg.datapath.id, stat.port_no,
                            stat.rx_bytes, result_rx_2_1, stat.tx_bytes, result_2_1)
                            #stat.rx_packets, stat.tx_packets)
                    print
                     
                    # Calculo de banda para bytes transmitidos (tx_bytes)
                    # Se o valor bytes transmitidos iniciais forem 0
                    if tx_ini_2_1 == 0: tx_ini_2_1 = stat.tx_bytes  # valor inicial bytes armazenado
                    tx_fin_2_1 = stat.tx_bytes
                    band_2_1 = (tx_fin_2_1-tx_ini_2_1)*8 # 8 bits
                    result_2_1 = int(band_2_1/1048576) #divide 1Mb
                    tx_ini_2_1 = tx_fin_2_1

                    #Calculo de banda para bytes recebidos (rx_bytes)
                    if rx_ini_2_1 == 0: rx_ini_2_1 = stat.rx_bytes
                    rx_fin_2_1 = stat.rx_bytes
                    band_rx_2_1 = (rx_fin_2_1-rx_ini_2_1)*8
                    result_rx_2_1 = int(band_rx_2_1/1048576)
                    rx_ini_2_1 = rx_fin_2_1

                ###################################################################################
                #Seleciona a porta 2
                if stat.port_no == 2:
                    self.logger.info('switch             '
                            'Port_no         '
                            'Rec_bytes          Rec_Banda       '
                            'Trans_bytes         Trans_banda       ')
                            #'Packet_loss       ')
                    self.logger.info('%04x              %8x         '
                            '%8d       %8d Mbps          %8d       %8d Mbps',
                            #'%8d         ',                            
                            ev.msg.datapath.id, stat.port_no,
                            stat.rx_bytes, result_rx_2_2, stat.tx_bytes, result_2_2)
                            #L2_2)
                    print
                    # Calculo de banda para bytes transmitidos
                    # Se o valor bytes transmitidos iniciais forem 0
                    if tx_ini_2_2 == 0: tx_ini_2_2 = stat.tx_bytes  # valor inicial bytes armazenado
                    
                    tx_fin_2_2 = stat.tx_bytes                    
                    band_2_2 = (tx_fin_2_2-tx_ini_2_2)*8
                    result_2_2 = int(band_2_2/1048576)
                    #print((int(band/1048576)),  'Mbit/s')
                    tx_ini_2_2 = tx_fin_2_2

                    #Calculo de banda para bytes recebidos
                    #Se o valor de bytes recebidos for 0 
                    if rx_ini_2_2 == 0: rx_ini_2_2 = stat.rx_bytes  # valor inicial bytes armazenado
                    
                    rx_fin_2_2 = stat.rx_bytes
                    band_rx_2_2 = (rx_fin_2_2-rx_ini_2_2)*8
                    result_rx_2_2 = int(band_rx_2_2/1048576)
                    rx_ini_2_2 = rx_fin_2_2

                #Seleciona a porta 3
                if stat.port_no == 3:
                    self.logger.info('switch             '
                            'Port_no         '
                            'Rec_bytes          Rec_Banda       '
                            'Trans_bytes         Trans_banda       ')
                            #'Rx_packets         Tx_packets       ')
                    self.logger.info('%04x              %8x         '
                            '%8d       %8d Mbps          %8d       %8d Mbps',
                            #'%8d              %8d         ',
                            ev.msg.datapath.id, stat.port_no,
                            stat.rx_bytes, result_rx_2_3, stat.tx_bytes, result_2_3)
                            #stat.rx_packets, stat.tx_packets)
                    print
                    L2_3 = (tx_2_3_packet - rx_3_2_packet)/stat.tx_packets
                    #calculo de banda para bytes transmitidos na porta 3
                    if tx_ini_2_3 == 0: tx_ini_2_3 = stat.tx_bytes # valor inicial bytes armazenado
                    
                    tx_fin_2_3 = stat.tx_bytes
                    band_2_3 = (tx_fin_2_3-tx_ini_2_3)*8
                    result_2_3 = int(band_2_3/1048576)
                    tx_ini_2_3 = tx_fin_2_3

                    #calculo de banda para bytes recebidos na porta 3
                    if rx_ini_2_3 == 0: rx_ini_2_3 = stat.rx_bytes
                    
                    rx_fin_2_3 = stat.rx_bytes
                    band_rx_2_3 = (rx_fin_2_3-rx_ini_2_3)*8
                    result_rx_2_3 = int(band_rx_2_3/1048576)
                    rx_ini_2_3 = rx_fin_2_3

        ################################################################################################
        #SELECIONA O DP 3
        if dpid == 3:
            for stat in sorted(body, key=attrgetter('port_no')):
                ########################################################################################
                #PORTA 1
                if stat.port_no == 1:
                    self.logger.info('switch             '
                            'Port_no         '
                            'Rec_bytes          Rec_Banda       '
                            'Trans_bytes         Trans_banda       ')
                            #'Rx_packets         Tx_packets       ')
                    self.logger.info('%04x              %8x         '
                            '%8d       %8d Mbps          %8d       %8d Mbps',
                            #'%8d              %8d         ',
                            ev.msg.datapath.id, stat.port_no,
                            stat.rx_bytes, result_rx_3_1, stat.tx_bytes, result_3_1)
                            #stat.rx_packets, stat.tx_packets)
                    print
                    # Calculo de banda para bytes transmitidos (tx_bytes)
                    # Se o valor bytes transmitidos iniciais forem 0
                    if tx_ini_3_1 == 0: tx_ini_3_1 = stat.tx_bytes  # valor inicial bytes armazenado

                    tx_fin_3_1 = stat.tx_bytes
                    band_3_1 = (tx_fin_3_1-tx_ini_3_1)*8
                    result_3_1 = int(band_3_1/1048576)
                    tx_ini_3_1 = tx_fin_3_1

                    #Calculo de banda para bytes recebidos (rx_bytes)
                    if rx_ini_3_1 == 0: rx_ini_3_1 = stat.rx_bytes
                    rx_fin_3_1 = stat.rx_bytes
                    band_rx_3_1 = (rx_fin_3_1-rx_ini_3_1)*8
                    result_rx_3_1 = int(band_rx_3_1/1048576)
                    rx_ini_3_1 = rx_fin_3_1

                ####################################################################################    
                #SELECIONA A PORTA 3
                if stat.port_no == 3:
                    self.logger.info('switch             '
                            'Port_no         '
                            'Rec_bytes          Rec_Banda       '
                            'Trans_bytes         Trans_banda       ')
                            #'Rx_packets         Tx_packets       ')
                    self.logger.info('%04x              %8x         '
                            '%8d       %8d Mbps          %8d       %8d Mbps',
                            #'%8d              %8d         ',
                            ev.msg.datapath.id, stat.port_no,
                            stat.rx_bytes, result_rx_3_2, stat.tx_bytes, result_3_2)
                            #stat.rx_packets, stat.tx_packets)
                    print
                    #L3_2 = (tx_3_2_packet - rx_2_3_packet)/stat.tx_packets
                    # Calculo de banda para bytes transmitidos (tx_bytes)
                    # Se o valor bytes transmitidos iniciais forem 0
                    if tx_ini_3_2 == 0: tx_ini_3_2 = stat.tx_bytes  # valor inicial bytes armazenado
                    
                    tx_fin_3_2 = stat.tx_bytes
                    band_3_2 = (tx_fin_3_2-tx_ini_3_2)*8#Multiplica por 8(bits)
                    result_3_2 = int(band_3_2/1048576)#Divide por 8
                    tx_ini_3_2 = tx_fin_3_2

                    #Calculo de banda para bytes recebidos (rx_bytes)
                    if rx_ini_3_2 == 0: rx_ini_3_2 = stat.rx_bytes                    
                    rx_fin_3_2 = stat.rx_bytes
                    band_rx_3_2 = (rx_fin_3_2-rx_ini_3_2)*8
                    result_rx_3_2 = int(band_rx_3_2/1048576)
                    rx_ini_3_2 = rx_fin_3_2
                    
                ###################################################################################
                throuput3_2 = result_3_2 + result_rx_3_2

                ###################################################################################
                if c == 1: c += 1 #variavel de controle alcancada na porta 2 e adiciona + 1
                if (throuput3_2 > MAX_BAND*0.8) and c == 2:# 
                    print '\033[1;31;47m Porta 3 Congestionada\033[1;m'# mensagem de porta entrevista
                    c += 1 
                elif (throuput3_2 < MAX_BAND*0.8) and c == 3:# quando a banda normalizar 
                    c = 0                                    # zera a variável de controle
                    self.send_flow_mod(datapath, stat.port_no, IP_3)# e modifica o fluxo de volta para porta 3
                    print '\033[1;34;47m Tráfego normalizado na porta ', stat.port_no,'\033[1;m'
                
                ###################################################################################
                #SELECIONA A PORTA 2
                if stat.port_no == 2:
                    self.logger.info('switch             '
                            'Port_no         '
                            'Rec_bytes          Rec_Banda       '
                            'Trans_bytes         Trans_banda       ')
                            #'Rx_packets         Tx_packets       ')
                            #'Rec_Dropped         Rec_Errors       '
                            #'Trans_Dropped         Trans_Errors       '
                            #'Propriedades(colisão,rx_crc_err, rx_frame_err, rx_over_err             ')
                    self.logger.info('%04x              %8x         '
                            '%8d       %8d Mbps          %8d       %8d Mbps',
                            #'%8d              %8d         '
                            #'%8d            %8d          %8d            %8d                     '
                            #'%s         %s         %s         %s',
                            ev.msg.datapath.id, stat.port_no,
                            stat.rx_bytes, result_rx_3_3, stat.tx_bytes, result_3_3)
                            #stat.rx_packets, stat.tx_packets)
                            #stat.rx_dropped, stat.rx_errors, stat.tx_dropped, stat.tx_errors,
                            #stat.properties[0].collisions, stat.properties[0].rx_crc_err, stat.properties[0].rx_frame_err,
                            #stat.properties[0].rx_over_err)
                    print
                    #L3_3 = (tx_3_3_packet - rx_4_3_packet)/stat.tx_packets
                    # Calculo de banda para bytes transmitidos (tx_bytes)
                    # Se o valor bytes transmitidos iniciais forem 0
                    if tx_ini_3_3 == 0: tx_ini_3_3 = stat.tx_bytes  # valor inicial bytes armazenado     
                    tx_fin_3_3 = stat.tx_bytes
                    band_3_3 = (tx_fin_3_3-tx_ini_3_3)*8 #Multiplica por 8 (bits)
                    result_3_3 = int(band_3_3/1048576) #Divide por 1Mb 
                    tx_ini_3_3 = tx_fin_3_3

                    #Calculo de banda para bytes recebidos (rx_bytes)
                    if rx_ini_3_3 == 0: rx_ini_3_3 = stat.rx_bytes                   
                    rx_fin_3_3 = stat.rx_bytes
                    band_rx_3_3 = (rx_fin_3_3-rx_ini_3_3)*8
                    result_rx_3_3 = int(band_rx_3_3/1048576)
                    rx_ini_3_3 = rx_fin_3_3                    

                    throughput3_3 = result_3_3 + result_rx_3_3

                    ###################################################################################
                    #Regras de Contexto: Congestionamento severo 
                    #Se o throuput maior que 80% da banda a porta de saida sera trocada
                    #O Status da porta é modificado e o sentido do fluxo modificado
                    if (throughput3_3 > MAX_BAND*0.8) and c == 0: #variavel c de controle
                        start_time_1 = time.time()
                        time_2 = start_time_1 - start_time
                        #salva o tempo de captura de evento
                        captura = open('cenario_2_captura.txt','a')
                        captura.writelines(str(time_2))
                        captura.writelines("\n")
                        captura.close()
                        print '\033[1;31;47m Porta 2 Congestionada\033[1;m'
                        print '\033[1;34;47m Redirecionando o Tráfego\033[1;m'
                        self.send_flow_mod(datapath, stat.port_no, IP_3)
                        c += 1 #adiciona + 1 a variavel de controle
                    #elif (throuput3_3 < MAX_BAND*0.8) and c > 1:
                    #    c = 0
                    #    print
                    #    print '\033[1;34;47m Restaurando fluxo anterior\033[1;m'
                    #    print
                        total_time = time.time() - start_time
                        #Salva o tempo de inferencia em um arquivo TXT
                        inference = open('cenario_2_inference.txt', 'a')
                        inference.writelines(str(total_time))
                        inference.writelines("\n")
                        inference.close()
                        print "informações salvas"
                    elif (throughput3_3 > MAX_BAND*0.6) and b == 0:
                        print "Congestionamento Leve"
                    else:
                        pass                        
        
        ################################################################################################
        #SELECIONA O DP 4
        if dpid == 4:
           for stat in sorted(body, key=attrgetter('port_no')):
               #SELECIONA A PORTA 1
                if stat.port_no == 1:
                    self.logger.info('switch             '
                            'Port_no         '
                            'Rec_bytes          Rec_Banda       '
                            'Trans_bytes         Trans_banda       ')
                            #'Rx_packets         Tx_packets       ')
                            #'Rec_Dropped         Rec_Errors       '
                            #'Trans_Dropped         Trans_Errors       '
                            #'Propriedades(colisão,rx_crc_err, rx_frame_err, rx_over_err             '                            
                    self.logger.info('%04x              %8x         '
                            '%8d       %8d Mbps          %8d       %8d Mbps',
                            #'%8d              %8d         ',
                            #'%8d            %8d          %8d            %8d                     '
                            #'%s         %s         %s         %s',
                            ev.msg.datapath.id, stat.port_no,
                            stat.rx_bytes, result_rx_4_1, stat.tx_bytes, result_4_1)
                            #stat.rx_packets, stat.tx_packets)
                            #stat.rx_dropped, stat.rx_errors, stat.tx_dropped, stat.tx_errors,
                            #stat.properties[0].collisions, stat.properties[0].rx_crc_err, stat.properties[0].rx_frame_err,
                            #stat.properties[0].rx_over_err)
                    print
                    # Calculo de banda para bytes transmitidos (tx_bytes)
                    # Se o valor bytes transmitidos iniciais forem 0
                    if tx_ini_4_1 == 0: tx_ini_4_1 = stat.tx_bytes  # valor inicial bytes armazenado
                    tx_fin_4_1 = stat.tx_bytes
                    band_4_1 = (tx_fin_4_1-tx_ini_4_1)*8 # 8 bits
                    result_4_1 = int(band_4_1/1048576) #divide a banda por 1Mb
                    tx_ini_4_1 = tx_fin_4_1

                    #Calculo de banda para bytes recebidos (rx_bytes)
                    if rx_ini_4_1 == 0: rx_ini_4_1 = stat.rx_bytes
                    rx_fin_4_1 = stat.rx_bytes
                    band_rx_4_1 = (rx_fin_4_1-rx_ini_4_1)*8
                    result_rx_4_1 = int(band_rx_4_1/1048576)
                    rx_ini_4_1 = rx_fin_4_1

                #######################################################################################
                #SELECIONA A PORTA 2
                if stat.port_no == 2:
                    self.logger.info('switch             '
                            'Port_no         '
                            'Rec_bytes          Rec_Banda       '
                            'Trans_bytes         Trans_banda       ')
                            #'Rx_packets         Tx_packets       ')
                            #'Rec_Dropped         Rec_Errors       '
                            #'Trans_Dropped         Trans_Errors       '
                            #'Propriedades(colisão,rx_crc_err, rx_frame_err, rx_over_err             ')
                    self.logger.info('%04x              %8x         '
                            '%8d       %8d Mbps          %8d       %8d Mbps',
                            #'%8d              %8d         ',
                            #'%8d            %8d          %8d            %8d                     '
                            #'%s         %s         %s         %s',
                            ev.msg.datapath.id, stat.port_no,
                            stat.rx_bytes, result_rx_4_2, stat.tx_bytes, result_4_2)
                            #stat.rx_packets, stat.tx_packets)
                            #stat.rx_dropped, stat.rx_errors, stat.tx_dropped, stat.tx_errors,
                            #stat.properties[0].collisions, stat.properties[0].rx_crc_err, stat.properties[0].rx_frame_err,
                            #stat.properties[0].rx_over_err)
                    print
                    #L4_2 = (tx_4_2_packet - rx_1_3_packet) /stat.tx_packets
                    # Calculo de banda para bytes transmitidos (tx_bytes)
                    # Se o valor bytes transmitidos iniciais forem 0
                    if tx_ini_4_2 == 0: tx_ini_4_2 = stat.tx_bytes  # valor inicial bytes armazenado
                    
                    tx_fin_4_2 = stat.tx_bytes
                    band_4_2 = (tx_fin_4_2-tx_ini_4_2)*8
                    result_4_2 = int(band_4_2/1048576)
                    tx_ini_4_2 = tx_fin_4_2

                    #Calculo de banda para bytes recebidos (rx_bytes)
                    if rx_ini_4_2 == 0: rx_ini_4_2 = stat.rx_bytes
                    
                    rx_fin_4_2 = stat.rx_bytes
                    band_rx_4_2 = (rx_fin_4_2-rx_ini_4_2)*8
                    result_rx_4_2 = int(band_rx_4_2/1048576)
                    rx_ini_4_2 = rx_fin_4_2
                ######################################################################################
                #SELECIONA A PORTA 3
                if stat.port_no == 3:
                    self.logger.info('switch             '
                            'Port_no         '
                            'Rec_bytes          Rec_Banda       '
                            'Trans_bytes         Trans_banda       ')
                            #'Rx_packets         Tx_packets       '                            
                            #'Rec_Dropped         Rec_Errors       '
                            #'Trans_Dropped         Trans_Errors       '
                            #'Propriedades(colisão,rx_crc_err, rx_frame_err, rx_over_err             ')
                    self.logger.info('%04x              %8x         '
                            '%8d       %8d Mbps          %8d       %8d Mbps',
                            #'%8d              %8d         '                            
                            #'%8d            %8d          %8d            %8d                     '
                            #'%s         %s         %s         %s',
                            ev.msg.datapath.id, stat.port_no,
                            stat.rx_bytes, result_rx_4_3, stat.tx_bytes, result_4_3)
                            #stat.rx_packets, stat.tx_packets, L4_3)
                            #stat.rx_dropped, stat.rx_errors, stat.tx_dropped, stat.tx_errors,
                            #stat.properties[0].collisions, stat.properties[0].rx_crc_err, stat.properties[0].rx_frame_err,
                            #stat.properties[0].rx_over_err)
                    print
                    #L4_3 = (tx_4_3_packet - rx_3_3_packet) /stat.tx_packets
                    # Calculo de banda para bytes transmitidos (tx_bytes)
                    # Se o valor bytes transmitidos iniciais forem 0
                    if tx_ini_4_3 == 0: tx_ini_4_3 = stat.tx_bytes  # valor inicial bytes armazenado     
                    tx_fin_4_3 = stat.tx_bytes
                    band_4_3 = (tx_fin_4_3-tx_ini_4_3)*8
                    result_4_3 = int(band_4_3/1048576)
                    tx_ini_4_3 = tx_fin_4_3

                    #Calculo de banda para bytes recebidos (rx_bytes)
                    if rx_ini_4_3 == 0: rx_ini_4_3 = stat.rx_bytes                    
                    rx_fin_4_3 = stat.rx_bytes
                    band_rx_4_3 = (rx_fin_4_3-rx_ini_4_3)*8
                    result_rx_4_3 = int(band_rx_4_3/1048576)
                    rx_ini_4_3 = rx_fin_4_3
    
        
    
