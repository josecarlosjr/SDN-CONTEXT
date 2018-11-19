#-*- coding: utf-8 -*-
from ryu.base import app_manager
from ryu.controller import mac_to_port, ofp_event
from ryu.controller.handler import CONFIG_DISPATCHER, MAIN_DISPATCHER, DEAD_DISPATCHER, set_ev_cls
from ryu.ofproto import ofproto_v1_3
from ryu.lib.mac import haddr_to_bin
from ryu.lib.packet import packet, arp, ethernet, ipv4, ipv6, ether_types, icmp
from ryu.lib import mac, ip, hub
from ryu.topology.api import get_switch, get_link, get_all_link, get_all_switch
from ryu.app.wsgi import ControllerBase
from ryu.topology import event, switches
from termcolor import colored
from collections import defaultdict
from operator import itemgetter, attrgetter
import os, random, time, copy
from datetime import datetime

MAX_PATHS = 2

IP_1 = '192.168.1.1'
IP_2 = '192.168.2.2'
IP_3 = '192.168.3.3'
IP_4 = '192.168.4.4'

MAX_BAND = 800 #Mbps

adjacency = defaultdict(lambda: defaultdict(lambda: None))
####################################

class ProjectController(app_manager.RyuApp):
    OFP_VERSIONS = [ofproto_v1_3.OFP_VERSION]
    
    #ADICIONADO 26/09/2018 variavel global
    ################################
    global dp, C, c, src, dst, first_port, last_port, out_ports

    #######################################################################################################################
    #Variaveis globais para calculo de banda
    #DP 1
    global band_1_1, result_1_1, band_rx_1_1, result_rx_1_1, tx_ini_1_1, tx_fin_1_1, rx_ini_1_1, rx_fin_1_1
    global band_1_2, result_1_2, band_rx_1_2, result_rx_1_2, tx_ini_1_2, tx_fin_1_2, rx_ini_1_2, rx_fin_1_2 #dp 1 port 2
    global band_1_3, result_1_3, band_rx_1_3, result_rx_1_3, tx_ini_1_3, tx_fin_1_3, rx_ini_1_3, rx_fin_1_3 #dp 1 port 3
    #DP 2
    global band_2_1, result_2_1, band_rx_2_1, result_rx_2_1, tx_ini_2_1, tx_fin_2_1, rx_ini_2_1, rx_fin_2_1
    global band_2_2, result_2_2, band_rx_2_2, result_rx_2_2, tx_ini_2_2, tx_fin_2_2, rx_ini_2_2, rx_fin_2_2 #dp 2 port 2
    global band_2_3, result_2_3, band_rx_2_3, result_rx_2_3, tx_ini_2_3, tx_fin_2_3, rx_ini_2_3, rx_fin_2_3 #dp 2 port 3
    #DP 3
    global band_3_1, result_3_1, band_rx_3_1, result_rx_3_1, tx_ini_3_1, tx_fin_3_1, rx_ini_3_1, rx_fin_3_1
    global band_3_2, result_3_2, band_rx_3_2, result_rx_3_2, tx_ini_3_2, tx_fin_3_2, rx_ini_3_2, rx_fin_3_2 #dp 3 port 2
    global band_3_3, result_3_3, band_rx_3_3, result_rx_3_3, tx_ini_3_3, tx_fin_3_3, rx_ini_3_3, rx_fin_3_3 #dp 3 port 3
    #DP 4
    global band_4_1, result_4_1, band_rx_4_1, result_rx_4_1, tx_ini_4_1, tx_fin_4_1, rx_ini_4_1, rx_fin_4_1
    global band_4_2, result_4_2, band_rx_4_2, result_rx_4_2, tx_ini_4_2, tx_fin_4_2, rx_ini_4_2, rx_fin_4_2 #dp 4 port 2
    global band_4_3, result_4_3, band_rx_4_3, result_rx_4_3, tx_ini_4_3, tx_fin_4_3, rx_ini_4_3, rx_fin_4_3 #dp 4 port 3
    ########################################################################################################################
    
    #Variaveis globais para armazenamento do endereco mac de todas interfaces do datapath
    global mac_addr_1_1, mac_addr_1_2, mac_addr_1_3, mac_addr_2_1, mac_addr_2_2, mac_addr_2_3
    global mac_addr_4_1, mac_addr_4_2, mac_addr_4_3, mac_addr_4_1, mac_addr_4_2, mac_addr_4_3

    #inicializando variáveis globais
    C = c = out_ports = 0
    
    #DP 1
    band_1_1 = result_1_1 = band_rx_1_1 = result_rx_1_1 = tx_ini_1_1 = tx_fin_1_1 = rx_ini_1_1 = rx_fin_1_1 = 0 #dp 1 port 1
    band_1_2 = result_1_2 = band_rx_1_2 = result_rx_1_2 = tx_ini_1_2 = tx_fin_1_2 = rx_ini_1_2 = rx_fin_1_2 = 0 #dp 1 port 2
    band_1_3 = result_1_3 = band_rx_1_3 = result_rx_1_3 = tx_ini_1_3 = tx_fin_1_3 = rx_ini_1_3 = rx_fin_1_3 = 0 #dp 1 port 3
    #DP 2
    band_2_1 = result_2_1 = band_rx_2_1 = result_rx_2_1 = tx_ini_2_1 = tx_fin_2_1 = rx_ini_2_1 = rx_fin_2_1 = 0 #dp 2 port 1
    band_2_2 = result_2_2 = band_rx_2_2 = result_rx_2_2 = tx_ini_2_2 = tx_fin_2_2 = rx_ini_2_2 = rx_fin_2_2 = 0 #dp 2 port 2
    band_2_3 = result_2_3 = band_rx_2_3 = result_rx_2_3 = tx_ini_2_3 = tx_fin_2_3 = rx_ini_2_3 = rx_fin_2_3 = 0 #dp 2 port 2
    #DP3
    band_3_1 = result_3_1 = band_rx_3_1 = result_rx_3_1 = tx_ini_3_1 = tx_fin_3_1 = rx_ini_3_1 = rx_fin_3_1 = 0 #dp 3 port 1
    band_3_2 = result_3_2 = band_rx_3_2 = result_rx_3_2 = tx_ini_3_2 = tx_fin_3_2 = rx_ini_3_2 = rx_fin_3_2 = 0 #dp 3 port 2
    band_3_3 = result_3_3 = band_rx_3_3 = result_rx_3_3 = tx_ini_3_3 = tx_fin_3_3 = rx_ini_3_3 = rx_fin_3_3 = 0 #dp 3 port 3
    #DP4
    band_4_1 = result_4_1 = band_rx_4_1 = result_rx_4_1 = tx_ini_4_1 = tx_fin_4_1 = rx_ini_4_1 = rx_fin_4_1 = 0 #dp 4 port 1
    band_4_2 = result_4_2 = band_rx_4_2 = result_rx_4_2 = tx_ini_4_2 = tx_fin_4_2 = rx_ini_4_2 = rx_fin_4_2 = 0 #dp 4 port 2
    band_4_3 = result_4_3 = band_rx_4_3 = result_rx_4_3 = tx_ini_4_3 = tx_fin_4_3 = rx_ini_4_3 = rx_fin_4_3 = 0 #dp 4 port 3
    
    mac_addr_1_1 = mac_addr_1_2 = mac_addr_1_3 = mac_addr_2_1 = mac_addr_2_2 = mac_addr_2_3 = 0
    mac_addr_4_1 = mac_addr_4_2 = mac_addr_4_3 = mac_addr_4_1 = mac_addr_4_2 = mac_addr_4_3 = 0

    def __init__(self, *args, **kwargs):
        super(ProjectController, self).__init__(*args, **kwargs)
        self.mac_to_port = {}
        self.topology_api_app = self
        self.datapath_list = {}
        self.arp_table = {}
        self.switches = []
        self.hosts = {}
        self.multipath_group_ids = {}
        self.group_ids = []
        self.adjacency = defaultdict(dict)
        self.bandwidths = defaultdict(lambda: defaultdict(lambda: 10000000))#DEFAULT_BW))
        #ADICIONADO 22/09/2018
        ##################################################
        self.monitor_thread = hub.spawn(self._monitor)
        self.eventos = []
        ##################################################

    #depth-first search
    def get_paths(self, src, dst):
        '''
        Get all paths from src to dst using DFS (DeeP Field Search) algorithm    
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

    def get_link_cost(self, s1, s2):
        '''
        Get the link cost between two switches 
        '''      
        e1 = self.adjacency[s1][s2]
        e2 = self.adjacency[s2][s1]
        bl = min(self.bandwidths[s1][e1], self.bandwidths[s2][e2])
        ew = 10000000/bl#REFERENCE_BW/bl
        return ew

    def get_path_cost(self, path):
        '''
        Get the path cost
        '''
        cost = 0
        for i in range(len(path) - 1):
            cost += self.get_link_cost(path[i], path[i+1])
        return cost

    def get_optimal_paths(self, src, dst):
        '''
        Get the n-most optimal paths according to MAX_PATHS
        '''
        paths = self.get_paths(src, dst)
        paths_count = len(paths) if len(
            paths) < MAX_PATHS else MAX_PATHS
        retorno = sorted(paths, key=lambda x: self.get_path_cost(x))[0:(paths_count)]
        #print ("get the most optimal paths", retorno)
        return sorted(paths, key=lambda x: self.get_path_cost(x))[0:(paths_count)]

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


    def install_paths(self, src, first_port, dst, last_port, ip_src, ip_dst):
        computation_start = time.time()
        paths = self.get_optimal_paths(src, dst)
        pw = []
        #print "Variavel paths = get_optimal_paths: ", paths
        for path in paths:
            pw.append(self.get_path_cost(path))
            #print path, "cost = ", pw[len(pw) - 1]
        #sum_of_pw = sum(pw) * 1.0
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
                    if (out_port, pw[i]) not in ports[in_port]:
                        ports[in_port].append((out_port, pw[i]))
                i += 1

            for in_port in ports:

                match_ip = ofp_parser.OFPMatch(
                    eth_type=0x0800, 
                    ipv4_src=ip_src, 
                    ipv4_dst=ip_dst
                )
                match_arp = ofp_parser.OFPMatch(
                    eth_type=0x0806, 
                    arp_spa=ip_src, 
                    arp_tpa=ip_dst
                )

                out_ports = ports[in_port]

                #elif len(out_ports) == 1:
          #      print "datapath tive apenas 1 caminho:"
          #      print
                actions = [ofp_parser.OFPActionOutput(out_ports[0][0])]
                
                self.add_flow(dp, 32767, match_ip, actions)
                self.add_flow(dp, 1, match_arp, actions)

        return paths_with_ports[0][src][1]

    def add_flow(self, datapath, priority, match, actions, buffer_id=None):
        
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
        #print "switch_features_handler is called"
        datapath = ev.msg.datapath
        #dp = ev.msg.datapath
        
        ofproto = datapath.ofproto
        parser = datapath.ofproto_parser

        match = parser.OFPMatch()
        actions = [parser.OFPActionOutput(ofproto.OFPP_CONTROLLER,
                                          ofproto.OFPCML_NO_BUFFER)]
        self.add_flow(datapath, 0, match, actions)

    @set_ev_cls(ofp_event.EventOFPPortDescStatsReply, MAIN_DISPATCHER)
    def port_desc_stats_reply_handler(self, ev):
        switch = ev.msg.datapath
        for p in ev.msg.body:
            self.bandwidths[switch.id][p.port_no] = p.curr_speed    
    
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
        #pkt_icmp = pkt.get_protocol(icmp.icmp)
        
        # avoid broadcast from LLDP
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
                print
                h1 = self.hosts[src]
                h2 = self.hosts[dst]
                out_port = self.install_paths(h1[0], h1[1], h2[0], h2[1], src_ip, dst_ip)
                self.install_paths(h2[0], h2[1], h1[0], h1[1], dst_ip, src_ip) # reverse
            elif arp_pkt.opcode == arp.ARP_REQUEST:
                if dst_ip in self.arp_table:
                    self.arp_table[src_ip] = src
                    dst_mac = self.arp_table[dst_ip]
                    h1 = self.hosts[src]
                    h2 = self.hosts[dst_mac]
                    out_port = self.install_paths(h1[0], h1[1], h2[0], h2[1], src_ip, dst_ip)
                    self.install_paths(h2[0], h2[1], h1[0], h1[1], dst_ip, src_ip) # reverse
        
        #if pkt_icmp:
        #    if pkt_icmp.type == icmp.ICMP_ECHO_REQUEST:
        #        print "Request"
        #    if pkt_icmp.type == icmp.ICMP_ECHO_REPLY:
        #        print "Reply"

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
        #print "link add handler"
        s1 = ev.link.src
        s2 = ev.link.dst
        #print ("s1 = ev.link.src", s1)
        #print ("s2 = ev.link.dst", s2)
        print '\033[1;34;47m Link Switch', s1.dpid, 'Porta', s1.port_no, 'Up\033[1;m'
        self.adjacency[s1.dpid][s2.dpid] = s1.port_no
        self.adjacency[s2.dpid][s1.dpid] = s2.port_no

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

        req = parser.OFPFlowStatsRequest(datapath)
        datapath.send_msg(req)

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
        global c
        ####dp1
        global band_1_1, result_1_1, band_rx_1_1, result_rx_1_1, tx_ini_1_1, tx_fin_1_1, rx_ini_1_1, rx_fin_1_1 #dp 1 port 1
        global band_1_2, result_1_2, band_rx_1_2, result_rx_1_2, tx_ini_1_2, tx_fin_1_2, rx_ini_1_2, rx_fin_1_2 #dp 1 port 2
        global band_1_3, result_1_3, band_rx_1_3, result_rx_1_3, tx_ini_1_3, tx_fin_1_3, rx_ini_1_3, rx_fin_1_3 #dp 1 port 3
        ####dp2
        global band_2_1, result_2_1, band_rx_2_1, result_rx_2_1, tx_ini_2_1, tx_fin_2_1, rx_ini_2_1, rx_fin_2_1 #dp 2 port 1
        global band_2_2, result_2_2, band_rx_2_2, result_rx_2_2, tx_ini_2_2, tx_fin_2_2, rx_ini_2_2, rx_fin_2_2 #dp 2 port 2
        global band_2_3, result_2_3, band_rx_2_3, result_rx_2_3, tx_ini_2_3, tx_fin_2_3, rx_ini_2_3, rx_fin_2_3 #dp 2 port 3
        ####dp3
        global band_3_1, result_3_1, band_rx_3_1, result_rx_3_1, tx_ini_3_1, tx_fin_3_1, rx_ini_3_1, rx_fin_3_1 #dp 3 port 1 
        global band_3_2, result_3_2, band_rx_3_2, result_rx_3_2, tx_ini_3_2, tx_fin_3_2, rx_ini_3_2, rx_fin_3_2 #dp 3 port 2
        global band_3_3, result_3_3, band_rx_3_3, result_rx_3_3, tx_ini_3_3, tx_fin_3_3, rx_ini_3_3, rx_fin_3_3 #dp 3 port 3
        ####dp4
        global band_4_1, result_4_1, band_rx_4_1, result_rx_4_1, tx_ini_4_1, tx_fin_4_1, rx_ini_4_1, rx_fin_4_1 #dp 4 port 1
        global band_4_2, result_4_2, band_rx_4_2, result_rx_4_2, tx_ini_4_2, tx_fin_4_2, rx_ini_4_2, rx_fin_4_2 #dp 4 port 2
        global band_4_3, result_4_3, band_rx_4_3, result_rx_4_3, tx_ini_4_3, tx_fin_4_3, rx_ini_4_3, rx_fin_4_3 #dp 4 port 3

        body = ev.msg.body
        dpid = ev.msg.datapath.id
        datapath = ev.msg.datapath
        #contador de segundos
        #t = time.localtime().tm_sec
        #print colored(t,'green')

        ################################################################################################
        #seleciona o dp 1
        #SELECIONA PORTA 1
        if dpid == 1:
            for stat in sorted(body, key=attrgetter('port_no')):
                #Statement para porta 1
                if stat.port_no == 1:
                    self.logger.info('switch             '
                            'Port_no         '
                            'Rec_bytes          Rec_Banda       '
                            'Trans_bytes         Trans_banda       '
                            )
                    self.logger.info('%04x              %8x         '
                            '%8d       %8d Mbps          %8d       %8d Mbps',
                            ev.msg.datapath.id, stat.port_no,
                            stat.rx_bytes, result_rx_1_1, stat.tx_bytes, result_1_1)
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
                            'Trans_bytes         Trans_banda       '
                            )
                    self.logger.info('%04x              %8x         '
                            '%8d       %8d Mbps          %8d       %8d Mbps',
                            ev.msg.datapath.id, stat.port_no,
                            stat.rx_bytes, result_rx_1_2, stat.tx_bytes, result_1_2)
                    print
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
                            'Trans_bytes         Trans_banda       '
                            )
                    self.logger.info('%04x              %8x         '
                            '%8d       %8d Mbps          %8d       %8d Mbps',
                            ev.msg.datapath.id, stat.port_no,
                            stat.rx_bytes, result_rx_1_3, stat.tx_bytes, result_1_3)
                    print
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
                            'Trans_bytes         Trans_banda       '
                            )
                    self.logger.info('%04x              %8x         '
                            '%8d       %8d Mbps          %8d       %8d Mbps',
                            ev.msg.datapath.id, stat.port_no,
                            stat.rx_bytes, result_rx_2_1, stat.tx_bytes, result_2_1)
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
                            'Trans_bytes         Trans_banda       '                            
                            )
                    self.logger.info('%04x              %8x         '
                            '%8d       %8d Mbps          %8d       %8d Mbps',
                            ev.msg.datapath.id, stat.port_no,
                            stat.rx_bytes, result_rx_2_2, stat.tx_bytes, result_2_2)
                    print
                    # Calculo de banda para bytes transmitidos
                    # Se o valor bytes transmitidos iniciais forem 0
                    if tx_ini_2_2 == 0: tx_ini_2_2 = stat.tx_bytes  # valor inicial bytes armazenado                    
                    tx_fin_2_2 = stat.tx_bytes                    
                    band_2_2 = (tx_fin_2_2-tx_ini_2_2)*8
                    result_2_2 = int(band_2_2/1048576)                    
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
                            'Trans_bytes         Trans_banda       '
                            )
                    self.logger.info('%04x              %8x         '
                            '%8d       %8d Mbps          %8d       %8d Mbps',
                            ev.msg.datapath.id, stat.port_no,
                            stat.rx_bytes, result_rx_2_3, stat.tx_bytes, result_2_3)
                    print
                    
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
                            'Trans_bytes         Trans_banda       '
                            )
                    self.logger.info('%04x              %8x         '
                            '%8d       %8d Mbps          %8d       %8d Mbps',
                            ev.msg.datapath.id, stat.port_no,
                            stat.rx_bytes, result_rx_3_1, stat.tx_bytes, result_3_1)
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
                #SELECIONA A PORTA 2
                if stat.port_no == 2:
                    self.logger.info('switch             '
                            'Port_no         '
                            'Rec_bytes          Rec_Banda       '
                            'Trans_bytes         Trans_banda       '
                            )
                    self.logger.info('%04x              %8x         '
                            '%8d       %8d Mbps          %8d       %8d Mbps',
                            ev.msg.datapath.id, stat.port_no,
                            stat.rx_bytes, result_rx_3_2, stat.tx_bytes, result_3_2)
                    print
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
                
                #Regra para normalização da porta 
                ###################################################################################
                if c == 1: c += 1 #variavel de controle alcancada na porta 2 e adiciona + 1
                if (throuput3_2 > MAX_BAND*0.8) and c == 2:# 
                    print '\033[1;31;47m Porta 2 Congestionada\033[1;m'# mensagem de porta entrevista
                    c += 1 
                elif (throuput3_2 < MAX_BAND*0.8) and c == 3:# quando a banda normalizar 
                    c = 0                                    # zera a variável de controle
                    self.send_flow_mod(datapath, stat.port_no, IP_3)#chama novamente a função para normalização da porta
                    print '\033[1;34;47m Tráfego normalizado na porta ', stat.port_no,'\033[1;m'

                ###################################################################################
                #SELECIONA A PORTA 3
                if stat.port_no == 3:
                    self.logger.info('switch             '
                            'Port_no         '
                            'Rec_bytes          Rec_Banda       '
                            'Trans_bytes         Trans_banda       '
                            )
                    self.logger.info('%04x              %8x         '
                            '%8d       %8d Mbps          %8d       %8d Mbps',
                            ev.msg.datapath.id, stat.port_no,
                            stat.rx_bytes, result_rx_3_3, stat.tx_bytes, result_3_3)
                    print
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

                    throuput3_3 = result_3_3 + result_rx_3_3

                    ###################################################################################
                    #Regras de Contexto: Congestionamento severo 
                    #Se o throuput maior que 80% da banda a porta de saida sera trocada
                    #O Status da porta é modificado e o sentido do fluxo modificado
                    if (throuput3_3 > MAX_BAND*0.8) and c == 0: #variavel c de controle
                        print '\033[1;31;47m Porta 3 Congestionada\033[1;m'
                        #print '\033[1;31;47m 80% da banda alcançada\033[1;m'
                        print '\033[1;34;47m Redirecionando o Tráfego\033[1;m'
                        self.send_port_mod(datapath, stat.port_no)
                        self.send_flow_mod(datapath, stat.port_no, IP_3)
                        c += 1 #adiciona + 1 a variavel de controle
                    #elif (throuput3_3 < MAX_BAND*0.8) and c > 1:
                    #    c = 0
                    #    print
                    #    print '\033[1;34;47m Restaurando fluxo anterior\033[1;m'
                    #    print
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
                            'Trans_bytes         Trans_banda       '
                            )
                    self.logger.info('%04x              %8x         '
                            '%8d       %8d Mbps          %8d       %8d Mbps',
                            ev.msg.datapath.id, stat.port_no,
                            stat.rx_bytes, result_rx_4_1, stat.tx_bytes, result_4_1)
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
                            'Trans_bytes         Trans_banda       '
                            )
                    self.logger.info('%04x              %8x         '
                            '%8d       %8d Mbps          %8d       %8d Mbps',
                            ev.msg.datapath.id, stat.port_no,
                            stat.rx_bytes, result_rx_4_2, stat.tx_bytes, result_4_2)
                    print
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
                            'Trans_bytes         Trans_banda       '
                            )
                    self.logger.info('%04x              %8x         '
                            '%8d       %8d Mbps          %8d       %8d Mbps',
                            ev.msg.datapath.id, stat.port_no,
                            stat.rx_bytes, result_rx_4_3, stat.tx_bytes, result_4_3)
                    print
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

    ###############################################################################################
    #ADICIONADO 24/10/2018
    #MODIFICA O ESTADO DA PORTA
    def send_port_mod(self, datapath, port_no):
        global out_ports
        global mac_addr_1_1, mac_addr_1_2, mac_addr_1_3, mac_addr_2_1, mac_addr_2_2, mac_addr_2_3
        global mac_addr_3_1, mac_addr_3_2, mac_addr_3_3, mac_addr_4_1, mac_addr_4_2, mac_addr_4_3
        
        ofp = datapath.ofproto
        ofp_parser = datapath.ofproto_parser
        port_no = 3        
        #print mac_addr_3_3
        #hw_addr = 'fa:c8:e8:76:1d:7e'
        hw_addr = mac_addr_3_3
        config = 3
        mask = (ofp.OFPPC_NO_FWD)
        #mask = (ofp.OFPPC_PORT_DOWN ofp.OFPPC_NO_RECV ofp.OFPPC_NO_FWD ofp.OFPPC_NO_PACKET_IN)
        #advertise = (ofp.OFPPF_10MB_HD | ofp.OFPPF_100MB_FD 
                     #ofp.OFPPF_1GB_FD | ofp.OFPPF_COPPER ofp.OFPPF_AUTONEG ofp.OFPPF_PAUSE | ofp.OFPPF_PAUSE_ASYM)
        advertise = (ofp.OFPPF_PAUSE)
        req = ofp_parser.OFPPortMod(datapath, port_no, hw_addr, config, mask, advertise)
        datapath.send_msg(req)        

    ##############################################################################################
    #ADICIONADO 24/10/2018
    #FUNCAO PARA MODIFICAR O FLUXO
    def send_flow_mod(self, datapath, out_ports, ip_n):
        #global out_ports        
        ofp = datapath.ofproto
        ofp_parser = datapath.ofproto_parser        
        cookie = cookie_mask = 0
        table_id = 0
        idle_timeout = hard_timeout = 0
        priority = 32768
        buffer_id = ofp.OFP_NO_BUFFER
         
        ##########################################################################################
        #Match field (de acordo com a tabela de fluxo 0)
        match_ip = ofp_parser.OFPMatch(eth_type=0x800, ipv4_src=ip_n, ipv4_dst='192.168.1.1')
        match_arp = ofp_parser.OFPMatch(eth_type=0x806, arp_spa=ip_n, arp_tpa='192.168.1.1')
        ##########################################################################################
        #remove fluxo com match para ipv4
        actions = [ofp_parser.OFPActionOutput(ofp.OFPP_NORMAL, 0)]
        inst = [ofp_parser.OFPInstructionActions(ofp.OFPIT_APPLY_ACTIONS,
            actions)]
        
        req = ofp_parser.OFPFlowMod(datapath, cookie, cookie_mask,
                table_id, ofp.OFPFC_DELETE,
                idle_timeout, hard_timeout,
                priority, buffer_id,
                ofp.OFPP_ANY, ofp.OFPG_ANY,
                ofp.OFPFF_SEND_FLOW_REM,
                match_ip, inst)
        datapath.send_msg(req)
        ###########################################################################################
        #remove fluxo com match para arp
        actions = [ofp_parser.OFPActionOutput(ofp.OFPP_NORMAL, 0)]
        inst = [ofp_parser.OFPInstructionActions(ofp.OFPIT_APPLY_ACTIONS, 
            actions)]

        req2 = ofp_parser.OFPFlowMod(datapath, cookie, cookie_mask,
                table_id, ofp.OFPFC_DELETE,
                idle_timeout, hard_timeout,
                priority, buffer_id,
                ofp.OFPP_ANY, ofp.OFPG_ANY,
                ofp.OFPFF_SEND_FLOW_REM,
                match_arp, inst)
        datapath.send_msg(req2)
        ############################################################################################
        #Adiciona um novo fluxo apontando para outra porta
        if out_ports == 3: out_ports = out_ports - 1#se a porta congestionada for 3 diminui e aponta para 2
        elif out_ports == 2: out_ports +=1 #se a porta for 2 soma e aponta para 3
        else: pass
        
        actions = [ofp_parser.OFPActionOutput(out_ports)]

        self.add_flow(datapath, 32768, match_ip, actions)
        self.add_flow(datapath, 32768, match_arp, actions)
        
    
    #ADICIONADO 23/09/2018
    #Exibe o status de portas do switch
    #classe utilizada ryu.controller.controller.Datapath
    #ryu.ofproto.ofproto_v1_3_parser.OFPPort
    #ryu.ofproto.ofproto_v1_3
    #flags OFPPS_LINK_DOWN
    ############################################################# 
    @set_ev_cls(ofp_event.EventOFPPortStatus, MAIN_DISPATCHER)
    def port_status_handler(self, ev):
        #variaveis usadas nessa função
        global C, src, dst, first_port, last_port  
        global mac_addr_1_1, mac_addr_1_2, mac_addr_1_3, mac_addr_2_1, mac_addr_2_2, mac_addr_2_3
        global mac_addr_3_1, mac_addr_3_2, mac_addr_3_3, mac_addr_4_1, mac_addr_4_2, mac_addr_4_3 
        
        msg = ev.msg #armazena a mensagem do evento
        dp = msg.datapath #dp.id
        ofp = dp.ofproto
        parser = dp.ofproto_parser
        #if msg.desc.state == 1:
        #if msg.reason == ofp.OFPPR_ADD: reason = 'ADD'
        if msg.reason == ofp.OFPPR_DELETE: reason = 'DELETE'
        #armazena o endereço Mac de todas as insterfaces dos datapath's
        if msg.reason == ofp.OFPPR_MODIFY: 
            if msg.desc.name == 's1_POP-eth1': mac_addr_1_1 = msg.desc.hw_addr
            if msg.desc.name == 's1_POP-eth2': mac_addr_1_2 = msg.desc.hw_addr
            if msg.desc.name == 's1_POP-eth3': mac_addr_1_3 = msg.desc.hw_addr
            if msg.desc.name == 's2_FUNDAJ-eth1': mac_addr_2_1 = msg.desc.hw_addr
            if msg.desc.name == 's2_FUNDAJ-eth2': mac_addr_2_2 = msg.desc.hw_addr
            if msg.desc.name == 's2_FUNDAJ-eth3': mac_addr_2_3 = msg.desc.hw_addr
            if msg.desc.name == 's3_CPOR-eth1': mac_addr_3_1 = msg.desc.hw_addr
            if msg.desc.name == 's3_CPOR-eth2': mac_addr_3_2 = msg.desc.hw_addr
            if msg.desc.name == 's3_CPOR-eth3': mac_addr_3_3 = msg.desc.hw_addr
            if msg.desc.name == 's4_IFPE-eth1': mac_addr_4_1 = msg.desc.hw_addr
            if msg.desc.name == 's4_IFPE-eth2': mac_addr_4_2 = msg.desc.hw_addr
            if msg.desc.name == 's4_IFPE-eth3': mac_addr_4_3 = msg.desc.hw_addr

        if msg.desc.state == ofp.OFPPS_LINK_DOWN:
            print
            print '\033[1;31;47m Nome da interface:', msg.desc.name, '\033[1;m'
            print '\033[1;31;47m Porta: ', msg.desc.port_no, 'Porta status DOWN\033[1;m'
            if (C == 0): #Condicional para armazenar o dp e in_port origem
                src = dp.id
                first_port = msg.desc.port_no
            
            if (C != 0): #Condicional para armazenar o dp e out_port destino
                dst = dp.id
                last_port = msg.desc.port_no
            
            if (C > 0 and src and dst and first_port and last_port):
                ip_src = ip_dst = None   
                           
            else: pass
            C += 1 #incrementa a variável de controle
            if (C == 2): 
                C = 0 #zera a variavel de controle ao alcançar 2
                print '\033[1;31;47m Deletando tabela de fluxos\033[1;m'
                if src and dst:
                    for datapath in self.datapath_list.values():
                        if datapath.id == src: src = datapath
                        if datapath.id == dst: dst = datapath
                    print '\033[1;42m Redirecionando o Tráfego\033[1;m'
                    self.remove_flows(src, 0)#chama a função para remover fluxo do dp adjacente
                    self.remove_flows(dst, 0)#chama a função para remover fluxo do dp adjacente
                    self.install_controller(src)
                    self.install_controller(dst)
        if msg.desc.state == ofp.OFPPS_BLOCKED: pass
        if msg.desc.state == ofp.OFPPS_LIVE: pass
        if msg.desc.state == ofp.OFPPC_NO_PACKET_IN: pass
        else:
            reason = 'UNKNOWN'        
    ##############################################################

    #ADICIONADO 25/09/2018
    #usa o valor retornado da função remove_tale_flow para enviar
    #a mensagem até o datapath(switch) 
    ##############################################################
    def remove_flows(self, datapath, table_id):        
        parser = datapath.ofproto_parser
        ofproto = datapath.ofproto
        empty_match = parser.OFPMatch()
        instructions = []        
        flow_mod = self.remove_table_flows(datapath, 
                table_id, 
                empty_match, 
                instructions)
        print '\033[1;42m Deletando entradas de fluxos da tabela: ',table_id ,'\033[1;m'
        datapath.send_msg(flow_mod)

    ##############################################################

    #ADICONADO 25/09/2018
    #Função retorna o valor para remover tabelas 
    ##############################################################
    def remove_table_flows(self, datapath, table_id, match, instructions):        
        ofproto = datapath.ofproto
        #OFPFlowMod(datapath, cookie=0, cookie_mask=0, table_id=0, command=0, idle_timeout=0, hard_timeout=0, priority=32768 buffer_id=4294967295, out_port=0, out_group=0, flags=0, match=None, instructions=None

        flow_mod = datapath.ofproto_parser.OFPFlowMod(datapath, 0, 0, table_id,
                ofproto.OFPFC_DELETE, 0, 0,
                1,
                ofproto.OFPCML_NO_BUFFER,
                ofproto.OFPP_ANY,
                ofproto.OFPP_ANY, 0,
                match, instructions)
                #ofproto.OFPG_ANY para grupos
        return flow_mod
    ##############################################################      
