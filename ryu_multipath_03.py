#-*- coding: utf-8 -*-

from ryu.base import app_manager
from ryu.controller import mac_to_port, ofp_event
from ryu.controller.handler import CONFIG_DISPATCHER, MAIN_DISPATCHER, DEAD_DISPATCHER, set_ev_cls
from ryu.ofproto import ofproto_v1_3
from ryu.lib.mac import haddr_to_bin
from ryu.lib.packet import packet, arp, ethernet, ipv4, ipv6, ether_types
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

# Cisco Reference bandwidth = 1 Gbps
REFERENCE_BW = 10000000

DEFAULT_BW = 10000000

MAX_PATHS = 2

#ADICIONADO 23/09/2018 variavel criada para o get_topology 
####################################
myswitches = []
datapath_list = {}
####################################


class ProjectController(app_manager.RyuApp):
    OFP_VERSIONS = [ofproto_v1_3.OFP_VERSION]
    
    #ADICIONADO 26/09/2018 variavel global
    ################################
    global dp, C, src, dst, first_port, last_port
    #global s_dpid = 0
    C = 0

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
        self.bandwidths = defaultdict(lambda: defaultdict(lambda: DEFAULT_BW))
        #ADICIONADO 22/09/2018
        ##################################################
        self.monitor_thread = hub.spawn(self._monitor)
        self.eventos = []
        ##################################################

    #Deep Field Search
    def get_paths(self, src, dst):
        '''
        Get all paths from src to dst using DFS algorithm    
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
        print
        print "Available paths from get path ", src, " to ", dst, " : ", paths
        print
        return paths

    def get_link_cost(self, s1, s2):
        '''
        Get the link cost between two switches 
        '''        
        e1 = self.adjacency[s1][s2]
        e2 = self.adjacency[s2][s1]
        bl = min(self.bandwidths[s1][e1], self.bandwidths[s2][e2])
        ew = REFERENCE_BW/bl
        
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
        #print ("get optimal path")
        paths = self.get_paths(src, dst)
        #print ("get_optimal_path resultado do get_path ", paths)
        paths_count = len(paths) if len(
            paths) < MAX_PATHS else MAX_PATHS
        retorno = sorted(paths, key=lambda x: self.get_path_cost(x))[0:(paths_count)]
        #print
        #print ("get the most optimal paths", retorno)
        return sorted(paths, key=lambda x: self.get_path_cost(x))[0:(paths_count)]

    def add_ports_to_paths(self, paths, first_port, last_port):
        '''
        Add the ports that connects the switches for all paths
        '''
        #print ("add port to path is called")
        #print ("paths", paths)
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

#    def generate_openflow_gid(self):
#        '''
#    #    Returns a random OpenFlow group id
#    #    '''
#        n = random.randint(0, 2**32)
#        while n in self.group_ids:
#            n = random.randint(0, 2**32)
#        return n

    def install_paths(self, src, first_port, dst, last_port, ip_src, ip_dst):
        computation_start = time.time()
        paths = self.get_optimal_paths(src, dst)
        pw = []
                
        #print "Variavel paths = get_optimal_paths: ", paths
        for path in paths:         
            pw.append(self.get_path_cost(path))
          #  print path, "cost = ", pw[len(pw) - 1]          
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

                #GROUP 
                print ("Porta de saida: ",out_ports) 

                #if len(out_ports) > 1:
                #    group_id = None
                #    group_new = False
                #    print "datapath tiver mais de um caminho"

                #    if (node, src, dst) not in self.multipath_group_ids:
                #        group_new = True
                #        self.multipath_group_ids[
                #            node, src, dst] = self.generate_openflow_gid()
                #    group_id = self.multipath_group_ids[node, src, dst]
                #    print "self.multipath_group_ids[node, src, dst]", self.multipath_group_ids[node, src, dst]
                        #print

                #    buckets = []
                #    print "node at ",node," out ports : ",out_ports
                #    for port, weight in out_ports:
                #        bucket_weight = int(round((1 - weight/sum_of_pw) * 10))
                #        bucket_action = [ofp_parser.OFPActionOutput(port)]
                #        buckets.append(
                #            ofp_parser.OFPBucket(
                #                weight=bucket_weight,
                #                watch_port=port,
                #                watch_group=ofp.OFPG_ANY,
                #                actions=bucket_action
                #            )
                #        )

                #    if group_new:
                #        req = ofp_parser.OFPGroupMod(
                #            dp, ofp.OFPGC_ADD, ofp.OFPGT_SELECT, group_id,
                #            buckets
                #        )
                #        dp.send_msg(req)
                #    else:
                #        req = ofp_parser.OFPGroupMod(
                #            dp, ofp.OFPGC_MODIFY, ofp.OFPGT_SELECT,
                #            group_id, buckets)
                #        dp.send_msg(req)

                #    actions = [ofp_parser.OFPActionGroup(group_id)]

                #    self.add_flow(dp, 32768, match_ip, actions)
                #    self.add_flow(dp, 1, match_arp, actions)

                #elif len(out_ports) == 1:
                print "datapath tive apenas 1 caminho:"
                print
                actions = [ofp_parser.OFPActionOutput(out_ports[0][0])]
                
                self.add_flow(dp, 32768, match_ip, actions)
                self.add_flow(dp, 1, match_arp, actions)
        #print "Path installation finished in ", time.time() - computation_start 
        return paths_with_ports[0][src][1]

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
        
        print colored('datapath.id Switch Features', 'blue')
        print datapath.id

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

        pkt = packet.Packet(msg.data)
        eth = pkt.get_protocol(ethernet.ethernet)
        arp_pkt = pkt.get_protocol(arp.arp)
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

        out_port = ofproto.OFPP_FLOOD
        
        if arp_pkt:
            src_ip = arp_pkt.src_ip
            dst_ip = arp_pkt.dst_ip
            #print (arp_pkt)
            if arp_pkt.opcode == arp.ARP_REPLY:
                self.arp_table[src_ip] = src
                print
                h1 = self.hosts[src]
                h2 = self.hosts[dst]                              
                out_port = self.install_paths(h1[0], h1[1], h2[0], h2[1], src_ip, dst_ip)
                #print colored('(h1[0], h1[1], h2[0], h2[1], src_ip, dst_ip)','blue')
                #print (h1[0], h1[1], h2[0], h2[1], src_ip, dst_ip)
                self.install_paths(h2[0], h2[1], h1[0], h1[1], dst_ip, src_ip) # reverse
            elif arp_pkt.opcode == arp.ARP_REQUEST:
                if dst_ip in self.arp_table:
                    self.arp_table[src_ip] = src
                    dst_mac = self.arp_table[dst_ip]                     
                    h1 = self.hosts[src]
                    h2 = self.hosts[dst_mac]
                    out_port = self.install_paths(h1[0], h1[1], h2[0], h2[1], src_ip, dst_ip)                    
                    #print colored('h1[0], h1[1], h2[0], h2[1], src_ip, dst_ip', 'green')
                    #print (h1[0], h1[1], h2[0], h2[1], src_ip, dst_ip)                    
                    self.install_paths(h2[0], h2[1], h1[0], h1[1], dst_ip, src_ip) # reverse
                       
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
        #print ev.link.src
        s1 = ev.link.src
        s2 = ev.link.dst
        #print ("s1 = ev.link.src", s1)
        #print ("s2 = ev.link.dst", s2)
        print '\033[1;34;47m Link Switch', s1.dpid, 'Porta', s1.port_no, 'Up\033[1;m'
        self.adjacency[s1.dpid][s2.dpid] = s1.port_no
        self.adjacency[s2.dpid][s1.dpid] = s2.port_no

    @set_ev_cls(event.EventLinkDelete, MAIN_DISPATCHER)
    def link_delete_handler(self, ev):
        global dp, s_dpid
         
        s1 = ev.link.src
        s2 = ev.link.dst
        #print '\033[1;31;47m Link Switch', s1.dpid, 'Porta', s1.port_no, 'Down\033[1;m'
        print
        #if dp.id == s_dpid:
        #    for n in [0, 1]:
        #        self.remove_flows(dp, n)
        #Exception handling if switch already deleted
        try:
            del self.adjacency[s1.dpid][s2.dpid]
            del self.adjacency[s2.dpid][s1.dpid]
        except KeyError:
            pass    

#--------------------------------------------------------------------------------

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
                #self.logger.debug('register datapath: %016x', datapath.id)
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


    #ADICIONADO 23/09/2018
    #Exibe o status de portas do switch
    #classe utilizada ryu.controller.controller.Datapath
    #ryu.ofproto.ofproto_v1_3_parser.OFPPort
    #ryu.ofproto.ofproto_v1_3
    #flag utilizada do ev.msg.desc.state --> OFPPS_LINK_DOWN
    ############################################################# 
    @set_ev_cls(ofp_event.EventOFPPortStatus, MAIN_DISPATCHER)
    def port_status_handler(self, ev):     
        global C, src, dst, first_port, last_port

        msg = ev.msg
        dp = msg.datapath #dp.id
        ofp = dp.ofproto
        
        #if msg.desc.state == 1:            
        if msg.reason == ofp.OFPPR_ADD:
            reason = 'ADD'
            #continue
        if msg.reason == ofp.OFPPR_DELETE:
            reason = 'DELETE'
            #continue
        if msg.reason == ofp.OFPPR_MODIFY:
            #reason = 'MODIFY'
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

            if (C > 0 and src and dst):
                print "instalando novo caminho"
                #out_port = self.install_paths(src, first_port, dst, last_port, ip_src, ip_dst)
            else: pass
            C += 1 #incrementa a variável de controle
            if (C == 2): C = 0 #zera a variavel de controle ao alcançar 2
        if msg.desc.state == ofp.OFPPS_BLOCKED: pass
        if msg.desc.state == ofp.OFPPS_LIVE: pass
        if msg.desc.state == ofp.OFPPC_NO_PACKET_IN: pass
        else:
            reason = 'UNKNOWN'
        
    ##############################################################

    #ADICIONADO 23/09/2018
    #Captura a topologia da rede
    ##############################################################
    @set_ev_cls(event.EventLinkDelete, MAIN_DISPATCHER)
    @set_ev_cls(event.EventLinkAdd, MAIN_DISPATCHER)
    def get_topology_data(self, ev):
        #print "get_topology"
        switch_list = get_all_switch(self.topology_api_app)
        myswitches = [switch.dp.id for switch in switch_list]

        for switch in switch_list:
            datapath_list[switch.dp.id] = switch.dp

        links_list = get_all_link(self.topology_api_app)
        mylinks = [(link.src.dpid, link.dst.dpid, link.src.port_no, link.dst.port_no) for link in links_list]
        for s1, s2, port1, port2 in mylinks:
            self.adjacency[s1][s2] = port1
            self.adjacency[s2][s1] = port2
            #print "Switch: ", s1, " Porta: ", port1, "<--->", "Switch: ", s2, " Porta: ", port2

    ##############################################################
    
  
    #ADICIONADO 25/09/2018
    ##############################################################
    #def remove_flows(self, datapath, table_id):
    #    
    #    parser = datapath.ofproto_parser
    #    ofproto = dp.ofproto
    #    empty_match = parser.OFPMatch()
    #    instructions = []
    #    flow_mod = self.remove_table_flows(dp, table_id, empty_match, 
    #            instructions)
    #    print "deletando entradas de fluxos da tabela:", table_id
    #    datapath.send_msg(flow_mod)
    ##############################################################

    #ADICONADO 25/09/2018
    ##############################################################
    #def remove_table_flows(self, datapath, table_id, match, instructions):
    #    """create OFP flow mod message to remove flows from table."""
    #    
    #    #print "dp remove_tables_flows", dp
    #    ofproto = datapath.ofproto
    #    #print colored('dp.id remove table flow','blue')
    #    #print dp.id
    #            
    #    flow_mod = datapath.ofproto_parser.OFPFlowMod(dp, 0, 0, table_id,
    #            ofproto.OFPFC_DELETE, 0, 0, 1, ofproto.OFPCML_NO_BUFFER,
    #            ofproto.OFPP_ANY, ofproto.OFPG_ANY,
    #            0, match, instructions)

    #    return flow_mod
    ##############################################################

    #ADICIONADO
    ###############################################################
    #eventos = [event.EventSwitchEnter, event.EventSwitchLeave, event.EventPortAdd,
    #        event.EventPortDelete, event.EventPortModify, event.EventLinkAdd,
    #        event.EventLinkDelete]

    #@set_ev_cls(eventos)
    #def event_handler(self, ev):
        #print "event_handler ", ev
        
