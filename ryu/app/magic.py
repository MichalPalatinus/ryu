from ryu.base import app_manager
from ryu.ofproto import ofproto_v1_3_parser
from ryu.controller import ofp_event
from ryu.controller import dpset
from ryu.controller import handler
from ryu.controller.handler import CONFIG_DISPATCHER, MAIN_DISPATCHER, DEAD_DISPATCHER
from ryu.controller.handler import set_ev_cls
from ryu.ofproto import ofproto_v1_3
from ryu.ofproto import ofproto_v1_3_parser
from ryu.ofproto import ether
from ryu.lib.packet import packet
from ryu.lib.packet import ethernet
from ryu.lib.packet import ipv4
from ryu.lib.packet import icmp
from ryu.lib.packet import arp
from ryu.ofproto import ofproto_parser
from ryu.ofproto import inet
from ryu.app.wsgi import ControllerBase, WSGIApplication
from webob import Response
from webob import Request
from cgi import parse_qs
#from networkx.readwrite import json_graph
import struct
import sys
import logging
import networkx as nx
from networkx.readwrite import json_graph
import json
import random
import socket
import ast
import array
import inspect
import pprint
import time
import urlparse
import datetime
import os
import subprocess
#import thread
#import sched
from ryu.lib import ofctl_v1_3
###Global variable initialization

##logger
##Usage: LOG.debug() / LOG.warning() / LOG.error()
LOG = logging.getLogger('ryu.app.experimenter_switch_in_progres.py')

##Static definition of of ports for vGSN and BSS
##TODO: Remove static definition(Either self-discovery or Yang)
BSS_PHY_PORT = 1
VGSN_PHY_PORT = 2
INET_PHY_PORT = None

##IP adresses used when controller generates packets
DISCOVERY_IP_SRC='10.1.1.252'
DISCOVERY_IP_DST='10.1.1.253'
##Due to nature of ARP protocol, DISCOVERY_ARP_IP must be in same subnet as host you want to discover
DISCOVERY_ARP_IP='172.20.255.99'
SNDCP_FRAG_WARNING_SRC_IP='224.42.42.3'

##Experimenter ID (self-assigned)
GPRS_SDN_EXPERIMENTER = int("0x42", 16)

##Number of OF table that contains GPRS-related flow rules on the way OUT
OF_GPRS_TABLE = 2

##Number of OF table that contains GPRS-related flow rules on th way IN
OF_GPRS_TABLE_IN = 4

##Number of OF table that contains MAC_TUNNEL-related flow rules
MAC_TUNNEL_TABLE = 3

##Hardcode IP adresses of our GPRS nodes
BSS_IP="192.168.27.125"
BSS_PORT=23000
VGSN_IP="192.168.27.2"
VGSN_PORT=23000

##Forwarders assigned to special groups
##XXX:Review usefulness
BSS_EDGE_FORWARDER=[0xa]
INET_EDGE_FORWARDER=[0xc]

##Generation of IP adresses  asigned to devices on PDP CNT actiavation
##XXX:Modify pool if needed
IP_POOL=[]
for i in range(100,199):
    IP_POOL.append('172.20.85.'+str(i))


##List of APNs in network
APN_POOL=[]
FREE_INTERFACES = {"14_3":"apn1", "13_4":"apn2"}
##List of BSSs in network
#XXX:for now it's static
BSS_POOL=['901-70-1-0']
#BSS_POOL=['231-1-1-0']

##List of active PDP CNTs
ACTIVE_CONTEXTS = []

##List of active tunnels
ACTIVE_TUNNELS=[]

##List of inactive tunnels (those that could not be created due to lack of path between end nodes)
INACTIVE_TUNNELS=[]

##List of used Tunnel identifiers
TID_POOL = []

##List of forwarders in topology
FORWARDERS = []

##FLOW TYPES VALUES
APN_SPECIAL=1
TOPOLOGY_DISCOVERY=2
ACCESS_EDGE_ADITIONAL=3
TUNNEL_RULES=4
PDP_FLOWS=5
USER_DEFINED=6

##ARRAY FOR PORTS STATISTICS
FWD_PSTATS = {}
FWD_FSTATS = {}
PREPINACE = []

class Stats:
    def __init__(self, port_no, rx_packets, tx_packets, rx_bytes, tx_bytes, rx_dropped, tx_dropped, rx_errors, tx_errors, rx_frame_err, rx_over_err, rx_crc_err, collisions, duration_sec, duration_nsec):
        self.port_no = port_no
        self.rx_packets = rx_packets
        self.tx_packets = tx_packets
        self.rx_bytes = rx_bytes
        self.tx_bytes = tx_bytes
        self.rx_dropped = rx_dropped
        self.tx_dropped = tx_dropped
        self.rx_errors = rx_errors
        self.tx_errors = tx_errors
        self.rx_frame_err = rx_frame_err
        self.rx_over_err = rx_over_err
        self.rx_crc_err = rx_crc_err
        self.collisions = collisions
        self.duration_sec = duration_sec
        self.duration_nsec = duration_nsec

class flowStats:
    def __init__(self, table_id, duration_sec, duration_nsec, priority, idle_timeout, hard_timeout, flags, cookie, packet_count, byte_count, match, instructions):
        self.table_id=table_id
        self.duration_sec = duration_sec
        self.duration_nsec = duration_nsec
        self.priority = priority
        self.idle_timeout = idle_timeout
        self.hadr_timeout = hard_timeout
        self.flags = str(flags)
        self.cookie = cookie
        self.packet_count = packet_count
        self.byte_count = byte_count
        self.match = match._fields2
        #self.instructions = instructions

class prepinac:
    def __init__(self, p, m, instruct, prep):
        self.p=p
        self.m=m
        self.instruct=instruct
        self.prep=prep

class flow:
    def __init__(self, priority, match, inst, flow_type, cookie):
        #LOG.debug("MICHAL: Initializing a new flow")
        self.priority = priority
        self.match = match 
        self.inst = inst
        self.flow_type = flow_type
        self.cookie = cookie


class table:

    def __init__(self, table_id):
        #LOG.debug("MICHAL: Initializing a new table.")
        self.id = table_id
        self.flows = []   

    def add_flow(self, priority, match, inst, flow_type, cookie):
        LOG.debug("MICHAL: Adding flow to table.")
        self.flows.append(flow(priority, match, inst, flow_type, cookie))


class forwarder:
    def __init__(self, datapath):
        self.id = datapath.id
        self.tables = []
 
    def add_flow(self, table_id, priority, match, inst, flow_type, cookie):
        if any(t.id == table_id for t in self.tables):
            for t in self.tables:
                if t.id == table_id:
                    t.flows.append(flow(priority, match, inst, flow_type, cookie))
        else:
            self.tables.append(table(table_id))
            for t in self.tables:
                if t.id == table_id:
                    t.flows.append(flow(priority, match, inst, flow_type, cookie))



class Contexts:
    def __init__(self, context_array= None):
        self.context_array = context_array

cont = Contexts()

###Topology and topology-related classes

class link:
    """Link between two nodes in network, has only one direction
       and is defined by forwarder(dpid) and its egress port(port_out)

       Keyword arguments:
           dpid -- datapath ID
           port_out -- Egress port
    """
    def __init__(self, dpid, port_out):
        self.dpid = dpid
        self.port_out = port_out


class tunnel:
    """
    Tunnel contains endpoints (BSS/APN), path between these nodes in both directions(IN/OUT)
    and identifiers for these paths
 
    Keyword arguments:

        _bss_ -- BSS endpoint idetifier in topology (can be string)
        _apn_ -- APN endpoint (must be of apn class)
        tid_out -- Tunnel identifier in outgoing direction (MAC addr. format)
        tid_in -- Tunnel identifier in incoming dirrection (MAC addr. format)
        path_out -- list of links for outgoing direction
        path_in -- list of links for incoming direction
    """
    def __init__(self,_bss_, _apn_, _tid_out, _tid_in, path_out=None, path_in=None):
      self.bss = _bss_
      self.apn = _apn_
      self.tid_out = _tid_out
      self.tid_in = _tid_in
      self.path_in = path_in
      self.path_out = path_out


class apn:
    """
    Acces point defined by its name, IP and mac addr. APN's only mandatory arg. is name
    IP and mac addr. are resolved with DNS/ARP provided there is DNS entry available

    Keyword arguments:
        name -- Acces Point Name (string)
        ip_addr -- IP address of APN
        eth_addr -- MAC address of APN
    """
    def __init__(self, name, ip_addr=None, eth_addr=None):
        self.name = name
        self.ip_addr = ip_addr
        self.eth_addr = eth_addr

##XXX:maybe should be created from config file (Yang?)
APN_POOL.append(apn('internet'))
#APN_POOL.append(apn('mms'))



class topology():
    """ 
    Topology class maintains graph of links between all nodes in network
    """
    OFP_VERSIONS = [ofproto_v1_3.OFP_VERSION]
    _CONTEXTS = {
        'dpset': dpset.DPSet
    }

    def __init__(self):
        self.StaticGraph=nx.DiGraph()
        self.DynamicGraph=nx.DiGraph()
        ##Static adding of nodes into topology (run reload_topology() after last modification)
        ##format:       From node
        ##              |  To node
        ##              |   |   Via port
        ##              V   V   V
        ##self.add_link(0xa,0xb,3)

        ##Below is static initialization of our test topology
        ##Uncomment in case of self-discovery fail
        ##0xa <-> 0xb
        #self.add_link(0xa,0xb,3)
        #self.add_link(0xb,0xa,1)
        
        ##0xa <-> 0xd
        #self.add_link(0xa,0xd,4)
        #self.add_link(0xd,0xa,1)
    
        ##0xb <-> 0xc
        #self.add_link(0xb,0xc,3)
        #self.add_link(0xc,0xb,1)

        ##0xb <-> 0xd
        #self.add_link(0xb,0xd,2)
        #self.add_link(0xd,0xb,2)

        ##0xc <-> 0xe
        #self.add_link(0xc,0xe,2)
        #self.add_link(0xe,0xc,2)

        ##0xd <-> 0xe
        #self.add_link(0xd,0xe,3)
        #self.add_link(0xe,0xd,1)
      
        ##TODO: Remove static nodes (BSS/vGSN remaining)

        ##Links between edge forwarders and non-SDN nodes
        ##BSS node <-> 0xa
        self.add_link('901-70-1-0',0xa,1)
        self.add_link(0xa,'901-70-1-0',1)
        #vGSN node <-> 0xa
        #XXX:self.add_link(1,0xa,1)
        #XXX:self.add_link(0xa,1,2)
        #internet <-> 0xc
        #self.add_link('internet',0xc,1)
        #self.add_link(0xc,'internet',3)
        self.reload_topology()

        
    def dump(self):
        data = json_graph.node_link_data(self.DynamicGraph)
        return json.dumps(data)

    def add_forwarder(self, fwID):
        self.StaticGraph.add_node(fwID)

    def del_forwarder(self, fwID):
        self.DynamicGraph.remove_node(fwID)

    def add_link(self, fwID1, fwID2, ifnumm):
        self.StaticGraph.add_edge(fwID1, fwID2, interf=ifnumm)

    def link_down(fwID1, fwID2):
        self.DynamicGraph.remove_edge(fwID1, fwID2)

    def link_up(fwID1, fwID2):
        self.DynamicGraph.edge[fwID1][fwID2] = StaticGraph[fwID1][fwID2]
	
    def forwarder_down(self, fwID):
        self.DynamicGraph.remove_edges_from(nx.edges(DynamicGraph, fwID))

    def forwarder_up(self, fwID):
        self.DynamicGraph.add_edges_from(StaticGraph.edges(fwID, data=True))

    def reload_topology(self):
        self.DynamicGraph = self.StaticGraph.to_directed()

    def get_tunnel(self, fwID1, fwID2):
        hops = nx.shortest_path(self.DynamicGraph, fwID1, fwID2)
        path = []
        tunnelID=get_tid()
        for k in hops[1:-1]:
            path.append(link(k,self.DynamicGraph[k][hops[hops.index(k)+1]]['interf']))
        return path
  
     
##Topology initialization
topo = topology()
f = open('/root/ryu/ryu/app/OF_actions.txt', 'r')
actions_dictionary=f.read().replace('\n', ',')
f.close()
f = open('/root/ryu/ryu/app/OF_instructions.txt', 'r')
inst_dictionary=f.read().replace('\n', ',')
f.close()
f = open('/root/ryu/ryu/app/OF_match_fields.txt', 'r')
matches_dictionary=f.read().replace('\n', ',')
f.close()

## convert IMSI string into byte array
def imsi_to_bytes(imsi_string):
  imsi_digits = list(imsi_string)
  imsi_bytes = [0,0,0,0,0,0,0,0]
  digit_no = 0

  # imsi is too long... fetch only first 15 characters and nag..
  if len(imsi_digits) > 15:
    print "imsi too long... "
    imsi_digits = imsi_digits[:15]

  # lower 3 bits indicate IMSI number... (0x1)
  imsi_bytes[0] = 0x1

  # convert string to bytes...
  for digit in imsi_digits:
    byte_no = (digit_no+1) / 2;
    if digit_no % 2:
      imsi_bytes[byte_no] |= int(digit, 16)
    else:
      imsi_bytes[byte_no] |= int(digit, 16) << 4
    digit_no += 1

  # if we have odd number of digits, set 4th bit to 1
  # and fill last octets upper nibble with 0xf
  if not len(imsi_digits)%2:
    imsi_bytes[0] |= 0x8
    imsi_bytes[(digit_no+1)/2] |= 0xf0

  return imsi_bytes

def _arp_send(dp, port_out, arp_code,  ip_sender, ip_target, eth_dst='ff:ff:ff:ff:ff:ff',eth_src=None,eth_target='00:00:00:00:00:00'):
    """
    Generates arp request and sends it out of 'port_out' of 'dp' forwarder

    Keyword arguments:
        dp -- Datapath
        port_out -- Port on forwarder (dp) used to spit out packet
        arp_code -- ARP OP code(1==reques, 2==reply)
        ip_sender -- Senders IP addres
        eth_dst  -- Ethernet destination address (in case of request, broadcast address is used)
        eth_src -- Ethernet source address. If none provided, it's generated from Datapath ID of sending forwarder (dp)
        eth_target -- Final recipients Ethernet address(in case of request, zeroed out address is used)
        ip_target --  Final recipients IP address
    """

    ofp = dp.ofproto
    parser = dp.ofproto_parser
    pkt = packet.Packet()

    ##If no src_mac was provided we generate one from Datapath ID of forwarder that recieved message
    ##If Datapath ID starts with zeros we cannot use it as legit MAC address
    ##Second hex digit must be 2 to indicate localy administered non-multicast address 
    if eth_src == None:
        str_hex_dpid = str(hex(dp.id)).rstrip('L').lstrip('0x')
        if len(str_hex_dpid) < 11:
            eth_src ='02'
            for i in range(10-len(str_hex_dpid)):
                eth_src += '0'
            eth_src += str_hex_dpid
        else:
            eth_src = dp.id
    
    eth = ethernet.ethernet(eth_dst, eth_src, ether.ETH_TYPE_ARP)
    arp_req = arp.arp_ip(arp_code, eth_src, ip_sender, eth_target, ip_target)

    pkt = packet.Packet()
    pkt.add_protocol(eth)
    pkt.add_protocol(arp_req)
    pkt.serialize()
    actions=[parser.OFPActionOutput(port_out)]
    out=parser.OFPPacketOut(datapath=dp, buffer_id=ofp.OFP_NO_BUFFER, in_port=ofp.OFPP_CONTROLLER, actions=actions, data=pkt.data)
    dp.send_msg(out)


def _icmp_send(dp, port_out, ip_src=DISCOVERY_IP_SRC, ip_dst=DISCOVERY_IP_DST, 
               eth_src='02:b0:00:00:00:b5', eth_dst='02:bb:bb:bb:bb:bb',
               icmp_type=8, icmp_code=0):
    """
    Generates ICMP packet and sends it out of 'port_out' on forwarder 'dp'
 
    Keyword arguments:
        dp -- Datapath
        port_out -- Port on forwarder (dp) used to spit out packet
        ip_src -- IP address of sender
        ip_dst  -- IP address of recipient
        eth_src -- Ethernet address of source (Default is 02:b0:00:00:00:b5 because none wanted to have 0xb00b5 as experimenter ID)
        eth_dst -- Ethernet destiation address (probably to be reworked)
        icmp_type -- ICMP type, default is 8 which is Echo
        icmp_code -- ICMP code, default is 0 which is No Code

    """
    LOG.debug("MICHAL: Sending ICMP packet")
    ofp = dp.ofproto
    parser = dp.ofproto_parser
    pkt = packet.Packet()
    pkt.add_protocol(ethernet.ethernet(ethertype=0x0800,
                                       dst=eth_dst,
                                       src=eth_src))

    pkt.add_protocol(ipv4.ipv4(dst=ip_dst,
                               src=ip_src,
                               proto=1))

    ##TODO: Rework payload and codes to properly work with Fragmentation needed
    pkt.add_protocol(icmp.icmp(type_=icmp_type,
                               code=icmp_code,
                               csum=0,
                               data=icmp.echo(1,1,"{'dpid' : "+str(dp.id)+",'port_out' : "+str(port_out)+"}")))
    pkt.serialize()
    data=pkt.data
    actions=[parser.OFPActionOutput(port_out,0)]
    out=parser.OFPPacketOut(datapath=dp, buffer_id=ofp.OFP_NO_BUFFER, in_port=ofp.OFPP_CONTROLLER, actions=actions, data=data)
    dp.send_msg(out)


def _icmp_parse_payload(pkt):
    """
    Used to parse payload of ICMP packets used for self-discovery which contains dictionary

    Keyword arguments:
        pkt -- ICMP paket
    """

    payload = ''
    icmp_pkt = pkt.get_protocol(icmp.icmp)
    for char in icmp_pkt.data.data:
        payload+=(chr(char))
    parsed_payload = ast.literal_eval(payload.rstrip('\0'))
    return(parsed_payload)


def get_tid():
    """
    Generator of Tunnel identifiers (in MAC addr. format)

    """

    mac_char='0123456789abcdef'
    mac_addr='02:'
    available=0
    while available == 0:
        for i in range(5):
            for y in range(2):
                mac_addr = mac_addr + random.choice(mac_char)
            mac_addr = mac_addr + ':'
   
        mac_addr = mac_addr[:-1]
        if mac_addr not in TID_POOL:
            available = 1
    TID_POOL.append(mac_addr)
    return(mac_addr)





class PDPContext:
    """
    Class used to store active PDP CNTs

    Keyword arguments:

    bvci -- BSSGP Virtual Connection Identifier
    tlli -- Temporary Logical Link Identifier
    sapi -- Service Access Point Identifier
    nsapi -- Network Service Acces Point Indetifier
    tid_out -- Tunnel identifier this context uses to get to APN
    tid_in -- Tunnel identifier this context uses on the way back IN
    """

    def __init__(self, bvci, tlli, sapi, nsapi, tid_out, tid_in, client_ip, imsi, drx_param):
        self.bvci = bvci
        self.tlli = tlli
        self.sapi = sapi
        self.nsapi = nsapi
        #TODO: QoS a tunnel treba premysliet
        self.tid_out = tid_out
        self.tid_in = tid_in
        self.client_ip = client_ip
        self.imsi = imsi
        self.drx_param = drx_param


#class Get_stats(threading.Thread):
        
#        def run():
#            LOG.debug('MICHAL: bezi nit')
#            time.sleep(10)

#thread1 = Get_stats
#thread1.run()

class GPRSControll(app_manager.RyuApp):
    """
    Main class of controller application
    """

    OFP_VERSIONS = [ofproto_v1_3.OFP_VERSION]
    _CONTEXTS = {
        'dpset': dpset.DPSet,
        'wsgi': WSGIApplication
    }

    def __init__(self, *args, **kwargs):
        super(GPRSControll, self).__init__(*args, **kwargs)

        global dpset
        dpset = kwargs['dpset']
        wsgi = kwargs['wsgi']
        self.waiters = {}
        self.data = {}
        self.data['dpset'] = dpset
        self.data['waiters'] = self.waiters
        mapper = wsgi.mapper
        #thread.start_new_thread(self.collect_stats, [])
        
        ##RestCall reffers to class that holds methods/functions (WTF python calls them),
        ##that can be called via REST interface
        wsgi.registory['RestCall'] = self.data
       
        ##path holds string that is used to adress REST calls
        ##e.g.: localhost:8080/gprs/info/whatever
        path = '/gprs'
         
        ##mapper.connect defines which method is executed for particular REST call
        uri = path + '/info/{opt}'
        mapper.connect('stats',uri,
                       controller=RestCall, action='info',
                       conditions=dict(method=['GET']))


        uri = path + '/pdp/{cmd}'
        mapper.connect('stats',uri,
                       controller=RestCall, action='mod_pdp',
                       conditions=dict(method=['GET', 'HEAD']))

        uri = path + '/pdp_dump'
        mapper.connect('statc', uri,
                       controller=RestCall, action='dump_active_pdps',
                       conditions=dict(method=['GET']))

        uri = '/topology/dump'
        mapper.connect('stats',uri,
                       controller=RestCall, action='dump_topology',
                       conditions=dict(method=['GET', 'HEAD']))

        uri = '/oftables/dump/{opt}'
        mapper.connect('stats', uri,
                       controller=RestCall, action='dump_oftables', 
                       conditions=dict(method=['GET', 'HEAD']))


        #Testing
        uri =  '/test/info'
        mapper.connect('stats', uri,
                        controller=RestCall, action='test_info',
                        conditions=dict(method=['GET']))      

        uri = '/tunnels/active/dump'
        mapper.connect('stats', uri,
                       controller=RestCall, action='dump_active_tunnels',
                       conditions=dict(method=['GET', 'HEAD']))


        uri = '/add_flow/{opt}'
        mapper.connect('stats',uri,
                       controller=RestCall, action='user_added_flow',
                       conditions=dict(method=['GET', 'HEAD']))

        uri = '/delete_flow/{opt}'
        mapper.connect('stats', uri,
                       controller=RestCall, action='delete_flow',
                       conditions=dict(method=['GET', 'HEAD']))


        uri = '/dump_port_stats'
        mapper.connect('stats', uri,
                       controller=RestCall, action='dump_statistics',
                       conditions=dict(method=['GET', 'HEAD']))

        uri = '/dump_flow_stats'
        mapper.connect('stats', uri,
                       controller=RestCall, action='dump_flow_statistics',
                       conditions=dict(method=['GET', 'HEAD']))
                       
        uri = '/add_apn/{opt}'
        mapper.connect('stats', uri,
                       controller=RestCall, action='add_apn',
                       conditions=dict(method=['GET', 'HEAD']))
                       
        uri = '/send_icmp/{opt}'
        mapper.connect('stats', uri,
                       controller=RestCall, action='send_icmp_packet',
                       conditions=dict(method=['GET', 'HEAD']))

        ## DNS ressolution of IP address of PDP CNTs if it's not already defined
        ## !!! MAKE SURE you have valid DNS entry available in /etc/hosts or DNS server !!!
        for apn in APN_POOL:
            if apn.ip_addr==None:
                try:
                    ip_addr = str(socket.gethostbyname(apn.name))
                    apn.ip_addr = ip_addr
                    LOG.debug('Resolved APN '+apn.name+' : '+apn.ip_addr)
                except socket.gaierror:
                    LOG.warning('Error while resolving apn name "'+apn.name+'"' )


    def on_edge_inet_dp_join(self, dp, port):
        """ Add special rules for forwader on edge (APN-side) of network

            Keyword arguments:
                dp -- datapath
                port -- ID of port with APN on the other side
        """

        ofp = dp.ofproto
        parser = dp.ofproto_parser

        ##All ARP requests that come from APN are forwarded to Controller which then handle them
        ##TODO: Pass also APN object so we can put it to debug log :)
        LOG.debug('TOPO MNGR: Redirecting all ARP req from APN to controller by OFrule on forwarder: ' + str(dp.id))
        match = parser.OFPMatch(in_port=port, eth_type=0x0806, arp_op=1)
        actions = [ parser.OFPActionOutput(ofp.OFPP_CONTROLLER) ]
        inst = [ parser.OFPInstructionActions(ofp.OFPIT_APPLY_ACTIONS, actions) ]
        req = parser.OFPFlowMod(datapath=dp, priority=10, match=match, instructions=inst)
        self.update_flows(dp, req, 0, 10, match, inst, APN_SPECIAL, 0)

    def on_inner_dp_join(self, dp):
        """ Add new inner (BSS side) forwarder joined our network.
        
        Keyword arguments:
            dp -- datapath

        TODO:
          VGSN inside our SDN network -- routing of GPRS-NS traffic

        """
        ofp = dp.ofproto
        parser = dp.ofproto_parser
        LOG.debug("MICHAL: ID of datapath = " + str(dp.id))
        #Deletion of already existing OF flows
        LOG.debug('TOPO MNGR: Deleting flow table configuration of newly added forwarder ID: ' + str(dp.id) )
        dp.send_msg(parser.OFPFlowMod(datapath=dp, command=ofp.OFPFC_DELETE))
        dp.send_msg(parser.OFPFlowMod(datapath=dp, command=ofp.OFPFC_DELETE, table_id=OF_GPRS_TABLE))
        #TODO: Shall we wipe-out OFconfig data as well?



        ##########################
        ## Main table (0)
        ## TODO:change to echo only!
       
        ## Networks self-discovery using icmp messages
        ## Redirect all pings with ipv4_dst=DISCOVERY_IP_DST to controller
        LOG.debug('TOPO MNGR: Installing ICMP topology discovery flows on forwarder: ' + str(dp.id))       
        match = parser.OFPMatch(eth_type=0x0800, ip_proto=1, icmpv4_type=8, icmpv4_code=0, ipv4_dst=DISCOVERY_IP_DST)
        actions = [ parser.OFPActionOutput(ofp.OFPP_CONTROLLER) ]
        self.add_flow(dp, 100, match, actions, TOPOLOGY_DISCOVERY, 0, 0)
         
        ##Controller uses ARP to resolve mac_addresses of APNs
        ## FIXED: All ARPs replies are redirected to the controller regardless of the target IP
        LOG.debug('TOPO MNGR: Installing ARP APN discovery flows on forwarder: ' + str(dp.id))
        match= parser.OFPMatch(eth_type=0x0806, arp_op=2)
        actions = [ parser.OFPActionOutput(ofp.OFPP_CONTROLLER)]
        self.add_flow(dp, 100, match, actions, TOPOLOGY_DISCOVERY, 0, 0)

 

        ##Following rules are applied only on forwarders bellonging to BSS_EDGE_FORWARDER group
        ##Rules are applied based on priority of match (highest priority first)
        if dp.id in BSS_EDGE_FORWARDER:
            
            LOG.debug('TOPO MNGR: Forwarder: ' + str(dp.id) + ' is an access edge forwarder, installing aditional rules')
            ## UDP 23000 is GPRS-NS and all packets that match this are forwarded to OF_GPRS_TABLE flow table
            inst = [ parser.OFPInstructionGotoTable(OF_GPRS_TABLE) ]
            match = parser.OFPMatch(eth_type=0x0800,ip_proto=inet.IPPROTO_UDP, udp_dst=VGSN_PORT)
            req = parser.OFPFlowMod(datapath=dp, priority=200, match=match, instructions=inst)
            self.update_flows(dp, req, 0, 200, match, inst, ACCESS_EDGE_ADITIONAL, 0)  #nebola udana tabulka
            #dp.send_msg(req)            

            ## VGSN_PHY and BSS_PHY ports are bridged -- DHCP, ARP, Abis & stuff
            ## XXX: what if vGSN is not on same forwarder as BSS
            actions = [ parser.OFPActionOutput(VGSN_PHY_PORT) ]
            inst = [ parser.OFPInstructionActions(ofp.OFPIT_APPLY_ACTIONS, actions) ]
            match = parser.OFPMatch(in_port=BSS_PHY_PORT)
            req = parser.OFPFlowMod(datapath=dp, priority=10, match=match, instructions=inst)
            self.update_flows(dp, req, 0, 10, match, inst, ACCESS_EDGE_ADITIONAL, 0)
            #dp.send_msg(req)
            actions = [ parser.OFPActionOutput(BSS_PHY_PORT) ]
            inst = [ parser.OFPInstructionActions(ofp.OFPIT_APPLY_ACTIONS, actions) ]
            match = parser.OFPMatch(in_port=VGSN_PHY_PORT)
            req = parser.OFPFlowMod(datapath=dp, priority=10, match=match, instructions=inst)
            self.update_flows(dp, req, 0, 10, match, inst, ACCESS_EDGE_ADITIONAL, 0)
            #dp.send_msg(req)
   
            #################
            ## OF_GPRS-TABLE (2)
            ##TODO: BSS <-> vGSS separate tunnel for communication!
            ##TODO: deletion, modification od  PDP CNT

            ## if packet is not first segment  of user data packet (IS part of sndcp fragmented packet) it's DROPED
            match = parser.OFPMatch( sndcp_first_segment=0 )
            actions = [ ] 
            inst = [ parser.OFPInstructionActions(ofp.OFPIT_APPLY_ACTIONS, actions) ]
            req = parser.OFPFlowMod(datapath=dp, table_id=OF_GPRS_TABLE, priority=200, match=match, instructions=inst)
            self.update_flows(dp, req, OF_GPRS_TABLE, 200, match, inst, ACCESS_EDGE_ADITIONAL, 0)
            
            ## if packet is first segment of SNDCP packet with more than one segment, it's forwarded to controller
            ## when controller recieves such packet it sends ICMP fragmentation_needed to its sender and drops original
            match = parser.OFPMatch( sndcp_first_segment=1, sndcp_more_segments=1 )
            actions = [parser.OFPActionOutput(ofp.OFPP_CONTROLLER) ] 
            inst = [ parser.OFPInstructionActions(ofp.OFPIT_APPLY_ACTIONS, actions) ]
            req = parser.OFPFlowMod(datapath=dp, table_id=OF_GPRS_TABLE, priority=200, match=match, instructions=inst)
            self.update_flows(dp, req, OF_GPRS_TABLE, 200, match, inst, ACCESS_EDGE_ADITIONAL, 0)
    
            ##if it's SNDCP packet taht still wasnt matched (rules with higher priority are inserted on PDP CNT activation)
            ##we assume it's packet of unknown PDP CNT and we DROP it
            match = parser.OFPMatch( sndcp_first_segment=1 )
            actions = [ ]
            inst = [ parser.OFPInstructionActions(ofp.OFPIT_APPLY_ACTIONS, actions) ]
            req = parser.OFPFlowMod(datapath=dp, table_id=OF_GPRS_TABLE, priority=1, match=match, instructions=inst)
            self.update_flows(dp, req, OF_GPRS_TABLE, 1, match, inst, ACCESS_EDGE_ADITIONAL, 0)

            ##Everything else is Signalzation and is forwarded either to BSS or vGSN
            # XXX: co ak bss a vgsn nie su spolu na jednom DPID?
            actions = [ parser.OFPActionOutput(VGSN_PHY_PORT) ]
            inst = [ parser.OFPInstructionActions(ofp.OFPIT_APPLY_ACTIONS, actions) ]
            match = parser.OFPMatch(in_port=BSS_PHY_PORT)
            req = parser.OFPFlowMod(datapath=dp, table_id=OF_GPRS_TABLE, priority=0, match=match, instructions=inst)
            self.update_flows(dp, req, OF_GPRS_TABLE, 0, match, inst, ACCESS_EDGE_ADITIONAL, 0)

            actions = [ parser.OFPActionOutput(BSS_PHY_PORT) ]
            inst = [ parser.OFPInstructionActions(ofp.OFPIT_APPLY_ACTIONS, actions) ]
            match = parser.OFPMatch(in_port=VGSN_PHY_PORT)
            req = parser.OFPFlowMod(datapath=dp, table_id=OF_GPRS_TABLE, priority=0, match=match, instructions=inst)
            self.update_flows(dp, req, OF_GPRS_TABLE, 0, match, inst, ACCESS_EDGE_ADITIONAL, 0)

    def stats_reply_handler(self, ev):
        """
        This method iss responsible for generation of HTTP replies to the REST calls
        """
        msg = ev.msg
        dp = msg.datapath

        if dp.id not in self.waiters:
            return
        if msg.xid not in self.waiters[dp.id]:
            return
        lock, msgs = self.waiters[dp.id][msg.xid]
        msgs.append(msg)
        flags = 0
        if dp.ofproto.OFP_VERSION == ofproto_v1_3.OFP_VERSION:
            flags = dp.ofproto.OFPMPF_REPLY_MORE

        if msg.flags & flags:
            return
        del self.waiters[dp.id][msg.xid]
        lock.set()

    @set_ev_cls(ofp_event.EventOFPPacketIn)
    def _packet_in(self, ev):
        """
        This method handles are packets that arrive directly to Controller
        """

        dp = ev.msg.datapath
        ofp = dp.ofproto
        parser = dp.ofproto_parser
        match = ev.msg.match

        ##SNDCP packet with multiple fragments recieved - print warning, send ICMP fragmentation needed
        ##TODO: Not WOrking correctly
        if (match['eth_type'] == 0x0800 and match['ip_proto'] == inet.IPPROTO_UDP 
            and match['udp_dst'] == VGSN_PORT and match['sndcp_first_segment'] == 1 
            and match['sndcp_more_segments'] == 1):
            _icmp_send(dp,match['in_port'],match['ipv4_dst'],match['ipv4_src'],match['eth_dst'],match['eth_src'],icmp_type=3,icmp_code=4)
            LOG.warning('WARNING: Device with IP: '+match['ipv4_src']+' sent fragmented sndcp packet')
            return

        ##ARP request recieved - send 'I'm here' response
        if match['eth_type'] == 0x0806 and match['arp_op'] == 1:
            LOG.debug("ARP request accepted")
            _arp_send(dp=dp, port_out=match['in_port'], arp_code=2, eth_dst=match['eth_src'], eth_target=match['arp_sha'],
                      ip_target=match['arp_spa'], ip_sender=match['arp_tpa'])
            LOG.debug('Reply to '+match['arp_spa'] +': Host '+match['arp_tpa']+' is at forwarder '+str(dp.id) )
            return

        ##FIXED: All ARP responses are replied, regardless of the target IP
        if match['eth_type'] == 0x0806 and match['arp_op'] == 2:
            LOG.debug('TOPO MNGR: ARP response with target APN discovery IP recieved at controller, processing for APN extraction')
            pkt = packet.Packet(array.array('B', ev.msg.data))
            arp_pkt=pkt.get_protocol(arp.arp)
            apn_ip = arp_pkt.src_ip
            apn_mac= arp_pkt.src_mac
            port = match['in_port']
            
            ##Search for apn in APN_POOL to add mac addr. and update topology
            for apn in APN_POOL:
                if apn.ip_addr == apn_ip:
                    LOG.debug('Recieved ARP response was from ' + apn.name + ' APN')
                    apn.eth_addr = apn_mac
                    topo.add_link(dp.id,str(apn.name),port)
                    topo.add_link(str(apn.name),dp.id,0)
                    topo.reload_topology()
                    LOG.debug('TOPO MNGR: APN '+str(apn.name)+' found at forwarder: '+str(dp.id)+', port: '+str(port) + ' by ARP search')
                    key = str(dp.id)+"_"+str(port)
                    #if key in FREE_INTERFACES: 
                        #del FREE_INTERFACES[key]
                    LOG.debug('MICHAL: FREE_INTERFACES:' + str(FREE_INTERFACES))
                    ##Add special rules to edge forwarder
                    self.on_edge_inet_dp_join(dp, port)  
                    ##Create MAC-tunnels between APN and all BSSs
                    for bss in BSS_POOL:
                        self.add_tunnel(bss,apn)
                    break
            return

        ##ICMP echo with dst_ip==DISCOVERY_IP_DST recieved - new link between forwarders is up
        if match['eth_type'] == 0x0800 and match['ipv4_dst'] == DISCOVERY_IP_DST and match['ip_proto'] == 1:
            LOG.debug('TOPO MNGR: ICMP echo recieved at controller, processing for link extraction')
            pkt = packet.Packet(array.array('B', ev.msg.data))

            ##Discovery pings carry information about sending datapath in payload of icmp packet
            ##these information are in Dictionary format, we parse the out with _icmp_parse_payload() method
            body = _icmp_parse_payload(pkt) 
            neighbourDPID=body['dpid']
            neighbourPort=body['port_out']
            
            ##and add them to topology.
            topo.add_link(ev.msg.datapath.id, neighbourDPID, ev.msg.match['in_port'])
            topo.add_link(neighbourDPID, ev.msg.datapath.id, neighbourPort )
            topo.reload_topology()
            LOG.debug('TOPO MNGR: Topology changed: New link between '+str(ev.msg.datapath.id)+' and '+str(neighbourDPID)+' was discovered.')

            ##retry to create inactive tunnels/find better paths for already active tunnels
            self.retry_tunnels()
        return

    @set_ev_cls(dpset.EventDP, [MAIN_DISPATCHER, DEAD_DISPATCHER])
    def forwarder_state_changed(self, ev):
        """
        This method handles change of forwarders state

        ev.enter is True   -- New forwarder is connected
        ev.enter is False  -- Forwarder got disconnected  
        """


        dp = ev.dp
        ofp = dp.ofproto
        parser = dp.ofproto_parser
            

        if ev.enter is True:
            # in plain MAC setup, this should install only ICMP and ARP re-route rules, watchout for hardcoded DP id
            self.on_inner_dp_join(dp)
	    ##For evry new forwarder we send out discovery ICMP packets out of every port except OFPP_CONTROLLER
            LOG.debug('TOPO MNGR: Forwarder: ' + str(dp.id) + ' saying hello to Unifycore Controller, Unifycore warmly welcomes you!')
            for port in dp.ports:
                if port != (ofp.OFPP_CONTROLLER):
                    LOG.debug('TOPO MNGR: Controller is sending topology discovery ICMPs to forwarder: ' + str(dp.id) + ', port: ' + str(port))
                    _icmp_send(dp,port,DISCOVERY_IP_SRC, DISCOVERY_IP_DST)
                    for apn in APN_POOL:
                        if apn.ip_addr != None:
                            ## FIXED: We have to generate ARPs from the APNs subnet, for now,
                            ##        an incremented Ip will be used, however the ARP originator
                            ##        IP address should be in configuration file per APN
                            ## TODO:  Add ARP originator IP into configuration

                            # We convert string IP into unsigned int
                            integerIp = struct.unpack('!I',socket.inet_aton(apn.ip_addr))[0]
                            # decrementt it
                            integerIp -= 1
                            # and put it back to string format                      
                            ArpOriginStringIp = socket.inet_ntoa(struct.pack("!I",integerIp))
                            LOG.debug('TOPO MNGR: Forwarder: '+str(dp.id)+', port: '+ str(port)   + ' is looking for APN: ' + str(apn.name) +' at IP: '+str(apn.ip_addr)+' with ARP search source IP: ' + ArpOriginStringIp)
                            _arp_send(dp=dp, port_out=port, arp_code=1, ip_target=apn.ip_addr, ip_sender=ArpOriginStringIp)


        if ev.enter is False:
	    ##TODO: We need to scan if any tunnels were affected, and if so, if any PDP COntexts were affected
            ##JUST REMOVING NODE FROM TOPOLOGY ISNT ENOUGH!
            LOG.debug('TOPO MNGR: Forwarder: ' + str(dp.id) + ' is leaving topology. It was a pleasure for us!')
            topo.del_forwarder(dp.id)



    def retry_tunnels(self):
        """ 
             This is very similar to add_tunnel method...I'm too tired to make and call
             modified version of add_tunnel... 
        """

        ##Search inactive tunels to see if any path can be resolved now, if yes...do the same thing as add_tunnel()
        for inact_tunnel in INACTIVE_TUNNELS:
            try:
                self.path_out = topo.get_tunnel(inact_tunnel.bss, inact_tunnel.apn.name)
                self.path_in  = topo.get_tunnel(inact_tunnel.apn.name, inact_tunnel.bss)
                
            except nx.NetworkXNoPath:
                LOG.warning("Warning: Couldn't find path, network might not be converged yet. Retrying when next forwarder joins network...again...")
                return
            
            INACTIVE_TUNNELS.remove(inact_tunnel)

            ##Set forwarding rules for all but last forwarder on the way OUT 
            ##On first forwarder on the way OUT these rules are placed into table MAC_TUNNEL_TABLE while on 'dumb' forwarders it goes to 0
            dp = dpset.get(self.path_out[0].dpid)
            parser = dp.ofproto_parser
            match = parser.OFPMatch(eth_dst=inact_tunnel.tid_out)
            actions = [parser.OFPActionOutput(self.path_out[0].port_out)]
            self.add_flow(dp, 300, match, actions, TUNNEL_RULES, 0, MAC_TUNNEL_TABLE)

            ##Rules for all 'dumb' forwardes on the way OUT
            for node in self.path_out[1:-1]:
                dp = dpset.get(node.dpid)
                parser = dp.ofproto_parser
                match = parser.OFPMatch(eth_dst=inact_tunnel.tid_out)
                actions = [parser.OFPActionOutput(node.port_out)]
                self.add_flow(dp, 300, match, actions, TUNNEL_RULES, 0, 0)

            ##Last forwarder on the way OUT needs to set eth_dst to eth_addr of APN otherwise it wont be processed
            dp = dpset.get(self.path_out[-1].dpid)
            parser = dp.ofproto_parser
            match = parser.OFPMatch(eth_dst=inact_tunnel.tid_out)
            actions = [ parser.OFPActionSetField(eth_dst=inact_tunnel.apn.eth_addr), parser.OFPActionOutput(self.path_out[-1].port_out)]
            self.add_flow(dp, 300, match, actions, TUNNEL_RULES, 0, 0)

            ##Here comes tunnel for the way IN
            ##On first forwarder on the way IN these rules are placed into table MAC_TUNNEL_TABLE while on 'dumb' forwarders it goes to 0
            dp = dpset.get(self.path_in[0].dpid)
            parser = dp.ofproto_parser
            match = parser.OFPMatch(eth_dst=inact_tunnel.tid_in)
            actions = [parser.OFPActionOutput(self.path_in[0].port_out)]
            self.add_flow(dp, 300, match, actions, TUNNEL_RULES, 0, MAC_TUNNEL_TABLE)

            ##Rules for all 'dumb' forwardes on the way IN
            for node in self.path_in[1:-1]:
                dp = dpset.get(node.dpid)
                parser = dp.ofproto_parser
                match = parser.OFPMatch(eth_dst=inact_tunnel.tid_in)
                actions = [parser.OFPActionOutput(node.port_out)]
                self.add_flow(dp, 300, match, actions, TUNNEL_RULES, 0, 0)

            ##Last forwarder on the way IN sends packet to table OF_GPRS_TABLE_IN where it's matched based on active PDP CNTs
            dp = dpset.get(self.path_in[-1].dpid)
            parser = dp.ofproto_parser
            match = parser.OFPMatch(eth_dst=inact_tunnel.tid_in)
            inst = [ parser.OFPInstructionGotoTable(OF_GPRS_TABLE_IN) ]
            req = parser.OFPFlowMod(datapath=dp, priority=500, match=match, instructions=inst, table_id=0)
            self.update_flows(dp, req, 0, 500, match, inst, TUNNEL_RULES, 0)

            ACTIVE_TUNNELS.append(tunnel(inact_tunnel.bss, inact_tunnel.apn, self.tid_out, self.tid_in, self.path_out, self.path_in))
            LOG.debug('TOPO MNGR: Inactive tunnel between ' + str(inact_tunnel.bss) + ' and ' + str(inact_tunnel.apn.name) +' put into active state!')



   

    def add_tunnel(self, _bss_, _apn_):
        """
        This method is called when new APN is discovered to connect it with all BSS stations via MAC Tunnels

        Keyword arguments:
            _bss_ -- usualy string representing BSS node in topology
            _apn_ -- object of apn class representing APN in topology
            
        """

        self.bss = _bss_
        self.apn = _apn_
        self.tid_out = get_tid()
        self.tid_in  = get_tid()

        ##Attempt to find path between the two nodes
        ##If no path is found, tunnel is added to INACTIVE_TUNNELS and is attempted to recreate next time
        ##when new link between forwarders is up
        try:
            self.path_out = topo.get_tunnel(self.bss, self.apn.name)
            self.path_in  = topo.get_tunnel(self.apn.name, self.bss)
        except nx.NetworkXNoPath:
            LOG.warning("Warning: Couldn't find path, network might not be converged yet. Retrying when next forwarder joins network.")
            INACTIVE_TUNNELS.append(tunnel(self.bss,self.apn, self.tid_out, self.tid_in))
            return

        ##Set forwarding rules for all but last forwarder on the way OUT
        ##On first forwarder on the way OUT these rules are placed into table MAC_TUNNEL_TABLE while on 'dumb' forwarders it goes to 0
        dp = dpset.get(self.path_out[0].dpid)
        parser = dp.ofproto_parser
        match = parser.OFPMatch(eth_dst=self.tid_out)
        actions = [parser.OFPActionOutput(self.path_out[0].port_out)]
        self.add_flow(dp, 300, match, actions, TUNNEL_RULES, 0, MAC_TUNNEL_TABLE)

        ##Rules for all 'dumb' forwardes on the way OUT
        for node in self.path_out[1:-1]:
            dp = dpset.get(node.dpid)
            parser = dp.ofproto_parser
            match = parser.OFPMatch(eth_dst=self.tid_out)
            actions = [parser.OFPActionOutput(node.port_out)]
            self.add_flow(dp, 300, match, actions, TUNNEL_RULES, 0, 0)

        ##Last forwarder on the way OUT needs to set eth_dst to eth_addr of APN otherwise it wont be processed
        dp = dpset.get(self.path_out[-1].dpid)
        parser = dp.ofproto_parser
        match = parser.OFPMatch(eth_dst=self.tid_out)
        actions = [ parser.OFPActionSetField(eth_dst=self.apn.eth_addr), parser.OFPActionOutput(self.path_out[-1].port_out)]
        self.add_flow(dp, 300, match, actions, TUNNEL_RULES, 0, 0)

        ##Here comes tunnel for way IN
        ##On first forwarder on the way IN these rules are placed into table MAC_TUNNEL_TABLE while on 'dumb' forwarders it goes to 0
        dp = dpset.get(self.path_in[0].dpid)
        parser = dp.ofproto_parser
        match = parser.OFPMatch(eth_dst=self.tid_in)
        actions = [parser.OFPActionOutput(self.path_in[0].port_out)]
        self.add_flow(dp, 300, match, actions, TUNNEL_RULES, 0, MAC_TUNNEL_TABLE)

        ##Rules for 'dumb' forwarders
        for node in self.path_in[1:-1]:
            dp = dpset.get(node.dpid)
            parser = dp.ofproto_parser
            match = parser.OFPMatch(eth_dst=self.tid_in)
            actions = [parser.OFPActionOutput(node.port_out)]
            self.add_flow(dp, 300, match, actions, TUNNEL_RULES, 0, 0)

        ##Last forwarder on the way IN sends packet to table #4 where it's matched based on active PDP CNTs
        dp = dpset.get(self.path_in[-1].dpid)
        dp.ofproto_parser
        match = parser.OFPMatch(eth_dst=self.tid_in)
        inst = [ parser.OFPInstructionGotoTable(OF_GPRS_TABLE_IN) ]
        req = parser.OFPFlowMod(datapath=dp, priority=500, match=match, instructions=inst, table_id=0)
        self.update_flows(dp, req, 0, 500, match, inst, TUNNEL_RULES, 0)       

        ACTIVE_TUNNELS.append(tunnel(self.bss,self.apn, self.tid_out, self.tid_in, self.path_out, self.path_in))
        LOG.debug('Tunnel between '+str(self.bss)+' and '+str(self.apn.name) + ' was set up.')


    def update_flows(self, dp, mod, table_id, priority, match, inst, flow_type, cookie):
        if any(fwd.id == dp.id for fwd in FORWARDERS):
            for fwd in FORWARDERS:
                if fwd.id == dp.id:
                    fwd.add_flow(table_id, priority, match, inst, flow_type, cookie)            
        else:
            LOG.debug('MICHAL: Appending new forwarder')
            FORWARDERS.append(forwarder(dp))
            for fwd in FORWARDERS:
                if fwd.id == dp.id:
                    fwd.add_flow(table_id, priority, match, inst, flow_type, cookie)    
        dp.send_msg(mod)
                   
       

    def add_flow(self, dp, priority, match, actions, flow_type, cookie, table=0):
        ofp = dp.ofproto
        parser = dp.ofproto_parser
        inst = [parser.OFPInstructionActions(ofp.OFPIT_APPLY_ACTIONS, actions)]
        mod = parser.OFPFlowMod(datapath=dp, table_id=table, priority=priority, match=match, instructions=inst)
        PREPINACE.append(prepinac(priority, match, inst, dp))
        self.update_flows(dp, mod, table, priority, match, inst, flow_type, cookie)
        
    
    @set_ev_cls(ofp_event.EventOFPPortStatsReply, MAIN_DISPATCHER)
    def port_stats_reply_handler(self, ev):
        PORTS_STATS = []
        #LOG.debug('MICHAL PORTSTATS ID' + str(ev.msg.datapath.id))
        #LOG.debug('MICHAL: stats msg.body = ' + str(ev.msg))
        for stat in ev.msg.body:
            stats = Stats(stat.port_no,
                      stat.rx_packets, stat.tx_packets,
                      stat.rx_bytes, stat.tx_bytes,
                      stat.rx_dropped, stat.tx_dropped,
                      stat.rx_errors, stat.tx_errors,
                      stat.rx_frame_err, stat.rx_over_err,
                      stat.rx_crc_err, stat.collisions,
                      stat.duration_sec, stat.duration_nsec) 
            PORTS_STATS.append(stats)
        FWD_PSTATS[ev.msg.datapath.id] = PORTS_STATS
        #LOG.debug('MICHAL POrtStats: %s', FWD_PSTATS)

    @set_ev_cls(ofp_event.EventOFPFlowStatsReply, MAIN_DISPATCHER)
    def flow_stats_reply_handler(self, ev):
        flows = []
        #LOG.debug("MICHAL flow stats" + str(ev.msg.body))
        for stat in ev.msg.body:
            stats = flowStats(stat.table_id, stat.duration_sec, stat.duration_nsec, stat.priority, stat.idle_timeout,
                              stat.hard_timeout, stat.flags, stat.cookie, stat.packet_count, stat.byte_count,
                              stat.match, stat.instructions)
            flows.append(stats)
        FWD_FSTATS[ev.msg.datapath.id]=flows
        
        LOG.debug('MICHAL Flow stats %s', str(FWD_FSTATS))    

 


class RestCall(ControllerBase):
    """
    This Class contains methods that can be executed via REST calls
    """

    def __init__(self, req, link, data, **config):
        super(RestCall, self).__init__(req, link, data, **config)
        self.dpset = data['dpset']
        self.waiters = data['waiters']

    #Testing
    def test_info(self,req):
        global dpset
        response = '<H1>Topology status DUMP</H1> </BR>'
        response += '<B>Dump created on: </B> ' + str(datetime.datetime.now())
        response += '</BR></BR><B>BSS edge forwarders list(decimal values):      </B> ' + str(BSS_EDGE_FORWARDER)
        response +=      '</BR><B>Internet edge forwarders list(decimal values): </B> ' + str(INET_EDGE_FORWARDER)

        response +=      '</BR><B>Active tunnels:   </B>'        
        for tunnel in ACTIVE_TUNNELS:
            response += '</BR>***Tunnel from: ' + tunnel.bss + ' to: ' + tunnel.apn.name + '***</BR>'
            for node in tunnel.path_out:
                response += str(node.dpid) + ' via port: ' + str(node.port_out) +', ' 
            response += '</BR>***Tunnel from: ' + tunnel.apn.name + ' to: ' + tunnel.bss + '***</BR>'
            for node in tunnel.path_in:
                response += str(node.dpid) + ' via port: ' + str(node.port_out) +', '
                

        response +=      '</BR><B>Inactive tunnels: </B>'
        for tunnel in INACTIVE_TUNNELS:
            response += '</BR>***Tunnel from: ' + tunnel.bss + ' to: ' + tunnel.apn.name + '***</BR>'
            for node in tunnel.path_out:
                response += str(node.dpid) + ' via port: ' + str(node.port_out) +', '
            response += '</BR>***Tunnel from: ' + tunnel.apn.name + ' to: ' + tunnel.bss + '***</BR>'
            for node in tunnel.path_in:
                response += str(node.dpid) + ' via port: ' + str(node.port_out) +',' 



        response +=      '</BR><B>Static topology graph nodes:  </B>' + str(topo.StaticGraph.nodes())
        response +=      '</BR><B>Dynamic topology graph nodes: </B>' + str(topo.DynamicGraph.nodes())

        #FIXME: Temporary hack (0th index), since we have only one ePCU/PCU-ng at the time being == one entry point for GPRS traffic, and also one exit point (Internet)
        try:
            #already implemented in topology class(get_tunnel function), but I am not particularly happy with it ==> standard networkX call used, works as a charm
            path_out = nx.shortest_path(topo.DynamicGraph, BSS_EDGE_FORWARDER[0], INET_EDGE_FORWARDER[0])
            path_in  = nx.shortest_path(topo.DynamicGraph, INET_EDGE_FORWARDER[0], BSS_EDGE_FORWARDER[0])
            LOG.debug('STATUS DUMP: Path between GPRS edge and Internet found: ' + str(path_out))
            LOG.debug('STATUS DUMP: Path between Internet edge na GPRS edge found: ' + str(path_in))
        except nx.NetworkXNoPath:
            LOG.warning("STATUS DUMP: Warning: Couldn't find path, network might not be converged yet. Retrying when next forwarder joins network.")
            path_out = []
            path_in  = []

        if BSS_EDGE_FORWARDER and INET_EDGE_FORWARDER \
           and  topo.StaticGraph.number_of_nodes() and topo.DynamicGraph.number_of_nodes() \
           and (BSS_EDGE_FORWARDER[0] in topo.StaticGraph) and (BSS_EDGE_FORWARDER[0] in topo.DynamicGraph) \
           and (INET_EDGE_FORWARDER[0] in topo.StaticGraph) and (INET_EDGE_FORWARDER[0] in topo.DynamicGraph) \
           and len(path_out) and len(path_in):
            

            response += '</BR><B>Path to the Internet:  </B>' + str(path_out)
            response += '</BR><B>Path to the GPRS edge: </B>' + str(path_in)
            response += '<H1 style="color:green"> TOPOLOGY HEALTHY! </H1>'
        else:
            response += '<H1 style="color:red"> TOPOLOGT NOT HEALTHY </H1>'


        if ACTIVE_TUNNELS or INACTIVE_TUNNELS:
            response += '<H2 style="color:green"> USER-PLANE TUNNELS ARE PRESENT </H2>'
        else:
            response += '<H2 style="color:orange"> USER-PLANE TUNNELS NOT PRESENT </H2>'


        LOG.debug('STATUS DUMP: Dumping Topology state at /test/info URL!')
        return (response)

    def add_apn(self, req, opt):
        arguments = opt.split(',')
		
        forwarder = arguments[0].split('=')
        dp = self.dpset.get(int(forwarder[1]))
        fwd_h = hex(int(forwarder[1]))
        fwd_id = fwd_h.split('x')
        LOG.debug("MICHAL: KONVERTOVANE ID FORWARDERA " + fwd_id[1])
        port = arguments[1].split('=')
        port_num = int(port[1])
		
        apn_name = arguments[2].split('=')
        new_apn = apn(apn_name[1])
        ip_addr = 	arguments[3].split('=')	
        apn_ip= ip_addr[1]
        mask_arr = arguments[4].split('=')
        mask = mask_arr[1]
        LOG.debug("MICHAL pi=" + ip_addr[1])
        #pridaj ip do /etc/hosts
        key = forwarder[1]+"_"+port[1]
        #if key in FREE_INTERFACES:
           #interf = FREE_INTERFACES[key]
           
        cmd = ("grep core'" + fwd_id[1] + port[1] +"' /root/unifycore/support/network_init.sh | head -n 1 | cut -f4 -d ' '")
        interface_name_ = subprocess.check_output(cmd, shell=True)
           #cmd = ("echo -n '" + interface_name_ +"'")
           #interface_name = subprocess.check_output(cmd, shell=True)
        interface_name = interface_name_[:-1]
        LOG.debug("MICHAL: interface_name=" + interface_name)
        #LOG.debug("MICHAL: ADD APN " + interf + " " +apn_ip)
        cmd = str("echo "+ apn_ip+" "+apn_name[1] + " >>/etc/hosts")
        LOG.debug("MICHAL: ADD APN " +cmd)
        os.system(cmd)
        cmd = "ifconfig "+interface_name + " " + apn_ip + "/" + mask
        LOG.debug("MICHAL: ADD ADD APN " +cmd)
        os.system(cmd)
        cmd = 'ifconfig '+interface_name + ' up'
        LOG.debug("MICHAL: ADD APN " +cmd)
        os.system(cmd)
         #del FREE_INTERFACES[forwarder[1]+"_"+port[1]]

           #FREE_INTERFACES = {"14_3":"apn1", "13_4":"apn2"}	
        APN_POOL.append(new_apn)
        
           ##Resolving APN IP
        if new_apn.ip_addr==None:
            try:
                ip_addr = str(socket.gethostbyname(new_apn.name))
                new_apn.ip_addr = ip_addr
                LOG.debug('Resolved APN '+new_apn.name+' : '+new_apn.ip_addr)
            except socket.gaierror:
                LOG.warning('Error while resolving apn name "'+new_apn.name+'"' )
        
        if new_apn.ip_addr != None:
            ## FIXED: We have to generate ARPs from the APNs subnet, for now,
            ##        an incremented Ip will be used, however the ARP originator
            ##        IP address should be in configuration file per APN
            ## TODO:  Add ARP originator IP into configuration

            # We convert string IP into unsigned int
            integerIp = struct.unpack('!I',socket.inet_aton(new_apn.ip_addr))[0]
            # increment it
            integerIp -= 1
            # and put it back to string format                      
            ArpOriginStringIp = socket.inet_ntoa(struct.pack("!I",integerIp))
            LOG.debug('TOPO MNGR: Forwarder: '+str(dp.id)+', port: '+ str(port_num)   + ' is looking for APN: ' + str(new_apn.name) +' at IP: '+str(new_apn.ip_addr)+' with ARP search source IP: ' + ArpOriginStringIp)
            _arp_send(dp=dp, port_out=port_num, arp_code=1, ip_target=new_apn.ip_addr, ip_sender=ArpOriginStringIp)
    
        return (Response(body="APN "+new_apn.name+" successfully connected to forwarder "+forwarder[1]+" on port " + str(port_num), headerlist=[('Access-Control-Allow-Origin', '*')]))
     #else:
		#return (Response(body="APN "+new_apn.name+" Port is already in use ", headerlist=[('Access-Control-Allow-Origin', '*')]))

    def send_icmp_packet(self, req, opt):
		arguments = opt.split(',')
		forwarder = arguments[0].split('=')
		dp = self.dpset.get(int(forwarder[1]))
		port = arguments[1].split('=')
		port_num = int(port[1]) 
		for i in range(0,100):
        		_icmp_send(dp, port_num)
 		return (Response(body="100 ICMP packets sent on port:" +port[1] + "of forwarder " + forwarder[1] , headerlist=[('Access-Control-Allow-Origin', '*')]))
			


    def dump_statistics(self, req):       
        for fwd in FORWARDERS:             
            dp = self.dpset.get(int(fwd.id))
            self.send_port_stats_request(dp)
        return (Response(content_type='application/json', body=json.dumps(FWD_PSTATS, default=lambda o: o.__dict__, indent = 1), headerlist=[('Access-Control-Allow-Origin', '*')]))



    def send_port_stats_request(self, datapath):
        ofp = datapath.ofproto
        ofp_parser = datapath.ofproto_parser
        req = ofp_parser.OFPPortStatsRequest(datapath, 0, ofp.OFPP_ANY)
        datapath.send_msg(req)


    def dump_flow_statistics(self, req):
		 for fwd in FORWARDERS:
		     dp = self.dpset.get(int(fwd.id))
		     self.send_flow_stats_request(dp)
		# stats_json = json.dumps(FWD_FSTATS, default=lambda o: o.__dict__, indent = 1).encode('ISO-8859-1').strip()
		 #LOG.debug('MICHAL JSON:')
		 #OG.debug(stats_json)
		 return (Response(content_type='application/json', body=json.dumps(FWD_FSTATS, default=lambda o: o.__dict__, indent = 1), headerlist=[('Access-Control-Allow-Origin', '*')]))

    def send_flow_stats_request(self, datapath):
        ofp = datapath.ofproto
        ofp_parser = datapath.ofproto_parser

        cookie = cookie_mask = 0
        match = ofp_parser.OFPMatch()
        req = ofp_parser.OFPFlowStatsRequest(datapath, 0,
                                         ofp.OFPTT_ALL,
                                         ofp.OFPP_ANY, ofp.OFPG_ANY,
                                         cookie, cookie_mask,
                                         match)
        datapath.send_msg(req)


    def delete_flow (self, req, opt):
        LOG.debug('MICHAL: Deleting flow with REST CALL')
        LOG.debug('MICHAL: url opt: ' + str(opt)) 
        flow = json.loads(opt)
        #LOG.debug('MICHAL: url data id: ' + str(flow['id']))
        #LOG.debug('MICHAL: url data inst: ' + str(flow['instruction']))
           
        
        for fwd in FORWARDERS:
	        dp = self.dpset.get(int(fwd.id))
	        if fwd.id == flow['id']:
				for tab in fwd.tables:
					if tab.id == flow['table']:
						for f in tab.flows:
							counter = 0 
							i = 0
							if f.priority == int(flow['priority']):
								if len(f.match._fields2) == len(flow['fields2']):
									#LOG.debug('MICHAL: rovnake dlzky fieldov2')
									for m in f.match._fields2:
										#LOG.debug('MICHAL: url data fields[i]: ' + str(flow['fields2'][i]))
										url_mtch = str(flow['fields2'][i][0]) + "="+str(flow['fields2'][i][1])
										fwd_mtch=str(m[0]) + "=" +str(m[1])
										#LOG.debug('MICHAL: url_mtch fields: ' + url_mtch)
										#LOG.debug('MICHAL: fwd_mtch fields2: ' + fwd_mtch)
										i = i+1
										if url_mtch == fwd_mtch:
											counter = counter + 1
								if counter ==  len(f.match._fields2):
									LOG.debug('MICHAL: delete_flow() - Found matching flow')
									self.remove_table_flows(dp, flow['table'],f.match, f.inst)
									tab.flows.remove(f)
									if len(tab.flows) == 0:
										fwd.tables.remove(tab)
									break
		#LOG.debug('MICHAL: No matching flow found')
        return (Response(content_type='application/json', body="DELETING FLOW", headerlist=[('Access-Control-Allow-Origin', '*')]))


    def remove_table_flows(self, datapath, table_id, match, instructions):
        #Create OFP flow mod message to remove flows from table.
        ofproto = datapath.ofproto
        flow_mod = datapath.ofproto_parser.OFPFlowMod(datapath=datapath, table_id=table_id, command=ofproto.OFPFC_DELETE, 
                                                out_port=ofproto.OFPP_ANY, out_group=ofproto.OFPG_ANY, match=match, instructions=instructions)
        datapath.send_msg(flow_mod)

    def dump_topology (self, req):
        LOG.debug('TOPO DUMP: Dumping topology to JSON at /topology/dump ')
        return (Response(content_type='application/json', body=topo.dump(), headerlist=[('Access-Control-Allow-Origin', '*')]))

    def dump_oftables (self, req, opt):
        LOG.debug('MICHAL: Dumping OF tables to JSON at /oftables/dump/')
        #index = next(index for index,fwd in enumerate(FORWARDERS) if fwd.id == opt)
        for fwd in FORWARDERS:
            if fwd.id == int(opt):
                fwdIndex = FORWARDERS.index(fwd)
                return (Response(content_type='application/json', body=json.dumps(FORWARDERS[fwdIndex], default=lambda o: o.__dict__, indent = 1, sort_keys = True),  headerlist=[('Access-Control-Allow-Origin', '*')]))

    def dump_active_pdps(self, req):
        LOG.debug('MICHAL: Dumping ACTIVE_CONTEXTS to JSON at /gprs/pdp_dump')
        cont.context_array = ACTIVE_CONTEXTS
        return (Response(content_type='application/json', body=json.dumps(cont, default=lambda o: o.__dict__, indent = 1, sort_keys = True),
        headerlist=[('Access-Control-Allow-Origin', '*')]))

    def dump_active_tunnels(self, req):
        LOG.debug('MICHAL: Dumping ACTIVE_TUNNELS to JSON at /tunnels/active/dump')
        return (Response(content_type='application/json', body=json.dumps(ACTIVE_TUNNELS, default=lambda o: o.__dict__, indent = 1, sort_keys = True),
        headerlist=[('Access-Control-Allow-Origin', '*')]))


    def user_added_flow(self, req, opt):
        LOG.debug('MICHAL: Adding flow: ' + opt)
        flow = json.loads(opt)
        LOG.debug('MICHAL: ID of flow = ' + str(flow['id']))

        dp = self.dpset.get(flow['id'])
        ofp = dp.ofproto
        parser = dp.ofproto_parser
        match_string = ""
        counter = 0
        for mtch in flow['matches']:
            match_string += str(mtch)
            counter+=1
            if counter < len(flow['matches']):
                match_string +=", "
        LOG.debug('MICHAL: match_string: ' + match_string)
        exec("match = parser.OFPMatch( "+match_string+")") 
        LOG.debug('MICHAL: match=' + str(match))
        
        
        all_actions = "" 
        for act in flow['actions']:
            if act['a_type']=="PushGPRSNS" or act['a_type']=="PopGPRSNS" or act['a_type']=="PushUDPIP" or act['a_type']=="PopUDPIP": 
			    name="GPRSAction" + act['a_type'] + "("
				#GPRSActionPushGPRSNS(bvci, tlli, sapi, nsapi, drx_param, imsi),
                # GPRSActionPushUDPIP(sa=VGSN_IP, da=BSS_IP, sp=VGSN_PORT, dp=BSS_PORT),
            else:
			    name = "parser."+act['a_type']+"("
            attributes = ""
            for prop in act['properties']:
				attributes = attributes + prop + ", "
            attributes = attributes[:-2]
            all_actions = all_actions + name + attributes + "), "
       
        all_actions = all_actions[:-2] 
        LOG.debug('MICHAL: adding actions:    action = [' + all_actions +"]")
        exec("actions = ["+ all_actions +"]")
		
        all_inst = ""
        for ins in flow['inst']:
			name =ins['i_type']
			if name=="OFPInstructionGotoTable" or name=="OFPInstructionWriteMetadata" or name=="OFPInstructionMeter":
				name = "parser."+ins['i_type']+"("
				attr = ""
				for prop in ins['properties']:
					attr = attr + prop + ", "
				attr = attr[:-2]
				all_inst = all_inst + name + attr + "), "
			else:
				name = "parser.OFPInstructionActions("
				attr = "ofp." + ins['i_type'] + ", actions"
				all_inst = all_inst + name + attr + "), "
			
        all_inst = all_inst[:-2]
        exec("inst = ["+ all_inst +"]")
        LOG.debug('MICHAL: adding instructions:    instructions = [' + all_inst +"]")
	
        if flow['cookie'] == "":
			self.add_flow(dp, 0, flow['table_id'], flow['priority'], match, actions, USER_DEFINED, inst)
        else:
			self.add_flow(dp, int(flow['cookie']), flow['table_id'], flow['priority'], match, actions, USER_DEFINED, inst)
        return (Response(body="Flow successfuly added.", headerlist=[('Access-Control-Allow-Origin', '*')]))
       
            
        
    def update_flows(self, dp, req, table_id, priority, match, inst, flow_type, cookie):
        if any(fwd.id == dp.id for fwd in FORWARDERS):
            for fwd in FORWARDERS:
                if fwd.id == dp.id:
                    fwd.add_flow(table_id, priority, match, inst, flow_type, cookie)
        else:
            FORWARDERS.append(forwarder(dp))
            for fwd in FORWARDERS:
                if fwd.id == dp.id:
                    fwd.add_flow(table_id, priority, match, inst, flow_type, cookie)
        
        
        
    def add_flow(self, dp, cookie, table, priority, match, actions, flow_type, inst):
        ofp = dp.ofproto
        parser = dp.ofproto_parser
        mod = parser.OFPFlowMod(datapath=dp, cookie=cookie, priority=int(priority), table_id=int(table), match=match, instructions=inst)
        dp.send_msg(mod)
        self.update_flows(dp, mod, int(table), int(priority), match, inst, flow_type, cookie)


    def mod_pdp (self, req, cmd):
        LOG.debug('REST: mod_pdp: Modification of PDP called')
        #parsing GET parameters out of REST call
        body = urlparse.parse_qs(cmd)
        
        ##TODO:Change vGSN to make REST call in format where 'cmd' is paired with value, for now we assume cmd=add
        #parse_qs method returns results with garbage around, this ugly hack cuts it away [3:-2]
        start = str(body.get('rai'))[3:-2]
        end = str(body.get('apn'))[3:-2]
        imsi = str(body.get('imsi'))[3:-2]
        bvci = int(str(body.get('bvci'))[3:-2])
        tlli = int(str(body.get('tlli'))[3:-2], 16)
        drx_param = int(str(body.get('drx_param'))[3:-2], 16)
        sapi = int(str(body.get('sapi'))[3:-2])
        nsapi = int(str(body.get('nsapi'))[3:-2])


        tid_out=None
        tid_in=None
        path_in=None
        path_out=None
        #XXX:How about a HTTP response to vGSN if required tunnel doesnt exist?
        ## We find tunnel that matches criteria from Activate PDP context request
        for act_tunnel in ACTIVE_TUNNELS:
            if start == act_tunnel.bss and end == act_tunnel.apn.name:
                tid_out = act_tunnel.tid_out
                tid_in = act_tunnel.tid_in
                path_in =  act_tunnel.path_in
                path_out = act_tunnel.path_out
                LOG.debug('REST: mod_pdp: Tunnel was found')
                break

        if tid_out == None or tid_in == None or path_in == None or path_out == None:
            LOG.error('REST: mod_pdp: ERROR: No suitable tunnel for given PDP was found')
            return Response(status=500, content_type='text', body='Tunnel not found')

   
        #XXX:review, maybe larger ip pool, for now it's enough
        #TODO:in case on CNT deactivation, return IP to pool
        ## IP address is picked, in case there is no left, method ends and returns Internal Error HTTP response to caller
        if len(IP_POOL) == 0:
            LOG.error('REST: mod_pdp: ERROR: We are out of IP addresses') 
            return Response(status=500, content_type='text',body='Out of IPs')
        
        client_ip=IP_POOL.pop()
     
        #TODO: Handling of 'cmd' value
        ACTIVE_CONTEXTS.append( PDPContext(bvci, tlli, sapi, nsapi, tid_out, tid_in, client_ip, imsi, drx_param) )
        
        
        ###WAY OUT
        ##First node on the way OUT removes GPRS headers, sets eth addr. to appropriate tunnel ID
        ##and sends packet to table MAC_TUNNEL_TABLE
        ##In_port of packet on first node on its way OUT is equal to the port_out of last node on the way IN, therfore in_port=path_in[-1].port_out
        dp = self.dpset.get(path_out[0].dpid)
        parser = dp.ofproto_parser
        ofp = dp.ofproto
        match = parser.OFPMatch( in_port=path_in[-1].port_out,
                                 ns_type=0,
                                 ns_bvci=bvci, 
                                 bssgp_tlli=tlli, 
                                 llc_sapi=sapi, 
                                 sndcp_nsapi=nsapi)

        actions = [GPRSActionPopGPRSNS(), GPRSActionPopUDPIP(),
                   parser.OFPActionSetField(eth_src=tid_in),parser.OFPActionSetField(eth_dst=tid_out)]
        inst = [parser.OFPInstructionActions(ofp.OFPIT_APPLY_ACTIONS, actions), parser.OFPInstructionGotoTable(MAC_TUNNEL_TABLE)]                   
        req = parser.OFPFlowMod(datapath=dp, priority=100, match=match, instructions=inst, table_id = OF_GPRS_TABLE)
        #dp.send_msg(req)
        self.update_flows(dp, req, OF_GPRS_TABLE, 100, match, inst, PDP_FLOWS, 0)

        ###WAY IN
        ##On the way IN we need to match packet on both first and last forwarder
        ##First forwarder matches Clients IP to determine appropriate tunnel
        ##for first in_port match aplies same rule as on the way out: in_port=path_out[-1].port_out
        dp = self.dpset.get(path_in[0].dpid)
        parser = dp.ofproto_parser
        ofp = dp.ofproto
        match = parser.OFPMatch(in_port=path_out[-1].port_out,
                                eth_type=0x0800,
                                ipv4_dst=client_ip)
        actions = [ parser.OFPActionSetField(eth_dst=tid_in), parser.OFPActionSetField(eth_src=tid_out) ]
        inst = [parser.OFPInstructionActions(ofp.OFPIT_APPLY_ACTIONS, actions), parser.OFPInstructionGotoTable(MAC_TUNNEL_TABLE)]
        req = parser.OFPFlowMod(datapath=dp, priority=300, match=match, instructions=inst, table_id = 0)
        #dp.send_msg(req)
        self.update_flows(dp, req, 0, 300, match, inst, PDP_FLOWS, 0)
     
        #LOG.debug('MICHAL: dp = self.dpset.get(path_in[-1].dpid)=' + str(path_in[-1].dpid))
        dp = self.dpset.get(path_in[-1].dpid)
        parser = dp.ofproto_parser
        ofp = dp.ofproto
        
        ##XXX:Setfield eth_dst is ahrdcoded to work with our BTS!
        ##Last forwarder machtes Clients IP to push appropriate GPRS headers and determine port_out
        match = parser.OFPMatch(eth_type=0x0800,
                                ipv4_dst=client_ip)
        actions=[ GPRSActionPushGPRSNS(bvci, tlli, sapi, nsapi, drx_param, imsi),
                  GPRSActionPushUDPIP(sa=VGSN_IP, da=BSS_IP, sp=VGSN_PORT, dp=BSS_PORT),
                  parser.OFPActionSetField(eth_dst='00:d0:cc:08:02:ba'),
                  parser.OFPActionOutput(path_in[-1].port_out)]
        inst=[ parser.OFPInstructionActions(ofp.OFPIT_APPLY_ACTIONS, actions) ]
 
        req = parser.OFPFlowMod(datapath=dp, priority=100, match=match, instructions=inst, table_id = OF_GPRS_TABLE_IN)
        #dp.send_msg(req)
        self.update_flows(dp, req, OF_GPRS_TABLE_IN, 100, match, inst, PDP_FLOWS, 0)


        return (Response(content_type='application/json', body='{"address":"'+client_ip+'","dns1":"8.8.8.8","dns2":"8.8.8.8"}', headerlist=[('Access-Control-Allow-Origin', '*')]))




class GPRSAction(ofproto_v1_3_parser.OFPActionExperimenter):
    subtype = 0

    def __init__(self, subtype):
        super(GPRSAction, self).__init__(experimenter=GPRS_SDN_EXPERIMENTER)
        self.subtype = subtype
        self.len = 16

    def serialize(self, buf, offset):
        """ Serialize action into buffer. """
        super(GPRSAction,self).serialize(buf, offset)
        ofproto_parser.msg_pack_into("!H", buf, offset+8, self.subtype)

class GPRSActionPushGPRSNS(GPRSAction):
    def __init__(self, bvci, tlli, sapi, nsapi, drx_param, imsi):
        super(GPRSActionPushGPRSNS,self).__init__(0x0001)
        self.len = 32
        self.bvci = bvci
        self.tlli = tlli
        self.sapi = sapi
        self.nsapi = nsapi
        self.drx_param = drx_param
        self.imsi = imsi

    def serialize(self, buf, offset):
        """ Serialize PushGPRSNS action into buffer. """
        super(GPRSActionPushGPRSNS,self).serialize(buf, offset)

        imsi_bytes = imsi_to_bytes(self.imsi)

        LOG.debug("push_gprsns.serialize self="+pprint.pformat(self))
        ofproto_parser.msg_pack_into("!HxxIHBBHBBBBBBBBBx", buf, offset+8, 
                self.subtype, self.tlli, self.bvci, self.sapi, self.nsapi, self.drx_param, 
                len(imsi_bytes), *imsi_bytes)

class GPRSActionPopGPRSNS(GPRSAction):
    def __init__(self):
        super(GPRSActionPopGPRSNS,self).__init__(0x0002)

class GPRSActionPushUDPIP(GPRSAction):
    def __init__(self, dp, sp, da, sa):
        super(GPRSActionPushUDPIP,self).__init__(0x0003)
        self.len = 24
        self.sp = sp
        self.dp = dp
        self.da = socket.inet_aton(da)
        self.sa = socket.inet_aton(sa)

    def serialize(self, buf, offset):
        """ Serialize PushUDPIP action into buffer. """
        super(GPRSActionPushUDPIP,self).serialize(buf, offset)
        ofproto_parser.msg_pack_into("!Hxx4s4sHH", buf, offset+8, 
                self.subtype, self.da, self.sa, self.dp, self.sp)

class GPRSActionPopUDPIP(GPRSAction):
    def __init__(self):
        super(GPRSActionPopUDPIP,self).__init__(0x0004)
