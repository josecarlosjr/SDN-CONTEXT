#!/usr/bin/python

"""
This creates an sdn Mininet object
(without a topology object) and add nodes to it manually.
"""

from mininet.net import Mininet
from mininet.node import Controller
from mininet.cli import CLI
from mininet.log import setLogLevel, info


def sdnNet():
    "Create an sdn network and add nodes to it."

    net = Mininet(controller=Controller)

    info('*** Adding controller\n')
    net.addController('c0')

    info('*** Adding hosts\n')
    h1_cpor = net.addHost('h1_cpor')
    h2_fundaj = net.addHost('h2_fundaj')
    h3_ifpe = net.addHost('h3_ifpe')
    h4_popBD = net.addHost('h4_popBD')

    info('*** Adding switch\n')
    s1_cpor = net.addSwitch('s1_cpor')
    s2_fundaj = net.addSwitch('s2_fundaj')
    s3_ifpe = net.addSwitch('s3_ifpe')
    s4_popBD = net.addSwitch('s4_popBD')

    info('*** Creating links\n')
    net.addLink(h1_cpor, s1_cpor)
    net.addLink(h2_fundaj, s2_fundaj)
    net.addLink(h3_ifpe, s3_ifpe)
    net.addLink(h4_popBD, s4_popBD)
    net.addLink(s1_cpor, s2_fundaj)
    net.addLink(s3_ifpe, s4_popBD)
    net.addLink(s2_fundaj, s4_popBD)

    info('*** Starting network\n')
    net.start()

    info('*** Running CLI\n')
    CLI(net)

    info('*** Stopping network')
    net.stop()


if __name__ == '__main__':
    setLogLevel('info')
    sdnNet()
