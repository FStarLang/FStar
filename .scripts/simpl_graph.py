#!/usr/bin/env python3

from parse import parse
import sys

def add(adj, m, n):
    adj[m,n] = True

def redundant(adj, nodes, i, j):
    for k in nodes:
        if k == i or k == j: continue
        if adj.get((i,k), False) and adj.get((k,j), False):
            return True

    return False

# Assumes the graph is already transitive
def simpl (adj):
    new_adj = {}
    nodes = []
    for (i, j) in adj.keys():
        nodes.append(i)
        nodes.append(j)

    for (i, j) in adj.keys():
        if i == j: continue
        if redundant(adj, nodes, i ,j): continue
        new_adj[i,j] = True

    return new_adj

def output (adj):
    print ("digraph{")
    for (i, j) in adj.keys():
        print ("  \"{0}\" -> \"{1}\"".format(i, j))
    print ("}")

def parse_graph(fname):
    adj = {}
    f = open(fname, 'r')
    lines = f.readlines()
    for line in lines:
        try:
            # Brittle, FIXME
            res = parse("  \"{}\" -> \"{}\"\n", line)
            (i,j) = res.fixed
            add(adj, i, j)
        except AttributeError:
            pass
    return adj

file = sys.argv[1]
graph = parse_graph(file)
graph2 = simpl(graph)
output(graph2)
