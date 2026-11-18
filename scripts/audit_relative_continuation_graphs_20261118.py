#!/usr/bin/env python3
"""Exact small-graph regression for raw C5 traces and continuation classes.

This is an independent finite checker, NOT a proof for arbitrary
forbidden families or functional languages. Every graph is loopless,
undirected, and rooted over two distinct nonadjacent vertices.
"""
from collections import defaultdict

def graphs(n):
    edges=[(i,j) for i in range(n) for j in range(i+1,n)]
    for bits in range(1<<len(edges)):
        e=frozenset(p for k,p in enumerate(edges) if bits&(1<<k))
        if (0,1) not in e: yield e

def edge(e,x,y):
    return x!=y and tuple(sorted((x,y))) in e

def walk(e,n,k,x,y):
    v={x}
    for _ in range(k):
        v={z for a in v for z in range(n) if edge(e,a,z)}
    return y in v

def allowed(e,n):
    # A C5 homomorphism exists iff there is a closed walk of length five.
    return not any(walk(e,n,5,x,x) for x in range(n))

def trace(e,n,diagonals=True):
    pairs=((0,0),(0,1),(1,0),(1,1)) if diagonals else ((0,1),(1,0))
    return tuple(walk(e,n,k,x,y) for k in (2,3) for x,y in pairs)

def glue(a,na,b,nb):
    shift=lambda x: x if x<2 else na+x-2
    return a | frozenset(tuple(sorted((shift(x),shift(y)))) for x,y in b)

def stable(e,n,d,nd,embed):
    return all(walk(e,n,k,x,y)==walk(d,nd,k,embed(x),embed(y))
               for k in (2,3) for x in range(n) for y in range(n))

def main():
    cases=[(n,e,trace(e,n)) for n in range(2,5) for e in graphs(n)
           if allowed(e,n)]
    assert len(cases)==30
    matching=0
    rows=defaultdict(list)
    for i,(na,a,ta) in enumerate(cases):
        row=[]
        for nb,b,tb in cases:
            d=glue(a,na,b,nb); nd=na+nb-2
            ok=allowed(d,nd)
            row.append(ok)
            if ta==tb:
                matching+=1
                assert ok
                assert stable(a,na,d,nd,lambda x:x)
                assert stable(b,nb,d,nd,lambda x:x if x<2 else na+x-2)
        rows[tuple(row)].append(i)
    assert matching==196 and len(rows)==3
    a=frozenset(); b=frozenset({(0,2)})
    assert trace(a,2,False)==trace(b,3,False)
    assert trace(a,2)!=trace(b,3)
    assert not stable(a,2,glue(a,2,b,3),3,lambda x:x)
    print("PASS: 30 allowed graphs, 900 ordered pairs, 196 matching raw-trace pairs,")
    print("3 continuation classes; diagonal omission changes the canonical trace.")

if __name__=="__main__":
    main()
