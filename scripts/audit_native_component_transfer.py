#!/usr/bin/env python3
"""Finite audit of the English one-pass native component transfer.

All source structures on <=3 vertices in a loopless symmetric binary
relation and one PARTIAL UNARY FUNCTION. Irreducibility is computed by
FULL CLOSED free decompositions, NOT by ambient Gaifman cliques.
Targets: all 72 full star amalgams of two 2-point sides over a 1-point
closed root, plus 8 larger targets with genuine function closures.
Checks all EHN source maps, all available one-component right moves,
and the simultaneous move whenever every left component transfers.
"""
from dataclasses import dataclass
from itertools import product, combinations
from pathlib import Path
import hashlib, json, time

@dataclass(frozen=True)
class Native:
    n: int
    edges: frozenset
    u: tuple

def edge(x,y): return (min(x,y),max(x,y))
def subsets(n): return [frozenset(x for x in range(n) if m&(1<<x)) for m in range(1<<n)]
def closed(a,s): return all(a.u[x]==-1 or a.u[x] in s for x in s)
def adjacent(a,x,y):
    return x!=y and (edge(x,y) in a.edges or a.u[x]==y or a.u[y]==x)
def irreducibles(a):
    c=[s for s in subsets(a.n) if closed(a,s)]
    out=[]
    for s in c:
        reducible=False
        for p in c:
            if not p<s: continue
            for q in c:
                if q<s and p|q==s:
                    # Closed sides already preserve every positive unary fibre.
                    if all({x,y}<=p or {x,y}<=q for x,y in a.edges if x in s and y in s):
                        reducible=True;break
            if reducible: break
        if not reducible: out.append(tuple(sorted(s)))
    return out

def full(a,b,f,s):
    if len({f[x] for x in s})!=len(s): return False
    if any(b.u[f[x]]!=(-1 if a.u[x]==-1 else f[a.u[x]]) for x in s): return False
    return all((edge(x,y) in a.edges)==(edge(f[x],f[y]) in b.edges)
               for x,y in combinations(s,2))
def ehn(a,b,f,tests):
    if any(b.u[f[x]]!=f[a.u[x]] for x in range(a.n) if a.u[x]!=-1): return False
    if any(f[x]==f[y] or edge(f[x],f[y]) not in b.edges for x,y in a.edges): return False
    return all(full(a,b,f,s) for s in tests)
def induce(a,s):
    s=tuple(sorted(s));r={v:k for k,v in enumerate(s)}
    assert closed(a,set(s))
    return Native(len(s),frozenset(edge(r[x],r[y]) for x,y in a.edges if x in r and y in r),
                  tuple(-1 if a.u[x]==-1 else r[a.u[x]] for x in s)),s

def comps(a,root):
    rem=set(range(a.n))-set(root);out=[]
    while rem:
        x=min(rem); rem.remove(x);seen={x}; todo=[x]
        while todo:
            x=todo.pop(); nxt={y for y in rem if adjacent(a,x,y)}
            rem-=nxt;seen|=nxt;todo.extend(nxt)
        out.append(seen)
    return out

def models(n):
    pairs=list(combinations(range(n),2))
    for bits in product((False,True),repeat=len(pairs)):
        es=frozenset(x for x,b in zip(pairs,bits) if b)
        for u in product(range(-1,n),repeat=n):yield Native(n,es,u)

def targets():
    out=[]
    for u0,u1,u2,e1,e2 in product((-1,0),(-1,0,1),(-1,0,2),(False,True),(False,True)):
        es=frozenset(e for e,b in (((0,1),e1),((0,2),e2)) if b)
        out.append((Native(3,es,(u0,u1,u2)),{0,1},{0,2}))
    for u0,linked,rel in product((-1,0),(False,True),(False,True)):
        us=(u0,2,0,4,0) if linked else (u0,-1,-1,-1,-1)
        es=frozenset(((0,1),(1,2),(0,3),(3,4))) if rel else frozenset()
        out.append((Native(5,es,us),{0,1,2},{0,3,4}))
    return out

def run():
    counts=dict(sources=0,targets=0,maps_tested=0,ehn_maps=0,
                closed_root_tests=0,source_component_decompositions=0,
                irreducible_no_crossing_checks=0,right_component_candidates=0,
                valid_right_transfers=0,strict_support_checks=0,
                simultaneous_transfers=0,nonclique_irreducible_source_tests=0)
    ts=targets(); counts['targets']=len(ts)
    # Avoid re-enumerating possible piece maps for each original f.
    cache={}
    for a in (a for n in range(4) for a in models(n)):
        counts['sources']+=1;tests=irreducibles(a)
        counts['nonclique_irreducible_source_tests']+=sum(
            not all(adjacent(a,x,y) for x,y in combinations(s,2)) for s in tests)
        for tid,(d,left,right) in enumerate(ts):
            assert left&right=={0} and closed(d,left) and closed(d,right)
            for f in product(range(d.n),repeat=a.n):
                counts['maps_tested']+=1
                if not ehn(a,d,f,tests):continue
                counts['ehn_maps']+=1
                root=frozenset(x for x in range(a.n) if f[x]==0)
                assert closed(a,root);counts['closed_root_tests']+=1
                cs=comps(a,root)
                assert all({f[x] for x in c}<=left-{0} or {f[x] for x in c}<=right-{0} for c in cs)
                chosen=[];possible=True
                for c in cs:
                    p=frozenset(root|c);q=frozenset(set(range(a.n))-c)
                    assert closed(a,p) and closed(a,q)
                    assert all({x,y}<=p or {x,y}<=q for x,y in a.edges)
                    counts['source_component_decompositions']+=1
                    for test in tests:
                        assert set(test)<=p or set(test)<=q
                        counts['irreducible_no_crossing_checks']+=1
                    if not {f[x] for x in c}<=left-{0}:continue
                    key=(a,tid,root,p)
                    if key not in cache:
                        pa,vs=induce(a,p);ptests=irreducibles(pa);good=[]
                        private=[x for x in vs if x not in root]
                        for vals in product(sorted(right),repeat=len(private)):
                            h={x:0 for x in root};h.update(zip(private,vals))
                            ps=tuple(h[x] for x in vs)
                            counts['right_component_candidates']+=1
                            if ehn(pa,d,ps,ptests):good.append(h)
                        cache[key]=good
                    good=cache[key]
                    if not good:possible=False;continue
                    chosen.append((c,good[0]))
                    for h in good:
                        g=tuple(h[x] if x in c else f[x] for x in range(a.n))
                        assert ehn(a,d,g,tests)
                        assert all(g[x]==f[x] for x in range(a.n) if f[x] in right)
                        old=sum(f[x] in left-{0} for x in range(a.n))
                        new=sum(g[x] in left-{0} for x in range(a.n))
                        assert old-new==len(c)>0
                        counts['valid_right_transfers']+=1
                        counts['strict_support_checks']+=1
                if possible:
                    g=list(f)
                    for c,h in chosen:
                        for x in c:g[x]=h[x]
                    assert all(y in right for y in g)
                    assert ehn(a,d,tuple(g),tests)
                    assert all(g[x]==f[x] for x in range(a.n) if f[x] in right)
                    counts['simultaneous_transfers']+=1
    assert counts['nonclique_irreducible_source_tests']>0
    assert counts['valid_right_transfers']>0
    return dict(status='PASS',scope='bounded native partial-unary sanity check; not a general proof or Lean certificate',counts=counts)

if __name__=='__main__':
    start=time.monotonic();result=run();result['elapsed_seconds']=round(time.monotonic()-start,3)
    result['script_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    Path(__file__).with_suffix('.results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
