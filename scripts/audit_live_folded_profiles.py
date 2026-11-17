#!/usr/bin/env python3
"""Independent finite checks AFTER the English proof and adversarial audit.

Tests the new LIVE folded-observation counterexample, not just the older
raw saturation quotient. No Lean modules or earlier checker are imported.
All nonempty irreducible tests of the path-blowups are singletons/edges;
the checker verifies triangle-freeness before using that characterization.
"""
from dataclasses import dataclass
from itertools import combinations
from pathlib import Path
import hashlib, json, time

@dataclass(frozen=True)
class Structure:
    n: int
    red: frozenset
    blue: frozenset
    marked: frozenset

def ed(a,b):
    return (min(a,b),max(a,b))

def wedge_blowup(i):
    nbase=3*i
    red={ed(a,b) for a,b in combinations(range(i),2)}
    cycle=[0]+list(range(i,nbase))
    blue={ed(cycle[t],cycle[(t+1)%len(cycle)]) for t in range(len(cycle))}
    def blow(edges):
        return frozenset(ed(a*i+x,b*i+y) for a,b in edges
                         for x in range(i) for y in range(i))
    return Structure(nbase*i,blow(red),blow(blue),frozenset(range(i)))

def components(a,removed):
    edges=a.red|a.blue
    neighbours=[set() for _ in range(a.n)]
    for u,v in edges:
        if u!=v:
            neighbours[u].add(v);neighbours[v].add(u)
    unseen=set(range(a.n))-set(removed)
    result=[]
    while unseen:
        x=min(unseen); unseen.remove(x); c={x}; stack=[x]
        while stack:
            y=stack.pop()
            z=neighbours[y]&unseen
            unseen-=z;c|=z;stack.extend(z)
        result.append(c)
    return result

def induce(a,vertices):
    vertices=tuple(vertices); rev={v:k for k,v in enumerate(vertices)}
    def rest(e):
        return frozenset(ed(rev[u],rev[v]) for u,v in e if u in rev and v in rev)
    return Structure(len(vertices),rest(a.red),rest(a.blue),
                     frozenset(rev[u] for u in a.marked if u in rev))

def blue_cycle(length):
    return Structure(length,frozenset(),
                     frozenset(ed(k,(k+1)%length) for k in range(length)),
                     frozenset())

def odd_walk_exists(length,target_length):
    states={0}
    for _ in range(length):
        states={(x+d)%target_length for x in states for d in (-1,1)}
    return 0 in states

def constructed_walk(i,j):
    assert i>=j>=2
    return [0,1]+[y for _ in range(i-j) for y in (2,1)]+list(range(2,2*j-1))+[0]

def ehn_trianglefree(a,b,f):
    assert len(f)==a.n and all(0<=y<b.n for y in f)
    gaif=a.red|a.blue
    assert not any(ed(x,y) in gaif and ed(x,z) in gaif and ed(y,z) in gaif
                   for x,y,z in combinations(range(a.n),3))
    # Every full singleton: unary values and both loops must reflect.
    for x in range(a.n):
        assert (x in a.marked)==(f[x] in b.marked)
        for aa,bb in ((a.red,b.red),(a.blue,b.blue)):
            assert (ed(x,x) in aa)==(ed(f[x],f[x]) in bb)
    # Every full two-vertex irreducible test, and every positive pair.
    for x,y in gaif:
        assert f[x]!=f[y]
        for aa,bb in ((a.red,b.red),(a.blue,b.blue)):
            assert (ed(x,y) in aa)==(ed(f[x],f[y]) in bb)
    return a.n+len(gaif)

def run():
    counts=dict(source_examples=0,minimal_cut_restorations=0,
                threshold_cells=0,positive_closed_walk_maps=0,
                full_irreducible_tests=0,triangle_extension_maps=0,
                distinct_live_profile_pairs=0,small_deletion_sets=0)
    matrix=[]
    for i in range(3,7):
        a=wedge_blowup(i)
        root=set(range(i*i,(i+1)*i))|set(range((3*i-1)*i,3*i*i))
        comp=set(range((i+1)*i,(3*i-1)*i))
        rest=set(range(i*i))
        cs=components(a,root)
        assert len(cs)==2 and comp in cs and rest in cs
        for r in root:
            assert len(components(a,root-{r}))==1
            counts['minimal_cut_restorations']+=1
        pat=induce(a,range(i*i,3*i*i))
        assert pat.n==2*i*i and not pat.marked and not pat.red
        assert len(pat.blue)==(2*i-1)*i*i
        counts['source_examples']+=1
        row=[]
        for j in range(3,7):
            b=blue_cycle(2*j-1)
            exists=odd_walk_exists(2*i-1,b.n)
            assert exists==(j<=i)
            row.append(exists);counts['threshold_cells']+=1
            if exists:
                walk=constructed_walk(i,j)
                assert len(walk)==2*i and walk[0]==walk[-1]==0
                f=tuple(walk[layer] for layer in range(2*i) for _ in range(i))
                roots=tuple(range(i))+tuple(range((2*i-1)*i,2*i*i))
                assert all(f[r]==0 for r in roots)
                counts['full_irreducible_tests']+=ehn_trianglefree(pat,b,f)
                counts['positive_closed_walk_maps']+=1
            # A FREE blue triangle extension over the same old singleton.
            x,y=b.n,b.n+1
            c=Structure(b.n+2,b.red,b.blue|frozenset((ed(0,x),ed(x,y),ed(y,0))),b.marked)
            assert induce(c,range(b.n))==b
            walk=constructed_walk(i,2)
            labels=(0,x,y)
            f=tuple(labels[walk[layer]] for layer in range(2*i) for _ in range(i))
            counts['full_irreducible_tests']+=ehn_trianglefree(pat,c,f)
            counts['triangle_extension_maps']+=1
        matrix.append(row)
    for i,k in combinations(range(3,7),2):
        assert not matrix[i-3][k-3] and matrix[k-3][k-3]
        counts['distinct_live_profile_pairs']+=1
    for i in (3,4):
        a=wedge_blowup(i); c=0
        for size in range(i):
            for deleted in combinations(range(a.n),size):
                assert len(components(a,deleted))==1
                c+=1
        assert c=={3:379,4:18473}[i]
        counts['small_deletion_sets']+=c
    return {'status':'PASS','scope':'finite sanity checks, not an infinite proof or Lean certificate',
            'indices':list(range(3,7)),'threshold_matrix':matrix,'counts':counts}

if __name__=='__main__':
    start=time.monotonic(); result=run()
    result['elapsed_seconds']=round(time.monotonic()-start,3)
    result['script_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    Path(__file__).with_suffix('.results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
