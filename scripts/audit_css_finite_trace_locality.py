#!/usr/bin/env python3
"""Independent bounded checks of the finite HE trace-lift argument.

No claim of a Lean proof or exhaustive unbounded verification. All relational
substructures are FULL induced substructures; source irreducibility is intrinsic.
Only the Python standard library is used.
"""
from __future__ import annotations
from dataclasses import dataclass
from functools import lru_cache
from itertools import combinations, permutations, product
from random import Random
import hashlib
import json
from pathlib import Path
from typing import Iterable

@dataclass(frozen=True)
class Rel:
    n: int
    arities: tuple[int, ...]
    tables: tuple[frozenset[tuple[int, ...]], ...]

    def __post_init__(self):
        assert len(self.arities) == len(self.tables)
        for r, table in zip(self.arities, self.tables):
            assert r > 0
            assert all(len(t) == r and all(0 <= x < self.n for x in t) for t in table)

    def induced(self, vertices: Iterable[int]) -> 'Rel':
        vs = tuple(sorted(vertices))
        idx = {v: i for i, v in enumerate(vs)}
        return Rel(len(vs), self.arities, tuple(frozenset(tuple(idx[x] for x in t)
                   for t in tab if all(x in idx for x in t)) for tab in self.tables))

@lru_cache(None)
def supports(a: Rel) -> tuple[frozenset[int], ...]:
    return tuple({frozenset(t) for tab in a.tables for t in tab})

@lru_cache(None)
def connected(a: Rel) -> bool:
    if a.n == 0:
        return False
    reached = {0}
    while True:
        nxt = reached | set().union(*(s for s in supports(a) if s & reached))
        if nxt == reached:
            return len(reached) == a.n
        reached = nxt

@lru_cache(None)
def irred_subsets(a: Rel) -> tuple[tuple[int, ...], ...]:
    ans = []
    for k in range(1, a.n + 1):
        for vs in combinations(range(a.n), k):
            vset = frozenset(vs)
            local = [s for s in supports(a) if s <= vset]
            if all(any({u,v} <= s for s in local) for u,v in combinations(vs,2)):
                ans.append(vs)
    return tuple(ans)

@lru_cache(None)
def constraints(a: Rel):
    """Positive tuples, and exact diagrams/inequalities of all induced tests."""
    positive = [(j,t,True) for j,tab in enumerate(a.tables) for t in tab]
    exact = set()
    unequal = set()
    for vs in irred_subsets(a):
        unequal.update(combinations(vs,2))
        for j,r in enumerate(a.arities):
            for t in product(vs, repeat=r):
                exact.add((j,t,t in a.tables[j]))
    return tuple(set(positive)|exact), tuple(unequal)

def is_he(a: Rel, b: Rel, f: tuple[int,...]) -> bool:
    if a.arities != b.arities or len(f) != a.n or any(x < 0 or x >= b.n for x in f):
        return False
    cs, neq = constraints(a)
    return all(f[u] != f[v] for u,v in neq) and all(
        (tuple(f[x] for x in t) in b.tables[j]) == val for j,t,val in cs)

@lru_cache(maxsize=30000)
def he_maps(a: Rel, b: Rel) -> tuple[tuple[int,...], ...]:
    assert a.arities == b.arities
    cs, neq = constraints(a)
    candidates = [[y for y in range(b.n) if all(
        (((x,)*r in a.tables[j]) == ((y,)*r in b.tables[j]))
        for j,r in enumerate(a.arities))] for x in range(a.n)]
    # Constraints are checked as soon as all their coordinates have been assigned.
    order = sorted(range(a.n), key=lambda x: (len(candidates[x]), -sum(x in t for _,t,_ in cs)))
    assigned = [-1] * a.n
    out = []
    def visit(k):
        if k == a.n:
            out.append(tuple(assigned)); return
        x = order[k]
        for y in candidates[x]:
            assigned[x] = y
            if any(assigned[u] >= 0 and assigned[v] >= 0 and assigned[u] == assigned[v]
                   for u,v in neq):
                continue
            if any(all(assigned[z] >= 0 for z in t) and
                   ((tuple(assigned[z] for z in t) in b.tables[j]) != val)
                   for j,t,val in cs):
                continue
            visit(k+1)
        assigned[x] = -1
    visit(0)
    return tuple(out)


def pattern_list(fs: tuple[Rel,...]) -> tuple[Rel,...]:
    ps = set()
    for f in fs:
        for k in range(1, f.n+1):
            for vs in combinations(range(f.n), k):
                p = f.induced(vs)
                if connected(p):
                    ps.add(p)
    return tuple(sorted(ps, key=lambda p: (p.n, repr(p.tables))))


def traces(ps: tuple[Rel,...], a: Rel, keep: tuple[int,...] | None = None,
           rename: dict[int,int] | None = None):
    """All nonempty rooted induced patterns, with repeated target coordinates."""
    keep_set = set(range(a.n) if keep is None else keep)
    rename = {x:x for x in keep_set} if rename is None else rename
    vals = set()
    for pi,p in enumerate(ps):
        for f in he_maps(p,a):
            eligible = [i for i,x in enumerate(f) if x in keep_set]
            for k in range(1,len(eligible)+1):
                for root in combinations(eligible,k):
                    vals.add((pi,root,tuple(rename[f[i]] for i in root)))
    return frozenset(vals)


def glue(base: Rel, petals: list[tuple[tuple[int,...],Rel]]) -> tuple[Rel,list[tuple[int,...]]]:
    """Petal's first |root| vertices map to the indicated ordered base tuple."""
    tabs = [set(t) for t in base.tables]
    next_vertex = base.n
    maps=[]
    for root, w in petals:
        assert len(set(root)) == len(root)
        # Root is in increasing order in every call below.
        assert w.induced(range(len(root))) == base.induced(root)
        emb = tuple(root) + tuple(range(next_vertex,next_vertex+w.n-len(root)))
        next_vertex += w.n-len(root)
        maps.append(emb)
        for j,tab in enumerate(w.tables):
            tabs[j].update(tuple(emb[x] for x in t) for t in tab)
    return Rel(next_vertex,base.arities,tuple(frozenset(t) for t in tabs)), maps


def model(colours: str, edges: Iterable[tuple[int,int]], triples=()) -> Rel:
    n=len(colours)
    unary=tuple(frozenset((i,) for i,c in enumerate(colours) if c==letter) for letter in 'CPQ')
    ee=frozenset((u,v) for e in edges for u,v in (e,e[::-1]))
    tt=frozenset(t for tri in triples for t in permutations(tri))
    return Rel(n,(1,1,1,2,3),unary+(ee,tt))


def finite_diagnostic():
    s=model('CPCQQ',[(0,1),(1,2),(2,3),(3,4),(4,0)])
    k=model('CQQ',[(0,1),(1,2),(2,0)])
    left=model('CP',[(0,1)])
    right=model('CQQ',[(0,1),(1,2),(2,0)],[(0,1,2)])
    fs=(s,k); ps=pattern_list(fs)
    assert not any(he_maps(f,left) or he_maps(f,right) for f in fs)
    assert traces(ps,left,(0,)) != traces(ps,right,(0,))
    h,_=glue(model('C',[]),[((0,),left),((0,),right)])
    assert len(he_maps(s,h))==2 and len(he_maps(k,h))==0
    # Enumerate root-C models with the specified four colour profiles, all E/T tables.
    models=[]
    enumerated=0
    for cols in ('C','CP','CQQ','CPP','CPPQ','CPQQ'):
        n=len(cols); pairs=list(combinations(range(n),2)); tris=list(combinations(range(n),3))
        for em in range(1<<len(pairs)):
            for tm in range(1<<len(tris)):
                a=model(cols,[e for i,e in enumerate(pairs) if em>>i&1],
                        [t for i,t in enumerate(tris) if tm>>i&1])
                enumerated+=1
                if not any(he_maps(f,a) for f in fs):
                    models.append(a)
    groups={}
    for a in models:
        groups.setdefault(traces(ps,a,(0,)),[]).append(a)
    rng=Random(170112026)
    pairs_to_test=[]
    for group in groups.values():
        if len(group)>1:
            for _ in range(min(12,len(group))):
                pairs_to_test.append((rng.choice(group),rng.choice(group)))
    # Restrict to moderate number; all generator models and all root profiles were enumerated.
    rng.shuffle(pairs_to_test); pairs_to_test=pairs_to_test[:100]
    trace_instances=0; noninjective=0
    for a,b in pairs_to_test:
        d, embs=glue(model('C',[]),[((0,),a),((0,),b)])
        assert not any(he_maps(f,d) for f in fs)
        for w,emb in zip((a,b),embs):
            tr=traces(ps,d,emb,{x:i for i,x in enumerate(emb)})
            expect=traces(ps,w)
            assert tr==expect
            trace_instances+=len(expect)
        for p in ps:
            noninjective+=sum(len(set(f))<len(f) for f in he_maps(p,d))
    return dict(patterns=len(ps),enumerated_old_models=enumerated,allowed_models=len(models),
                singleton_profiles=len(groups),same_profile_amalgams=len(pairs_to_test),
                positive_side_trace_instances_checked=trace_instances,
                noninjective_pattern_maps_in_checked_amalgams=noninjective,
                distinct_root_regression='PASS')


def graph(n,edges):
    return Rel(n,(2,),(frozenset((x,y) for u,v in edges for x,y in ((u,v),(v,u))),))


def check_triangle_local_witness_covers():
    """All 4-vertex triangle-free bases with every consistent neighbour flag.

    Forb_he(K3) trace data are exactly the graph and the existential nonisolation
    flags (up to duplicate rooted-pattern symbols). Independent choices of local
    witnesses are attached over ALL <=3 subsets. This tests n=4 > N=3.
    """
    f=graph(3,[(0,1),(1,2),(0,2)]); ps=pattern_list((f,))
    n=4; ep=list(combinations(range(n),2)); total=0; vertices=0; maxw=0; maximal_count=0
    for em in range(1<<len(ep)):
        base=graph(n,[e for i,e in enumerate(ep) if em>>i&1])
        if he_maps(f,base): continue
        neighbours={x for t in base.tables[0] for x in t}
        isolates=sorted(set(range(n))-neighbours)
        for bits in range(1<<len(isolates)):
            active=neighbours|{x for i,x in enumerate(isolates) if bits>>i&1}
            # Independent central model for the intended global trace assignment.
            edges=list({tuple(sorted(t)) for t in base.tables[0]})
            cnt=n
            for v in sorted(active-neighbours):
                edges.append((v,cnt));cnt+=1
            central=graph(cnt,edges)
            expected=traces(ps,central,tuple(range(n)))
            petals=[]
            for size in range(1,4):
                for z in combinations(range(n),size):
                    wz=base.induced(z)
                    ee=list({tuple(sorted(t)) for t in wz.tables[0]})
                    nv=size
                    current={x for t in wz.tables[0] for x in t}
                    for i,v in enumerate(z):
                        if v in active and i not in current:
                            # Choose different finite witnesses without changing root trace.
                            ee.append((i,nv));nv+=1
                            if (sum(z)+i+bits)%2:
                                ee.append((nv-1,nv));nv+=1
                    w=graph(nv,ee)
                    assert not he_maps(f,w)
                    got=traces(ps,w,tuple(range(size)),{i:v for i,v in enumerate(z)})
                    assert got==traces(ps,central,z)
                    petals.append((z,w))
            d,_=glue(base,petals)
            assert not he_maps(f,d)
            assert traces(ps,d,tuple(range(n)))==expected
            total+=1; vertices+=d.n;maxw=max(maxw,d.n)
            if active == set(range(n)):
                maximal_count+=1
    return dict(covers=total,subsets_per_cover=14,base_vertices=4,forbidden_size=3,
                total_glued_vertices=vertices,max_glued_vertices=maxw,
                maximal_profile_covers=maximal_count,
                local_to_global_trace_and_avoidance='PASS')


def intrinsic_decomposition_check():
    """All simple E + symmetric-distinct T tables on <=4 source vertices,
    all assignments to a base and three private witness regions. Checks the
    source-side component and full-test assertions in the multi-witness proof.
    """
    model_count=0; compatible=0; test_checks=0; comps=0
    for n in range(1,5):
        pairs=list(combinations(range(n),2)); tris=list(combinations(range(n),3))
        for em in range(1<<len(pairs)):
            for tm in range(1<<len(tris)):
                edges=[e for i,e in enumerate(pairs) if em>>i&1]
                tt=[t for i,t in enumerate(tris) if tm>>i&1]
                p=Rel(n,(2,3),(frozenset((u,v) for e in edges for u,v in (e,e[::-1])),
                              frozenset(t for tri in tt for t in permutations(tri))))
                model_count+=1
                if not connected(p): continue
                for labels in product(range(4),repeat=n):
                    base={i for i,x in enumerate(labels) if x==0}
                    if not base: continue
                    if any(len({labels[x] for x in s}-{0})>1 for s in supports(p)):continue
                    compatible+=1
                    pieces=[]
                    for petal in range(1,4):
                        vset={i for i,x in enumerate(labels) if x in (0,petal)}
                        left=set(vset)
                        while left:
                            component={min(left)}
                            while True:
                                nxt=component|set().union(*(s for s in supports(p)
                                                           if s<=vset and s&component))
                                if nxt==component: break
                                component=nxt
                            left-=component
                            if any(labels[x]==petal for x in component):
                                assert component&base
                                comps+=1; pieces.append(component)
                    for vs in irred_subsets(p):
                        u=set(vs)
                        assert u<=base or any(u<=c for c in pieces)
                        test_checks+=1
    return dict(source_relation_tables=model_count,compatible_based_region_assignments=compatible,
                transferred_components=comps,irreducible_test_containment_checks=test_checks)


def main():
    result={
      'scope':'English theorem has separate proof; these are bounded computational regressions only.',
      'intrinsic_multi_witness_decomposition':intrinsic_decomposition_check(),
      'coloured_ternary_diagnostic_and_amalgams':finite_diagnostic(),
      'local_to_global_witness_covers':check_triangle_local_witness_covers(),
      'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'status':'PASS'
    }
    path=Path(__file__).with_name('results.json')
    path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    main()
