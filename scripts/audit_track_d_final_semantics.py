#!/usr/bin/env python3
"""Final independent finite audit of the English lifting obstruction.

No import of earlier checkers. Generic relational EHN tests are computed
from every INDUCED source subset, using all tuple coordinates. Supports
arity 0, 1, 2 and 3, loops and directed binary relations. Finite evidence
is not a proof of the infinite construction or a Lean certificate.
"""
from dataclasses import dataclass
from itertools import combinations, product
from pathlib import Path
import hashlib, json, time

@dataclass
class Structure:
    n: int
    arity: dict
    rel: dict

def subsets(n):
    for mask in range(1 << n):
        yield tuple(x for x in range(n) if mask & (1 << x))

def irreducible_tests(a):
    """Full relational irreducibility, computed AFTER restriction to S."""
    supports = {frozenset(t) for ts in a.rel.values() for t in ts}
    answer = []
    for vs in subsets(a.n):
        S = frozenset(vs)
        pair_cover = set()
        for t in supports:
            if t <= S:
                pair_cover.update(combinations(sorted(t), 2))
        if all(p in pair_cover for p in combinations(vs, 2)):
            answer.append(vs)
    return answer

def full_on(a, b, f, vs):
    return (len({f[x] for x in vs}) == len(vs)
        and all((t in a.rel[R]) == (tuple(f[x] for x in t) in b.rel[R])
                for R, ar in a.arity.items() for t in product(vs, repeat=ar)))

def ehn(a, b, f, tests=None):
    return (len(f) == a.n and all(0 <= x < b.n for x in f)
        and all(tuple(f[x] for x in t) in b.rel[R]
                for R, ts in a.rel.items() for t in ts)
        and all(full_on(a, b, f, vs)
                for vs in (irreducible_tests(a) if tests is None else tests)))

def generated(a, f):
    n = max(f, default=-1) + 1
    assert set(f) == set(range(n))
    return Structure(n, a.arity,
        {R: {tuple(f[x] for x in t) for t in ts} for R, ts in a.rel.items()})

def gamma_edge(m, x, y):
    return x != y and m <= (y-x) % (3*m-1) <= 2*m-1

def forbidden_source(m):
    sig = {'C': 1, 'P': 1, 'Q': 1, 'Start': 1, 'End': 1,
           'E': 2, 'D': 2, 'T': 3}
    rel = {r: set() for r in sig}
    cut = tuple(range(m, 2*m))
    private = tuple(x for x in range(3*m-1) if x not in cut)
    root = {v: k for k, v in enumerate(cut)}
    rel['C'] = {(i,) for i in range(m)}
    n = m
    for side in ('P', 'Q'):
        chart = dict(root)
        for v in private:
            chart[v] = n
            rel[side].add((n,))
            if v == 1: rel['Start'].add((n,))
            if v == 3*m-2: rel['End'].add((n,))
            n += 1
        rel['E'].update((chart[x], chart[y]) for x, y in product(range(3*m-1), repeat=2)
                        if gamma_edge(m, x, y))
        chain = tuple(x for j in range(1, m) for x in (j, 2*m+j-1))
        rel['D'].update((chart[x], chart[y]) for x, y in zip(chain, chain[1:]))
    a = Structure(n, sig, rel)
    fold = tuple(0 if x < m else 1 + x-m for x in range(n))
    image = generated(a, fold)
    p = {0} | {x for x, in image.rel['P']}
    q = {0} | {x for x, in image.rel['Q']}
    target = Structure(image.n, sig, {r: set(ts) for r, ts in image.rel.items()})
    target.rel['T'] = {t for s in (p,q) for t in product(s, repeat=3) if len(set(t)) == 3}
    return a, fold, image, target, (p,q)

def coloured_triangle(a, vs):
    return (len(vs) == 3
        and all((x,y) in a.rel['E'] for x,y in product(vs,repeat=2) if x != y)
        and all((x,x) not in a.rel[R] for R in ('E','D') for x in vs)
        and not any(t in a.rel['T'] for t in product(vs,repeat=3)))

def root_deletion_connected(a, deleted):
    rem=set(range(a.n))-{deleted}
    if not rem: return True
    seen={next(iter(rem))}; todo=list(seen)
    while todo:
        x=todo.pop()
        new={y for y in rem-seen if (x,y) in a.rel['E'] or (y,x) in a.rel['E']}
        seen |= new; todo.extend(new)
    return seen == rem

def protected_amalgams():
    c={'generic_source_subsets':0,'actual_source_tests':0,'generated_EHN_maps':0,
       'decorated_EHN_maps':0,'single_cross_tuple_mutations':0,
       'maximal_cross_extensions':0,'extensions_with_an_extra_vertex':0,
       'generated_triangles':0,'singleton_cut_checks':0}
    certificate={}
    for m in (3,4):
        a,f,q,d,blocks=forbidden_source(m)
        tests=irreducible_tests(a)
        c['generic_source_subsets'] += 1 << a.n
        c['actual_source_tests'] += len(tests)
        assert all(len(vs)<=2 for vs in tests)
        assert ehn(a,q,f,tests);c['generated_EHN_maps']+=1
        assert ehn(a,d,f,tests);c['decorated_EHN_maps']+=1
        for vs in tests:
            assert any({f[x] for x in vs} <= block for block in blocks)
        for x in range(a.n):
            assert root_deletion_connected(a,x)
            c['singleton_cut_checks']+=1
        mixed = {R: [t for t in product(range(d.n), repeat=ar)
                     if not any(set(t)<=block for block in blocks)]
                 for R,ar in a.arity.items() if ar>=2}
        # EVERY individual permissible binary/ternary cross-tuple, not samples.
        for R, tuples in mixed.items():
            for t in tuples:
                assert t not in d.rel[R]
                d.rel[R].add(t)
                assert ehn(a,d,f,tests), (m,R,t)
                d.rel[R].remove(t)
                c['single_cross_tuple_mutations']+=1
        # All cross-tuples simultaneously, allowing asymmetric E and arbitrary D.
        dense=Structure(d.n,d.arity,{R:set(ts)|set(mixed.get(R,())) for R,ts in d.rel.items()})
        assert ehn(a,dense,f,tests);c['maximal_cross_extensions']+=1
        # Arbitrary exterior vertices: add every tuple touching one new vertex.
        n=d.n; extended=Structure(n+1,d.arity,{R:set(ts) for R,ts in dense.rel.items()})
        for R, ar in d.arity.items():
            extended.rel[R].update(t for t in product(range(n+1),repeat=ar) if n in t)
        assert ehn(a,extended,f,tests);c['extensions_with_an_extra_vertex']+=1
        triangles=[vs for vs in combinations(range(q.n),3) if coloured_triangle(q,vs)]
        assert len(triangles)==m*(m-1)
        assert all(not full_on(q,d,tuple(range(q.n)),vs) for vs in triangles)
        c['generated_triangles']+=len(triangles)
        if m==3:
            certificate={'parameter':m,'source_size':a.n,'target_size':d.n,
                'signature':a.arity,'source':{R:sorted(ts) for R,ts in a.rel.items()},
                'fold':f,'halves':[sorted(s) for s in blocks],
                'generated_image':{R:sorted(ts) for R,ts in q.rel.items()},
                'decorated_target':{R:sorted(ts) for R,ts in d.rel.items()},
                'all_irreducible_source_tests':tests,'generated_forbidden_triangles':triangles}
    return c,certificate

def canonical_kernels(n):
    if n==0:
        yield ();return
    def rec(v,maximum):
        if len(v)==n:
            yield tuple(v);return
        for x in range(maximum+2):
            yield from rec(v+[x],max(x,maximum))
    yield from rec([0],0)

def binary_nullary_audit():
    sig={'H':0,'M':1,'E':2,'D':2}
    counts={'sources':0,'kernels':0,'EHN_target_extensions':0,
            'EHN_generated_inclusions':0,'nonfull_inclusions':0,
            'nullary_reflections':0}
    for n in (1,2):
        coordinates=[(R,t) for R,ar in sig.items() for t in product(range(n),repeat=ar)]
        for mask in range(1<<len(coordinates)):
            rel={R:set() for R in sig}
            for i,(R,t) in enumerate(coordinates):
                if mask & (1<<i):rel[R].add(t)
            a=Structure(n,sig,rel); atests=irreducible_tests(a);counts['sources']+=1
            for f in canonical_kernels(n):
                counts['kernels']+=1
                if any(len({f[x] for x in s})!=len(s) for s in atests):continue
                q=generated(a,f)
                fixed={};contradiction=False
                for s in atests:
                    for R,ar in sig.items():
                        for t in product(s,repeat=ar):
                            k=(R,tuple(f[x] for x in t));value=t in rel[R]
                            if k in fixed and fixed[k]!=value:contradiction=True
                            fixed[k]=value
                if contradiction:continue
                all_coords=[(R,t) for R,ar in sig.items() for t in product(range(q.n),repeat=ar)]
                free=[k for k in all_coords if k not in fixed]
                for values in product((False,True),repeat=len(free)):
                    b_rel={R:set() for R in sig}
                    for (R,t),value in list(fixed.items())+list(zip(free,values)):
                        if value:b_rel[R].add(t)
                    b=Structure(q.n,sig,b_rel)
                    assert ehn(a,b,f,atests)
                    assert ehn(a,q,f,atests)
                    assert ehn(q,b,tuple(range(q.n)))
                    counts['EHN_target_extensions']+=1
                    counts['EHN_generated_inclusions']+=1
                    counts['nullary_reflections']+=int(q.rel['H']==b.rel['H'])
                    if not full_on(q,b,tuple(range(q.n)),tuple(range(q.n))):
                        counts['nonfull_inclusions']+=1
    return counts

def ternary_boundary():
    sig={'E':2,'T':3}
    a=Structure(5,sig,{'E':{(x,y) for x,y in product(range(5),repeat=2)
                                   if (x-y)%5 in (1,4)},'T':set()})
    f=(0,1,2,0,1);q=generated(a,f)
    d=Structure(3,sig,{'E':set(q.rel['E']),'T':{(0,1,2)}})
    assert ehn(a,q,f) and ehn(a,d,f)
    assert not ehn(q,d,(0,1,2))
    return {'source_EHN_into_both':True,'generated_inclusion_EHN':False,
            'new_tuple':[0,1,2],'source_map':list(f)}

if __name__=='__main__':
    start=time.monotonic()
    counts,certificate=protected_amalgams()
    result={'status':'PASS','scope':'finite independent semantic checks; not kernel certification',
        'protected_amalgams':counts,'binary_with_two_relations_and_nullary':binary_nullary_audit(),
        'sharp_ternary_boundary':ternary_boundary(),
        'elapsed_seconds':round(time.monotonic()-start,3),
        'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    here=Path(__file__).parent
    (here/'finite_certificate_m3.json').write_text(json.dumps(certificate,indent=2)+'\n')
    (here/'final_validation_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
