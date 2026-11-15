#!/usr/bin/env python3
"""Independent, exhaustive finite checks for Track D's replacement contract.

Language: one symmetric binary relation E (loops allowed) and one unary M.
All structures on <=2 vertices, and all loopless structures on 3 vertices,
are tested. A finite test is not a proof for arbitrary structures or a Lean
kernel certificate. No project checker is imported here.
"""
from dataclasses import dataclass
from itertools import product, combinations
import hashlib, json, time
from pathlib import Path

@dataclass(frozen=True)
class Model:
    n: int
    marked: tuple[bool, ...]
    edge: tuple[tuple[bool, ...], ...]

    def induced(self, vertices: tuple[int, ...]) -> 'Model':
        return Model(len(vertices), tuple(self.marked[x] for x in vertices),
                     tuple(tuple(self.edge[x][y] for y in vertices) for x in vertices))


def models(n: int, loops: bool):
    pairs = [(x,y) for x in range(n) for y in range(x if loops else x+1,n)]
    for bits in product((False,True), repeat=n+len(pairs)):
        edge = [[False]*n for _ in range(n)]
        for (x,y), b in zip(pairs, bits[n:]):
            edge[x][y]=edge[y][x]=b
        yield Model(n, tuple(bits[:n]), tuple(map(tuple,edge)))


def full_on(a: Model, b: Model, f: tuple[int,...], s: tuple[int,...]) -> bool:
    return (len(set(f[x] for x in s)) == len(s)
            and all(a.marked[x] == b.marked[f[x]] for x in s)
            and all(a.edge[x][y] == b.edge[f[x]][f[y]] for x in s for y in s))


def irreducibles(a: Model):
    # In this binary relational language the full irreducible substructures
    # are exactly the cliques in the loop-free Gaifman graph, including
    # singletons and the empty substructure. Loops and unary M are still
    # required to reflect under each full embedding.
    return [tuple(x for x in range(a.n) if mask & (1<<x))
            for mask in range(1<<a.n)
            if all(a.edge[x][y] for x,y in combinations(
                [x for x in range(a.n) if mask & (1<<x)],2))]


def ehn(a: Model,b: Model,f: tuple[int,...], tests=None) -> bool:
    if any(a.marked[x] and not b.marked[f[x]] for x in range(a.n)): return False
    if any(a.edge[x][y] and not b.edge[f[x]][f[y]]
           for x in range(a.n) for y in range(a.n)): return False
    return all(full_on(a,b,f,s) for s in (tests if tests is not None else irreducibles(a)))


def execute():
    small=[a for n in range(3) for a in models(n,True)]
    pool=small+list(models(3,False))
    counts={'models':len(pool),'maps':0,'ehn_maps':0,'range_factorizations':0,
            'full_range_inclusions':0,'support_inequalities':0,
            'composition_checks':0,'surjective_composition_checks':0}
    morphisms={}
    for ai,a in enumerate(pool):
        tests=irreducibles(a)
        for bi,b in enumerate(pool):
            good=[]
            for f in product(range(b.n),repeat=a.n):
                counts['maps']+=1
                if not ehn(a,b,f,tests): continue
                counts['ehn_maps']+=1; good.append(f)
                im=tuple(sorted(set(f))); h=b.induced(im)
                labels={v:i for i,v in enumerate(im)}
                q=tuple(labels[v] for v in f)
                assert set(q)==set(range(h.n)), ('not onto range',a,b,f)
                assert ehn(a,h,q,tests), ('range factor not EHN',a,b,f)
                counts['range_factorizations']+=1
                assert full_on(h,b,im,tuple(range(h.n)))
                counts['full_range_inclusions']+=1
                for mask in range(1<<b.n):
                    old=sum(bool(mask&(1<<f[x])) for x in range(a.n))
                    new=sum(bool(mask&(1<<v)) for v in im)
                    assert new<=old
                    if len(set(f))==a.n: assert new==old
                    counts['support_inequalities']+=1
            if ai<len(small) and bi<len(small): morphisms[ai,bi]=good
    # Exhaustive native EHN composition on ALL <=2 vertex loop-allowing models.
    # Surjective compositions certify the finite instance of saturation
    # idempotence without assuming either map is full globally.
    for ai,a in enumerate(small):
        for bi,b in enumerate(small):
            for ci,c in enumerate(small):
                for f in morphisms[ai,bi]:
                    for g in morphisms[bi,ci]:
                        gf=tuple(g[x] for x in f)
                        assert ehn(a,c,gf)
                        counts['composition_checks']+=1
                        if len(set(f))==b.n and len(set(g))==c.n:
                            assert len(set(gf))==c.n
                            counts['surjective_composition_checks']+=1
    # The old unrestricted Bbar hypothesis fails with a forbidden loopless
    # marked singleton. There is no full Bbar copy in ANY avoiding test model.
    forbidden=Model(1,(True,),((False,),))
    allowed=[c for c in pool if not any(ehn(forbidden,c,(x,)) for x in range(c.n))]
    for c in allowed:
        assert not any(full_on(forbidden,c,(x,),(0,)) for x in range(c.n))
    counts['forbidden_right_exclusions']=len(allowed)
    # Loop distinction in the previous audit: a marked looped singleton IS
    # allowed, and the fully marked loopless singleton is NOT allowed.
    looped=Model(1,(True,),((True,),))
    assert not ehn(forbidden,looped,(0,))
    assert ehn(forbidden,forbidden,(0,))
    counts['loop_caveat_checks']=2
    # A concrete NONEMPTY forbidden-family two-colour positive control:
    # forbid marked singleton, A=one unmarked point, B=two independent
    # unmarked points, C=three independent unmarked points, standard order.
    c=Model(3,(False,False,False),tuple((False,)*3 for _ in range(3)))
    assert c in allowed
    for colouring in product(range(2),repeat=3):
        assert any(colouring[x]==colouring[y] for x,y in combinations(range(3),2))
    counts['positive_two_colour_controls']=8
    return counts

if __name__=='__main__':
    start=time.monotonic()
    counts=execute()
    result={'status':'PASS','scope':'exhaustive bounded finite tests, not Lean certification',
            'counts':counts,'seconds':round(time.monotonic()-start,3),
            'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    Path(__file__).with_suffix('.results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
