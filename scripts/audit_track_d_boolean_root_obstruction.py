#!/usr/bin/env python3
"""Independent reimplementation of the permanent-root obstruction.

No import of the earlier checker. Tests protected source supports, the
Boolean family of equal-size finite contexts, and arbitrary cross-tuple
invariance by proving all tested image tuples lie inside a full half.
Not an infinite proof and not a Lean certificate.
"""
from itertools import combinations, product
from dataclasses import dataclass
from pathlib import Path
import hashlib, json, time

C,P,Q,START,END = 1,2,4,8,16
@dataclass(frozen=True)
class R:
    labels: tuple[int,...]
    E: frozenset[tuple[int,int]]
    D: frozenset[tuple[int,int]]
    blocks: tuple[frozenset[int],...]=()
    @property
    def n(self):return len(self.labels)
    def t(self,xyz):return len(set(xyz))==3 and any(set(xyz)<=b for b in self.blocks)

def cyclic_edge(m,u,v):return u!=v and m <= (v-u)%(3*m-1) <= 2*m-1

def source(m):
    cut=list(range(m,2*m)); priv=[x for x in range(3*m-1) if x not in cut]
    root={v:i for i,v in enumerate(cut)}; labs=[C]*m; E=set();D=set();views=[]
    for side in (P,Q):
        mp=dict(root)
        for v in priv:
            mp[v]=len(labs)
            labs.append(side|(START if v==1 else END if v==3*m-2 else 0))
        for u,v in product(range(3*m-1),repeat=2):
            if cyclic_edge(m,u,v):E.add((mp[u],mp[v]))
        chain=[x for k in range(1,m) for x in (k,2*m+k-1)]
        D.update((mp[x],mp[y]) for x,y in zip(chain,chain[1:]))
        views.append(mp)
    return R(tuple(labs),frozenset(E),frozenset(D)),views

def bouquet(word,first=3):
    labs=[C]; E=set(); D=set(); blocks=[];half_maps={}
    for m,bit in enumerate(word,first):
        side=P if bit==0 else Q
        vs=[0]+list(range(1,m))+list(range(2*m,3*m-1))
        mp={v:len(labs)+k for k,v in enumerate(vs)}
        for v in vs:labs.append(side|(START if v==1 else END if v==3*m-2 else 0))
        b=frozenset({0}|set(mp.values()));blocks.append(b)
        for v in vs:E.add((0,mp[v]));E.add((mp[v],0))
        for u,v in product(vs,repeat=2):
            if cyclic_edge(m,u,v):E.add((mp[u],mp[v]))
        chain=[x for k in range(1,m) for x in (k,2*m+k-1)]
        D.update((mp[x],mp[y]) for x,y in zip(chain,chain[1:]))
        half_maps[m,side]=mp
    return R(tuple(labs),frozenset(E),frozenset(D),tuple(blocks)),half_maps

def pair_target(m):
    # Construct two independently labelled full halves and identify only root.
    left,lm=bouquet((0,),m);right,rm=bouquet((1,),m)
    off=left.n-1; trans=lambda x:0 if x==0 else x+off
    labels=left.labels+right.labels[1:]
    E=left.E|frozenset((trans(x),trans(y)) for x,y in right.E)
    D=left.D|frozenset((trans(x),trans(y)) for x,y in right.D)
    blocks=left.blocks+tuple(frozenset(trans(x) for x in b) for b in right.blocks)
    return R(labels,E,D,blocks),(lm[m,P],{v:trans(x) for v,x in rm[m,Q].items()})

def full_test(s,b,f,vertices):
    if len({f[x] for x in vertices})!=len(vertices):return False
    if any(s.labels[x]!=b.labels[f[x]] for x in vertices):return False
    if any(((x,y) in old)!=((f[x],f[y]) in new)
           for old,new in ((s.E,b.E),(s.D,b.D)) for x,y in product(vertices,repeat=2)):
        return False
    return all(s.t(t)==b.t(tuple(f[x] for x in t)) for t in product(vertices,repeat=3))

def directed_end_reachable(a,side,length):
    v={x for x in range(a.n) if a.labels[x]==(side|START)}
    for _ in range(length):v={y for x,y in a.D if x in v}
    return any(a.labels[x]==(side|END) for x in v)

def run():
    cnt=dict(source_parameters=0,full_source_tests=0,protected_image_tuples=0,
        unprotected_target_tuples=0,tuple_surjective_images=0,
        generated_triangle_witnesses=0,boolean_contexts=0,boolean_side_path_checks=0,
        allowed_context_triangle_checks=0,pairwise_boolean_obstructions=0)
    source_data={};boolean_summary=[]
    for m in range(3,9):
        s,views=source(m);b,bviews=pair_target(m);cnt['source_parameters']+=1
        assert s.n==5*m-2 and b.n==4*m-1
        assert all((u,v) in s.E for u,v in s.D)
        assert not any(all((x,y) in s.E for x,y in combinations(t,2))
                       for t in combinations(range(s.n),3))
        f=[None]*s.n
        for v in range(m):f[v]=0
        for side in range(2):
            for v,sv in views[side].items():
                if m<=v<2*m:continue
                f[sv]=bviews[side][v]
        assert set(f)==set(range(b.n))
        # Independent source-generated quotient, deliberately WITHOUT T.
        h=R(b.labels,frozenset((f[x],f[y]) for x,y in s.E),
            frozenset((f[x],f[y]) for x,y in s.D))
        assert h.E==b.E and h.D==b.D
        cnt['tuple_surjective_images']+=1
        tests=[(x,) for x in range(s.n)]+[p for p in combinations(range(s.n),2) if p in s.E]
        protected=set()
        for t in tests:
            assert full_test(s,h,f,t) and full_test(s,b,f,t)
            im={f[x] for x in t}
            assert any(im<=block for block in b.blocks)
            for ar in (1,2,3):
                protected.update((ar,tuple(f[x] for x in u)) for u in product(t,repeat=ar))
            cnt['full_source_tests']+=1
        # Quantifier-free certificate for EVERY assignment of arbitrary cross
        # binary/ternary tuples: no such tuple is inspected by a source test.
        free=0
        for ar in (2,3):
            for u in product(range(b.n),repeat=ar):
                if not any(set(u)<=block for block in b.blocks):
                    assert (ar,u) not in protected
                    free+=1
        cnt['unprotected_target_tuples']+=free
        cnt['protected_image_tuples']+=len(protected)
        triangles=[t for t in combinations(range(b.n),3) if all((x,y) in h.E for x,y in combinations(t,2))]
        assert len(triangles)==m*(m-1)
        for t in triangles:
            assert not h.t(t) and b.t(t)
            assert not full_test(h,b,tuple(range(b.n)),t)
            cnt['generated_triangle_witnesses']+=1
        source_data[str(m)]=dict(source_size=s.n,image_size=b.n,
            protected_tuples=len(protected),free_cross_tuples=free,
            irreducible_image_triangles=len(triangles))
    for r in range(1,5):
        words=list(product((0,1),repeat=r));contexts=[]
        for w in words:
            a,_=bouquet(w);contexts.append(a);cnt['boolean_contexts']+=1
            assert a.n==(r+2)**2-3
            for j,bit in enumerate(w,3):
                l=directed_end_reachable(a,P,2*j-3)
                rr=directed_end_reachable(a,Q,2*j-3)
                assert l==(bit==0) and rr==(bit==1)
                assert not(l and rr)
                cnt['boolean_side_path_checks']+=2
            for t in combinations(range(a.n),3):
                if all((x,y) in a.E for x,y in combinations(t,2)):
                    assert a.t(t)
                    cnt['allowed_context_triangle_checks']+=1
        for x,y in combinations(range(len(words)),2):
            j=next(j for j in range(r) if words[x][j]!=words[y][j]);m=j+3
            assert directed_end_reachable(contexts[x],P if words[x][j]==0 else Q,2*m-3)
            assert directed_end_reachable(contexts[y],P if words[y][j]==0 else Q,2*m-3)
            cnt['pairwise_boolean_obstructions']+=1
        boolean_summary.append(dict(indices=r,contexts=len(words),vertices_each=(r+2)**2-3,
                                    incompatible_pairs=len(words)*(len(words)-1)//2))
    return dict(status='PASS',scope='independent finite support and Boolean-context checks, not Lean certification',
                counts=cnt,source_parameters=source_data,boolean_contexts=boolean_summary)

if __name__=='__main__':
    start=time.monotonic();ans=run();ans['elapsed_seconds']=round(time.monotonic()-start,3)
    ans['script_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    Path(__file__).with_suffix('.results.json').write_text(json.dumps(ans,indent=2)+'\n')
    print(json.dumps(ans,indent=2))
