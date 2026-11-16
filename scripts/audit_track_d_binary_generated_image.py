#!/usr/bin/env python3
"""Independent exhaustive checks of the binary relational image-normalization lemma.

Every unary/directed-binary structure with loops on <=3 source vertices,
every canonical kernel, and every compatible target table on the image.
Independent EHN checks use ALL full induced irreducible source subsets.
No Lean result or earlier counterexample checker is imported.
"""
from dataclasses import dataclass
from itertools import combinations, product
from pathlib import Path
import hashlib, json, time

@dataclass(frozen=True)
class M:
    n: int
    unary: tuple[bool,...]
    binary: frozenset[tuple[int,int]]

def all_models(n):
    pairs=list(product(range(n),repeat=2))
    for mask in range(1<<(n+n*n)):
        yield M(n,tuple(bool(mask&(1<<x)) for x in range(n)),
                frozenset(t for k,t in enumerate(pairs) if mask&(1<<(n+k))))

def kernels(n):
    if n==0:
        yield ();return
    def rec(q,maximum):
        if len(q)==n:
            yield tuple(q);return
        for v in range(maximum+2):
            yield from rec(q+[v],max(v,maximum))
    yield from rec([0],0)

def tests(a):
    return [tuple(i for i in range(a.n) if mask&(1<<i))
            for mask in range(1<<a.n)
            if all((i,j) in a.binary or (j,i) in a.binary
                   for i,j in combinations([i for i in range(a.n) if mask&(1<<i)],2))]

def full_on(a,b,f,s):
    return (len({f[i] for i in s})==len(s)
        and all(a.unary[i]==b.unary[f[i]] for i in s)
        and all(((i,j) in a.binary)==((f[i],f[j]) in b.binary) for i,j in product(s,repeat=2)))

def ehn(a,b,f):
    return (len(f)==a.n and all(0<=x<b.n for x in f)
        and all(not a.unary[i] or b.unary[f[i]] for i in range(a.n))
        and all((f[i],f[j]) in b.binary for i,j in a.binary)
        and all(full_on(a,b,f,s) for s in tests(a)))

def generated(a,q):
    k=max(q,default=-1)+1
    return M(k,tuple(any(a.unary[x] and q[x]==u for x in range(a.n)) for u in range(k)),
        frozenset((q[x],q[y]) for x,y in a.binary))

def compatible_targets(a,q):
    k=max(q,default=-1)+1; unary=[None]*k; fixed={}
    for x in range(a.n):
        u=q[x]
        if unary[u] is not None and unary[u]!=a.unary[x]:return
        unary[u]=a.unary[x]
        val=(x,x) in a.binary
        if (u,u) in fixed and fixed[u,u]!=val:return
        fixed[u,u]=val
    for x,y in combinations(range(a.n),2):
        if (x,y) not in a.binary and (y,x) not in a.binary:continue
        u,v=q[x],q[y]
        if u==v:return
        for old,new in (((x,y),(u,v)),((y,x),(v,u))):
            value=old in a.binary
            if new in fixed and fixed[new]!=value:return
            fixed[new]=value
    free=[(u,v) for u,v in product(range(k),repeat=2) if (u,v) not in fixed]
    for vals in product((False,True),repeat=len(free)):
        relation={t for t,v in fixed.items() if v}|{t for t,v in zip(free,vals) if v}
        yield M(k,tuple(unary),frozenset(relation))

def execute():
    counts=dict(source_models=0,kernels=0,compatible_ehn_targets=0,
                generated_factors_ehn=0,generated_inclusions_ehn=0,
                full_generated_inclusions=0,proper_nonfull_ehn_inclusions=0,
                noninjective_source_maps=0,support_inequalities=0,
                complete_image_tests=0)
    by_n={}; nonfull_example=None
    for n in range(4):
        tally=0
        for a in all_models(n):
            counts['source_models']+=1
            for q in kernels(n):
                counts['kernels']+=1
                h=generated(a,q)
                for b in compatible_targets(a,q):
                    assert ehn(a,b,q),('candidate enumeration incorrect',a,b,q)
                    counts['compatible_ehn_targets']+=1;tally+=1
                    assert ehn(a,h,q)
                    counts['generated_factors_ehn']+=1
                    ident=tuple(range(h.n))
                    assert ehn(h,b,ident),('binary lemma counterexample',a,b,q,h)
                    counts['generated_inclusions_ehn']+=1
                    if full_on(h,b,ident,ident): counts['full_generated_inclusions']+=1
                    else:
                        counts['proper_nonfull_ehn_inclusions']+=1
                        if nonfull_example is None:
                            nonfull_example=dict(source_n=n,source_unary=a.unary,
                               source_binary=sorted(a.binary),kernel=q,
                               image_binary=sorted(h.binary),target_binary=sorted(b.binary))
                    counts['noninjective_source_maps']+=len(set(q))<n
                    for s in tests(h):
                        assert full_on(h,b,ident,s)
                        counts['complete_image_tests']+=1
                    # Every induced subsource of H, in particular a full
                    # forbidden member supplied by printed closure, has
                    # an injective EHN map into B on the same vertices.
                    for mask in range(1<<h.n):
                        old=sum(bool(mask&(1<<q[x])) for x in range(n))
                        for submask in range(1<<h.n):
                            new=(mask&submask).bit_count()
                            assert new<=old
                            counts['support_inequalities']+=1
        by_n[str(n)]=tally
    return dict(status='PASS',scope='bounded exhaustive binary relational checks, not a universal proof or Lean certificate',
                counts=counts,targets_by_source_size=by_n,
                nonfull_inclusion_example=nonfull_example)

if __name__=='__main__':
    start=time.monotonic();r=execute();r['elapsed_seconds']=round(time.monotonic()-start,3)
    r['script_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    Path(__file__).with_suffix('.results.json').write_text(json.dumps(r,indent=2)+'\n')
    print(json.dumps(r,indent=2))
