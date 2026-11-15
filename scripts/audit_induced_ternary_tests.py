#!/usr/bin/env python3
"""Regression: ambient Gaifman cliques are not induced irreducible tests."""
from itertools import combinations, product
import json
V=tuple(range(6))
source={(0,1,3),(1,2,4),(0,2,5)}
target=source|{(0,1,2)}
def adj(x,y,tuples):
    return x!=y and any(x in t and y in t for t in tuples)
def irred(S,induced):
    triples={t for t in source if set(t)<=S} if induced else source
    return all(adj(x,y,triples) for x,y in combinations(S,2))
def full(S):
    return all((t in source)==(t in target) for t in product(S,repeat=3))
subsets=[set(x for x in V if mask&(1<<x)) for mask in range(1<<6)]
correct=[S for S in subsets if irred(S,True)]
wrong=[S for S in subsets if irred(S,False)]
assert source<=target
assert all(full(S) for S in correct)
assert not all(full(S) for S in wrong)
assert {0,1,2} in wrong and {0,1,2} not in correct
print(json.dumps({'status':'PASS','subsets':len(subsets),
  'actual_irreducible_tests':len(correct), 'ambient_clique_tests':len(wrong),
  'identity_EHN_correct_predicate':True,
  'identity_EHN_old_ambient_predicate':False,
  'bad_test':[0,1,2], 'extra_target_tuple':[0,1,2]},indent=2))
