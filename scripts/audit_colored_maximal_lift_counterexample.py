#!/usr/bin/env python3
"""Finite audit; no external packages. Run with Python 3.

Enumerates all source maps and all 52 partitions of the coloured C5.
The arbitrary-carrier image-closure and maximality arguments are in
../docs/lifts-track-d-maximal-lift-counterexample-and-repair-20261115.md.
This executable check is not a substitute for native Lean validation.
"""
from itertools import product, combinations
import json


def sym(edges):
    return frozenset((a, b) for u, v in edges for a, b in [(u, v), (v, u)])


def structure(n, red=(), blue=(), shield=()):
    return {'n': n, 'R': sym(red), 'B': sym(blue), 'T': frozenset(shield)}


def all_subsets(n):
    return (s for k in range(n + 1) for s in combinations(range(n), k))


def irreducible_subsets(S):
    gaif = set()
    for symbol in ('R', 'B', 'T'):
        for tup in S[symbol]:
            gaif.update((x, y) for x in tup for y in tup if x != y)
    return [xs for xs in all_subsets(S['n'])
            if all((x, y) in gaif for x, y in combinations(xs, 2))]


def is_full_on(S, T, f, xs):
    if len({f[x] for x in xs}) != len(xs):
        return False
    for name, arity in [('R', 2), ('B', 2), ('T', 3)]:
        for tup in product(xs, repeat=arity):
            if (tup in S[name]) != (tuple(f[x] for x in tup) in T[name]):
                return False
    return True


def is_ehn(S, T, f):
    for name in ('R', 'B', 'T'):
        if any(tuple(f[x] for x in tup) not in T[name] for tup in S[name]):
            return False
    return all(is_full_on(S, T, f, xs) for xs in irreducible_subsets(S))


def maps(S, T):
    return [f for f in product(range(T['n']), repeat=S['n']) if is_ehn(S, T, f)]


C = structure(5, [(0, 1), (1, 2), (2, 3)], [(3, 4), (4, 0)])
A = structure(3, [(0, 1), (1, 2), (2, 0)],
              shield=[p for p in product(range(3), repeat=3) if len(set(p)) == 3])
B = structure(2, blue=[(0, 1)])
D = structure(4, [(0, 1), (1, 2), (2, 0)], [(0, 3)], shield=A['T'])
T_R = structure(3, [(0, 1), (0, 2), (1, 2)])
T_RBB = structure(3, [(0, 1)], [(0, 2), (1, 2)])
family = [C, T_R, T_RBB]


def partitions(n):
    if n == 0:
        yield ()
        return

    def rec(p):
        if len(p) == n:
            yield p
            return
        for x in range(max(p) + 2):
            yield from rec(p + (x,))

    yield from rec((0,))


def quotient(S, p):
    Q = {'n': 1 + max(p)}
    for name in ('R', 'B', 'T'):
        Q[name] = frozenset(tuple(p[x] for x in tup) for tup in S[name])
    return Q


def contains_family(Q):
    return any(any(is_full_on(S, Q, f, tuple(range(S['n'])))
                   for f in product(range(Q['n']), repeat=S['n']))
               for S in family)


def connected(S, remaining):
    if not remaining:
        return True
    seen = {next(iter(remaining))}
    while True:
        nxt = seen | {y for x, y in S['R'] | S['B'] if x in seen and y in remaining}
        if nxt == seen:
            return seen == remaining
        seen = nxt


admissible = []
for p in partitions(5):
    Q = quotient(C, p)
    if is_ehn(C, Q, p):
        assert contains_family(Q), (p, Q)
        admissible.append({'partition': p, 'image_size': Q['n']})

assert len(list(partitions(5))) == 52
assert len(admissible) == 5
assert all(connected(S, set(range(S['n'])) - {v})
           for S in family for v in range(S['n']))
assert is_full_on(A, D, (0, 1, 2), tuple(range(3)))
assert is_full_on(B, D, (0, 3), tuple(range(2)))
assert not any(maps(S, A) for S in family)
assert not any(maps(S, B) for S in family)
assert is_ehn(C, D, (0, 1, 2, 0, 3))
assert [len(maps(S, D)) for S in family] == [2, 0, 0]
assert all(sum(v in (1, 2) for v in f) == 2 for f in maps(C, D))

print(json.dumps({
    'forbidden_representatives': 3,
    'forbidden_maps_to_A': [len(maps(S, A)) for S in family],
    'forbidden_maps_to_B': [len(maps(S, B)) for S in family],
    'forbidden_maps_to_D': [len(maps(S, D)) for S in family],
    'cycle_maps_to_D': maps(C, D),
    'left_exclusive_source_supports':
        [[sum(v in (1, 2) for v in f) for f in maps(S, D)] for S in family],
    'partitions_checked': 52,
    'EHN_quotient_partitions': admissible,
    'all_admissible_images_contain_full_forbidden_copy': True,
    'no_forbidden_source_has_singleton_cut': True,
}, indent=2))
