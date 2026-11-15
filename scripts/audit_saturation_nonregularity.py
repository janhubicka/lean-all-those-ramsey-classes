#!/usr/bin/env python3
"""Finite checks for the regular-F, nonregular-Sat_EHN(F) graph family.

These checks do NOT prove the infinite theorem. They test small
coloured blow-ups, the closed odd-walk threshold, and clique-fullness
of explicit source homomorphisms. Uses Python standard library only.
"""
from itertools import combinations


def wedge(i, j):
    """Red K_i and blue C_(2j+1) glued at vertex 0."""
    n = i + 2*j
    red = {frozenset(pair) for pair in combinations(range(i), 2)}
    cycle = [0] + list(range(i, n))
    blue = {frozenset((cycle[t], cycle[(t+1) % len(cycle)]))
            for t in range(len(cycle))}
    return n, red, blue


def blowup(i):
    n, red, blue = wedge(i, i)
    def lift(E):
        return {frozenset((x*i+a, y*i+b))
                for pair in E for x, y in [tuple(pair)]
                for a in range(i) for b in range(i)}
    return n*i, lift(red), lift(blue)


def is_connected(n, red, blue, deleted):
    remaining = set(range(n)) - set(deleted)
    if not remaining:
        return True
    nbr = [set() for _ in range(n)]
    for edge in red | blue:
        a, b = tuple(edge)
        nbr[a].add(b)
        nbr[b].add(a)
    start = next(iter(remaining))
    seen = {start}
    todo = [start]
    while todo:
        u = todo.pop()
        for v in nbr[u] & remaining:
            if v not in seen:
                seen.add(v)
                todo.append(v)
    return seen == remaining


def check_small_connectivity(i):
    n, red, blue = blowup(i)
    count = 0
    for size in range(i):
        for deleted in combinations(range(n), size):
            assert is_connected(n, red, blue, deleted), (i, deleted)
            count += 1
    return count


def odd_cycle_closed_walk(k, j, onto=False):
    """Walk length 2k+1 on blue C_(2j+1), rooted at vertex 0."""
    n = 2*j+1
    states = {(0, 1): (0,)}
    for _ in range(2*k+1):
        nxt = {}
        for (x, mask), path in states.items():
            for y in ((x-1) % n, (x+1) % n):
                nxt.setdefault((y, mask | (1 << y)), path+(y,))
        states = nxt
    if onto:
        return states.get((0, (1 << n)-1))
    return next((p for (x, _), p in states.items() if x == 0), None)


def check_base_ehn(k, j, walk):
    """Fullness on ALL irreducible source cliques of H_k."""
    n, sr, sb = wedge(k, k)
    m, tr, tb = wedge(k, j)
    def f(x):
        if x < k:
            return x
        w = walk[x-k+1]
        return 0 if w == 0 else k+w-1
    assert set(map(f, range(n))) == set(range(m))
    def has(E, a, b):
        return a != b and frozenset((a,b)) in E
    for size in range(1, k+1):
        for S in combinations(range(n), size):
            if not all(has(sr | sb, a, b) for a,b in combinations(S,2)):
                continue
            assert len({f(a) for a in S}) == size
            for a,b in combinations(S,2):
                assert has(sr,a,b) == has(tr,f(a),f(b))
                assert has(sb,a,b) == has(tb,f(a),f(b))



def marked_blue_walk(k, j):
    """Surjective rooted odd walk avoiding marked 0 except at endpoints.

    This is essential for the strengthened PRINTED-image-closed
    counterexample: every source nonroot has M=False, and every
    target nonroot has M=False, so an EHN map must reflect unary M.
    """
    n = 2*j + 1
    length = 2*k + 1
    states = {(0, 1): (0,)}
    for t in range(length):
        nxt = {}
        for (x, mask), path in states.items():
            for y in ((x-1) % n, (x+1) % n):
                if y == 0 and t < length-1:
                    continue
                nxt.setdefault((y, mask | (1 << y)), path + (y,))
        states = nxt
    return states.get((0, (1 << n)-1))


def check_marked_variant():
    """Test the stronger unary-marked image-closed variant through 6.

    Full EHN tests for the RED clique and BLUE edge tests are inherited
    from check_base_ehn; unary singleton reflection additionally
    requires the blue walk never hit the unique marked root internally.
    Blow-up fibre collapse preserves unary marks exactly.
    """
    for k in range(3, 7):
        for j in range(3, 7):
            path = marked_blue_walk(k, j)
            assert (path is not None) == (j <= k), (k, j, path)
            if path is not None:
                assert path[0] == 0 and path[-1] == 0
                assert all(v != 0 for v in path[1:-1]), (k, j, path)
                check_base_ehn(k, j, path)
    print("PASS: unary-marked-root image-closed variant and full EHN clique tests")



if __name__ == "__main__":
    for i in (3, 4):
        print("blowup i", i, "vertices", 3*i*i,
              "small deletions checked", check_small_connectivity(i))
    for k in range(3, 7):
        for j in range(3, 7):
            w = odd_cycle_closed_walk(k,j,onto=True)
            assert (w is not None) == (j <= k)
            assert (odd_cycle_closed_walk(k,j) is not None) == (j <= k)
            if w is not None:
                check_base_ehn(k,j,w)
    for i in range(3,7):
        print("threshold i", i, [j <= i for j in range(3,7)])
    print("PASS: finite checks; infinite proof is in the mathematical note")
    check_marked_variant()
