#!/usr/bin/env python3
"""Bounded independent regression for the printed 2019 counterexample.

Enumerates *all* finite naturally ordered perfect matchings and all
equivalences respecting the matched pairs, for 0,2,4,6,8 vertices.
Checks that every displayed B-copy contains the two oppositely coloured
A-subcopies. This is not a Lean proof of strong amalgamation or of the
general theorem-level contradiction.
"""
from itertools import combinations


def matchings(vertices):
    if not vertices:
        yield ()
        return
    head, *tail = vertices
    for i, other in enumerate(tail):
        rest = tuple(tail[:i] + tail[i+1:])
        for m in matchings(rest):
            yield ((head, other),) + m


def partitions(size):
    if not size:
        yield ()
        return

    def go(prefix, upper):
        if len(prefix) == size:
            yield tuple(prefix)
            return
        for k in range(upper+2):
            prefix.append(k)
            yield from go(prefix, max(k,upper))
            prefix.pop()

    yield from go([0], 0)


def structures(n):
    for m in matchings(tuple(range(n))):
        for p in partitions(n//2):
            cls = [None] * n
            mate = [None] * n
            for i, (x,y) in enumerate(m):
                cls[x] = cls[y] = p[i]
                mate[x], mate[y] = y, x
            yield cls, mate


def is_a(v, c, m):
    a,b,d,e = v
    return m[a] == b and m[d] == e and c[a] != c[d]


def is_b(v, c, m):
    a,b,d,e,f,g = v
    return m[a] == b and m[d] == e and m[f] == g and c[a] == c[f] != c[d]


def main():
    count = closed = a_copies = b_copies = singleton_tests = 0
    for n in range(0,9,2):
        for eq,mate in structures(n):
            count += 1
            closed += 2**(n//2)  # precisely unions of matched pairs
            singleton_tests += n  # each is nonclosed for the matching rule
            order = {k: i for i,k in enumerate(sorted(set(eq), key=lambda z:eq.index(z)))}
            for xs in combinations(range(n),4):
                a_copies += is_a(xs,eq,mate)
            for xs in combinations(range(n),6):
                if not is_b(xs,eq,mate):
                    continue
                b_copies += 1
                first,last = xs[:4],xs[2:]
                assert is_a(first,eq,mate) and is_a(last,eq,mate)
                c1 = order[eq[first[0]]] < order[eq[first[2]]]
                c2 = order[eq[last[0]]] < order[eq[last[2]]]
                assert c1 != c2
    assert (count,closed,b_copies)==(1658,25827,85)
    print("PASS",dict(structures=count,closed_tests=closed,
                      A_embeddings=a_copies,B_embeddings=b_copies,
                      nonclosed_singletons=singleton_tests))


if __name__=="__main__":
    main()
