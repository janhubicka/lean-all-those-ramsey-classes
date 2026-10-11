#!/usr/bin/env python3
"""Bounded independent regression for the proposed 2019 ATR cycle gadgets.

Not a Lean proof or a replacement for proving the universal closed-test
local-completion implication. Tests EVERY exact weak vertex subset S with
|S| <= k in the concrete C_k for k = 0,...,4, including omitted mates.
"""
from itertools import combinations
from math import comb


def control_E(a, b):
    return a == b or (min(a, b), max(a, b)) in {(0, 1), (0, 2), (1, 3)}


def check(k):
    m = 2 * k + 5
    labels = [3 if i == m - 1 else i % 2 for i in range(m)]
    labels += [4] * (m - 1) + [2]
    gadgets = [(i, i + 1, m + i) for i in range(m - 1)]
    gadgets += [(0, 2 * m - 1, m - 1)]
    assert len(labels) == 2 * m and len(gadgets) == m
    pairs = {(a, a) for a in range(2 * m)}
    for triple in gadgets:
        pairs.update((a, b) for a in triple for b in triple)

    def E(a, b):
        return (a, b) in pairs and control_E(labels[a], labels[b])

    assert all(E(i, i + 1) for i in range(m - 1))
    assert not E(0, m - 1)
    expected_triangles = {tuple(sorted(t)) for t in gadgets}
    actual_triangles = {
        t for t in combinations(range(2 * m), 3)
        if all((a, b) in pairs for a, b in combinations(t, 2))
    }
    assert actual_triangles == expected_triangles, ("unexpected 3-clique", k)
    assert not any(
        all((a, b) in pairs for a, b in combinations(t, 2))
        for t in combinations(range(2 * m), 4)
    ), ("4-clique", k)
    for triple in gadgets:
        a, b, c = sorted(triple, key=lambda v: labels[v])
        assert labels[a] < labels[b] < labels[c]
        assert E(a, b) and not E(a, c) and not E(b, c)

    tests = 0
    for size in range(k + 1):
        for vertex_tuple in combinations(range(4 * m), size):
            vertices = set(vertex_tuple)
            touched = {v // 2 for v in vertices}
            assert any(i not in touched for i in range(m))
            parent = {b: b for b in touched}

            def root(a):
                while parent[a] != a:
                    parent[a] = parent[parent[a]]
                    a = parent[a]
                return a

            def union(a, b):
                a, b = root(a), root(b)
                if a != b:
                    parent[a] = b

            for a, b in combinations(sorted(touched), 2):
                if E(a, b):
                    union(a, b)

            # The K-completion candidate takes matching-pair closure,
            # transitive E closure and a linear order sorted by C0
            # label, block index and bit. Test full E/order reflection
            # for related blocks (stronger than closed tests alone).
            for a, b in combinations(sorted(touched), 2):
                if (a, b) in pairs:
                    assert (root(a) == root(b)) == E(a, b), (k, vertex_tuple, a, b)
                    assert labels[a] != labels[b]
            closed_blocks = {
                b for b in touched if 2 * b in vertices and 2 * b + 1 in vertices
            }
            for r in range(1, min(3, len(closed_blocks)) + 1):
                for blocks in combinations(sorted(closed_blocks), r):
                    if all((a, b) in pairs for a, b in combinations(blocks, 2)):
                        for a, b in combinations(blocks, 2):
                            assert (root(a) == root(b)) == E(a, b)
            tests += 1
    assert tests == sum(comb(8 * k + 20, i) for i in range(k + 1))
    return tests


if __name__ == "__main__":
    count = 0
    for k in range(5):
        n = check(k)
        count += n
        print(f"k={k}: {n} exact weak subsets passed")
    print(f"{count} bounded weak tests passed; mathematical generalization remains open.")
