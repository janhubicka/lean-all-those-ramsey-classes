#!/usr/bin/env python3
"""Exhaustive bounded strong-amalgamation regression.

All finite naturally ordered isomorphism types on 0,2,4,6 vertices
with an equivalence E and a perfect matching M contained in E are tested.
For each ordered closed-root embedding span with both sides <= 6
vertices, construct a strong pushout, unite the matchings, close E
under transitivity and extend both vertex orders. Verify that both
input structures are STILL INDUCED (including negative relations),
the matching is total and conflict-free, and the overlap is exact.

This is computational evidence, NOT an unbounded Lean theorem.
"""
from collections import defaultdict
from heapq import heappop, heappush
from itertools import combinations


def perfect_matchings(vertices):
    if not vertices:
        yield ()
        return
    x = vertices[0]
    for y in vertices[1:]:
        rest = tuple(v for v in vertices[1:] if v != y)
        for matching in perfect_matchings(rest):
            yield ((x, y),) + matching


def partitions(k):
    if k == 0:
        yield ()
        return

    def build(prefix, maximum):
        if len(prefix) == k:
            yield tuple(prefix)
            return
        for i in range(maximum + 2):
            yield from build(prefix + [i], max(maximum, i))

    yield from build([0], 0)


def models(n):
    for pairs in perfect_matchings(tuple(range(n))):
        for block in partitions(n // 2):
            mate = [-1] * n
            eq = [-1] * n
            for i, (a, b) in enumerate(pairs):
                mate[a], mate[b] = b, a
                eq[a] = eq[b] = block[i]
            yield n, tuple(mate), tuple(eq), pairs


def closed_subset_profile(model, selected_pairs):
    _, mate, eq, pairs = model
    vertices = tuple(sorted(v for i in selected_pairs for v in pairs[i]))
    index = {v: i for i, v in enumerate(vertices)}
    classes, profile = {}, []
    for v in vertices:
        if eq[v] not in classes:
            classes[eq[v]] = len(classes)
        profile.append(classes[eq[v]])
    return vertices, (tuple(index[mate[v]] for v in vertices), tuple(profile))


def check_strong_span(left, right, root_left, root_right):
    n, ml, el, _ = left
    m, mr, er, _ = right
    assert len(root_left) == len(root_right)
    map_left = dict(enumerate(range(n)))
    overlap = dict(zip(root_right, root_left))
    map_right = {}
    count = n
    for x in range(m):
        if x in overlap:
            map_right[x] = overlap[x]
        else:
            map_right[x] = count
            count += 1
    assert set(map_left.values()) & set(map_right.values()) == set(root_left)

    # The matching is the union of the two sides' matching graphs.
    mate = {}
    for model, embed in ((left, map_left), (right, map_right)):
        for a in range(model[0]):
            x, y = embed[a], embed[model[1][a]]
            assert x != y
            if x in mate:
                assert mate[x] == y
            else:
                mate[x] = y
    assert len(mate) == count
    assert all(x != mate[x] and mate[mate[x]] == x for x in mate)

    # Equivalence closure: union-find computes exactly the least
    # equivalence relation containing both side relations.
    parent = list(range(count))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(x, y):
        x, y = find(x), find(y)
        if x != y:
            parent[y] = x

    for model, embed in ((left, map_left), (right, map_right)):
        for a in range(model[0]):
            for b in range(a):
                if model[2][a] == model[2][b]:
                    union(embed[a], embed[b])

    # Verify BOTH implications for induced embeddings, including
    # reflection of E and M, not just preservation.
    for model, embed in ((left, map_left), (right, map_right)):
        for a in range(model[0]):
            for b in range(model[0]):
                assert (find(embed[a]) == find(embed[b])) == (
                    model[2][a] == model[2][b]
                )
                assert (mate[embed[a]] == embed[b]) == (
                    model[1][a] == b
                )

    # Combine both precedence orders and find a linear extension.
    precedes = [set() for _ in range(count)]
    follows = [set() for _ in range(count)]
    for model, embed in ((left, map_left), (right, map_right)):
        for a in range(model[0] - 1):
            x, y = embed[a], embed[a + 1]
            assert x != y
            follows[x].add(y)
            precedes[y].add(x)
    queue = []
    for x in range(count):
        if not precedes[x]:
            heappush(queue, x)
    ordered = []
    while queue:
        x = heappop(queue)
        ordered.append(x)
        for y in follows[x]:
            precedes[y].remove(x)
            if not precedes[y]:
                heappush(queue, y)
    assert len(ordered) == count, "cycle in combined orders"
    rank = {x: i for i, x in enumerate(ordered)}
    for model, embed in ((left, map_left), (right, map_right)):
        for a in range(model[0]):
            for b in range(a + 1, model[0]):
                assert rank[embed[a]] < rank[embed[b]]


def main():
    objects = [v for n in (0, 2, 4, 6) for v in models(n)]
    assert len(objects) == 83
    closed = []
    for model in objects:
        dictionary = defaultdict(list)
        for k in range(model[0] // 2 + 1):
            for selected in combinations(range(model[0] // 2), k):
                vertices, profile = closed_subset_profile(model, selected)
                dictionary[profile].append(vertices)
        closed.append(dictionary)

    total = 0
    counts = defaultdict(int)
    for i, source_left in enumerate(closed):
        for j, source_right in enumerate(closed):
            for profile, left_copies in source_left.items():
                for right_copy in source_right.get(profile, ()):
                    for left_copy in left_copies:
                        check_strong_span(
                            objects[i], objects[j], left_copy, right_copy
                        )
                        total += 1
                        counts[len(profile[0])] += 1
    assert total == 72839, total
    assert dict(counts) == {0: 6889, 2: 56644, 4: 9231, 6: 75}
    print(f"PASS: {len(objects)} ordered models, {total} strong spans")
    print(f"Root sizes: {dict(sorted(counts.items()))}")


if __name__ == "__main__":
    main()
