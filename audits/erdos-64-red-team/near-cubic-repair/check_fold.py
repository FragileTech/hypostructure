"""Check degree/boundary preservation, not the EG residual or quotient reading."""
from itertools import combinations
import json


def frame(k):
    g = {i: set() for i in range(2 * k + 2)}
    def edge(a, b):
        g[a].add(b)
        g[b].add(a)
    for i in range(k):
        edge(0, 2 + i)
        edge(1, 2 + k + i)
        edge(2 + i, 2 + k + i)
    for i in range(0, k, 2):
        edge(2 + i, 2 + i + 1)
        edge(2 + k + (i + 1) % k, 2 + k + (i + 2) % k)
    return g


def main():
    checked = 0
    for k in range(6, 25, 2):
        g = frame(k)
        assert min(map(len, g.values())) == 3
        assert all(len(g[a] & g[b]) <= 1 for a, b in combinations(g, 2))
        for h in (0, 1):
            assert all(len(g[x]) == 3 for x in g[h])
            for a, b in combinations(sorted(g[h]), 2):
                support = {h} | g[h] | g[a] | g[b]
                assert support < set(g)
                assert all(g[x] <= support for x in (h, a, b))
                boundary = {x for x in support if g[x] - support}
                q = {x: set() for x in g if x != b}
                image = lambda x: a if x == b else x
                for x in g:
                    for y in g[x]:
                        u, v = image(x), image(y)
                        if u != v:
                            q[u].add(v)
                reduced = support - {b}
                assert len(q) == len(g) - 1
                assert min(map(len, q.values())) >= 3
                assert len(q[h]) == len(g[h]) - 1
                assert len(q[a]) == 5 - 2 * (b in g[a])
                assert all(len(q[x]) == len(g[x]) for x in g if x not in (h, a, b))
                assert {x for x in reduced if q[x] - reduced} == boundary
                assert all(len(g[x] & support) == len(q[x] & reduced) for x in boundary)
                checked += 1
    print(json.dumps({
        'folds_checked': checked,
        'centres': 'degrees 6,8,...,24 in explicit C4-free minimum-degree-three frames',
        'checked': ['proper support', 'internal folded vertices', 'ambient degree', 'boundary identity', 'boundary degree profile', 'strict vertex decrease'],
        'not_checked': ['power-of-two avoidance', 'minimal-counterexample status', 'declared quotient identification', 'Node 144 closure']
    }, indent=2))

if __name__ == '__main__':
    main()
