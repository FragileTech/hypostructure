"""Exhaust the small cubic two-terminal case in the 172a construction queue.

Terminals are labelled 0,1. Their degrees are two; all other degrees are
three. A graph is generated once by fixing each vertex's higher-labelled
neighbours in increasing vertex order. Thus no graph with this labelled degree
sequence is omitted. Only a witnessed 4-cycle prunes a partial graph.

This is a construction-selection check, not a Lean closure certificate.
"""

from itertools import combinations, permutations
import json


def census(n):
    graph = [set() for _ in range(n)]
    remaining = [2, 2] + [3] * (n - 2)
    counts = {"order": n, "c4_free": 0, "connected_c4_free": 0,
              "target_free": 0, "first_survivor": None}
    connected_graphs = set()
    cycle_witnesses = {}

    def closes_four(a, b):
        return any(graph[x] & graph[b] for x in graph[a] if x != b)

    def connected():
        seen, frontier = {0}, [0]
        while frontier:
            for other in graph[frontier.pop()] - seen:
                seen.add(other)
                frontier.append(other)
        return len(seen) == n

    def eight_cycle():
        if n < 8:
            return None

        def extend(path, seen):
            if len(path) == 8:
                return path if path[0] in graph[path[-1]] else None
            for other in graph[path[-1]] - seen:
                witness = extend(path + [other], seen | {other})
                if witness is not None:
                    return witness
            return None

        for root in range(n):
            witness = extend([root], {root})
            if witness is not None:
                assert len(set(witness)) == 8
                assert all(b in graph[a] for a, b in
                           zip(witness, witness[1:] + witness[:1]))
                return witness
        return None

    def generate(vertex):
        if vertex == n:
            if any(remaining):
                return
            counts["c4_free"] += 1
            if not connected():
                return
            counts["connected_c4_free"] += 1
            edges = tuple((a, b) for a in range(n) for b in sorted(graph[a]) if a < b)
            connected_graphs.add(edges)
            witness = eight_cycle()
            if witness is not None:
                cycle_witnesses[edges] = witness
            else:
                counts["target_free"] += 1
                if counts["first_survivor"] is None:
                    counts["first_survivor"] = [
                        [a, b] for a in range(n) for b in sorted(graph[a]) if a < b
                    ]
            return
        needed = remaining[vertex]
        available = [other for other in range(vertex + 1, n) if remaining[other] > 0]
        if needed < 0 or needed > len(available):
            return
        for neighbours in combinations(available, needed):
            inserted = []
            safe = True
            for other in neighbours:
                if closes_four(vertex, other):
                    safe = False
                    break
                graph[vertex].add(other)
                graph[other].add(vertex)
                remaining[other] -= 1
                inserted.append(other)
            if safe:
                remaining[vertex] = 0
                possible = all(remaining[a] <= sum(remaining[b] > 0
                                                  for b in range(vertex + 1, n) if a != b)
                               for a in range(vertex + 1, n))
                if possible:
                    generate(vertex + 1)
                remaining[vertex] = needed
            for other in inserted:
                graph[vertex].remove(other)
                graph[other].remove(vertex)
                remaining[other] += 1

    generate(0)
    # A second, explicit certificate of the terminal table: partition it into
    # terminal-preserving isomorphism orbits and retain each actual template.
    unseen = connected_graphs.copy()
    templates = []
    while unseen:
        representative = min(unseen)
        orbit = set()
        for terminals in ((0, 1), (1, 0)):
            for internal in permutations(range(2, n)):
                relabel = terminals + internal
                orbit.add(tuple(sorted(tuple(sorted((relabel[a], relabel[b])))
                                       for a, b in representative)))
        assert orbit <= connected_graphs
        unseen -= orbit
        templates.append({"edges": representative, "labelled_orbit_size": len(orbit),
                          "cycle": cycle_witnesses.get(representative)})
    counts["templates"] = templates
    return counts


if __name__ == "__main__":
    print(json.dumps([census(n) for n in (4, 6, 8)], indent=2))
