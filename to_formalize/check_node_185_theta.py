#!/usr/bin/env python3
"""Exhaust the induced-theta length projection below EG node 185.

This checks local graphs, not the complete EG residual or its closure.
No third-party dependencies are required. Run from the repository root.
"""

import json
from itertools import combinations


def theta(lengths):
    graph = [set(), set()]
    for length in lengths:
        previous = 0
        for _ in range(length - 1):
            vertex = len(graph)
            graph.append({previous})
            graph[previous].add(vertex)
            previous = vertex
        assert 1 not in graph[previous], "parallel length-one arms"
        graph[previous].add(1)
        graph[1].add(previous)
    return graph


def longest_induced_path(graph):
    best = []

    def visit(path, used):
        nonlocal best
        if len(path) > len(best):
            best = path[:]
        for vertex in sorted(graph[path[-1]] - used):
            if graph[vertex] & used == {path[-1]}:
                visit(path + [vertex], used | {vertex})

    for start in range(len(graph)):
        visit([start], {start})
    return best


def cycle_lengths(graph):
    """Independent simple-cycle DFS; use the least vertex as cycle root."""
    lengths = set()

    def visit(start, path, used):
        for vertex in graph[path[-1]]:
            if vertex == start and len(path) >= 3:
                lengths.add(len(path))
            elif vertex > start and vertex not in used:
                visit(start, path + [vertex], used | {vertex})

    for start in range(len(graph)):
        visit(start, [start], {start})
    return sorted(lengths)


def power_of_two(value):
    return value >= 4 and value & (value - 1) == 0


def main():
    survivors = []
    counts = {"candidates": 0, "target_hit": 0, "induced_P13": 0}
    # Deleting one branch vertex from any two arms gives an induced path
    # with a_i + a_j - 1 vertices. Thus every pair sum is at most 13.
    for a in range(1, 13):
        for b in range(max(a, 2), 13):
            for c in range(b, 14 - b):
                lengths = (a, b, c)
                graph = theta(lengths)
                counts["candidates"] += 1
                cycles = cycle_lengths(graph)
                assert cycles == sorted({x + y for x, y in combinations(lengths, 2)})
                path = longest_induced_path(graph)
                # Check the explicit witness against every pair of vertices.
                for i, u in enumerate(path):
                    for j, v in enumerate(path):
                        if i < j:
                            assert (v in graph[u]) == (j == i + 1)
                if any(map(power_of_two, cycles)):
                    counts["target_hit"] += 1
                elif len(path) >= 13:
                    counts["induced_P13"] += 1
                else:
                    survivors.append({
                        "arms": lengths,
                        "vertices": len(graph),
                        "frontier_incidences": sum(lengths) - 3,
                        "cycle_lengths": cycles,
                        "longest_induced_path_vertices": len(path),
                    })
    assert any(row["arms"] == (1, 2, 4) for row in survivors)
    assert counts["candidates"] == sum(counts[key] for key in
                                      ("target_hit", "induced_P13")) + len(survivors)
    print(json.dumps({
        "scope": "local induced theta graphs only; no EG closure certified",
        "counts": {**counts, "survivors": len(survivors)},
        "survivors": survivors,
    }, indent=2))


if __name__ == "__main__":
    main()
