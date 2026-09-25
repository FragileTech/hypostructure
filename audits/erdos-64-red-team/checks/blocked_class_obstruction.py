"""Check edo's block and the absent-completion obstruction in its outside record.

This is evidence about the stated counting class, not a counterexample to the
selected-counterexample residual or the Erdős–Gyárfás conjecture.  The all-p
argument is the disjoint-union argument in blocked_class_note.pdf.
"""

from itertools import combinations
import json


def check() -> dict:
    graph = {vertex: set() for vertex in range(66)}

    def edge(left: int, right: int) -> None:
        graph[left].add(right)
        graph[right].add(left)

    for triangle in range(7):
        for left, right in combinations(range(3 * triangle, 3 * triangle + 3), 2):
            edge(left, right)
    for triangle in range(6):
        edge(3 * triangle + 1, 3 * (triangle + 1))
    ports = [vertex for vertex in range(21) if len(graph[vertex]) == 2]
    for index, port in enumerate(ports):
        u, v, w, z, root = range(21 + 5 * index, 26 + 5 * index)
        for left, right in combinations((u, v, w, z), 2):
            if (left, right) != (u, v):
                edge(left, right)
        edge(root, u)
        edge(root, v)
        edge(port, root)

    window = [v for t in range(6) for v in (3 * t, 3 * t + 1)] + [18]
    windows = set(window)
    central = {9, 10, 11}
    assert len(ports) == 9
    assert all(len(neighbours) == 3 for neighbours in graph.values())
    assert sum(map(len, graph.values())) // 2 == 99
    assert all(
        (right in graph[left]) == (j == i + 1)
        for i, left in enumerate(window)
        for j, right in enumerate(window)
        if i < j
    )

    paths = 0
    longest_avoiding_two_central = 0

    def extend(path: list[int], seen: set[int]) -> None:
        nonlocal paths, longest_avoiding_two_central
        central_count = len(seen & central)
        if central_count < 2:
            longest_avoiding_two_central = max(longest_avoiding_two_central, len(path))
        if len(path) == 13:
            assert central_count == 2
            paths += path[0] < path[-1]
            return
        for vertex in graph[path[-1]] - seen:
            if graph[vertex] & seen == {path[-1]}:
                extend(path + [vertex], seen | {vertex})

    for vertex in graph:
        extend([vertex], {vertex})
    assert paths == 208
    assert longest_avoiding_two_central == 12

    def component(start: int, allowed: set[int], forbidden=None) -> set[int]:
        reached, stack = {start}, [start]
        while stack:
            left = stack.pop()
            for right in graph[left] & allowed:
                if forbidden == frozenset((left, right)) or right in reached:
                    continue
                reached.add(right)
                stack.append(right)
        return reached

    all_vertices = set(graph)
    bridges = {
        frozenset((left, right))
        for left in graph
        for right in graph[left]
        if left < right
        and right not in component(left, all_vertices, frozenset((left, right)))
    }
    assert len(bridges) == 15
    # Every non-bridge edge meeting the window lies in its own triangle;
    # deleting the bridges separates those triangles from the gadgets.
    for vertex in windows:
        triangle = set(range(3 * (vertex // 3), 3 * (vertex // 3) + 3))
        assert all(
            neighbour in triangle or frozenset((vertex, neighbour)) in bridges
            for vertex in triangle for neighbour in graph[vertex]
        )

    remaining = all_vertices - windows
    outside_components = []
    while remaining:
        vertices = component(min(remaining), all_vertices - windows)
        remaining -= vertices
        incident = {vertex for vertex in vertices if graph[vertex] & windows}
        outside_components.append((len(vertices), len(incident)))
        assert len(incident) <= 2

    # A positive-length first and second arm, with simple concatenation,
    # require THREE DISTINCT incident vertices in one outside component.
    # The preceding certificate excludes that at every scale.  It uses only
    # edges with an endpoint outside the window.  Consequently it remains
    # true for EVERY graph in the a-priori fibre with this outside record,
    # even if the edges inside the window are changed.
    return {
        "vertices": 66,
        "edges": 99,
        "degrees": [3],
        "bridges": len(bridges),
        "induced_P13_paths_unoriented": paths,
        "max_path_vertices_using_at_most_one_central_vertex": longest_avoiding_two_central,
        "maximum_disjoint_P13_packing": 1,
        "outside_components_size_and_incident_vertex_count": sorted(outside_components),
        "max_incident_vertices_per_outside_component": 2,
        "positive_two_arm_completion_supports_at_any_scale": 0,
    }


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
