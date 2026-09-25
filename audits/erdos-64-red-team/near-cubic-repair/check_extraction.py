"""Check the finite record-partition algorithm; does not certify EG handoffs."""
from itertools import combinations
import json


def extract(edges, order):
    remaining = set(edges)
    events = []
    while True:
        found = None
        for candidate in combinations(sorted(remaining), order):
            vertices = [v for edge in candidate for v in edge]
            matching = len(set(vertices)) == 2 * order
            common = set(candidate[0])
            for edge in candidate[1:]:
                common.intersection_update(edge)
            if matching or common:
                found = set(candidate)
                break
        if found is None:
            return remaining, events
        before = len(remaining)
        remaining.difference_update(found)
        assert before - len(remaining) == order
        events.append(found)


def main():
    checked = 0
    for vertices in range(1, 6):
        complete = list(combinations(range(vertices), 2))
        for mask in range(1 << len(complete)):
            edges = {e for i, e in enumerate(complete) if mask & (1 << i)}
            for order in (2, 3):
                remaining, events = extract(edges, order)
                seen = set(remaining)
                for event in events:
                    assert len(event) == order
                    assert not (seen & event)
                    seen.update(event)
                assert seen == edges
                bound = (order - 1) * (2 * order - 3)
                assert len(remaining) <= bound
                assert len(edges) == len(remaining) + order * len(events)
                assert max(0, len(edges) - bound) <= order * len(events)
                checked += 1
    report = {
        "instances": checked,
        "scope": "all simple pair-fibre graphs on 1..5 labels, pattern sizes 2 and 3",
        "checked": ["strict decrease", "pair partition", "bounded remainder", "exact event count"],
        "not_checked": ["EG graph hypotheses", "Type B envelope construction", "payer capacity", "branch closure"],
    }
    print(json.dumps(report, indent=2))

if __name__ == '__main__':
    main()
