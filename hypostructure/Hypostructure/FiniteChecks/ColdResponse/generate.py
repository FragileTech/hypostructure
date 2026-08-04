#!/usr/bin/env python3
"""Emit inert cold-response encodings from presentation-derived dimensions.

The output deliberately contains no semantic response bit or route tag.  Lean's
`Audit` module recomputes both representative responses from the evaluator.
"""

from __future__ import annotations

import argparse
import json
from itertools import product


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--interface-labels", type=int, required=True)
    parser.add_argument("--germ-states", type=int, required=True)
    parser.add_argument("--context-states", type=int, required=True)
    args = parser.parse_args()
    dimensions = (
        args.interface_labels,
        args.germ_states,
        args.germ_states,
        args.context_states,
    )
    if any(dimension < 0 for dimension in dimensions):
        parser.error("all carrier dimensions must be nonnegative")
    rows = [
        {
            "interface_index": interface,
            "source_index": source,
            "replacement_index": replacement,
            "context_index": context,
        }
        for interface, source, replacement, context in product(
            *(range(dimension) for dimension in dimensions)
        )
    ]
    print(json.dumps({"dimensions": dimensions, "rows": rows}, sort_keys=True))


if __name__ == "__main__":
    main()
