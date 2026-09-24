"""Keep incremental proof modules independent of their compatibility imports."""
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[2]
TREES = {
    "HypostructureErdos64EG.Assembly": ROOT / "proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly",
    "Hypostructure.Graph.Strategy.SpineRows": ROOT / "hypostructure/Hypostructure/Graph/Strategy/SpineRows",
}


def imports(path):
    # Import commands precede module documentation in these files.
    return set(re.findall(r"^import ([\w.]+)$", path.read_text().split("/-!", 1)[0], re.M))


class ModuleBoundaryTests(unittest.TestCase):
    def test_no_cycles_or_umbrella_imports_inside_split_modules(self):
        graph = {}
        for prefix, directory in TREES.items():
            for path in directory.rglob("*.lean"):
                name = prefix + "." + ".".join(path.relative_to(directory).with_suffix("").parts)
                graph[name] = imports(path)
                self.assertFalse(graph[name] & {*TREES, "Hypostructure", "HypostructureErdos64EG"}, path)
        complete = set()

        def visit(name, active):
            self.assertNotIn(name, active, f"Import cycle: {active} -> {name}")
            if name in complete:
                return
            for dep in graph.get(name, set()):
                visit(dep, active + [name])
            complete.add(name)

        for name in graph:
            visit(name, [])

    def test_compatibility_imports_reach_every_split_module(self):
        for prefix, directory in TREES.items():
            graph = {prefix: imports(directory.with_suffix(".lean"))}
            for path in directory.rglob("*.lean"):
                name = prefix + "." + ".".join(path.relative_to(directory).with_suffix("").parts)
                graph[name] = imports(path)
            reached = set()
            pending = [prefix]
            while pending:
                name = pending.pop()
                if name in reached:
                    continue
                reached.add(name)
                pending.extend(graph.get(name, set()))
            self.assertFalse(set(graph) - reached, sorted(set(graph) - reached))


if __name__ == "__main__":
    unittest.main()
