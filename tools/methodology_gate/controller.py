#!/usr/bin/env python3
"""Repository entry point; use python3 -I with the canonical local workflow."""
from pathlib import Path
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from tools.methodology_gate.runner import main

if __name__ == '__main__':
    main()
