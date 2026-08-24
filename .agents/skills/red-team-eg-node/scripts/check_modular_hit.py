"""Audit odd-part, full-modulus, and central-range power-of-two hits."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any


class SpecError(ValueError):
    """A malformed arithmetic audit specification."""


def _integer(mapping: dict[str, Any], key: str) -> int:
    value = mapping.get(key)
    if isinstance(value, bool) or not isinstance(value, int):
        raise SpecError(f"{key} must be an integer")
    return value


def two_adic_decomposition(g: int) -> tuple[int, int]:
    if g <= 0:
        raise SpecError("g must be positive")
    a = 0
    odd = g
    while odd % 2 == 0:
        a += 1
        odd //= 2
    return a, odd


def audit_spec(spec: dict[str, Any]) -> dict[str, Any]:
    if not isinstance(spec, dict):
        raise SpecError("the input must be a JSON object")
    g = _integer(spec, "g")
    base = _integer(spec, "L")
    k_min = _integer(spec, "k_min")
    k_max = _integer(spec, "k_max")
    central = _integer(spec, "C_sys")
    if k_min < 0 or k_max < k_min:
        raise SpecError("require 0 <= k_min <= k_max")
    if central < 0:
        raise SpecError("C_sys must be nonnegative")
    residues = spec.get("residues")
    if not isinstance(residues, list) or not residues:
        raise SpecError("residues must be a nonempty list")

    a, odd = two_adic_decomposition(g)
    two_power = 1 << a
    rows = []
    for index, residue_record in enumerate(residues):
        if not isinstance(residue_record, dict):
            raise SpecError(f"residues[{index}] must be an object")
        residue = _integer(residue_record, "r")
        t_max = _integer(residue_record, "T_r")
        compatible = (base + residue) % two_power == 0
        raw_target = (base + residue) % odd
        reduced_target = ((base + residue) // two_power) % odd if compatible else None

        raw_odd_part_hits = [
            exponent
            for exponent in range(k_min, k_max + 1)
            if pow(2, exponent, odd) == raw_target
        ]
        odd_part_hits = []
        exact_lifts = []
        for exponent in range(max(k_min, a), k_max + 1):
            orbit = pow(2, exponent - a, odd)
            if compatible and orbit == reduced_target:
                odd_part_hits.append(exponent)

            numerator = (1 << exponent) - base - residue
            if numerator % g != 0:
                continue
            coefficient = numerator // g
            in_range = central <= coefficient <= t_max - central
            exact_lifts.append(
                {
                    "k": exponent,
                    "t": coefficient,
                    "lower_ok": central <= coefficient,
                    "upper_ok": coefficient <= t_max - central,
                    "central_range": in_range,
                }
            )

        rows.append(
            {
                "r": residue,
                "T_r": t_max,
                "two_adic_compatible": compatible,
                "raw_target_mod_u": raw_target,
                "raw_odd_part_hit_exponents": raw_odd_part_hits,
                "reduced_target_mod_u": reduced_target,
                "odd_part_hit_exponents": odd_part_hits,
                "exact_full_modulus_lifts": exact_lifts,
                "valid_direct_hits": [lift for lift in exact_lifts if lift["central_range"]],
            }
        )

    valid = [
        {"r": row["r"], **hit}
        for row in rows
        for hit in row["valid_direct_hits"]
    ]
    return {
        "input": spec,
        "decomposition": {"g": g, "a": a, "two_power": two_power, "u": odd},
        "compatible_residues": [row["r"] for row in rows if row["two_adic_compatible"]],
        "raw_odd_part_hits": [
            {"r": row["r"], "k": exponent}
            for row in rows
            for exponent in row["raw_odd_part_hit_exponents"]
        ],
        "residue_audits": rows,
        "valid_direct_hits": valid,
        "has_valid_direct_hit": bool(valid),
        "warning": (
            "raw_odd_part_hit_exponents intentionally shows the potentially misleading "
            "projection modulo u. A raw odd-part hit is insufficient without 2-adic "
            "compatibility, the normalized reduced congruence, an exact integer lift, and the "
            "central coefficient range. Graph realization remains a separate test."
        ),
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("spec", type=Path, help="JSON audit specification")
    parser.add_argument(
        "--require-hit",
        action="store_true",
        help="exit with status 1 when no valid central direct hit exists",
    )
    args = parser.parse_args(argv)
    try:
        spec = json.loads(args.spec.read_text(encoding="utf-8"))
        result = audit_spec(spec)
    except (OSError, json.JSONDecodeError, SpecError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(result, ensure_ascii=False, indent=2, sort_keys=True))
    return 1 if args.require_hit and not result["has_valid_direct_hit"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
