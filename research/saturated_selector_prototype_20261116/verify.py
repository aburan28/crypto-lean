#!/usr/bin/env python3
"""Separate exact point/scalar replay; no saturation, LLL or root recovery.

UNEXECUTED. Run inside the admitted verification budget. A producer-written
checker and its booleans are not an independent signed PCC verdict.
"""

import argparse
import json
from pathlib import Path

from sage.all import EllipticCurve, GF, Integer


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--result", type=Path, required=True)
    args = parser.parse_args()
    config, result = json.loads(args.input.read_text()), json.loads(args.result.read_text())
    if result.get("status") != "success":
        raise ValueError("result records no successful recovery")
    data = config["curve"]
    p, r = int(data["p"]), int(data["r"])
    if not Integer(p).is_prime(proof=True) or not Integer(r).is_prime(proof=True):
        raise ValueError("nonprime field/subgroup input")
    curve = EllipticCurve(GF(p), [int(data["a"]), int(data["b"])])
    zero = curve(0)
    generator = curve(*[GF(p)(int(v)) for v in data["G"]])
    target = zero if data["Q"] is None else curve(*[GF(p)(int(v)) for v in data["Q"]])
    if generator == zero or r*generator != zero or r*target != zero:
        raise ValueError("invalid input subgroup points")
    scalar = int(result["scalar"])
    if not 0 <= scalar < r or scalar*generator != target:
        raise ValueError("final scalar check failed")
    if target == zero and scalar == 0 and not result.get("relations"):
        print(json.dumps({"replay": "pass", "relations": 0,
                          "scope": "exact curve/scalar replay; no signed PCC verdict"}))
        return
    catalog, seen = [], set()
    bound = int(config["search"]["x_bound"])
    for coordinates in result["catalog"]:
        x, y = map(int, coordinates)
        if not 0 <= x < bound or x in seen or not 0 <= y <= p//2:
            raise ValueError("noncanonical or duplicate catalog point")
        point = curve(GF(p)(x), GF(p)(y))
        if r*point != zero:
            raise ValueError("catalog point outside the r-primary subgroup")
        seen.add(x)
        catalog.append(point)
    relations = result["relations"]
    for relation in relations:
        ids, signs = relation["catalog_ids"], relation["signs"]
        if len(ids) != len(signs) or any(s not in (-1, 1) for s in signs):
            raise ValueError("invalid signed provenance")
        if any(type(i) is not int or not 0 <= i < len(catalog) for i in ids):
            raise ValueError("invalid original catalog index")
        counts = [0]*len(catalog)
        for i, s in zip(ids, signs):
            counts[i] += s
        if counts != relation["coefficients"]:
            raise ValueError("lost original occurrence multiplicity")
        a, b = int(relation["alpha"]), int(relation["beta"])
        if not 0 <= a < r or not 0 <= b < r:
            raise ValueError("noncanonical original labels")
        point = sum((s*catalog[i] for i, s in zip(ids, signs)), zero)
        if point != a*generator+b*target:
            raise ValueError("original point relation failed replay")
        encoded = None if point == zero else [int(point[0]), int(point[1])]
        if encoded != relation["point"]:
            raise ValueError("stored point differs from replay")
    dependence = [int(v) for v in result["dependence"]]
    if len(dependence) != len(relations) or not any(dependence):
        raise ValueError("zero or wrong-size original target dependence")
    if any(not 0 <= v < r for v in dependence):
        raise ValueError("noncanonical dependence coefficient")
    totals = [sum(lam*relation["coefficients"][j]
                  for lam, relation in zip(dependence, relations)) % r
              for j in range(len(catalog))]
    if any(totals):
        raise ValueError("factor base did not cancel")
    A = sum(lam*int(relation["alpha"]) for lam, relation in zip(dependence, relations)) % r
    B = sum(lam*int(relation["beta"]) for lam, relation in zip(dependence, relations)) % r
    if not B or A != int(result["A"]) or B != int(result["B"]):
        raise ValueError("invalid recovery coefficient")
    if scalar != -A*pow(B, -1, r) % r:
        raise ValueError("scalar differs from checked relation recovery")
    print(json.dumps({"replay": "pass", "relations": len(relations),
                      "scope": "exact point/scalar replay; no signed PCC verdict"}))


if __name__ == "__main__":
    main()
