#!/usr/bin/env python3
"""UNEXECUTED Sage prototype: saturation, certified shifts, checked recovery.

This source has no measured yield or subexponential success guarantee.
Run only inside an admitted, capped numerical research job.
"""

import argparse
from collections import defaultdict
from itertools import combinations, product
import json
from math import isqrt
from pathlib import Path
import random
import traceback

from sage.all import EllipticCurve, GF, Integer, PolynomialRing, QQ, ZZ, matrix
from sage.version import version as sage_version

from metadata import (CapExceeded, Caps, bounded_staircase, exponent_vectors,
                      require_at_most, shift_row_count)


class GlobalCap(CapExceeded):
    pass


class Evidence:
    def __init__(self, directory, caps):
        self.directory, self.caps = Path(directory), caps
        self.artifacts = self.directory / "artifacts"
        self.artifacts.mkdir(exist_ok=False)
        self.events = (self.directory / "events.jsonl").open("x", buffering=1)
        self.bytes, self.sequence = 0, 0
        self.counts = defaultdict(int)

    def take(self, name, amount, cap):
        self.counts[name] += amount
        if self.counts[name] > cap:
            raise GlobalCap(f"global {name} cap exceeded")

    def event(self, stage, **data):
        line = json.dumps({"stage": stage, **data}, sort_keys=True) + "\n"
        self._charge(len(line.encode()))
        self.events.write(line)

    def _charge(self, count):
        self.bytes += count
        # Reserve a small final result even when detailed evidence fills the cap.
        if self.bytes > self.caps.output_mib * 1024**2 - 4096:
            raise GlobalCap("shared artifact byte cap exceeded")

    def write(self, tag, data):
        self.sequence += 1
        name = f"{self.sequence:05d}-{tag}.json"
        text = json.dumps(data, sort_keys=True, indent=2) + "\n"
        self._charge(len(text.encode()))
        with (self.artifacts / name).open("x") as stream:
            stream.write(text)
        return "artifacts/" + name


def check_poly(poly, caps):
    if not poly:
        return
    require_at_most(len(poly.dict()), caps.max_terms, "polynomial terms")
    require_at_most(int(poly.total_degree()), caps.max_polynomial_degree,
                    "polynomial total degree")
    for coefficient in poly.coefficients():
        if poly.base_ring() is QQ:
            numerator, denominator = int(coefficient.numerator()), int(coefficient.denominator())
        else:  # Only ZZ and prime fields are used by this worker.
            numerator, denominator = int(coefficient), 1
        bits = max(abs(numerator).bit_length(), denominator.bit_length())
        require_at_most(bits, caps.max_coefficient_bits, "coefficient bits")


def encoded_poly(poly, caps):
    check_poly(poly, caps)
    return {"variables": list(poly.parent().variable_names()),
            "terms": [{"exponents": [int(e) for e in exponent],
                       "coefficient": str(coefficient)}
                      for exponent, coefficient in sorted(poly.dict().items())]}


def monomial(ring, exponents):
    result = ring.one()
    for variable, exponent in zip(ring.gens(), exponents):
        result *= variable**exponent
    return result


def grade(poly, length):
    values = {tuple(int(e[length+j] + e[2*length-2+j])
                    for j in range(length-2)) for e in poly.dict()}
    if len(values) != 1:
        raise CapExceeded("a nonzero generator is not separately homogeneous")
    return next(iter(values))


def homogeneous_s3(a, b, first, second, third):
    u, v = first
    s, t = second
    w, z = third
    return ((u*t-s*v)**2*w**2
            - 2*((u*t+s*v)*(u*s+a*v*t)+2*b*(v*t)**2)*w*z
            + ((u*s-a*v*t)**2-4*b*(u*t+s*v)*v*t)*z**2)


def point_key(point):
    return None if point.is_zero() else (int(point[0]), int(point[1]))


def make_path(p, a, b, target_x, length):
    names = ([f"x{i}" for i in range(length)]
             + [f"u{i}" for i in range(length-2)]
             + [f"v{i}" for i in range(length-2)])
    ring = PolynomialRing(GF(p), names=names, order="degrevlex")
    variables = ring.gens()
    xs = variables[:length]
    us = variables[length:2*length-2]
    vs = variables[2*length-2:]
    pairs = list(zip(us, vs))
    rows = [homogeneous_s3(a, b, (xs[0], 1), (xs[1], 1), pairs[0])]
    for j in range(1, length-2):
        rows.append(homogeneous_s3(a, b, pairs[j-1], (xs[j+1], 1), pairs[j]))
    rows.append(homogeneous_s3(a, b, pairs[-1], (xs[-1], 1), (target_x, 1)))
    denominator = ring.one()
    for variable in vs:
        denominator *= variable
    return ring, rows, denominator


def localized_generators(ring, original, denominator, mode, length, evidence):
    caps = evidence.caps
    for poly in original:
        check_poly(poly, caps)
    ideal = ring.ideal(original)
    if mode == "ordinary":
        generators, exponent = list(original), 0
        witnesses = [[ring.one() if i == j else ring.zero()
                      for i in range(len(original))] for j in range(len(original))]
    else:
        saturated, exponent = ideal.saturation(ring.ideal(denominator))
        exponent = int(exponent)
        if exponent < 0:
            raise ValueError("negative saturation exponent")
        require_at_most(exponent, caps.max_saturation_exponent, "saturation exponent")
        generators = list(saturated.gens())
        require_at_most(len(generators), caps.max_generators, "saturated generators")
        witnesses = []
        for poly in generators:
            check_poly(poly, caps)
            lifted_value = denominator**exponent * poly
            check_poly(lifted_value, caps)
            witness = list(lifted_value.lift(ideal))
            if len(witness) != len(original):
                raise ValueError("saturation lift has wrong length")
            for coefficient in witness:
                check_poly(coefficient, caps)
            if sum((coefficient*source for coefficient, source in zip(witness, original)),
                   ring.zero()) != lifted_value:
                raise ValueError("saturation identity failed exact verification")
            witnesses.append(witness)
    require_at_most(len(generators), caps.max_generators, "generators")
    record = evidence.write("saturation", {
        "mode": mode, "length": length, "exponent": exponent,
        "original": [encoded_poly(f, caps) for f in original],
        "denominator": encoded_poly(denominator, caps),
        "generators": [encoded_poly(g, caps) for g in generators],
        "witnesses": [[encoded_poly(a, caps) for a in w] for w in witnesses],
    })
    integers = PolynomialRing(ZZ, names=ring.variable_names(), order="degrevlex")
    p = int(ring.base_ring().characteristic())
    lifted = []
    for poly in generators:
        if not poly:
            continue
        coefficients = {}
        for exponent_vector, coefficient in poly.dict().items():
            c = int(coefficient)
            coefficients[tuple(exponent_vector)] = c if c <= p//2 else c-p
        g = integers(coefficients)
        grade(g, length)
        lifted.append(g)
    evidence.event("localization_verified", receipt=record, generators=len(lifted))
    return integers, lifted


def shifted_blocks(p, ring, generators, length, multiplicity, shift_degree, evidence):
    caps = evidence.caps
    count = shift_row_count(ring.ngens(), len(generators), multiplicity, shift_degree)
    require_at_most(count, caps.max_shift_rows, "full shift family rows")
    evidence.take("shift_rows", count, caps.max_total_shift_rows)
    blocks = defaultdict(list)
    for powers in exponent_vectors(len(generators), multiplicity):
        base = ring(p**(multiplicity-sum(powers)))
        for g, exponent in zip(generators, powers):
            base *= g**exponent
            check_poly(base, caps)
        for exponent in exponent_vectors(ring.ngens(), shift_degree):
            row = base * monomial(ring, exponent)
            check_poly(row, caps)
            if row:
                blocks[grade(row, length)].append(row)
    return blocks


def certified_short_rows(p, rows, length, bound, height, multiplicity, evidence):
    caps = evidence.caps
    columns = sorted({tuple(e) for row in rows for e in row.dict()})
    require_at_most(len(columns), caps.max_columns, "lattice columns")
    require_at_most(len(rows)*len(columns), caps.max_matrix_cells, "matrix cells")
    evidence.take("lattices", 1, caps.max_lattices)
    scales = [bound**sum(e[:length]) * height**sum(e[length:]) for e in columns]
    basis = matrix(ZZ, [[row.monomial_coefficient(monomial(row.parent(), e))*scale
                         for e, scale in zip(columns, scales)] for row in rows])
    reduced, transformation = basis.LLL(algorithm="fpLLL:proved", transformation=True)
    if transformation*basis != reduced:
        raise ValueError("LLL transformation identity failed exact verification")
    accepted = []
    records = []
    ring = rows[0].parent()
    for index in range(reduced.nrows()):
        vector = list(reduced.row(index))
        l1 = sum(abs(c) for c in vector)
        if not l1 or l1 >= p**multiplicity:
            continue
        coeffs = {}
        for e, scaled, scale in zip(columns, vector, scales):
            quotient, remainder = divmod(int(scaled), scale)
            if remainder:
                raise ValueError("LLL coordinate not divisible by its declared scale")
            if quotient:
                coeffs[e] = quotient
        poly = ring(coeffs)
        reconstructed = sum((transformation[index, j]*rows[j]
                             for j in range(len(rows))), ring.zero())
        if poly != reconstructed:
            raise ValueError("polynomial row-combination certificate mismatch")
        grade(poly, length)
        accepted.append(poly)
        records.append({"row": index, "l1": str(l1), "modulus": str(p**multiplicity),
                        "polynomial": encoded_poly(poly, caps)})
    require_at_most(len(accepted), caps.max_short_relations, "short integer relations")
    receipt = evidence.write("lattice", {
        "columns": [list(e) for e in columns], "scales": [str(s) for s in scales],
        "basis": [[str(c) for c in row] for row in basis.rows()],
        "transformation": [[str(c) for c in row] for row in transformation.rows()],
        "reduced": [[str(c) for c in row] for row in reduced.rows()],
        "source_rows": [encoded_poly(g, caps) for g in rows], "accepted": records,
    })
    evidence.event("lll_verified", receipt=receipt, short_rows=len(accepted))
    return accepted


def checked_groebner(ideal, evidence):
    """Check membership in both directions and Buchberger critical pairs."""
    caps = evidence.caps
    basis = [g for g in ideal.groebner_basis() if g]
    require_at_most(len(basis), caps.max_generators, "Groebner generators")
    require_at_most(len(basis)*(len(basis)-1)//2, caps.max_groebner_pairs,
                    "Groebner critical pairs")
    membership = []
    for g in basis:
        check_poly(g, caps)
        lift = list(g.lift(ideal))
        if len(lift) != len(ideal.gens()) or sum(
                (a*f for a, f in zip(lift, ideal.gens())), ideal.ring().zero()) != g:
            raise ValueError("Groebner membership witness failed")
        membership.append([encoded_poly(a, caps) for a in lift])
    for f in ideal.gens():
        if f.reduce(basis) != 0:
            raise ValueError("input not in returned Groebner ideal")
    for f, g in combinations(basis, 2):
        lcm = f.lm().lcm(g.lm())
        s = (lcm//f.lm())*f/f.lc() - (lcm//g.lm())*g/g.lc()
        if ideal.ring()(s).reduce(basis) != 0:
            raise ValueError("Buchberger critical pair failed exact verification")
    evidence.write("groebner-membership", {
        "input": [encoded_poly(f, caps) for f in ideal.gens()],
        "basis": [encoded_poly(g, caps) for g in basis], "lifts": membership,
        "critical_pairs_checked": len(basis)*(len(basis)-1)//2,
    })
    return basis


def leaf_candidates(short_rows, length, evidence):
    """Project only certified homogeneous integer identities, never modular inputs."""
    if not short_rows:
        return []
    caps = evidence.caps
    slots = length-2
    ring = PolynomialRing(QQ, names=([f"z{i}" for i in range(slots)]
                                    + [f"x{i}" for i in range(length)]), order="lex")
    z, x = ring.gens()[:slots], ring.gens()[slots:]
    source = short_rows[0].parent()
    projection = source.hom(list(x)+list(z)+[ring.one()]*slots, ring)
    identities = [projection(g) for g in short_rows if projection(g)]
    if not identities:
        return []
    ideal = ring.ideal(identities)
    basis = checked_groebner(ideal, evidence)
    leaf_ring = PolynomialRing(QQ, names=[f"x{i}" for i in range(length)], order="lex")
    erase_z = ring.hom([leaf_ring.zero()]*slots+list(leaf_ring.gens()), leaf_ring)
    leaf_basis = [erase_z(g) for g in basis
                  if all(all(e[i] == 0 for i in range(slots)) for e in g.dict())]
    if not leaf_basis:
        evidence.event("no_leaf_projection", length=length)
        return []
    leading = [tuple(int(a) for a in g.lm().exponents()[0]) for g in leaf_basis]
    standard = bounded_staircase(leading, length, caps.max_standard_monomials)
    receipt = evidence.write("projective-projection", {
        "identities": [encoded_poly(g, caps) for g in identities],
        "groebner_basis": [encoded_poly(g, caps) for g in basis],
        "leaf_basis": [encoded_poly(g, caps) for g in leaf_basis],
        "standard_monomials": [list(e) for e in standard],
    })
    evidence.event("finite_leaf_projection", receipt=receipt, degree=len(standard))
    if not standard:
        return []
    # Exact rational roots only. No floating, AA, CC or partial approximate roots.
    roots = leaf_ring.ideal(leaf_basis).variety(ring=QQ)
    require_at_most(len(roots), caps.max_standard_monomials, "rational roots")
    result = []
    for root in roots:
        values = [QQ(root[v]) for v in leaf_ring.gens()]
        if any(v.denominator() != 1 for v in values):
            continue
        evidence.take("candidates", 1, caps.max_candidates)
        result.append([int(v) for v in values])
    evidence.write("rational-leaf-candidates", {"candidates": result})
    return result


class Selector:
    """This object never receives scalar labels alpha or beta."""
    def __init__(self, curve, catalog, search, evidence):
        self.curve, self.catalog, self.search, self.evidence = curve, catalog, search, evidence
        self.lookup = {int(point[0]): i for i, point in enumerate(catalog)}
        self.direct, self.pairs = {}, {}
        require_at_most(4*len(catalog)**2, evidence.caps.max_pair_entries, "signed pair trials")
        for i, point in enumerate(catalog):
            for sign in (-1, 1):
                self.direct.setdefault(point_key(sign*point), ([i], [sign]))
        for i, first in enumerate(catalog):
            for j, second in enumerate(catalog):
                for s, t in product((-1, 1), repeat=2):
                    self.pairs.setdefault(point_key(s*first+t*second), ([i, j], [s, t]))

    def checked(self, target, ids, signs, method):
        total = sum((s*self.catalog[i] for i, s in zip(ids, signs)), self.curve(0))
        if total != target:
            raise ValueError("returned original point decomposition failed")
        coefficients = [0]*len(self.catalog)
        for i, s in zip(ids, signs):
            coefficients[i] += s
        return {"catalog_ids": ids, "signs": signs, "coefficients": coefficients,
                "method": method}

    def decompose(self, target):
        evidence, search = self.evidence, self.search
        if target.is_zero():
            return self.checked(target, [], [], "identity")
        for method, table in (("catalog", self.direct), ("two_sum", self.pairs)):
            if point_key(target) in table:
                ids, signs = table[point_key(target)]
                return self.checked(target, ids, signs, method)
        p = int(self.curve.base_ring().characteristic())
        a, b = int(self.curve.a4()), int(self.curve.a6())
        for length in range(3, search["max_length"]+1):
            try:
                ring, rows, denominator = make_path(p, a, b, int(target[0]), length)
                integers, generators = localized_generators(
                    ring, rows, denominator, search["mode"], length, evidence)
            except GlobalCap:
                raise
            except CapExceeded as error:
                evidence.event("profile_cap", length=length, reason=str(error))
                continue
            short = []
            for multiplicity, degree in product(search["multiplicities"], search["shift_degrees"]):
                try:
                    blocks = shifted_blocks(p, integers, generators, length,
                                            multiplicity, degree, evidence)
                    for block in blocks.values():
                        short.extend(certified_short_rows(
                            p, block, length, search["x_bound"], search["height_bound"],
                            multiplicity, evidence))
                    require_at_most(len(short), evidence.caps.max_short_relations, "all short rows")
                    candidates = leaf_candidates(short, length, evidence)
                    for leaves in candidates:
                        if any(not 0 <= x < search["x_bound"] or x not in self.lookup for x in leaves):
                            continue
                        ids = [self.lookup[x] for x in leaves]
                        for signs in product((-1, 1), repeat=length):
                            evidence.take("sign_trials", 1, evidence.caps.max_sign_trials)
                            total = sum((s*self.catalog[i] for i, s in zip(ids, signs)), self.curve(0))
                            if total == target:
                                return self.checked(target, ids, list(signs),
                                                    search["mode"]+"_lattice")
                except GlobalCap:
                    raise
                except CapExceeded as error:
                    evidence.event("profile_cap", length=length, multiplicity=multiplicity,
                                   shift_degree=degree, reason=str(error))
        return None


def run(config, evidence):
    caps = evidence.caps
    data, search = config["curve"], dict(config["search"])
    if set(data) != {"p", "a", "b", "N", "r", "G", "Q"}:
        raise ValueError("curve input keys must be exactly p,a,b,N,r,G,Q")
    p, a, b, order, r = (int(data[k]) for k in ("p", "a", "b", "N", "r"))
    require_at_most(p.bit_length(), caps.max_field_bits, "field bits")
    require_at_most(r.bit_length(), caps.max_field_bits+2, "subgroup bits")
    require_at_most(order.bit_length(), caps.max_field_bits+2, "group-order bits")
    require_at_most(max(abs(a).bit_length(), abs(b).bit_length()),
                    caps.max_field_bits+1, "curve-coefficient bits")
    if p <= 3 or r <= 2 or not Integer(p).is_prime(proof=True) or not Integer(r).is_prime(proof=True):
        raise ValueError("p>3 and odd prime r required")
    if order % r or (order//r) % r == 0:
        raise ValueError("require order=h*r and gcd(h,r)=1")
    curve = EllipticCurve(GF(p), [a, b])
    if int(curve.cardinality()) != order:
        raise ValueError("input curve order did not match point count")
    generator = curve(*[GF(p)(int(v)) for v in data["G"]])
    target = curve(0) if data["Q"] is None else curve(*[GF(p)(int(v)) for v in data["Q"]])
    if generator.is_zero() or r*generator != curve(0) or r*target != curve(0):
        raise ValueError("invalid subgroup input")
    required = {"x_bound", "max_length", "mode", "multiplicities", "shift_degrees"}
    if set(search) - (required | {"height_bound"}) or not required <= set(search):
        raise ValueError("unexpected/missing search fields")
    search.setdefault("height_bound", isqrt(p)+2)
    if search["mode"] not in ("ordinary", "saturated"):
        raise ValueError("unknown mode")
    if any(type(search[k]) is not int for k in ("x_bound", "max_length", "height_bound")):
        raise ValueError("integer bounds required")
    if not 1 < search["x_bound"] < p or not 1 < search["height_bound"] <= p:
        raise ValueError("invalid coordinate bounds")
    require_at_most(search["x_bound"], caps.max_catalog, "catalog interval")
    if not 3 <= search["max_length"] <= caps.max_leaf_length:
        raise ValueError("leaf length outside admitted cap")
    for name, low, high in (("multiplicities", 1, 4), ("shift_degrees", 0, 4)):
        if not isinstance(search[name], list) or not search[name] or any(
                type(v) is not int or not low <= v <= high for v in search[name]):
            raise ValueError("invalid finite profile list")
        require_at_most(len(search[name]), 5, "profile list length")
    catalog = []
    for x in range(search["x_bound"]):
        rhs = GF(p)(x)**3 + GF(p)(a)*x + GF(p)(b)
        if rhs.is_square():
            y = int(rhs.sqrt())
            point = curve(GF(p)(x), GF(p)(min(y, p-y)))
            if not point.is_zero() and r*point == curve(0):
                catalog.append(point)
    evidence.write("fixed-catalog", {"points": [list(point_key(point)) for point in catalog],
                                      "search": search, "sage": sage_version})
    if target.is_zero():
        return {"status": "success", "scalar": "0", "verified_scalar": True,
                "catalog": [list(point_key(point)) for point in catalog], "relations": []}
    if not catalog:
        return {"status": "capped_failure", "reason": "empty fixed catalog"}
    selector = Selector(curve, catalog, search, evidence)
    labels = config.get("query_labels")
    if labels is not None:
        if not isinstance(labels, list):
            raise ValueError("query_labels must be a list")
        require_at_most(len(labels), caps.max_targets, "frozen target labels")
    rng = random.SystemRandom()
    label_width = len(str(r-1))
    def label_text(value):
        return str(int(value)).zfill(label_width)

    pivots, accepted = {}, []
    for query in range(caps.max_targets if labels is None else len(labels)):
        if labels is None:
            alpha, beta = rng.randrange(r), rng.randrange(r)
        else:
            alpha, beta = map(int, labels[query])
            if not 0 <= alpha < r or not 0 <= beta < r:
                raise ValueError("frozen labels must be canonical residues")
        point = alpha*generator + beta*target
        evidence.event("mixed_target", query=query, alpha=label_text(alpha), beta=label_text(beta),
                       point=point_key(point))
        decomposition = selector.decompose(point)  # No alpha, beta argument.
        evidence.event("query_finished", query=query, accepted=decomposition is not None)
        if decomposition is None:
            continue
        relation = {"alpha": label_text(alpha), "beta": label_text(beta), "point": point_key(point),
                    **decomposition}
        accepted.append(relation)
        c = [v % r for v in decomposition["coefficients"]]
        A, B = alpha, beta
        provenance = [0]*len(accepted)
        provenance[-1] = 1
        for pivot in sorted(pivots):
            value = c[pivot]
            row, rowA, rowB, row_provenance = pivots[pivot]
            c = [(x-value*y) % r for x, y in zip(c, row)]
            A, B = (A-value*rowA) % r, (B-value*rowB) % r
            for i, coefficient in enumerate(row_provenance):
                provenance[i] = (provenance[i]-value*coefficient) % r
        if not any(c):
            if not any(provenance):
                raise ValueError("zero original-target provenance")
            if B:
                scalar = -A*pow(B, -1, r) % r
                if scalar*generator != target:
                    raise ValueError("final scalar multiplication failed")
                return {"status": "success", "scalar": label_text(scalar), "verified_scalar": True,
                        "catalog": [list(point_key(point)) for point in catalog],
                        "relations": accepted, "dependence": [label_text(c) for c in provenance],
                        "A": label_text(A), "B": label_text(B), "counts": dict(evidence.counts)}
            if A:
                raise ValueError("checked relations gave a nonzero multiple of G equal to zero")
        else:
            pivot = next(i for i, v in enumerate(c) if v)
            inverse = pow(c[pivot], -1, r)
            pivots[pivot] = ([v*inverse % r for v in c], A*inverse % r, B*inverse % r,
                             [v*inverse % r for v in provenance])
        evidence.write("accepted-relations", {"relations": accepted, "rank": len(pivots)})
    return {"status": "capped_failure", "reason": "target-attempt cap without recovery",
            "catalog": [list(point_key(point)) for point in catalog], "relations": accepted,
            "counts": dict(evidence.counts)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    config = json.loads(args.input.read_text())
    evidence = Evidence(args.output, Caps.parse(config.get("caps", {})))
    try:
        result = run(config, evidence)
    except CapExceeded as error:
        result = {"status": "capped_failure", "reason": str(error),
                  "counts": dict(evidence.counts)}
    except Exception as error:
        traceback.print_exc()
        result = {"status": "error", "type": type(error).__name__, "reason": str(error)}
    text = json.dumps(result, indent=2) + "\n"
    if evidence.bytes + len(text.encode()) > evidence.caps.output_mib*1024**2:
        result = {"status": "capped_failure", "reason": "final result exceeds evidence cap"}
        text = json.dumps(result) + "\n"
    with (args.output / "result.json").open("x") as stream:
        stream.write(text)
    if result["status"] == "error":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
