"""Dependency-free resource metadata. No finite-field or curve arithmetic."""

from collections import deque
from dataclasses import asdict, dataclass, fields
from math import comb


class CapExceeded(RuntimeError):
    """A declared cap was reached; this does not certify absence."""


@dataclass(frozen=True)
class Caps:
    max_field_bits: int = 64
    max_catalog: int = 64
    max_leaf_length: int = 6
    max_targets: int = 128
    max_chart_trials: int = 64
    max_pair_entries: int = 16384
    max_saturation_exponent: int = 32
    max_generators: int = 32
    max_terms: int = 4096
    max_polynomial_degree: int = 64
    max_coefficient_bits: int = 8192
    max_shift_rows: int = 256
    max_total_shift_rows: int = 2048
    max_columns: int = 256
    max_matrix_cells: int = 65536
    max_lattices: int = 64
    max_short_relations: int = 128
    max_standard_monomials: int = 128
    max_groebner_pairs: int = 1024
    max_candidates: int = 256
    max_sign_trials: int = 8192
    wall_seconds: int = 120
    cpu_seconds: int = 90
    memory_mib: int = 8192
    output_mib: int = 64

    @classmethod
    def parse(cls, values):
        if not isinstance(values, dict):
            raise ValueError("caps must be an object")
        names = {f.name for f in fields(cls)}
        if set(values) - names:
            raise ValueError("unknown cap names")
        if any(type(v) is not int or not 1 <= v <= 2**24 for v in values.values()):
            raise ValueError("caps must be positive bounded integers")
        result = cls(**values)
        if result.wall_seconds > 3600 or result.cpu_seconds > 3600:
            raise ValueError("prototype deadlines cannot exceed one hour")
        if result.memory_mib > 65536 or result.output_mib > 1024:
            raise ValueError("prototype memory/output ceiling exceeded")
        if result.max_field_bits > 1024 or result.max_leaf_length > 10:
            raise ValueError("prototype field/variable ceiling exceeded")
        return result

    def dictionary(self):
        return asdict(self)


def require_at_most(value, cap, name):
    if value > cap:
        raise CapExceeded(f"{name}: {value} exceeds {cap}")


def shift_row_count(variables, generators, multiplicity, shift_degree):
    """Count the FULL declared power/monomial family before construction."""
    if min(variables, generators, multiplicity, shift_degree) < 0:
        raise ValueError("negative combinatorial parameter")
    return comb(generators + multiplicity, multiplicity) * comb(
        variables + shift_degree, shift_degree
    )


def exponent_vectors(length, degree):
    """Yield nonnegative tuples with total at most degree, without a list."""
    if length < 0 or degree < 0:
        raise ValueError("negative exponent parameter")
    if length == 0:
        yield ()
        return
    for first in range(degree + 1):
        for rest in exponent_vectors(length - 1, degree - first):
            yield (first,) + rest


def bounded_staircase(leading_exponents, variables, cap):
    """Enumerate an order ideal exactly, or raise before admitting a large one.

    The caller must certify that these are leading monomials of a Groebner
    basis. No CAS dimension/count scalar is trusted here. An infinite
    staircase reaches the same cap as an oversized finite staircase.
    """
    if variables < 1 or cap < 1:
        raise ValueError("positive variable count and cap required")
    leading = tuple(tuple(e) for e in leading_exponents)
    if any(len(e) != variables or any(type(v) is not int or v < 0 for v in e)
           for e in leading):
        raise ValueError("invalid leading monomial")
    zero = (0,) * variables
    if zero in leading:
        return []
    pending, seen, standard = deque([zero]), {zero}, []
    while pending:
        exponent = pending.popleft()
        if any(all(a <= b for a, b in zip(lm, exponent)) for lm in leading):
            continue
        if len(standard) == cap:
            raise CapExceeded("standard-monomial staircase exceeds cap")
        standard.append(exponent)
        for index in range(variables):
            child = list(exponent)
            child[index] += 1
            child = tuple(child)
            if child not in seen:
                seen.add(child)
                pending.append(child)
    return standard
