"""UNEXECUTED coefficient-first search for ONE rank-one endpoint block.

Precondition: the parent has certified that p is an odd prime. This library
neither certifies p nor solves ECDLP. It performs no work on import. Numerical
use needs the existing execution/budget/backend/admission rules.

The callback must retain every event and enforce a shared output limit. It
raises IncompleteSearch on that limit; the parent reserves terminal-result
space and applies whole-process deadlines/memory limits. Reuse ONE Budget
across all calls/profiles. Complete-empty refers only to the declared row
family p*Z^20 + Z*F, with the specified positive monomial weights.
"""

from dataclasses import dataclass


class IncompleteSearch(RuntimeError):
    pass


@dataclass
class Budget:
    max_pairs: int = 100_000
    max_certificates: int = 128
    max_field_bits: int = 1024
    reserved_pairs: int = 0
    certificates: int = 0
    exhausted: bool = False

    def reserve(self, pairs):
        if self.exhausted:
            raise IncompleteSearch("shared budget already exhausted")
        self.reserved_pairs += pairs
        if self.reserved_pairs > self.max_pairs:
            self.exhausted = True
            raise IncompleteSearch("full pair-family reservation exceeds shared cap")
        if pairs and self.certificates >= self.max_certificates:
            self.exhausted = True
            raise IncompleteSearch("shared certificate cap already reached")


def centered(value, p):
    residue = value % p
    return residue if residue <= p//2 else residue-p


def first_endpoint_coefficients(a, b, tau):
    """Integer lift of S3(x,y,tau+U/V)*V^2; no discarded zero columns.

    Dictionary order is the fixed column order. Terms with equal monomials
    have been combined; the 24-term expansion has 20 distinct monomials.
    """
    return {
        (2, 0, 2, 0): 1,
        (1, 1, 2, 0): -2,
        (0, 2, 2, 0): 1,
        (2, 0, 1, 1): 2*tau,
        (1, 1, 1, 1): -4*tau,
        (0, 2, 1, 1): 2*tau,
        (2, 1, 1, 1): -2,
        (1, 2, 1, 1): -2,
        (1, 0, 1, 1): -2*a,
        (0, 1, 1, 1): -2*a,
        (0, 0, 1, 1): -4*b,
        (2, 0, 0, 2): tau*tau,
        (1, 1, 0, 2): -2*tau*tau-2*a,
        (0, 2, 0, 2): tau*tau,
        (2, 1, 0, 2): -2*tau,
        (1, 2, 0, 2): -2*tau,
        (1, 0, 0, 2): -2*a*tau-4*b,
        (0, 1, 0, 2): -2*a*tau-4*b,
        (0, 0, 0, 2): a*a-4*b*tau,
        (2, 2, 0, 2): 1,
    }


def select_first_endpoint(p, a, b, B, H, budget, emit):
    """Find a minimal representative for every admissible scalar/offset pair.

    Exactness is conditional on the declared prime/model preconditions and
    a completed search. No claim that a returned row isolates roots, that a
    point decomposition exists, or that a useful fraction of targets succeeds.
    Raw scalar/coefficient-pair records are retained even if rows coincide.
    """
    values = (p, a, b, B, H)
    if any(type(v) is not int for v in values):
        raise ValueError("integer model parameters required")
    if p < 5 or p % 2 == 0 or not 2 <= B < p or not 1 <= H < p:
        raise ValueError("require caller-certified odd prime p>=5, 2<=B<p, 1<=H<p")
    if p.bit_length() > budget.max_field_bits:
        raise ValueError("field bit cap exceeded")
    if max(abs(a).bit_length(), abs(b).bit_length()) > budget.max_field_bits+1:
        raise ValueError("curve-coefficient input bit cap exceeded")
    if (type(budget.max_pairs) is not int or budget.max_pairs < 0
            or type(budget.max_certificates) is not int or budget.max_certificates < 0):
        raise ValueError("invalid shared cap")
    a, b = a % p, b % p
    first_weight = B**4*H**2
    second_weight = B**2*H**2
    first_cap = (p-1)//first_weight
    second_cap = (p-1)//second_weight
    planned = 2*first_cap*(2*second_cap+1)
    visited, found = 0, 0
    status, reason = "incomplete", None
    try:
        emit({
            "stage": "model", "scope": "first-order rank-one certificate selection only",
            "p": str(p), "a": str(a), "b": str(b), "B": str(B), "H": str(H),
            "prime_precondition": "must be certified by parent; this library does not certify p",
            "first_cap": str(first_cap), "second_cap": str(second_cap),
            "planned_pairs": str(planned), "columns": 20,
        })
        budget.reserve(planned)
        for c1 in range(-first_cap, first_cap+1):
            if c1 == 0:
                continue
            # Bounds make |c1|<p/2, so this is a nonzero residue for prime p.
            inverse = pow(2*c1 % p, -1, p)
            for c2 in range(-second_cap, second_cap+1):
                tau = c2*inverse % p
                coefficients = first_endpoint_coefficients(a, b, tau)
                columns = list(coefficients)
                weights = [B**(e[0]+e[1])*H**(e[2]+e[3]) for e in columns]
                row = [centered(c1*coefficients[e], p) for e in columns]
                norm = sum(abs(c)*w for c, w in zip(row, weights))
                visited += 1
                if row[columns.index((2, 2, 0, 2))] != c1:
                    raise ArithmeticError("first coefficient window lost its residue representative")
                if row[columns.index((2, 0, 1, 1))] != c2:
                    raise ArithmeticError("second coefficient window lost its residue representative")
                accepted = any(row) and norm < p
                event = {
                    "stage": "pair", "index": visited,
                    "first_coefficient": str(c1), "second_coefficient": str(c2),
                    "scalar_residue": str(c1 % p), "offset": str(tau),
                    "columns": [list(e) for e in columns],
                    "source_row": [str(coefficients[e]) for e in columns],
                    "weights": [str(w) for w in weights],
                    "centered_row": [str(c) for c in row], "l1": str(norm),
                    "accepted": accepted,
                }
                if accepted:
                    witness = []
                    for e, c in zip(columns, row):
                        q, remainder = divmod(c-c1*coefficients[e], p)
                        if remainder or c != c1*coefficients[e]+p*q:
                            raise ArithmeticError("exact rank-one row witness failed")
                        witness.append(str(q))
                    event["modulus_row_witness"] = witness
                emit(event)
                if accepted:
                    found += 1
                    budget.certificates += 1
                    if budget.certificates >= budget.max_certificates and visited < planned:
                        budget.exhausted = True
                        raise IncompleteSearch("certificate cap before pair-family completion")
        status = "complete_nonempty" if found else "complete_empty"
    except IncompleteSearch as error:
        status, reason = "incomplete", str(error)
    return {
        "status": status, "reason": reason,
        "scope": "exact first-order rank-one block only; no ECDLP/root/yield claim",
        "planned_pairs": str(planned), "visited_pairs": visited,
        "certificates_emitted": found,
        "shared_reserved_pairs": str(budget.reserved_pairs),
        "shared_certificates": budget.certificates,
        "complete_algorithm_criterion_met": False,
    }
