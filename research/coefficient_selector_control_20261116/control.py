"""UNEXECUTED Sage control library. No CLI or work on import.

Call only from an already admitted, source-bound parent enforcing protocol.json,
the whole-process original deadline/memory limits and raw/compressed output caps.
The parent retains every event, reserves terminal metadata space, and classifies
external interruption as incomplete. Source preparation grants no execution or
spending authority. This controls the frozen FIRST-endpoint implementation only.
"""

from collections import Counter
import hashlib
import importlib.util
import sys
from pathlib import Path


class IncompleteControl(RuntimeError):
    """The admitted parent may raise this on its shared output/deadline cap."""


SELECTOR_SHA256 = "3e06648f3f1b6e1ad8a8153b4410035593a3e2d4c272a8a0fda91af27e704096"
CASES = (("empty17", 17, -3, 1, 2, 1), ("positive257", 257, -3, 1, 2, 1))
COLUMNS = (
    (2, 0, 2, 0), (1, 1, 2, 0), (0, 2, 2, 0), (2, 0, 1, 1),
    (1, 1, 1, 1), (0, 2, 1, 1), (2, 1, 1, 1), (1, 2, 1, 1),
    (1, 0, 1, 1), (0, 1, 1, 1), (0, 0, 1, 1), (2, 0, 0, 2),
    (1, 1, 0, 2), (0, 2, 0, 2), (2, 1, 0, 2), (1, 2, 0, 2),
    (1, 0, 0, 2), (0, 1, 0, 2), (0, 0, 0, 2), (2, 2, 0, 2),
)
_STARTED = False


def _load_frozen(root):
    path = Path(root) / "research/coefficient_first_selector_20261116/selector.py"
    if hashlib.sha256(path.read_bytes()).hexdigest() != SELECTOR_SHA256:
        raise ValueError("frozen selector source hash mismatch")
    name = "coefficient_selector_frozen_control_20261116"
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def _signed(residue, p):
    half = (p - 1) // 2
    return (int(residue) + half) % p - half


def _delta(counter):
    return [{"scalar": str(key[0]), "offset": str(key[1]),
             "centered_row": [str(c) for c in key[2]], "multiplicity": count}
            for key, count in sorted(counter.items())]


def run_controls(repo_root, emit):
    """Run the frozen control only inside an already admitted Sage parent.

    A parent output cap raises IncompleteControl. An incomplete or failed run
    cannot certify absence or benchmark performance. Every pair event survives;
    equal polynomial values never collapse the recorded block multiplicity.
    """
    global _STARTED
    if _STARTED:
        raise IncompleteControl("one frozen control panel per process; no budget/deadline reset")
    _STARTED = True
    library = _load_frozen(repo_root)
    # One Budget across BOTH fast/reference cases and the final cap control.
    budget = library.Budget(max_pairs=70_210, max_certificates=128, max_field_bits=16)
    baseline_total = sum(p * (p - 1) for _, p, *_ in CASES)
    fast_total = sum(2 * ((p - 1) // (B**4 * H**2)) *
                     (2 * ((p - 1) // (B**2 * H**2)) + 1)
                     for _, p, _, _, B, H in CASES)
    if baseline_total + fast_total != budget.max_pairs:
        raise ValueError("frozen whole-panel pair count mismatch")
    terminal = {"status": "incomplete", "component_only": True,
                "complete_algorithm_criterion_met": False}
    try:
        emit({"stage": "panel", "status": "control_not_ecdlp",
              "selector_source_sha256": SELECTOR_SHA256,
              "planned_main_pairs": str(budget.max_pairs),
              "reference_pairs_reserved": str(baseline_total),
              "limits": {"max_certificates": str(budget.max_certificates)}})
        budget.reserve(baseline_total)
        # Import and mathematical work occur ONLY inside the admitted call.
        from sage.all import GF, PolynomialRing, ZZ

        summaries = []
        for case, p, a, b, B, H in CASES:
            if not ZZ(p).is_prime(proof=True):
                raise AssertionError("control prime precondition failed")
            field = GF(p)
            if field(4) * field(a)**3 + field(27) * field(b)**2 == 0:
                raise AssertionError("singular curve control")
            ring = PolynomialRing(field, names=("x", "y", "U", "V"))
            x, y, U, V = ring.gens()
            aa, bb = field(a), field(b)
            weights = tuple(B**(e[0] + e[1]) * H**(e[2] + e[3]) for e in COLUMNS)
            cache = {}

            def reference(offset):
                if offset not in cache:
                    tau = field(offset)
                    poly = ((x - y)**2 * (U + tau*V)**2
                            - 2*((x + y)*(x*y + aa) + 2*bb)*(U + tau*V)*V
                            + ((x*y - aa)**2 - 4*bb*(x + y))*V**2)
                    terms = {tuple(int(k) for k in key): value
                             for key, value in poly.dict().items()}
                    if not set(terms).issubset(COLUMNS):
                        raise AssertionError("reference support outside frozen layout")
                    cache[offset] = tuple(int(terms.get(e, field(0))) for e in COLUMNS)
                return cache[offset]

            fast = Counter()

            def capture(event):
                # Retain the raw event BEFORE interpreting it.
                emit({"case": case, "method": "fast", "event": event})
                if event["stage"] != "pair":
                    return
                scalar, offset = int(event["scalar_residue"]), int(event["offset"])
                coefficients = reference(offset)
                row = tuple(_signed(field(scalar)*field(c), p) for c in coefficients)
                norm = sum(abs(c)*w for c, w in zip(row, weights))
                if tuple(tuple(e) for e in event["columns"]) != COLUMNS:
                    raise AssertionError("fast column layout changed")
                if any(len(event[key]) != len(COLUMNS)
                       for key in ("source_row", "weights", "centered_row")):
                    raise AssertionError("fast vector length mismatch")
                if any(int(c) % p != r for c, r in zip(event["source_row"], coefficients)):
                    raise AssertionError("fast source coefficient mismatch")
                if tuple(int(c) for c in event["weights"]) != weights:
                    raise AssertionError("fast monomial weight mismatch")
                if tuple(int(c) for c in event["centered_row"]) != row or int(event["l1"]) != norm:
                    raise AssertionError("fast centered row/norm mismatch")
                accepted = any(row) and norm < p
                if event["accepted"] != accepted:
                    raise AssertionError("fast acceptance mismatch")
                if accepted:
                    signed_scalar = int(event["first_coefficient"])
                    if signed_scalar % p != scalar or int(event["second_coefficient"]) != row[3]:
                        raise AssertionError("fast coefficient anchor mismatch")
                    witness = tuple(int(q) for q in event["modulus_row_witness"])
                    source = tuple(int(c) for c in event["source_row"])
                    if len(witness) != len(COLUMNS) or any(
                            c != signed_scalar*f + p*q for c, f, q in zip(row, source, witness)):
                        raise AssertionError("fast exact modulus witness mismatch")
                    fast[(scalar, offset, row)] += 1

            result = library.select_first_endpoint(p, a, b, B, H, budget, capture)
            emit({"stage": "fast_result", "case": case, "result": result})
            expected = "complete_empty" if case == "empty17" else "complete_nonempty"
            if result["status"] == "incomplete":
                raise IncompleteControl("main fast family did not finish")
            if result["status"] != expected:
                raise AssertionError("frozen case prediction failed")

            baseline = Counter()
            visited = 0
            planned = p*(p - 1)
            for offset in range(p):
                coefficients = reference(offset)
                for scalar in range(1, p):
                    if budget.exhausted or budget.certificates >= budget.max_certificates:
                        raise IncompleteControl("shared cap before next reference pair")
                    row = tuple(_signed(field(scalar)*field(c), p) for c in coefficients)
                    norm = sum(abs(c)*w for c, w in zip(row, weights))
                    accepted = any(row) and norm < p
                    event = {"stage": "reference_pair", "case": case,
                             "scalar": str(scalar), "offset": str(offset),
                             "source_row": [str(c) for c in coefficients],
                             "weights": [str(w) for w in weights],
                             "centered_row": [str(c) for c in row],
                             "l1": str(norm), "accepted": accepted}
                    if accepted:
                        witness = tuple((c - scalar*f)//p for c, f in zip(row, coefficients))
                        event["modulus_row_witness"] = [str(q) for q in witness]
                    emit(event)
                    visited += 1
                    if accepted:
                        if any(c != scalar*f + p*q for c, f, q in zip(row, coefficients, witness)):
                            raise AssertionError("reference exact witness mismatch")
                        baseline[(scalar, offset, row)] += 1
                        budget.certificates += 1
                        if budget.certificates >= budget.max_certificates and visited < planned:
                            budget.exhausted = True
                            raise IncompleteControl("shared certificate cap in reference family")
            emit({"stage": "comparison", "case": case,
                  "fast_only": _delta(fast - baseline),
                  "reference_only": _delta(baseline - fast),
                  "reference_visited": str(visited), "reference_planned": str(planned)})
            if fast != baseline or visited != planned:
                raise AssertionError("complete accepted multiset mismatch")
            if case == "positive257":
                known = tuple(_signed(c, p) for c in reference(0))
                if baseline[(1, 0, known)] != 1 or sum(abs(c)*w for c, w in zip(known, weights)) != 141:
                    raise AssertionError("frozen positive software control missing")
            summaries.append({"case": case, "status": expected,
                              "accepted_pairs": str(sum(fast.values())),
                              "reference_pairs": str(visited)})

        # Do NOT reset Budget. The next full reservation must fail preflight.
        guard_pairs = []

        def guard_capture(event):
            emit({"case": "shared_cap", "method": "fast", "event": event})
            if event["stage"] == "pair":
                guard_pairs.append(event)

        guard = library.select_first_endpoint(17, -3, 1, 2, 1, budget, guard_capture)
        emit({"stage": "cap_control_result", "result": guard})
        if guard["status"] != "incomplete" or guard["visited_pairs"] != 0 or guard_pairs:
            raise AssertionError("shared cap did not remain incomplete before pairs")
        terminal.update(status="controls_passed", summaries=summaries,
                        shared_reserved_pairs=str(budget.reserved_pairs),
                        shared_certificates=str(budget.certificates),
                        cap_control="incomplete_expected")
    except (IncompleteControl, library.IncompleteSearch) as error:
        terminal.update(status="incomplete", reason=str(error))
    except Exception as error:
        terminal.update(status="controls_failed", error_type=type(error).__name__, reason=str(error))
    # Parent reserves space and persists this return even when the sink is full.
    return terminal
