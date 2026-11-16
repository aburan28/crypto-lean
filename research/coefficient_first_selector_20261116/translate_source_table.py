"""Translate the restricted coefficient-table AST into a fresh Lean probe.

This performs source parsing only: it never imports/runs the selector or
performs prime-field/curve arithmetic. Use a fresh --tag for each receipt.
"""

import argparse
import ast
import hashlib
import json
from pathlib import Path
import re


def expression(node):
    names = {"a": "a", "b": "b", "tau": "τ"}
    if isinstance(node, ast.Name) and node.id in names:
        return names[node.id]
    if isinstance(node, ast.Constant) and type(node.value) is int:
        return str(node.value)
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
        return "(-" + expression(node.operand) + ")"
    if isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Add, ast.Sub, ast.Mult)):
        operator = {ast.Add: "+", ast.Sub: "-", ast.Mult: "*"}[type(node.op)]
        return "(" + expression(node.left) + operator + expression(node.right) + ")"
    raise ValueError("unsupported source polynomial expression: " + ast.dump(node))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--tag", required=True)
    args = parser.parse_args()
    if not re.fullmatch(r"[A-Za-z0-9_]+", args.tag):
        raise ValueError("tag must be a simple fresh identifier")
    root = args.repo.resolve()
    source = root / "research/coefficient_first_selector_20261116/selector.py"
    tree = ast.parse(source.read_text())
    function = next(n for n in tree.body if isinstance(n, ast.FunctionDef)
                    and n.name == "first_endpoint_coefficients")
    body = [n for n in function.body if not (
        isinstance(n, ast.Expr) and isinstance(n.value, ast.Constant)
        and isinstance(n.value.value, str))]
    if len(body) != 1 or not isinstance(body[0], ast.Return) or not isinstance(body[0].value, ast.Dict):
        raise ValueError("coefficient function must be one literal dictionary return")
    table = body[0].value
    keys = [ast.literal_eval(k) for k in table.keys]
    if len(keys) != 20 or len(set(keys)) != 20 or any(
            len(k) != 4 or any(type(x) is not int or x < 0 for x in k)
            or k[2]+k[3] != 2 for k in keys):
        raise ValueError("unexpected coefficient monomial layout")
    model = (root / "CryptoLean/Polynomial/EndpointCoefficients.lean").read_text()
    block = model.split("def firstExponents", 1)[1].split(
        "theorem first_exponents_injective", 1)[0]
    formal_keys = [tuple(map(int, x)) for x in re.findall(
        r"!\[(\d+),(\d+),(\d+),(\d+)\]", block)]
    if keys != formal_keys:
        raise ValueError("source and formal monomial order differ")
    namespace = "PythonTableProbe" + args.tag
    values = [expression(v) for v in table.values]
    text = ("import CryptoLean.Polynomial.EndpointCoefficients\n"
            "set_option autoImplicit false\nnoncomputable section\nnamespace " + namespace
            + "\nvariable {R : Type*} [CommRing R]\n"
            "def sourceVector (a b τ : R) : Fin 20 → R := ![\n  "
            + ",\n  ".join(values) + "]\n"
            "theorem sourceVector_eq_model (a b τ : R) :\n"
            "    sourceVector a b τ = CryptoLean.EndpointCoefficients.firstVector a b τ := by\n"
            "  funext i\n  fin_cases i <;> norm_num [sourceVector,"
            "CryptoLean.EndpointCoefficients.firstVector]\n  all_goals ring\n"
            "#print axioms sourceVector_eq_model\nend " + namespace + "\n")
    proof = root / "docs/receipts/FirstOrderSelector20261116" / (namespace + ".lean")
    receipt = root / "docs/receipts/first-order-selector-20261116" / (
        "source-table-" + args.tag + ".json")
    if proof.exists() or receipt.exists():
        raise FileExistsError("fresh probe and receipt paths required")
    with proof.open("x") as stream:
        stream.write(text)
    metadata = {
        "scope": "AST/literal source translation; no selector execution",
        "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "columns": len(keys), "keys_match_formal_model": True,
        "probe": str(proof.relative_to(root)),
        "probe_sha256": hashlib.sha256(proof.read_bytes()).hexdigest(),
        "scientific_execution": False,
    }
    with receipt.open("x") as stream:
        json.dump(metadata, stream, indent=2)
        stream.write("\n")
    print(json.dumps(metadata))


if __name__ == "__main__":
    main()
