import CryptoLean.Curve.ConductorGap
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-! Instance probe: the transfer law applies verbatim to Mathlib's group of
points of two Weierstrass curves over a field. The isogeny `φ` and its dual
`ψ` (with `ψ ∘ φ = [d]`) are hypotheses: Mathlib has no isogenies yet. -/

open CryptoLean.ConductorGap

variable {F : Type*} [Field F] [DecidableEq F]
  (E E' : WeierstrassCurve.Affine F)

theorem curve_dlog_transfer (φ : E.Point →+ E'.Point) (ψ : E'.Point →+ E.Point) (d : ℕ)
    (hdual : ∀ x, ψ (φ x) = d • x) {P Q : E.Point}
    (hcop : Nat.Coprime d (addOrderOf P)) (hQ : Q ∈ AddSubgroup.zmultiples P)
    {k : ℤ} (hk : φ Q = k • φ P) : Q = k • P :=
  dlog_transfer φ ψ d hdual hcop hQ hk

theorem curve_order_preserved (φ : E.Point →+ E'.Point) (ψ : E'.Point →+ E.Point) (d : ℕ)
    (hdual : ∀ x, ψ (φ x) = d • x) {P : E.Point} (hcop : Nat.Coprime d (addOrderOf P)) :
    addOrderOf (φ P) = addOrderOf P :=
  addOrderOf_map_eq φ ψ d hdual hcop

/-- The 2026-10-22 study's class: `t² − 4p = −11·(2⁶·631409)²` and
`N = 631409 ∣ t + 2`, so the twist's Frobenius eigenvalue `−t/2 ≡ 1 (mod N)`;
`N ∤ #E` so `gap_prime_dvd_order` does not apply there (no pairing weakness). -/
theorem study_class_facts :
    (-5051274 : ℤ) ^ 2 - 4 * 4497080234220953 = -11 * (2 ^ 6 * 631409) ^ 2 ∧
    (631409 : ℤ) ∣ -5051274 + 2 ∧ ¬ (631409 : ℤ) ∣ 4497080234220953 + 1 - (-5051274) := by
  refine ⟨by norm_num, by norm_num, by decide⟩

#print axioms curve_dlog_transfer
#print axioms study_class_facts
