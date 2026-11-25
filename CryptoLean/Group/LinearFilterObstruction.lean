import CryptoLean.Group.SingleRelation
import Mathlib.Tactic.FieldSimp

/-!
# Linear coefficient-filter obstruction

For a residual scalar `a + d * b`, a filter on the fixed linear coordinate
`u * a + v * b` is independent in the exact finite-cardinality sense whenever
`u * d - v ≠ 0`.  The two coordinates then form an equivalence of coefficient
pairs.  Consequently, fixing a filter value leaves exactly one coefficient
pair for every residual scalar, and arbitrary predicates on the filter and
residual coordinates factor as a product.

The excluded direction `u * d - v = 0` is precisely the direction parallel to
the residual coordinate; selecting it requires encoding the hidden scalar
`d`.  These are structural statements only.  They make no timing or benchmark
claim.
-/

set_option autoImplicit false

namespace CryptoLean.SingleRelation

variable {F : Type*} [Field F]

/-- The filter coordinate `u*a + v*b` and residual coordinate `a + d*b`
give an invertible reparametrization of coefficient pairs unless their
directions are parallel. -/
def linearFilterResidualEquiv (u v d : F) (h : u * d - v ≠ 0) :
    F × F ≃ F × F where
  toFun ab := (u * ab.1 + v * ab.2, ab.1 + d * ab.2)
  invFun ts :=
    let b := (u * ts.2 - ts.1) / (u * d - v)
    (ts.2 - d * b, b)
  left_inv := by
    intro ab
    have hduv : d * u - v ≠ 0 := by simpa [mul_comm] using h
    dsimp
    apply Prod.ext
    · field_simp [h, hduv]
      ring
    · field_simp [h, hduv]
      ring
  right_inv := by
    intro ts
    have hduv : d * u - v ≠ 0 := by simpa [mul_comm] using h
    dsimp
    apply Prod.ext
    · field_simp [h, hduv]
      ring
    · field_simp [h, hduv]
      ring

/-- A product predicate on two coordinates is equivalent to the product of
the two predicate subtypes. -/
def independentPredicateProductEquiv (Keep Rel : F → Prop) :
    {ts : F × F // Keep ts.1 ∧ Rel ts.2} ≃
      {t : F // Keep t} × {s : F // Rel s} where
  toFun ts := (⟨ts.1.1, ts.2.1⟩, ⟨ts.1.2, ts.2.2⟩)
  invFun ts := ⟨(ts.1.1, ts.2.1), ts.1.2, ts.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Any predicates on a nonparallel linear filter coordinate and on the
residual scalar factor through a product equivalence. -/
def linearFilteredSetEquiv (u v d : F) (h : u * d - v ≠ 0)
    (Keep Rel : F → Prop) :
    {ab : F × F // Keep (u * ab.1 + v * ab.2) ∧ Rel (ab.1 + d * ab.2)} ≃
      {t : F // Keep t} × {s : F // Rel s} :=
  ((linearFilterResidualEquiv u v d h).subtypeEquiv (by intro ab; rfl)).trans
    (independentPredicateProductEquiv Keep Rel)

/-- Exact cardinality factorization for arbitrary filter and relation
predicates.  On a finite field this is the counting form of independence. -/
theorem linear_filtered_set_card (u v d : F) (h : u * d - v ≠ 0)
    (Keep Rel : F → Prop) :
    Nat.card
        {ab : F × F //
          Keep (u * ab.1 + v * ab.2) ∧ Rel (ab.1 + d * ab.2)} =
      Nat.card {t : F // Keep t} * Nat.card {s : F // Rel s} := by
  calc
    _ = Nat.card ({t : F // Keep t} × {s : F // Rel s}) :=
      Nat.card_congr (linearFilteredSetEquiv u v d h Keep Rel)
    _ = _ := Nat.card_prod _ _

/-- Fixing one admitted filter value leaves exactly the unfiltered residual
predicate: one coefficient pair for every accepted residual scalar. -/
def linearFilteredFiberEquiv (u v d t : F) (h : u * d - v ≠ 0)
    (Rel : F → Prop) :
    {ab : F × F //
        u * ab.1 + v * ab.2 = t ∧ Rel (ab.1 + d * ab.2)} ≃
      {s : F // Rel s} :=
  (linearFilteredSetEquiv u v d h (fun x => x = t) Rel).trans
    { toFun := fun ts => ts.2
      invFun := fun s => (⟨t, rfl⟩, s)
      left_inv := by
        intro ts
        apply Prod.ext
        · apply Subtype.ext
          exact ts.1.2.symm
        · rfl
      right_inv := by intro s; rfl }

/-- Cardinality form of `linearFilteredFiberEquiv`. -/
theorem linear_filtered_fiber_card (u v d t : F) (h : u * d - v ≠ 0)
    (Rel : F → Prop) :
    Nat.card
        {ab : F × F //
          u * ab.1 + v * ab.2 = t ∧ Rel (ab.1 + d * ab.2)} =
      Nat.card {s : F // Rel s} :=
  Nat.card_congr (linearFilteredFiberEquiv u v d t h Rel)

end CryptoLean.SingleRelation
