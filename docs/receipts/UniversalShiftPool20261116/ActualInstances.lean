import CryptoLean.Group.TranslatedSupports
import CryptoLean.Combinatorics.UniversalPools
import CryptoLean.Group.TranslatedIntersections
import CryptoLean.Curve.CharacterCarry

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical

example (p r : ℕ) [Fact p.Prime] (E : WeierstrassCurve.Affine (ZMod p))
    (K : AddSubgroup E.Point) (W : K) (S T : Finset K)
    (hS : ∑ P ∈ S, P = 0) (hT : ∑ P ∈ T, P = 0)
    (horder : addOrderOf W = r) (hpos : 0 < T.card) (hsmall : T.card < r) :
    S ≠ T.image (W - ·) :=
  CryptoLean.TranslatedSupports.centered_reflection_ne W S T hS hT hpos
    (horder.symm ▸ hsmall)

example (p : ℕ) [Fact p.Prime] (E : WeierstrassCurve.Affine (ZMod p))
    (K : AddSubgroup E.Point) (T : Finset K)
    (hdis : Disjoint T (T.image Neg.neg)) :
    (∑ P ∈ T ∪ T.image Neg.neg, P) = 0 :=
  CryptoLean.TranslatedSupports.sum_symmetric_union T hdis

example (p k Q a : ℕ) [Fact p.Prime] (E : WeierstrassCurve.Affine (ZMod p))
    (K : AddSubgroup E.Point) [Fintype K] (anchor : Fin k → ZMod p) :
    let kap := fun (j : Fin k) (P : K) ↦ if P=0 then (1 : ℤ) else
      quadraticChar (ZMod p) ((P : E.Point).xRep 0-anchor j)
    let D := Finset.univ.filter (fun P : K ↦ ∀ j, kap j P = 1)
    let A := fun uv : K × K ↦ Finset.univ.filter
      (fun t : K ↦ uv.1+t ∈ D ∧ uv.2-t ∈ D)
    (∀ uv, a ≤ (A uv).card) →
    (Fintype.card K)^2 * (Fintype.card K-a)^Q < (Fintype.card K)^Q →
    ∃ pool : Fin Q → K, ∀ U V : K, ∃ j, U+pool j ∈ D ∧ V-pool j ∈ D := by
  intro kap D A hA hcap
  have hc : (Finset.univ : Finset (K × K)).card *
      (Fintype.card K-a)^Q < (Fintype.card K)^Q := by
    simpa only [Finset.card_univ, Fintype.card_prod, pow_two] using hcap
  obtain ⟨pool, hp⟩ := CryptoLean.UniversalPools.exists_universal_pool Q a
    (Finset.univ : Finset (K × K)) A (fun uv _ ↦ hA uv) hc
  refine ⟨pool, fun U V ↦ ?_⟩
  obtain ⟨j, hj⟩ := hp (U,V) (Finset.mem_univ _)
  exact ⟨j, (Finset.mem_filter.mp hj).2⟩

example {H : Type*} [Fintype H] [DecidableEq H] (S : Finset (Fin 0)) :
    CryptoLean.UniversalPools.badPools 0 S (fun _ ↦ (∅ : Finset H)) = ∅ := by
  have hS : S = ∅ := Finset.eq_empty_of_forall_notMem (fun i _ ↦ Fin.elim0 i)
  simp only [hS, CryptoLean.UniversalPools.badPools, Finset.biUnion_empty]

example {H : Type*} [Fintype H] [DecidableEq H] (A : Finset H) :
    (CryptoLean.UniversalPools.missPools 0 A).card = 1 := by
  rw [CryptoLean.UniversalPools.fixed_miss_count, pow_zero]
