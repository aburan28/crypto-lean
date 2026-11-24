import CryptoLean.Curve.TightNormRelation

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Polynomial WeierstrassCurve.Affine CryptoLean.TightNormRelation

namespace TightNormMixedActual
variable {K : Type*} [Field K] [DecidableEq K] {W : WeierstrassCurve.Affine K}

theorem colored_mixed_tight_row_recovers {t b : ℕ}
    (ha₁ : W.a₁=0) (ha₂ : W.a₂=0) (ha₃ : W.a₃=0)
    (G H : W.Point) (q k : ℕ) [Fact q.Prime] (ho : addOrderOf G=q) (hH : H=k • G)
    (α β : Fin t × Fin b → ℕ) (x y : Fin t × Fin b → K)
    (hx : Function.Injective x) (hc : ∀ p, W.Nonsingular (x p) (y p))
    (hm : ∀ p, (Point.some (x p) (y p) (hc p) : W.Point)=α p • G+β p • H)
    (choice : Fin t → Fin b) (u v : K[X]) (hp : (u,v) ≠ 0)
    (hr : ∀ i, u.eval (x (i,choice i))+y (i,choice i)*v.eval (x (i,choice i))=0)
    (hu : 2*u.natDegree ≤ t) (hv : 3+2*v.natDegree ≤ t)
    (hb : (∑ i, (β (i,choice i) : ZMod q)) ≠ 0) :
    -(∑ i, (α (i,choice i) : ZMod q))/(∑ i, (β (i,choice i) : ZMod q))=
      (k : ZMod q) := by
  apply recover_from_short_tight_row W ha₁ ha₂ ha₃ G H q k ho hH
    (fun i ↦ α (i,choice i)) (fun i ↦ β (i,choice i))
    (fun i ↦ x (i,choice i)) (fun i ↦ y (i,choice i)) ?_
    (fun i ↦ hc (i,choice i)) (fun i ↦ hm (i,choice i)) u v hp hr ?_ hb
  · intro i j hij
    exact congrArg Prod.fst (hx hij)
  · simpa only [Fintype.card_fin] using
      CryptoLean.NormSaturatedInterpolation.curveNorm_degree_bound W.a₄ W.a₆ u v t hu hv

end TightNormMixedActual
