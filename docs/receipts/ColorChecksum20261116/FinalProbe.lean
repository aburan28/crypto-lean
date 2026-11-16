import CryptoLean.Group.ColorChecksums
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false
noncomputable section
open scoped BigOperators

example (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve.Affine (ZMod p))
    (H : AddSubgroup W.Point) {I J : Type*} [Fintype I]
    (weights : I → J → H) (j0 : J) :
    (∃ target : H, ∀ c : I → J, ∑ i : I, weights i (c i) = target) ↔
      ∀ i : I, ∀ j k : J, weights i j = weights i k :=
  CryptoLean.ColorChecksums.common_target_iff weights j0

example (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve.Affine (ZMod p))
    (H : AddSubgroup W.Point) {I J : Type*} [Fintype I] [Fintype J]
    (V : Finset (I → J → ℕ)) (weights : I → H) (K : ℕ)
    (hcap : ∀ u ∈ V, ∀ i : I, (∑ j : J, u i j) ≤ K) :
    letI : DecidableEq H := Classical.decEq H
    (V.image (fun u : I → J → ℕ ↦ ∑ i : I, ∑ j : J, u i j • weights i)).card ≤
      (K+1)^Fintype.card I := by
  letI : DecidableEq H := Classical.decEq H
  exact CryptoLean.ColorChecksums.checksum_image_card_le V weights K hcap

example (q : ℕ) {I J : Type*} [Fintype I] [Fintype J]
    (V : Finset (I → J → ℕ)) (weights : I → ZMod q) (K : ℕ)
    (hcap : ∀ u ∈ V, ∀ i : I, (∑ j : J, u i j) ≤ K) :
    (V.image (fun u : I → J → ℕ ↦ ∑ i : I, ∑ j : J, u i j • weights i)).card ≤
      (K+1)^Fintype.card I :=
  CryptoLean.ColorChecksums.checksum_image_card_le V weights K hcap
