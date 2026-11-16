import CryptoLean.Group.PairColourIsolation
import CryptoLean.Curve.CharacterCarry

set_option autoImplicit false
noncomputable section

example (N M ell : ℕ) (S T : Finset (Fin N × Fin M)) (hT : T ⊆ S)
    (hsize : 2*S.card ≤ Fintype.card (Fin ell → ZMod 2)) :
    let A := fun e : Fin N × Fin M ↦
      Finset.univ.filter (fun w : (Fin N → Fin ell → ZMod 2) ×
        (Fin M → Fin ell → ZMod 2) ↦ CryptoLean.PairColourIsolation.edgeColour e w = 0)
    T.card*Fintype.card ((Fin N → Fin ell → ZMod 2) × (Fin M → Fin ell → ZMod 2)) ≤
      2*Fintype.card (Fin ell → ZMod 2)*
        (T.biUnion (fun e ↦ A e \ (S.erase e).biUnion A)).card :=
  CryptoLean.PairColourIsolation.target_colour_count S T hT hsize

open Classical in
example (p : ℕ) [Fact p.Prime] (N M ell : ℕ)
    (W : WeierstrassCurve.Affine (ZMod p)) (a : ZMod p)
    (P : Fin N → W.Point) (Q : Fin M → W.Point) :
    let kappa := fun R : W.Point ↦ if R=0 then (1 : ℤ) else
      quadraticChar (ZMod p) (R.xRep 0-a)
    let S := Finset.univ.filter (fun e : Fin N × Fin M ↦ kappa (P e.1+Q e.2) = 1)
    ∀ T : Finset (Fin N × Fin M), T ⊆ S →
      2*S.card ≤ Fintype.card (Fin ell → ZMod 2) →
    let A := fun e : Fin N × Fin M ↦
      Finset.univ.filter (fun w : (Fin N → Fin ell → ZMod 2) ×
        (Fin M → Fin ell → ZMod 2) ↦ CryptoLean.PairColourIsolation.edgeColour e w = 0)
    T.card*Fintype.card ((Fin N → Fin ell → ZMod 2) × (Fin M → Fin ell → ZMod 2)) ≤
      2*Fintype.card (Fin ell → ZMod 2)*
        (T.biUnion (fun e ↦ A e \ (S.erase e).biUnion A)).card := by
  intro kappa S T hT hsize
  exact CryptoLean.PairColourIsolation.target_colour_count S T hT hsize
