import CryptoLean.Polynomial.EndpointCoefficients
import CryptoLean.Polynomial.RankOneSelector
import CryptoLean.Polynomial.WeightedRowCertificate

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open CryptoLean.EndpointCoefficients CryptoLean.RankOneSelector
open CryptoLean.WeightedRowCertificate CryptoLean.FieldRectangles

namespace FirstOrderActual

example {K : Type*} [CommRing K] (a b τ : K) :
    (((((firstEndpoint a b τ).coeff 2).coeff 2).coeff 0).coeff 2)=1 ∧
    (((((firstEndpoint a b τ).coeff 2).coeff 0).coeff 1).coeff 1)=2*τ :=
  ⟨first_endpoint_coefficient_one a b τ,first_endpoint_coefficient_offset a b τ⟩

example (p : ℕ) [Fact p.Prime] (scale center : ZMod p) (b : ℕ)
    (weight : Fin 20 → ℕ) (F : ZMod p → Fin 20 → ZMod p) :
    selectedPairs p scale center 0 b weight F=∅ := by
  simp [selectedPairs,pairCandidates,intWindow]

example (p B H : ℕ) [Fact p.Prime] (hodd : 2 < p) (hB : 2 ≤ B) (hH : 1 ≤ H)
    (a b offset : ZMod p) (Fint : Fin 20 → ℤ)
    (hlift : ∀ i, (Fint i : ZMod p)=firstVector a b offset i) :
    (∃ scalar : ℤ, ∃ row base : Fin 20 → ℤ,
      row ≠ 0 ∧ rowNorm (firstWeights B H) row < p ∧
      ∀ i, row i=(p : ℤ)*base i+scalar*Fint i) ↔
    ∃ scalar : ZMod p, (scalar,offset) ∈
      selectedPairs p 2 0 ((p-1)/(firstWeights B H 19))
        ((p-1)/(firstWeights B H 3)) (firstWeights B H) (firstVector a b) := by
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hz
    exact (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) hodd)
      ((ZMod.natCast_eq_zero_iff 2 p).mp hz)
  have hweights (i : Fin 20) : 1 ≤ firstWeights B H i := by
    unfold firstWeights
    have hbpos : 0 < B := by omega
    have hhpos : 0 < H := by omega
    exact Nat.mul_pos (pow_pos hbpos _) (pow_pos hhpos _)
  have hp : 0 < p := (Fact.out : p.Prime).pos
  apply selected_iff_integer_short p 2 0 offset htwo
    ((p-1)/(firstWeights B H 19)) ((p-1)/(firstWeights B H 3))
    (firstWeights B H) hweights (firstVector a b) Fint hlift (19 : Fin 20) (3 : Fin 20)
  · norm_num [firstVector]
  · norm_num [firstVector]
  · exact cutoff_of_positive p _ hp (hweights 19)
  · exact cutoff_of_positive p _ hp (hweights 3)

example (p B H : ℕ) (a b τ x y U V scalar : ℤ) (row base : Fin 20 → ℤ)
    (hx : x.natAbs ≤ B) (hy : y.natAbs ≤ B) (hU : U.natAbs ≤ H) (hV : V.natAbs ≤ H)
    (hrow : ∀ i, row i=(p : ℤ)*base i+scalar*firstVector a b τ i)
    (hshort : rowNorm (firstWeights B H) row < p)
    (hroot : (p : ℤ) ∣
      (x-y)^2*(U+τ*V)^2 - 2*((x+y)*(x*y+a)+2*b)*(U+τ*V)*V +
        ((x*y-a)^2-4*b*(x+y))*V^2) :
    rowValue row (firstMonomials x y U V)=0 := by
  apply short_row_value_zero p (firstWeights B H) row (firstMonomials x y U V)
    (first_monomials_bound B H x y U V hx hy hU hV) hshort
  apply row_value_divisible p scalar row base (firstVector a b τ) _ hrow
  simpa only [rowValue,first_vector_expansion] using hroot

example (p Q : ℕ) [Fact p.Prime] (scale center : ZMod p) (a b : ℕ)
    (weight : Fin 20 → ℕ) (F : ZMod p → Fin 20 → ZMod p)
    (pool : Fin Q → ZMod p)
    (hpool : pool ∈ CryptoLean.UniversalPools.missPools Q
      (rectangleImage scale center (intWindow (ZMod p) a) (intWindow (ZMod p) b))) :
    ∀ j scalar, (scalar,pool j) ∉ selectedPairs p scale center a b weight F := by
  intro j scalar hs
  have hm := (Finset.mem_filter.mp hpool).2 j
  exact hm (selected_offset_in_rectangle p scale center scalar (pool j) a b weight F hs)

end FirstOrderActual
