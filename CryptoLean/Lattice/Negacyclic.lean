import Mathlib.RingTheory.AdjoinRoot
import CryptoLean.Lattice.ModuleLWE

/-!
# The negacyclic ring `R_q = Z_q[X]/(X^n + 1)` and the Ring- and Module-LWE instance

The ring of Ring-LWE in its usual polynomial form (Lyubashevsky–Peikert–Regev 2010 with
`n` a power of two, where `X^n + 1` is the `2n`-th cyclotomic polynomial and the
polynomial and canonical-embedding forms agree up to scaling), and of ML-KEM / ML-DSA
(`n = 256`). The ring is Mathlib's `AdjoinRoot`; its power basis gives the coefficient
embedding. Instance obligations:

* `negacyclic_X_pow`: `X^n = -1` in `R_q` (the "negacyclic wrap-around");
* `mlwe_coeff_is_lwe`: the endpoint of `repr_sample` for this ring: a Module-LWE
  sample of rank `d` over `R_q` is `n` LWE samples over `Z_q` in dimension `d·n`.
  Ring-LWE is `d = 1` (`sample_fin_one`).
-/

set_option autoImplicit false

namespace CryptoLean.Lattice

open Polynomial Matrix

variable (q n : ℕ)

/-- `X^n + 1` over `ZMod q`. -/
noncomputable def negacyclicPoly : (ZMod q)[X] := X ^ n + C 1

/-- `R_q = Z_q[X]/(X^n + 1)`. -/
abbrev NegacyclicRing := AdjoinRoot (negacyclicPoly q n)

theorem negacyclicPoly_monic (hn : n ≠ 0) : (negacyclicPoly q n).Monic :=
  monic_X_pow_add_C 1 hn

/-- `X^n = -1` in `R_q`. -/
theorem negacyclic_X_pow : (AdjoinRoot.root (negacyclicPoly q n)) ^ n = -1 := by
  have h := AdjoinRoot.eval₂_root (negacyclicPoly q n)
  unfold negacyclicPoly at h ⊢
  rw [eval₂_add, eval₂_X_pow, eval₂_C, map_one] at h
  exact eq_neg_of_add_eq_zero_left h

/-- The coefficient basis `1, X, …, X^(n-1)` of `R_q` over `Z_q`. -/
noncomputable def negacyclicBasis (hn : n ≠ 0) :
    Module.Basis (Fin (negacyclicPoly q n).natDegree) (ZMod q) (NegacyclicRing q n) :=
  (AdjoinRoot.powerBasis' (negacyclicPoly_monic q n hn)).basis

theorem negacyclicPoly_natDegree [Nontrivial (ZMod q)] :
    (negacyclicPoly q n).natDegree = n := natDegree_X_pow_add_C

/-- **Module-LWE over `R_q` is LWE over `Z_q`.** For rank `d` (`ι = Fin d`), the
coefficient vector of `⟪a, s⟫ + e` is `A *ᵥ s' + e'` with `A = flatMatrix`, `s'` the
`d·n` coefficients of `s` and `e'` those of `e`. -/
theorem mlwe_coeff_is_lwe (hn : n ≠ 0) {d : ℕ} (s a : Fin d → NegacyclicRing q n)
    (e : NegacyclicRing q n) :
    (fun j => (negacyclicBasis q n hn).repr (sample s a e).2 j)
      = flatMatrix (negacyclicBasis q n hn) a *ᵥ flatVec (negacyclicBasis q n hn) s
        + (fun j => (negacyclicBasis q n hn).repr e j) :=
  repr_sample _ s a e

end CryptoLean.Lattice
