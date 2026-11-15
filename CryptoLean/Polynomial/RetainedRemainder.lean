import CryptoLean.Polynomial.NormCharts
import Mathlib.Algebra.Ring.GeomSum

/-! Divisibility from an actual retained powering circuit and its norm endpoint. -/
namespace CryptoLean.Polynomial
open _root_.Polynomial

/-- Repeated retained squaring is congruent to the corresponding power.
The transition equations, rather than the desired divisibility, are inputs. -/
theorem retained_power_congruence {R : Type*} [CommRing R]
    (x u : R) (v q : ℕ → R) (n : ℕ) (h0 : v 0=x)
    (hstep : ∀ j<n, (v j)^2=q j*u+v (j+1)) : u ∣ x^(2^n)-v n := by
  have aux : ∀ k≤n, u ∣ x^(2^k)-v k := by
    intro k
    induction k with
    | zero =>
      intro _
      simpa only [pow_zero,pow_one,h0,sub_self] using (dvd_zero u)
    | succ k ih =>
      intro hk
      have hp := (ih (Nat.le_trans (Nat.le_succ k) hk)).trans
        (sub_dvd_pow_sub_pow (x^(2^k)) (v k) 2)
      have ht : u ∣ (v k)^2-v (k+1) := by
        rw [hstep k (Nat.lt_of_succ_le hk),add_sub_cancel_right]
        exact dvd_mul_left u (q k)
      simpa only [sub_add_sub_cancel,Nat.pow_succ,pow_mul] using dvd_add hp ht
  exact aux n le_rfl

/-- A genuine target chart on a quadratic norm gives exact monic linear
quotient reconstruction, without dividing by an unknown field coordinate. -/
theorem target_norm_division {K : Type*} [Field K] {A B f : K[X]} {r s : K}
    (hpoint : s^2=f.eval r) (htarget : A.eval r=s*B.eval r) :
    (X-C r)*((A^2-f*B^2) /ₘ (X-C r)) = A^2-f*B^2 := by
  apply mul_divByMonic_eq_iff_isRoot.mpr
  change (A^2-f*B^2).eval r=0
  rw [eval_sub,eval_pow,eval_mul,eval_pow,htarget,mul_pow,hpoint,sub_self]

/-- The retained Kummer circuit itself discharges membership for the shared
norm-chart theorem. Squarefreeness and coprimality are conclusions. -/
theorem retained_kummer_charts {K : Type*} [Field K]
    {A B f U : K[X]} {c r : K} (v q : ℕ → K[X]) (n : ℕ)
    (htwo : (2 : K) ≠ 0) (hc : c ≠ 0) (h0 : v 0=X)
    (hstep : ∀ j<n, (v j)^2=q j*U+v (j+1)) (hterminal : v n=C c)
    (hr : U.eval r ≠ 0) (hnorm : A^2-f*B^2=(X-C r)*U) :
    U.Separable ∧ IsCoprime U (derivative U) ∧ IsCoprime U B := by
  have hd : ((2^n : ℕ) : K) ≠ 0 := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using pow_ne_zero n htwo
  have hm := retained_power_congruence (X : K[X]) U v q n h0 hstep
  rw [hterminal] at hm
  exact kummer_norm_charts hd hc hm hr hnorm

end CryptoLean.Polynomial
