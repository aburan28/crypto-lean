import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Rat.Defs
import CryptoLean.Quaternion.ReducedNorm

/-!
# The maximal order `O₀ ≅ End(E₀)` of `B_{p,∞}` for `p ≡ 3 (mod 4)`

SQIsign (all versions) starts from `E₀ : y² = x³ + x` over `F_{p²}` with `p ≡ 3 (mod 4)`,
whose endomorphism ring is the maximal order
`O₀ = ℤ⟨1, i, (i + j)/2, (1 + k)/2⟩ ⊂ B_{p,∞} = (-1, -p | ℚ)`, with `i ↦ ι`
(`(x, y) ↦ (-x, √-1·y)`) and `j ↦ π` (Frobenius). Write `p = 4m + 3`.

Instance obligations proved here (the quaternion side of the Deuring dictionary):

* `o0_mul`: the explicit structure constants; with `o0_add`, `o0_neg`, `o0_one` this makes
  `O₀` a subring (`O0`) — the place where `p ≡ 3 (mod 4)` is used (`((i+j)/2)² = -(m+1)`);
* `nrd_o0`: the norm form `nrd(a + b i + c (i+j)/2 + d (1+k)/2) = a² + ad + b² + bc + (m+1)(c² + d²)`,
  integral and positive definite — degrees of isogenies from `E₀`;
* `i_mem`, `j_mem`, `k_mem`: `ℤ⟨i, j⟩ ⊂ O₀`;
* `gram_det`: the reduced-trace Gram determinant of the basis is `-(4m+3)² = -p²`, so
  `disc(O₀) = p = disc(B_{p,∞})`. Maximality then follows from the classical theorem that an
  order whose discriminant equals that of the algebra is maximal (Voight, *Quaternion
  Algebras*, Thm 15.5.5); that theorem is **not** formalized here.
-/

set_option autoImplicit false

open scoped Quaternion

namespace CryptoLean.Deuring

/-- `B_{p,∞} = (-1, -p | ℚ)` with `p = 4m + 3`: `i² = -1`, `j² = -p`, `k = ij`. -/
abbrev Bp (m : ℕ) := ℍ[ℚ, -1, 0, -(4 * (m : ℚ) + 3)]

/-- The element `a + b·i + c·(i+j)/2 + d·(1+k)/2` of `B_{p,∞}`. -/
def o0 (m : ℕ) (a b c d : ℤ) : Bp m :=
  ⟨a + d / 2, b + c / 2, c / 2, d / 2⟩

theorem o0_add (m : ℕ) (a b c d a' b' c' d' : ℤ) :
    o0 m a b c d + o0 m a' b' c' d' = o0 m (a + a') (b + b') (c + c') (d + d') := by
  ext <;> simp [o0] <;> ring

theorem o0_neg (m : ℕ) (a b c d : ℤ) : -o0 m a b c d = o0 m (-a) (-b) (-c) (-d) := by
  ext <;> simp [o0] <;> ring

theorem o0_one (m : ℕ) : (1 : Bp m) = o0 m 1 0 0 0 := by
  ext <;> simp [o0]

/-- Structure constants of `O₀` (computed symbolically, checked here by `ring`). -/
theorem o0_mul (m : ℕ) (a b c d a' b' c' d' : ℤ) :
    o0 m a b c d * o0 m a' b' c' d' =
      o0 m (a * a' - b * b' - b * c' - (m + 1) * (c * c' + d * d'))
        (a * b' + a' * b + b * d' + (m + 1) * (c * d' - c' * d))
        (a * c' + a' * c - b * d' + b' * d + c' * d)
        (a * d' + a' * d + b * c' - b' * c + d * d') := by
  ext <;> simp [o0] <;> ring

/-- `O₀` as a subring of `B_{p,∞}`. -/
def O0 (m : ℕ) : Subring (Bp m) where
  carrier := {x | ∃ a b c d : ℤ, x = o0 m a b c d}
  mul_mem' := by
    rintro _ _ ⟨a, b, c, d, rfl⟩ ⟨a', b', c', d', rfl⟩
    exact ⟨_, _, _, _, o0_mul m a b c d a' b' c' d'⟩
  one_mem' := ⟨1, 0, 0, 0, o0_one m⟩
  add_mem' := by
    rintro _ _ ⟨a, b, c, d, rfl⟩ ⟨a', b', c', d', rfl⟩
    exact ⟨_, _, _, _, o0_add m a b c d a' b' c' d'⟩
  zero_mem' := ⟨0, 0, 0, 0, by ext <;> simp [o0]⟩
  neg_mem' := by
    rintro _ ⟨a, b, c, d, rfl⟩
    exact ⟨_, _, _, _, o0_neg m a b c d⟩

/-- **Norm form of `O₀`.** -/
theorem nrd_o0 (m : ℕ) (a b c d : ℤ) :
    nrd (o0 m a b c d) =
      ((a ^ 2 + a * d + b ^ 2 + b * c + (m + 1) * (c ^ 2 + d ^ 2) : ℤ) : ℚ) := by
  rw [nrd_eq]
  simp [o0]
  ring

/-- Every element of `O₀` has integral reduced norm. -/
theorem nrd_integral (m : ℕ) {x : Bp m} (hx : x ∈ O0 m) : ∃ n : ℤ, nrd x = n := by
  obtain ⟨a, b, c, d, rfl⟩ := hx
  exact ⟨_, nrd_o0 m a b c d⟩

/-- The norm form is positive definite: it is `(a + d/2)² + (b + c/2)² + p (c² + d²)/4`. -/
theorem nrd_o0_pos (m : ℕ) (a b c d : ℤ) (h : (a, b, c, d) ≠ (0, 0, 0, 0)) :
    0 < a ^ 2 + a * d + b ^ 2 + b * c + (m + 1) * (c ^ 2 + d ^ 2) := by
  by_contra hle
  rw [not_lt] at hle
  have hm : (0 : ℤ) < 4 * m + 3 := by positivity
  have h1 : (4 * (m : ℤ) + 3) * (c ^ 2 + d ^ 2) ≤ 0 := by
    nlinarith [sq_nonneg (2 * a + d), sq_nonneg (2 * b + c)]
  have h2 : c ^ 2 + d ^ 2 ≤ 0 := by
    by_contra h3
    rw [not_le] at h3
    exact absurd h1 (not_le.2 (mul_pos hm h3))
  have hc : c = 0 := pow_eq_zero_iff two_ne_zero |>.1 (by nlinarith [sq_nonneg c, sq_nonneg d])
  have hd : d = 0 := pow_eq_zero_iff two_ne_zero |>.1 (by nlinarith [sq_nonneg c, sq_nonneg d])
  subst hc
  subst hd
  have ha : a = 0 := pow_eq_zero_iff two_ne_zero |>.1 (by nlinarith [sq_nonneg a, sq_nonneg b])
  have hb : b = 0 := pow_eq_zero_iff two_ne_zero |>.1 (by nlinarith [sq_nonneg a, sq_nonneg b])
  exact h (by simp [ha, hb])

theorem i_mem (m : ℕ) : (⟨0, 1, 0, 0⟩ : Bp m) = o0 m 0 1 0 0 := by
  ext <;> simp [o0]

theorem j_mem (m : ℕ) : (⟨0, 0, 1, 0⟩ : Bp m) = o0 m 0 (-1) 2 0 := by
  ext <;> simp [o0]

theorem k_mem (m : ℕ) : (⟨0, 0, 0, 1⟩ : Bp m) = o0 m (-1) 0 0 2 := by
  ext <;> simp [o0]

/-- `i² = -1`, `j² = -p`, `ij = k = -ji` in `B_{p,∞}`. -/
theorem relations (m : ℕ) :
    (⟨0, 1, 0, 0⟩ : Bp m) * ⟨0, 1, 0, 0⟩ = -1 ∧
    (⟨0, 0, 1, 0⟩ : Bp m) * ⟨0, 0, 1, 0⟩ = ⟨-(4 * m + 3), 0, 0, 0⟩ ∧
    (⟨0, 1, 0, 0⟩ : Bp m) * ⟨0, 0, 1, 0⟩ = ⟨0, 0, 0, 1⟩ ∧
    (⟨0, 0, 1, 0⟩ : Bp m) * ⟨0, 1, 0, 0⟩ = ⟨0, 0, 0, -1⟩ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext <;> simp

/-- The basis `1, i, (i+j)/2, (1+k)/2` of `O₀`. -/
def basisO0 (m : ℕ) : Fin 4 → Bp m :=
  ![o0 m 1 0 0 0, o0 m 0 1 0 0, o0 m 0 0 1 0, o0 m 0 0 0 1]

/-- The reduced-trace Gram matrix `trd(eᵢ eⱼ) = 2 re(eᵢ eⱼ)` of the basis. -/
theorem gram_eq (m : ℕ) :
    (Matrix.of fun i j => 2 * ((basisO0 m i) * (basisO0 m j)).re) =
      (!![2, 0, 0, 1; 0, -2, -1, 0; 0, -1, -2 * (m : ℚ) - 2, 0; 1, 0, 0, -2 * (m : ℚ) - 1] :
        Matrix (Fin 4) (Fin 4) ℚ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [basisO0, o0] <;> ring

/-- **Discriminant.** `det(trd(eᵢ eⱼ)) = -p²`, i.e. `disc(O₀) = p`. -/
theorem gram_det (m : ℕ) :
    (Matrix.of fun i j => 2 * ((basisO0 m i) * (basisO0 m j)).re).det
      = -((4 * m + 3 : ℚ) ^ 2) := by
  rw [gram_eq, Matrix.det_succ_row_zero]
  simp +decide [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Fin.succAbove]
  ring

end CryptoLean.Deuring
