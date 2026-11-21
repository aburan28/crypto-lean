import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.BigOperators.Fin

/-!
# Module-LWE samples, and LWE / Ring-LWE as instances

One object covers the three problems. Over a commutative ring `R` (the ring `R_q`)
and a finite index type `ι` (the module rank), a sample for a secret `s : ι → R`
is the pair `(a, ⟪a, s⟫ + e)`. Then:

* **LWE** (Regev 2005) is the instance `R = ZMod q`, `ι = Fin n`;
* **Ring-LWE** (Lyubashevsky–Peikert–Regev 2010, polynomial form) is
  `R = (ZMod q)[X] ⧸ (f)`, `ι = Fin 1` (`sample_fin_one`);
* **Module-LWE** (Brakerski–Gentry–Vaikuntanathan 2012; Langlois–Stehlé 2015) is
  `R = (ZMod q)[X] ⧸ (f)`, `ι = Fin d` (ML-KEM: `f = X^256 + 1`, `q = 3329`,
  `d ∈ {2,3,4}`).

This file states only the **algebra** of samples. It makes no hardness claim and
does not model distributions (see `UniformError.lean` for the one distributional
law). The laws here are the exact identities behind:

* random self-reducibility in the secret (`shift_sample`, Regev 2005 Lemma 4.1 style);
* sample combination in BKW and in the dual attack (`sample_add`, `sample_smul`,
  `sample_sum`);
* decryption of Regev / LPR / Kyber-PKE (`decrypt_identity`);
* "MLWE of rank `d` over a rank-`n` algebra is LWE in dimension `d·n`"
  (`repr_sample`, the coefficient-embedding flattening).

Every proof uses Mathlib's `dotProduct` / `mulVec` / `Algebra.leftMulMatrix` laws
as stated.
-/

set_option autoImplicit false

namespace CryptoLean.Lattice

open Matrix

section Sample

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]

/-- A (module-)LWE sample `(a, ⟪a, s⟫ + e)` for secret `s`, public vector `a` and
error `e`. -/
def sample (s a : ι → R) (e : R) : (ι → R) × R :=
  (a, a ⬝ᵥ s + e)

/-- The residual of a pair against a candidate secret `t`: `b - ⟪a, t⟫`. -/
def residual (t : ι → R) (p : (ι → R) × R) : R :=
  p.2 - p.1 ⬝ᵥ t

/-- With the right secret, the residual of a sample is its error. -/
@[simp] theorem residual_sample (s a : ι → R) (e : R) :
    residual s (sample s a e) = e := by
  simp [residual, sample]

/-- With a wrong secret `t`, the residual is the error plus `⟪a, s - t⟫`: a search
algorithm sees the secret only through this linear form. -/
theorem residual_sample_of_ne (s t a : ι → R) (e : R) :
    residual t (sample s a e) = e + a ⬝ᵥ (s - t) := by
  simp only [residual, sample, dotProduct_sub]
  ring

/-- The secret-shift map `(a, b) ↦ (a, b + ⟪a, t⟫)`. -/
def shift (t : ι → R) (p : (ι → R) × R) : (ι → R) × R :=
  (p.1, p.2 + p.1 ⬝ᵥ t)

/-- Random self-reducibility in the secret: shifting turns a sample for `s` into a
sample for `s + t` with the *same* public vector and error. With `t` uniform, a
worst-case secret becomes a uniform one. -/
theorem shift_sample (s t a : ι → R) (e : R) :
    shift t (sample s a e) = sample (s + t) a e := by
  simp only [shift, sample, dotProduct_add]
  ext <;> simp only
  ring

/-- Samples with one secret form an `R`-submodule of `(ι → R) × R`: the sum of two
samples is a sample with summed public vectors and errors (BKW, dual attacks). -/
theorem sample_add (s a₁ a₂ : ι → R) (e₁ e₂ : R) :
    sample s a₁ e₁ + sample s a₂ e₂ = sample s (a₁ + a₂) (e₁ + e₂) := by
  simp only [sample, Prod.mk_add_mk, add_dotProduct]
  ext <;> simp only
  ring

theorem sample_smul (s a : ι → R) (e r : R) :
    r • sample s a e = sample s (r • a) (r * e) := by
  simp only [sample, Prod.smul_mk, smul_dotProduct, smul_eq_mul]
  ext <;> simp only
  ring

theorem sample_neg (s a : ι → R) (e : R) :
    -sample s a e = sample s (-a) (-e) := by
  simp only [sample, Prod.neg_mk, neg_dotProduct]
  ext <;> simp only
  ring

/-- An `R`-linear combination of samples is a sample whose error is the same
combination of the errors. This is the identity every sample-combining attack
(BKW, coded-BKW, the dual attack) rests on: the error grows exactly as the
combination of the errors. -/
theorem sample_sum {κ : Type*} (S : Finset κ) (c : κ → R) (s : ι → R)
    (a : κ → ι → R) (e : κ → R) :
    ∑ k ∈ S, c k • sample s (a k) (e k) =
      sample s (∑ k ∈ S, c k • a k) (∑ k ∈ S, c k * e k) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [sample]; rfl
  | insert k S hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk, Finset.sum_insert hk, ih,
      sample_smul, sample_add]

/-- The sample map with `s` fixed is injective in `(a, e)`: a sample determines its
error once the secret is known. -/
theorem sample_injective (s : ι → R) :
    Function.Injective (fun p : (ι → R) × R => sample s p.1 p.2) := by
  rintro ⟨a, e⟩ ⟨a', e'⟩ h
  simp only [sample, Prod.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  simp only [add_left_cancel_iff] at h
  rw [h]

/-- **Uniform error hides the secret.** With `s` fixed, `(a, e) ↦ sample s a e` is a
bijection of `(ι → R) × R`. So if the error is uniform on a finite `R`, a sample is
uniform whatever the secret: decision-LWE with uniform error has advantage exactly
zero, and every hardness statement needs a *non-uniform* (short) error. -/
theorem sample_bijective (s : ι → R) :
    Function.Bijective (fun p : (ι → R) × R => sample s p.1 p.2) := by
  refine ⟨sample_injective s, fun q => ⟨(q.1, q.2 - q.1 ⬝ᵥ s), ?_⟩⟩
  simp [sample]

/-- Counting form: for every target `(a₀, b₀)` and every secret there is exactly one
`(a, e)` producing it. -/
theorem card_sample_preimage [Fintype R] [DecidableEq R] [DecidableEq ι] (s : ι → R)
    (q : (ι → R) × R) :
    (Finset.univ.filter fun p : (ι → R) × R => sample s p.1 p.2 = q).card = 1 := by
  rw [Finset.card_eq_one]
  obtain ⟨p, hp⟩ := (sample_bijective s).2 q
  refine ⟨p, Finset.ext fun p' => ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ⟨fun h => (sample_bijective s).1 (h.trans hp.symm), fun h => h ▸ hp⟩

end Sample

section Batch

variable {R : Type*} [CommRing R] {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- `m` samples at once, in matrix form `(A, A s + e)`. Row `k` is `sample s (A k) (e k)`. -/
def samples (s : ι → R) (A : Matrix κ ι R) (e : κ → R) : Matrix κ ι R × (κ → R) :=
  (A, A *ᵥ s + e)

omit [Fintype κ] in
theorem samples_row (s : ι → R) (A : Matrix κ ι R) (e : κ → R) (k : κ) :
    ((samples s A e).1 k, (samples s A e).2 k) = sample s (A k) (e k) := by
  simp [samples, sample, mulVec]

/-- **Decryption identity of Regev / LPR / Kyber-PKE.** With public key
`t = A s + e`, ciphertext `u = Aᵀ r + e₁`, `v = ⟪t, r⟫ + e₂ + μ`, the decryptor's
`v - ⟪u, s⟫` equals the message term `μ` plus the noise `⟪e, r⟫ - ⟪e₁, s⟫ + e₂`.
For LWE take `R = ZMod q`; for Ring- and Module-LWE take `R = R_q`. Correctness of
each scheme is this identity plus a bound on the noise (see `Rounding.lean`). -/
theorem decrypt_identity (A : Matrix κ ι R) (s : ι → R) (e r : κ → R) (e₁ : ι → R)
    (e₂ μ : R) :
    ((A *ᵥ s + e) ⬝ᵥ r + e₂ + μ) - (Aᵀ *ᵥ r + e₁) ⬝ᵥ s
      = μ + (e ⬝ᵥ r - e₁ ⬝ᵥ s + e₂) := by
  have h : (A *ᵥ s) ⬝ᵥ r = (Aᵀ *ᵥ r) ⬝ᵥ s := by
    rw [dotProduct_comm, dotProduct_comm (Aᵀ *ᵥ r), dotProduct_transpose_mulVec]
  rw [add_dotProduct, add_dotProduct, h]
  ring

end Batch

section Instances

/-- Ring-LWE is the rank-one case: the inner product over `Fin 1` is one ring
product. -/
theorem sample_fin_one {R : Type*} [CommRing R] (s a : Fin 1 → R) (e : R) :
    sample s a e = (a, a 0 * s 0 + e) := by
  simp [sample, dotProduct]

end Instances

section Flatten

/-! ### Module-LWE over a free `K`-algebra is LWE over `K`

Let `S` be a `K`-algebra with a finite basis `b : Basis β K S` (for Ring- and Module-LWE:
`K = ZMod q`, `S = K[X] ⧸ (f)` with its power basis, `β = Fin (deg f)`). Taking
coordinates, a module sample of rank `ι` over `S` is `|β|` LWE samples over `K`
in dimension `ι × β`, with the public matrix built from the multiplication
matrices `Algebra.leftMulMatrix b (a i)` and the error the coordinate vector of
`e`. This is the "coefficient embedding" every lattice attack on Ring- and Module-LWE
starts from. -/

variable {K S : Type*} [CommRing K] [CommRing S] [Algebra K S]
  {ι β : Type*} [Fintype ι] [Fintype β] [DecidableEq β]

/-- The `β × (ι × β)` public matrix of the flattened instance. -/
noncomputable def flatMatrix (b : Module.Basis β K S) (a : ι → S) : Matrix β (ι × β) K :=
  fun j ik => Algebra.leftMulMatrix b (a ik.1) j ik.2

/-- Coordinates of a module secret, as one vector over `ι × β`. -/
noncomputable def flatVec (b : Module.Basis β K S) (s : ι → S) : ι × β → K :=
  fun ik => b.repr (s ik.1) ik.2

/-- **Flattening.** The coordinates of `⟪a, s⟫ + e` are `flatMatrix b a *ᵥ flatVec b s`
plus the coordinates of `e`: a module-LWE sample over `S` of rank `|ι|` is exactly
`|β|` LWE samples over `K` in dimension `|ι|·|β|` with the same secret
coordinates. Uses `Algebra.leftMulMatrix_mulVec_repr` as stated. -/
theorem repr_sample (b : Module.Basis β K S) (s a : ι → S) (e : S) :
    (fun j => b.repr (sample s a e).2 j)
      = flatMatrix b a *ᵥ flatVec b s + (fun j => b.repr e j) := by
  funext j
  simp only [sample, map_add, Finsupp.add_apply, Pi.add_apply, add_left_inj]
  rw [dotProduct, map_sum, Finsupp.finsetSum_apply]
  simp only [mulVec, dotProduct, flatMatrix, flatVec, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Algebra.leftMulMatrix_mulVec_repr b (a i) (s i)]
  rfl

end Flatten

end CryptoLean.Lattice
