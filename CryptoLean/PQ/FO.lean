import Mathlib.Logic.Equiv.Fintype
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import CryptoLean.PQ.Games

/-!
# The Fujisaki–Okamoto transform of ML-KEM: correctness and failure in the ROM

ML-KEM turns K-PKE into a KEM with the FO transform with implicit rejection
(Hofheinz–Hövelmanns–Kiltz 2017, `FO^⊥̸`, in the "`m ‖ H(ek)`" variant). FIPS 203:

* `ML-KEM.Encaps_internal(ek, m)` (Alg. 17): `(K, r) ← G(m ‖ H(ek))`,
  `c ← K-PKE.Encrypt(ek, m, r)`, return `(K, c)`;
* `ML-KEM.Decaps_internal(dk, c)` (Alg. 18): `m' ← K-PKE.Decrypt(dk_PKE, c)`,
  `(K', r') ← G(m' ‖ h)`, `K̄ ← J(z ‖ c)`, `c' ← K-PKE.Encrypt(ek, m', r')`;
  return `K'` if `c = c'` and `K̄` otherwise.

Everything here is generic in the underlying deterministic PKE (`DetPKE`).

## What is proved

* `decaps_encaps`: if K-PKE decrypts the honest ciphertext to `m`, decapsulation returns
  the encapsulated key. (Re-encryption then reproduces `c` exactly, because the coins are
  derived from `m` and `H(ek)`.)
* `kemFail_imp_pkeFail`: every KEM failure is a K-PKE decryption failure at the derived
  coins.
* `kemFail_le_pkeFail_rom` (**δ-correctness transfer in the ROM**): if `G` is a uniformly
  random function (random oracle) and `m` is uniform, the KEM fails with probability at
  most the probability that K-PKE fails on uniform `(m, r)`. So ML-KEM's failure
  probability is bounded by K-PKE's δ (FIPS 203 §1: 2⁻¹³⁹, 2⁻¹⁶⁴, 2⁻¹⁷⁴; recomputed in
  `docs/pq-kem-20261125/failure_prob.py`).

## Not proved here

IND-CCA security of the FO transform (HHK17 Thm 3.2/3.4 in the ROM; Bindel et al. 2019,
Don–Fehr–Majenz–Schaffner 2022 in the QROM) needs oracle adversaries and query counting.
That is the next layer; it is listed as open in `docs/pq-kem-20261125/README.md`.
-/

set_option autoImplicit false

namespace CryptoLean.PQ

/-- A deterministic public-key encryption scheme with explicit coins. -/
structure DetPKE (PK SK M Coin Ct : Type*) where
  enc : PK → M → Coin → Ct
  dec : SK → Ct → M

variable {PK SK M Coin Ct K Hs Z : Type*}

/-- `ML-KEM.Encaps_internal`: returns `(K, c)`. `G` is the hash `G(m ‖ h)` and `H` the
hash of the encapsulation key. -/
def encaps (P : DetPKE PK SK M Coin Ct) (G : M → Hs → K × Coin) (H : PK → Hs) (ek : PK)
    (m : M) : K × Ct :=
  ((G m (H ek)).1, P.enc ek m (G m (H ek)).2)

/-- `ML-KEM.Decaps_internal`, with implicit rejection key `J(z ‖ c)`. The decapsulation key
holds `dk_PKE`, `ek`, `h = H(ek)` and `z`. -/
def decaps [DecidableEq Ct] (P : DetPKE PK SK M Coin Ct) (G : M → Hs → K × Coin)
    (J : Z → Ct → K) (dk : SK) (ek : PK) (h : Hs) (z : Z) (c : Ct) : K :=
  if P.enc ek (P.dec dk c) (G (P.dec dk c) h).2 = c then (G (P.dec dk c) h).1 else J z c

variable [DecidableEq Ct] (P : DetPKE PK SK M Coin Ct)

/-- **Correctness of the FO transform.** If the PKE decrypts the honest ciphertext, the
KEM returns the encapsulated key. -/
theorem decaps_encaps (G : M → Hs → K × Coin) (H : PK → Hs) (J : Z → Ct → K) (dk : SK)
    (ek : PK) (z : Z) (m : M) (hdec : P.dec dk (P.enc ek m (G m (H ek)).2) = m) :
    decaps P G J dk ek (H ek) z (encaps P G H ek m).2 = (encaps P G H ek m).1 := by
  simp only [encaps, decaps, hdec, ite_true]

/-- Every KEM failure is a PKE decryption failure at the coins `G(m ‖ H(ek)).2`. -/
theorem kemFail_imp_pkeFail (G : M → Hs → K × Coin) (H : PK → Hs) (J : Z → Ct → K)
    (dk : SK) (ek : PK) (z : Z) (m : M)
    (hfail : decaps P G J dk ek (H ek) z (encaps P G H ek m).2 ≠ (encaps P G H ek m).1) :
    P.dec dk (P.enc ek m (G m (H ek)).2) ≠ m :=
  fun h => hfail (decaps_encaps P G H J dk ek z m h)

section ROM

variable {α β V : Type*} [Fintype α] [Fintype β] [Fintype V]

/-- Probability over a product, as the average over the first coordinate. -/
theorem pr_prod (f : α × β → Bool) :
    pr f = (∑ a, pr fun b => f (a, b)) / Fintype.card α := by
  unfold pr
  rw [Fintype.sum_prod_type, Fintype.card_prod, ← Finset.sum_div, div_div, Nat.cast_mul,
    mul_comm (Fintype.card β : ℚ)]

/-- An event of the first coordinate only. -/
theorem pr_fst [Nonempty β] (g : α → Bool) : pr (fun x : α × β => g x.1) = pr g := by
  unfold pr
  have hb : (Fintype.card β : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hs : (∑ x : α × β, if g x.1 = true then (1 : ℚ) else 0)
      = (Fintype.card β : ℚ) * ∑ a, if g a = true then (1 : ℚ) else 0 := by
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by by_cases hg : g a = true <;> simp [hg]
  rw [hs, Fintype.card_prod, Nat.cast_mul, mul_comm (Fintype.card α : ℚ),
    mul_div_mul_left _ _ hb]

/-- **Random-oracle evaluation.** For a uniformly random function `F : α → V`, the value
`F a` at a fixed point is uniform. -/
theorem pr_eval [DecidableEq α] [Nonempty V] (a : α) (g : V → Bool) :
    pr (fun F : α → V => g (F a)) = pr g := by
  have : Nonempty ({j // j ≠ a} → V) := ⟨fun _ => Classical.arbitrary V⟩
  rw [pr_eq_of_equiv (Equiv.piSplitAt a (fun _ => V)) (fun F : α → V => g (F a))
    (fun x => g x.1) (fun F => rfl)]
  exact pr_fst g

variable [Fintype M] [DecidableEq M] [Fintype K] [Fintype Coin] [Nonempty K] [Nonempty Coin]
  [DecidableEq K]

/-- **δ-correctness transfer in the ROM.** With `G` a uniformly random function of `m`
(the random oracle `G(· ‖ h)` for the fixed `h = H(ek)`) and `m` uniform, the probability
that ML-KEM decapsulation disagrees with encapsulation is at most the probability that
K-PKE fails to decrypt `Enc(ek, m; r)` for uniform `(m, r)`. -/
theorem kemFail_le_pkeFail_rom (J : Z → Ct → K) (dk : SK) (ek : PK) (h : Hs) (z : Z) :
    pr (fun x : (M → K × Coin) × M =>
        decide (decaps P (fun m _ => x.1 m) J dk ek h z
            (encaps P (fun m _ => x.1 m) (fun _ => h) ek x.2).2
          ≠ (encaps P (fun m _ => x.1 m) (fun _ => h) ek x.2).1))
      ≤ pr (fun y : M × Coin => decide (P.dec dk (P.enc ek y.1 y.2) ≠ y.1)) := by
  -- Step 1: KEM failure implies PKE failure at the oracle's coins.
  refine (pr_mono _ (fun x : (M → K × Coin) × M =>
      decide (P.dec dk (P.enc ek x.2 (x.1 x.2).2) ≠ x.2)) ?_).trans (le_of_eq ?_)
  · intro x hx
    simp only [decide_eq_true_eq] at hx ⊢
    exact kemFail_imp_pkeFail P (fun m _ => x.1 m) (fun _ => h) J dk ek z x.2 hx
  -- Step 2: the oracle's coins at `m` are uniform and independent of `m`.
  rw [← pr_equiv (Equiv.prodComm M (M → K × Coin)), pr_prod, pr_prod]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  have h1 := pr_eval m (fun v : K × Coin => decide (P.dec dk (P.enc ek m v.2) ≠ m))
  have h2 : pr (fun v : K × Coin => decide (P.dec dk (P.enc ek m v.2) ≠ m))
      = pr (fun r : Coin => decide (P.dec dk (P.enc ek m r) ≠ m)) := by
    rw [← pr_equiv (Equiv.prodComm Coin K)]
    exact pr_fst (fun r : Coin => decide (P.dec dk (P.enc ek m r) ≠ m))
  exact h1.trans h2

end ROM

end CryptoLean.PQ
