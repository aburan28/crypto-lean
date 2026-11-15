import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Logic.Equiv.Set
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

/-! Exact bounded interpolation states over existing polynomial semantics.

Consumer: crypto PR4338 candidate A. Prospective statement/inheritance plan
1d7dc7c and inherited-law/actual-coordinate probe 0e381fb precede this file.
Different clean selected supports have different bounded evaluation kernels
while their size is at most the u-degree cap. This is an exact-state
enumeration statement, not a lower bound for symbolic unions or all selectors.
-/
set_option autoImplicit false

namespace CryptoLean.InterpolationKernels
open Polynomial

variable {F I : Type*} [Field F]

/-- The actual set of degree-bounded pairs satisfying the selected evaluations. -/
def kernel (x y : I → F) (dU dV : ℕ) (s : Finset I) : Set (F[X] × F[X]) :=
  {uv | uv.1.natDegree ≤ dU ∧ uv.2.natDegree ≤ dV ∧
    ∀ i ∈ s, uv.1.eval (x i) + y i * uv.2.eval (x i) = 0}

/-- The single membership interface that opens the bounded-kernel predicate. -/
theorem mem_kernel (x y : I → F) (dU dV : ℕ) (s : Finset I) (u v : F[X]) :
    (u, v) ∈ kernel x y dU dV s ↔
      u.natDegree ≤ dU ∧ v.natDegree ≤ dV ∧
        ∀ i ∈ s, u.eval (x i) + y i * v.eval (x i) = 0 := Iff.rfl

/-- Inherited nodal evaluation detects exactly the selected clean records. -/
theorem nodal_eval_zero_iff (x : I → F) (hx : Function.Injective x)
    (s : Finset I) (j : I) :
    (Lagrange.nodal s x).eval (x j) = 0 ↔ j ∈ s := by
  classical
  constructor
  · intro hz
    by_contra hj
    apply (Lagrange.eval_nodal_not_at_node (s := s) (v := x) ?_) hz
    intro i hi h
    exact hj ((hx h).symm ▸ hi)
  · exact Lagrange.eval_nodal_at_node

/-- The inherited nodal pair belongs to another kernel exactly when that
kernel's selected support is contained in its zero set. -/
theorem nodal_pair_mem_iff (x y : I → F) (hx : Function.Injective x)
    (dU dV : ℕ) (s t : Finset I) (hs : s.card ≤ dU) :
    (Lagrange.nodal s x, (0 : F[X])) ∈ kernel x y dU dV t ↔ t ⊆ s := by
  rw [mem_kernel]
  constructor
  · intro h j hj
    apply (nodal_eval_zero_iff x hx s j).mp
    simpa only [Polynomial.eval_zero, mul_zero, add_zero] using h.2.2 j hj
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · simpa only [Lagrange.natDegree_nodal] using hs
    · simp
    · intro j hj
      simpa only [Polynomial.eval_zero, mul_zero, add_zero] using
        Lagrange.eval_nodal_at_node (v := x) (h hj)

/-- A nonzero feasible pair exists for every support within the u-degree cap. -/
theorem nodal_witness (x y : I → F) (hx : Function.Injective x)
    (dU dV : ℕ) (s : Finset I) (hs : s.card ≤ dU) :
    (Lagrange.nodal s x, (0 : F[X])) ∈ kernel x y dU dV s ∧
      (Lagrange.nodal s x, (0 : F[X])) ≠ 0 := by
  constructor
  · exact (nodal_pair_mem_iff x y hx dU dV s s hs).mpr (Finset.Subset.refl s)
  · intro h
    have hz : Lagrange.nodal s x = 0 := congrArg Prod.fst h
    exact Lagrange.nodal_ne_zero hz

/-- Equality of bounded kernels recovers their clean selected supports. -/
theorem supports_eq_of_kernels_eq (x y : I → F) (hx : Function.Injective x)
    (dU dV : ℕ) (s t : Finset I) (hs : s.card ≤ dU) (ht : t.card ≤ dU)
    (h : kernel x y dU dV s = kernel x y dU dV t) : s = t := by
  have hts : t ⊆ s := (nodal_pair_mem_iff x y hx dU dV s t hs).mp (by
    rw [← h]
    exact (nodal_witness x y hx dU dV s hs).1)
  have hst : s ⊆ t := (nodal_pair_mem_iff x y hx dU dV t s ht).mp (by
    rw [h]
    exact (nodal_witness x y hx dU dV t ht).1)
  exact Finset.Subset.antisymm hst hts

/-- One actual primitive record is selected from every prefix color. -/
def prefixSupport {t b : ℕ} (choice : Fin t → Fin b) : Finset (Fin t × Fin b) :=
  Finset.univ.image fun i => (i, choice i)

/-- The interface exposing the selected-support construction. -/
theorem prefixSupport_eq_image {t b : ℕ} (choice : Fin t → Fin b) :
    prefixSupport choice = Finset.univ.image (fun i => (i, choice i)) := rfl

theorem mem_prefixSupport {t b : ℕ} (choice : Fin t → Fin b) (i : Fin t) (j : Fin b) :
    (i, j) ∈ prefixSupport choice ↔ j = choice i := by
  rw [prefixSupport_eq_image]
  constructor
  · intro h
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp h
    have hai : a = i := congrArg Prod.fst ha
    subst a
    exact (congrArg Prod.snd ha).symm
  · intro h
    subst j
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

theorem prefixSupport_card {t b : ℕ} (choice : Fin t → Fin b) :
    (prefixSupport choice).card = t := by
  rw [prefixSupport_eq_image, Finset.card_image_of_injective]
  · simp
  · intro i j h
    exact congrArg Prod.fst h

theorem prefixSupport_injective {t b : ℕ} :
    Function.Injective (prefixSupport (t := t) (b := b)) := by
  intro a b h
  funext i
  have ha : (i, a i) ∈ prefixSupport a := (mem_prefixSupport a i (a i)).mpr rfl
  have hb : (i, a i) ∈ prefixSupport b := h ▸ ha
  exact (mem_prefixSupport b i (a i)).mp hb

/-- Exact kernel memoization cannot identify distinct colored prefixes in
this range of the genuine polynomial degree bounds. -/
theorem prefix_kernel_injective {t b : ℕ} (x y : Fin t × Fin b → F)
    (hx : Function.Injective x) (dU dV : ℕ) (ht : t ≤ dU) :
    Function.Injective (fun choice : Fin t → Fin b =>
      kernel x y dU dV (prefixSupport choice)) := by
  intro a b h
  apply prefixSupport_injective
  apply supports_eq_of_kernels_eq x y hx dU dV _ _ ?_ ?_ h
  · simpa only [prefixSupport_card] using ht
  · simpa only [prefixSupport_card] using ht

/-- Finite count of actual distinct bounded-kernel sets, including empty
prefixes and empty choice domains. No surrogate state-count function. -/
theorem prefix_kernel_count {t b : ℕ} (x y : Fin t × Fin b → F)
    (hx : Function.Injective x) (dU dV : ℕ) (ht : t ≤ dU) :
    Nat.card (Set.range (fun choice : Fin t → Fin b =>
      kernel x y dU dV (prefixSupport choice))) = b ^ t := by
  classical
  calc
    Nat.card (Set.range (fun choice : Fin t → Fin b =>
        kernel x y dU dV (prefixSupport choice))) = Nat.card (Fin t → Fin b) :=
      Nat.card_congr (Equiv.ofInjective _ (prefix_kernel_injective x y hx dU dV ht)).symm
    _ = b ^ t := by simp [Nat.card_eq_fintype_card]

end CryptoLean.InterpolationKernels
