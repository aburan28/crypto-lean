import Mathlib

/-!
# Large-prime relation graphs: what a graph dependency certifies

Formal versions of the derived (`[pcc:unverified]`) claims of the catalog
"Graph algorithms and asymptotic costs for ECDLP index calculus"
(isogeny-labs/crypto PR #4917, 2026-11-22), sections 2, 5 and 6.

Relations are rows of a matrix `A_L` over a field `K` (in the application
`K = 𝔽_ℓ`, `ℓ` the prime subgroup order). A row combination `y` eliminates
all large primes exactly when `y ᵥ* A_L = 0`, so every statement here is
about the left kernel `{y | y ᵥ* A = 0}`.

* `vecMul_eq_zero_iff_peel` — singleton peeling: deleting the row that holds
  the only nonzero of some column preserves the left kernel (catalog §5).
* `triangle_det`, `triangle_vecMul_eq_zero` — a one-cycle support with no
  cancellation in odd characteristic, but with one in characteristic two
  (catalog §5: topology cannot replace coefficient algebra).
* `bridge_dependency`, `bridge_essential` — two triangles joined by a bridge:
  a left-kernel vector with coefficient `2` on the bridge, and deleting the
  bridge leaves only the zero combination (catalog §5, handcuff).
* `exists_perm_support_of_det_ne_zero`, `allOnes_rank` — a nonzero
  determinant forces a perfect matching of the support, while a perfect
  matching does not force full rank (catalog §5: structural rank is an upper
  bound).
* `span_edgeDiff_eq_sumZero`, `IsTree.linearIndependent_edgeDiff` — the edge
  differences of a spanning tree on `k` normalized rows form a basis of the
  `(k-1)`-dimensional space of coefficient vectors summing to zero
  (catalog §2: why an MST is relevant).

Not formalized here (upstream candidate): the frame-matroid rank formula
`rank A_L = v - #unflagged components` for rows with at most two nonzeros
(catalog §6, gain-aware DSU). Mathlib has no gain-graph / frame-matroid layer.
-/

namespace CryptoLean.Combinatorics.LargePrimeGraph

open Matrix

variable {K : Type*} [Field K]

/-! ## Singleton peeling -/

section Peeling

variable {ι κ : Type*} [Fintype ι]

/-- If column `c` has its only nonzero entry in row `i`, every left-kernel
vector vanishes at `i`. -/
theorem apply_eq_zero_of_singleton_column (A : Matrix ι κ K) {y : ι → K}
    (hy : y ᵥ* A = 0) {i : ι} {c : κ} (hic : A i c ≠ 0)
    (hc : ∀ j, j ≠ i → A j c = 0) : y i = 0 := by
  have h := congrFun hy c
  simp only [vecMul, dotProduct, Pi.zero_apply] at h
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [hc j hj, mul_zero])
    (by simp)] at h
  exact (mul_eq_zero.mp h).resolve_right hic

/-- A vector vanishing at row `i` acts on `A` as its restriction acts on `A`
with row `i` deleted. -/
theorem vecMul_eq_vecMul_peel [DecidableEq ι] (A : Matrix ι κ K) {y : ι → K} (i : ι)
    (hy : y i = 0) :
    y ᵥ* A = (fun j : {j // j ≠ i} => y j) ᵥ* A.submatrix Subtype.val id := by
  funext c
  simp only [vecMul, dotProduct, submatrix_apply, id]
  rw [Fintype.sum_eq_add_sum_subtype_ne _ i, hy, zero_mul, zero_add]

/-- Singleton peeling preserves the left kernel: if column `c` has its only
nonzero in row `i`, then `y` kills `A` iff `y i = 0` and the restriction of
`y` kills `A` with row `i` deleted. -/
theorem vecMul_eq_zero_iff_peel [DecidableEq ι] (A : Matrix ι κ K) (y : ι → K) {i : ι} {c : κ}
    (hic : A i c ≠ 0) (hc : ∀ j, j ≠ i → A j c = 0) :
    y ᵥ* A = 0 ↔
      y i = 0 ∧ (fun j : {j // j ≠ i} => y j) ᵥ* A.submatrix Subtype.val id = 0 := by
  constructor
  · intro hy
    have hi := apply_eq_zero_of_singleton_column A hy hic hc
    exact ⟨hi, (vecMul_eq_vecMul_peel A i hi).symm.trans hy⟩
  · rintro ⟨hi, h⟩
    exact (vecMul_eq_vecMul_peel A i hi).trans h

end Peeling

/-! ## A triangle can have no cancellation -/

/-- Large-prime parts `x + y`, `y + z`, `z + x`. -/
def triangle : Matrix (Fin 3) (Fin 3) K := !![1, 1, 0; 0, 1, 1; 1, 0, 1]

theorem triangle_det : (triangle : Matrix (Fin 3) (Fin 3) K).det = 2 := by
  simp [triangle, det_fin_three]
  norm_num

/-- Over a field of characteristic other than two the triangle has trivial
left kernel: no row combination cancels its large primes. -/
theorem triangle_vecMul_eq_zero (h2 : (2 : K) ≠ 0) {y : Fin 3 → K}
    (hy : y ᵥ* triangle = 0) : y = 0 := by
  have hdet : (triangle : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := by
    rw [triangle_det]; exact h2
  exact eq_zero_of_vecMul_eq_zero hdet hy

theorem triangle_rank (h2 : (2 : K) ≠ 0) :
    (triangle : Matrix (Fin 3) (Fin 3) K).rank = 3 := by
  have : IsUnit (triangle : Matrix (Fin 3) (Fin 3) K) := by
    rw [isUnit_iff_isUnit_det, triangle_det]; exact h2.isUnit
  simpa using rank_of_isUnit _ this

/-- In characteristic two the all-ones combination is a dependency. -/
theorem triangle_dependency_char_two (h2 : (2 : K) = 0) :
    ![1, 1, 1] ᵥ* (triangle : Matrix (Fin 3) (Fin 3) K) = 0 := by
  funext j
  fin_cases j <;>
    simp [triangle, vecMul, dotProduct, Fin.sum_univ_three] <;>
    linear_combination h2

/-! ## A bridge can be essential -/

/-- Vertices `a b c` (`inl 0, 1, 2`) and `d e f` (`inr 0, 1, 2`); edges in the
catalog's order `ab, bc, ca, de, ef, fd, cd`; the last one is the bridge. -/
def bridgeEdge : Fin 7 → (Fin 3 ⊕ Fin 3) × (Fin 3 ⊕ Fin 3) :=
  ![(.inl 0, .inl 1), (.inl 1, .inl 2), (.inl 2, .inl 0),
    (.inr 0, .inr 1), (.inr 1, .inr 2), (.inr 2, .inr 0),
    (.inl 2, .inr 0)]

/-- Coefficient `+1` at both endpoints of every edge row. -/
def bridgeIncidence : Matrix (Fin 7) (Fin 3 ⊕ Fin 3) K := fun e v =>
  if v = (bridgeEdge e).1 ∨ v = (bridgeEdge e).2 then 1 else 0

/-- The catalog's coefficients `(1, -1, -1, -1, 1, -1, 2)`. -/
def bridgeCoeff : Fin 7 → K := ![1, -1, -1, -1, 1, -1, 2]

/-- The combination cancels every vertex, over every field. -/
theorem bridge_dependency : bridgeCoeff ᵥ* (bridgeIncidence : Matrix _ _ K) = 0 := by
  funext v
  rcases v with v | v <;> fin_cases v <;>
    simp [vecMul, dotProduct, Fin.sum_univ_succ, bridgeIncidence, bridgeEdge,
      bridgeCoeff] <;> norm_num

/-- The bridge carries coefficient `2`, nonzero in odd characteristic. -/
theorem bridgeCoeff_bridge : (bridgeCoeff : Fin 7 → K) 6 = 2 := rfl

/-- Deleting the bridge destroys every dependency (characteristic not two). -/
theorem bridge_essential (h2 : (2 : K) ≠ 0) {y : Fin 6 → K}
    (hy : y ᵥ* (bridgeIncidence : Matrix _ _ K).submatrix Fin.castSucc id = 0) :
    y = 0 := by
  have e : ∀ v, (y ᵥ* (bridgeIncidence : Matrix _ _ K).submatrix Fin.castSucc id) v = 0 :=
    fun v => congrFun hy v
  have ha := e (.inl 0); have hb := e (.inl 1); have hc := e (.inl 2)
  have hd := e (.inr 0); have he := e (.inr 1); have hf := e (.inr 2)
  simp [vecMul, dotProduct, Fin.sum_univ_succ, bridgeIncidence, bridgeEdge] at ha hb hc hd he hf
  have k0 : 2 * y 0 = 0 := by linear_combination ha + hb - hc
  have k1 : 2 * y 1 = 0 := by linear_combination hb + hc - ha
  have k2 : 2 * y 2 = 0 := by linear_combination ha + hc - hb
  have k3 : 2 * y 3 = 0 := by linear_combination hd + he - hf
  have k4 : 2 * y 4 = 0 := by linear_combination he + hf - hd
  have k5 : 2 * y 5 = 0 := by linear_combination hd + hf - he
  have z : ∀ {t : K}, 2 * t = 0 → t = 0 := fun h => (mul_eq_zero.mp h).resolve_left h2
  funext k
  fin_cases k
  exacts [z k0, z k1, z k2, z k3, z k4, z k5]

/-! ## Structural rank is an upper bound -/

/-- A nonzero determinant forces a perfect matching of the support:
some permutation `σ` has `A (σ i) i ≠ 0` for every `i`. Applied to a nonzero
`r × r` minor, field rank `r` gives a matching of size `r`. -/
theorem exists_perm_support_of_det_ne_zero {n R : Type*} [Fintype n] [DecidableEq n]
    [CommRing R] (A : Matrix n n R) (h : A.det ≠ 0) :
    ∃ σ : Equiv.Perm n, ∀ i, A (σ i) i ≠ 0 := by
  rw [det_apply] at h
  obtain ⟨σ, -, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨σ, fun i hi => hσ ?_⟩
  have h0 : ∏ j, A (σ j) j = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi
  rw [h0, smul_zero]

/-- The support of `[[1,1],[1,1]]` has a perfect matching (the identity). -/
theorem allOnes_support_matching :
    ∀ i, (!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) K) (Equiv.refl _ i) i ≠ 0 := by
  intro i; fin_cases i <;> simp

/-- ... but its field rank is one. -/
theorem allOnes_rank : (!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) K).rank = 1 := by
  rw [rank_eq_finrank_span_cols]
  have h : Set.range (!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) K).col = {![1, 1]} := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      ext i; fin_cases j <;> fin_cases i <;> rfl
    · rintro rfl
      exact ⟨0, by ext i; fin_cases i <;> rfl⟩
  rw [h, finrank_span_singleton]
  intro h0
  simpa using congrFun h0 0

/-! ## Spanning trees and pivot-cancelling combinations -/

section Tree

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The coefficient vector of `B_u - B_v`. -/
def edgeDiff (u v : V) : V → K := Pi.single u 1 - Pi.single v 1

/-- Coefficient vectors whose entries sum to zero: the combinations of
normalized rows `B_i = a_i⁻¹ A_i` that cancel the shared pivot. -/
def sumZero : Submodule K (V → K) :=
  LinearMap.ker (∑ v, LinearMap.proj v : (V → K) →ₗ[K] K)

omit [DecidableEq V] in
theorem mem_sumZero {x : V → K} : x ∈ (sumZero : Submodule K (V → K)) ↔ ∑ v, x v = 0 := by
  simp [sumZero]

theorem edgeDiff_mem_sumZero (u v : V) : (edgeDiff u v : V → K) ∈ sumZero := by
  rw [mem_sumZero]; simp [edgeDiff, Finset.sum_sub_distrib]

theorem finrank_sumZero [Nonempty V] :
    Module.finrank K (sumZero : Submodule K (V → K)) = Fintype.card V - 1 := by
  set f : (V → K) →ₗ[K] K := ∑ v, LinearMap.proj v
  obtain ⟨r⟩ := ‹Nonempty V›
  have hrange : LinearMap.range f = ⊤ := by
    refine LinearMap.range_eq_top.mpr fun c => ⟨Pi.single r c, ?_⟩
    simp [f, Pi.single_apply]
  have h := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange, finrank_top, Module.finrank_self, Module.finrank_fintype_fun_eq_card] at h
  change Module.finrank K (LinearMap.ker f) = _
  omega

/-- The edge differences of a connected graph span exactly the
pivot-cancelling combinations. -/
theorem span_edgeDiff_eq_sumZero {G : SimpleGraph V} (hG : G.Connected) :
    Submodule.span K {x | ∃ u v, G.Adj u v ∧ x = edgeDiff u v} =
      (sumZero : Submodule K (V → K)) := by
  set S := Submodule.span K {x : V → K | ∃ u v, G.Adj u v ∧ x = edgeDiff u v}
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro x ⟨u, v, -, rfl⟩
    exact edgeDiff_mem_sumZero u v
  · intro x hx
    rw [mem_sumZero] at hx
    have hreach : ∀ u v, G.Reachable u v → (edgeDiff u v : V → K) ∈ S := by
      rintro u v ⟨p⟩
      induction p with
      | nil => simp [edgeDiff]
      | @cons a b c h p ih =>
        have e : (edgeDiff a c : V → K) = edgeDiff a b + edgeDiff b c := by
          simp [edgeDiff]
        rw [e]
        exact S.add_mem (Submodule.subset_span ⟨a, b, h, rfl⟩) ih
    obtain ⟨r⟩ := hG.nonempty
    have hx' : x = ∑ v, x v • (edgeDiff v r : V → K) := by
      ext w
      simp only [edgeDiff, Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
        mul_sub, Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero]
      split_ifs <;> simp [hx]
    rw [hx']
    exact Submodule.sum_mem _ fun v _ =>
      Submodule.smul_mem _ _ (hreach v r (hG.preconnected v r))

/-- The edge differences of a spanning tree, one orientation per edge, are a
basis of the pivot-cancelling combinations: linearly independent, and
`k - 1` of them. Their images as materialized rows may still be dependent. -/
theorem IsTree.linearIndependent_edgeDiff {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : G.IsTree) :
    LinearIndependent K
      (fun e : G.edgeFinset => (edgeDiff (Quot.out e.1).1 (Quot.out e.1).2 : V → K)) := by
  set b := fun e : G.edgeFinset => (edgeDiff (Quot.out e.1).1 (Quot.out e.1).2 : V → K)
  have : Nonempty V := hG.1.nonempty
  have hspan : Submodule.span K (Set.range b) = sumZero := by
    rw [← span_edgeDiff_eq_sumZero (K := K) hG.1]
    apply le_antisymm
    · apply Submodule.span_mono
      rintro _ ⟨e, rfl⟩
      refine ⟨(Quot.out e.1).1, (Quot.out e.1).2, ?_, rfl⟩
      have he := SimpleGraph.mem_edgeFinset.mp e.2
      rwa [← Quot.out_eq e.1] at he
    · rw [Submodule.span_le]
      rintro _ ⟨u, v, huv, rfl⟩
      have hmem : s(u, v) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr huv
      have hout : s((Quot.out (s(u, v) : Sym2 V)).1, (Quot.out (s(u, v) : Sym2 V)).2) =
          s(u, v) := by
        exact Quot.out_eq _
      have hb : (edgeDiff (Quot.out (s(u, v) : Sym2 V)).1 (Quot.out (s(u, v) : Sym2 V)).2 :
          V → K) ∈ Submodule.span K (Set.range b) :=
        Submodule.subset_span ⟨⟨_, hmem⟩, rfl⟩
      generalize Quot.out (s(u, v) : Sym2 V) = p at hb hout
      rcases Sym2.eq_iff.mp hout with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2] at hb; exact hb
      · rw [h1, h2] at hb
        have : (edgeDiff u v : V → K) = -edgeDiff v u := by simp [edgeDiff]
        rw [this]; exact Submodule.neg_mem _ hb
  rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, hspan, finrank_sumZero,
    Fintype.card_coe]
  have := hG.card_edgeFinset
  omega

end Tree

end CryptoLean.Combinatorics.LargePrimeGraph
