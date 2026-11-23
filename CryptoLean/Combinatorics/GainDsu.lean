import Mathlib

/-!
# Gain-aware union-find: exact rank of two-entry large-prime rows

Formal version of section 6 of the catalog "Graph algorithms and asymptotic
costs for ECDLP index calculus" (isogeny-labs/crypto PR #4917), implemented in
crypto `src/cryptanalysis/large_prime_graph.rs` (`GainDsu`).

A *flat* DSU state (after path compression) is a root map, nonzero
potentials and a set of flagged ("pinned") roots. It represents the space

  `{x | ∃ t, x w = pot w * t (root w) for all w, and t r = 0 on flagged r}`.

* `space_union`, `space_cycle_balanced`, `space_cycle_unbalanced`,
  `space_singleton`, `space_zero`: each DSU update replaces the represented
  space by its intersection with the solutions of the new row. So, by
  induction over the processed rows (starting from `space_init`), the state
  represents exactly the right kernel `{x | A x = 0}`.
* `WF.union`, `WF.pin`: the updates keep the state well formed.
* `finrank_space`: a well-formed state's space has dimension equal to the
  number of unflagged roots.
* `rank_eq_card_sub_unflagged`: hence `rank A = |V| − #unflagged roots`,
  the catalog's formula `rank(A_L) = v − #{unflagged components}`.

The step lemmas are stated for one row at a time; the row loop itself (and the
`find` with path compression that produces a flat state) is the Rust code.
-/

namespace CryptoLean.Combinatorics.GainDsu

variable {K : Type*} [Field K] {V : Type*} [DecidableEq V]

/-- A flat union-find state with multiplicative potentials. -/
structure State (V K : Type*) where
  root : V → V
  pot : V → K
  flagged : Set V

/-- The solution space a state represents. -/
def State.space (st : State V K) : Set (V → K) :=
  {x | ∃ t : V → K, (∀ w, x w = st.pot w * t (st.root w)) ∧ ∀ r ∈ st.flagged, t r = 0}

/-- Solutions of a two-entry row `a x_u + b x_v = 0`. -/
def edgeSet (a b : K) (u v : V) : Set (V → K) := {x | a * x u + b * x v = 0}

/-- Solutions of a one-entry row `a x_u = 0`. -/
def pinSet (a : K) (u : V) : Set (V → K) := {x | a * x u = 0}

/-- Well formed: roots are fixed points and potentials are nonzero. -/
def State.WF (st : State V K) : Prop :=
  (∀ w, st.root (st.root w) = st.root w) ∧ ∀ w, st.pot w ≠ 0

/-- Every vertex its own root, potential one, nothing flagged. -/
def State.init : State V K := ⟨id, fun _ => 1, ∅⟩

omit [DecidableEq V] in
theorem space_init : (State.init : State V K).space = Set.univ := by
  ext x
  simp only [State.space, State.init, Set.mem_ofPred_eq, Set.mem_univ, iff_true,
    Set.mem_empty_iff_false, IsEmpty.forall_iff, implies_true, and_true, id, one_mul]
  exact ⟨x, fun _ => rfl⟩

omit [DecidableEq V] in
theorem WF.init : (State.init : State V K).WF :=
  ⟨fun _ => rfl, fun _ => one_ne_zero⟩

/-! ## Union of two components -/

/-- Attach the root of `u` below the root of `v` for the row `a x_u + b x_v = 0`. -/
def State.union (st : State V K) (a b : K) (u v : V) : State V K where
  root w := if st.root w = st.root u then st.root v else st.root w
  pot w := if st.root w = st.root u then
      st.pot w * (-(b * st.pot v) / (a * st.pot u)) else st.pot w
  flagged := {r | (r ∈ st.flagged ∧ r ≠ st.root u) ∨ (r = st.root v ∧ st.root u ∈ st.flagged)}

theorem space_union (st : State V K) {a b : K} {u v : V} (ha : a ≠ 0) (hb : b ≠ 0)
    (hpu : st.pot u ≠ 0) (hpv : st.pot v ≠ 0) (hne : st.root u ≠ st.root v) :
    st.space ∩ edgeSet a b u v = (st.union a b u v).space := by
  set c : K := -(b * st.pot v) / (a * st.pot u) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]; exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero hb hpv)) (mul_ne_zero ha hpu)
  have key : a * st.pot u * c = -(b * st.pot v) := by
    rw [hc]; field_simp
  ext x
  simp only [Set.mem_inter_iff, State.space, edgeSet, State.union, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨t, hx, hf⟩, he⟩
    have hu := hx u
    have hv := hx v
    have htu : t (st.root u) = c * t (st.root v) := by
      rw [hu, hv] at he
      have : a * st.pot u * (t (st.root u) - c * t (st.root v)) = 0 := by
        linear_combination he - t (st.root v) * key
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (mul_ne_zero ha hpu)
      · exact sub_eq_zero.mp h
    refine ⟨t, fun w => ?_, ?_⟩
    · by_cases hw : st.root w = st.root u
      · rw [if_pos hw, if_pos hw, hx w, hw, htu, hc]; ring
      · rw [if_neg hw, if_neg hw, hx w]
    · rintro r (⟨hr, -⟩ | ⟨rfl, hru⟩)
      · exact hf r hr
      · have h0 := hf _ hru
        rw [htu] at h0
        exact (mul_eq_zero.mp h0).resolve_left hc0
  · rintro ⟨t', hx, hf⟩
    let t : V → K := fun w => if w = st.root u then c * t' (st.root v) else t' w
    have ht_ne : ∀ w, w ≠ st.root u → t w = t' w := fun w hw => if_neg hw
    have hxu : x u = st.pot u * c * t' (st.root v) := by
      rw [hx u, if_pos rfl, if_pos rfl]
    have hxv : x v = st.pot v * t' (st.root v) := by
      rw [hx v, if_neg (Ne.symm hne), if_neg (Ne.symm hne)]
    refine ⟨⟨t, fun w => ?_, ?_⟩, ?_⟩
    · by_cases hw : st.root w = st.root u
      · rw [hx w, if_pos hw, if_pos hw, hw]
        simp only [t, if_pos rfl]; ring
      · rw [hx w, if_neg hw, if_neg hw, ht_ne _ hw]
    · intro r hr
      by_cases hru : r = st.root u
      · subst hru
        simp only [t, if_pos rfl]
        rw [hf _ (Or.inr ⟨rfl, hr⟩), mul_zero]
      · rw [ht_ne _ hru]; exact hf r (Or.inl ⟨hr, hru⟩)
    · rw [hxu, hxv]
      linear_combination t' (st.root v) * key

/-! ## Cycles and singletons -/

/-- Flag the root `r`. -/
def State.pin (st : State V K) (r : V) : State V K := { st with flagged := insert r st.flagged }

omit [DecidableEq V] in
/-- A balanced cycle (`γ = a p_u + b p_v = 0`) adds nothing. -/
theorem space_cycle_balanced (st : State V K) {a b : K} {u v : V}
    (hroot : st.root u = st.root v) (hγ : a * st.pot u + b * st.pot v = 0) :
    st.space ∩ edgeSet a b u v = st.space := by
  refine Set.inter_eq_left.mpr ?_
  rintro x ⟨t, hx, -⟩
  simp only [edgeSet, Set.mem_ofPred_eq]
  rw [hx u, hx v, ← hroot]
  linear_combination t (st.root u) * hγ

omit [DecidableEq V] in
/-- An unbalanced cycle (`γ ≠ 0`) pins its component. -/
theorem space_cycle_unbalanced (st : State V K) {a b : K} {u v : V}
    (hroot : st.root u = st.root v) (hγ : a * st.pot u + b * st.pot v ≠ 0) :
    st.space ∩ edgeSet a b u v = (st.pin (st.root u)).space := by
  ext x
  simp only [Set.mem_inter_iff, State.space, edgeSet, State.pin, Set.mem_ofPred_eq,
    Set.mem_insert_iff]
  constructor
  · rintro ⟨⟨t, hx, hf⟩, he⟩
    refine ⟨t, hx, ?_⟩
    have h0 : (a * st.pot u + b * st.pot v) * t (st.root u) = 0 := by
      rw [hx u, hx v, ← hroot] at he; linear_combination he
    have htu := (mul_eq_zero.mp h0).resolve_left hγ
    rintro r (rfl | hr)
    · exact htu
    · exact hf r hr
  · rintro ⟨t, hx, hf⟩
    refine ⟨⟨t, hx, fun r hr => hf r (Or.inr hr)⟩, ?_⟩
    rw [hx u, hx v, ← hroot, hf _ (Or.inl rfl)]; ring

omit [DecidableEq V] in
/-- A one-entry row pins its component. -/
theorem space_singleton (st : State V K) {a : K} {u : V} (ha : a ≠ 0) (hpu : st.pot u ≠ 0) :
    st.space ∩ pinSet a u = (st.pin (st.root u)).space := by
  ext x
  simp only [Set.mem_inter_iff, State.space, pinSet, State.pin, Set.mem_ofPred_eq,
    Set.mem_insert_iff]
  constructor
  · rintro ⟨⟨t, hx, hf⟩, he⟩
    refine ⟨t, hx, ?_⟩
    rw [hx u] at he
    have htu : t (st.root u) = 0 := by
      rcases mul_eq_zero.mp he with h | h
      · exact absurd h ha
      · exact (mul_eq_zero.mp h).resolve_left hpu
    rintro r (rfl | hr)
    · exact htu
    · exact hf r hr
  · rintro ⟨t, hx, hf⟩
    exact ⟨⟨t, hx, fun r hr => hf r (Or.inr hr)⟩, by rw [hx u, hf _ (Or.inl rfl)]; ring⟩

omit [DecidableEq V] in
/-- An all-zero row changes nothing. -/
theorem space_zero (st : State V K) {u v : V} : st.space ∩ edgeSet 0 0 u v = st.space := by
  refine Set.inter_eq_left.mpr fun x _ => ?_
  simp [edgeSet]

/-! ## Well-formedness is preserved -/

theorem WF.union {st : State V K} (h : st.WF) {a b : K} {u v : V} (ha : a ≠ 0) (hb : b ≠ 0)
    (hne : st.root u ≠ st.root v) : (st.union a b u v).WF := by
  obtain ⟨hr, hp⟩ := h
  have hrv : st.root (st.root v) = st.root v := hr v
  refine ⟨fun w => ?_, fun w => ?_⟩
  · simp only [State.union]
    by_cases hw : st.root w = st.root u
    · rw [if_pos hw, hrv, if_neg (Ne.symm hne)]
    · rw [if_neg hw, hr w, if_neg hw]
  · simp only [State.union]
    split_ifs
    · exact mul_ne_zero (hp w) (div_ne_zero (neg_ne_zero.mpr (mul_ne_zero hb (hp v)))
        (mul_ne_zero ha (hp u)))
    · exact hp w

omit [DecidableEq V] in
theorem WF.pin {st : State V K} (h : st.WF) (r : V) : (st.pin r).WF := h

/-! ## Dimension and rank -/

variable [Fintype V]

/-- The represented space as a subspace. -/
def State.subspace (st : State V K) : Submodule K (V → K) where
  carrier := st.space
  add_mem' := by
    rintro x y ⟨s, hs, hsf⟩ ⟨t, ht, htf⟩
    exact ⟨s + t, fun w => by simp [hs w, ht w, mul_add], fun r hr => by simp [hsf r hr, htf r hr]⟩
  zero_mem' := ⟨0, fun w => by simp, fun r _ => rfl⟩
  smul_mem' := by
    rintro c x ⟨t, ht, htf⟩
    exact ⟨c • t, fun w => by simp [ht w]; ring, fun r hr => by simp [htf r hr]⟩

/-- Unflagged roots. -/
def unflaggedRoots (st : State V K) : Set V := {r | st.root r = r ∧ r ∉ st.flagged}

open Classical in
/-- A well-formed state's space is `K^(unflagged roots)`. -/
noncomputable def State.equivUnflagged (st : State V K) (h : st.WF) :
    st.subspace ≃ₗ[K] (unflaggedRoots st → K) where
  toFun x r := x.1 r.1 / st.pot r.1
  invFun s := ⟨fun w => st.pot w *
      (if hw : st.root w ∈ unflaggedRoots st then s ⟨st.root w, hw⟩ else 0), by
    refine ⟨fun r => if hr : r ∈ unflaggedRoots st then s ⟨r, hr⟩ else 0, fun w => rfl, ?_⟩
    intro r hr
    exact dif_neg fun h' => h'.2 hr⟩
  map_add' x y := by ext r; simp [add_div]
  map_smul' c x := by ext r; simp [mul_div_assoc]
  left_inv := by
    rintro ⟨x, t, hx, hf⟩
    apply Subtype.ext
    funext w
    have hrw : st.root (st.root w) = st.root w := h.1 w
    have hxr : x (st.root w) = st.pot (st.root w) * t (st.root w) := by rw [hx, hrw]
    by_cases hw : st.root w ∈ unflaggedRoots st
    · show st.pot w * (if hw : st.root w ∈ unflaggedRoots st then
          x (st.root w) / st.pot (st.root w) else 0) = x w
      rw [dif_pos hw, hxr, mul_div_cancel_left₀ _ (h.2 _), hx w]
    · show st.pot w * (if hw : st.root w ∈ unflaggedRoots st then
          x (st.root w) / st.pot (st.root w) else 0) = x w
      have : st.root w ∈ st.flagged := by
        by_contra hfl; exact hw ⟨hrw, hfl⟩
      rw [dif_neg hw, hx w, hf _ this, mul_zero]
  right_inv := by
    intro s
    funext r
    have hr : st.root r.1 = r.1 := r.2.1
    have hmem : st.root r.1 ∈ unflaggedRoots st := by rw [hr]; exact r.2
    show st.pot r.1 * (if hw : st.root r.1 ∈ unflaggedRoots st then
        s ⟨st.root r.1, hw⟩ else 0) / st.pot r.1 = s r
    rw [dif_pos hmem, mul_div_cancel_left₀ _ (h.2 _)]
    exact congrArg s (Subtype.ext hr)

open Classical in
theorem finrank_space (st : State V K) (h : st.WF) :
    Module.finrank K st.subspace = Fintype.card (unflaggedRoots st) := by
  rw [(st.equivUnflagged h).finrank_eq, Module.finrank_fintype_fun_eq_card]

open Classical in
/-- **Catalog §6.** If a well-formed state represents the right kernel of `A`
(as the step lemmas guarantee after processing its rows), then
`rank A = |V| − #unflagged roots`. -/
theorem rank_eq_card_sub_unflagged {ι : Type*} [Fintype ι] (A : Matrix ι V K)
    (st : State V K) (h : st.WF) (hker : {x | A.mulVec x = 0} = st.space) :
    A.rank = Fintype.card V - Fintype.card (unflaggedRoots st) := by
  have hsub : LinearMap.ker A.mulVecLin = st.subspace := by
    ext x
    change A.mulVec x = 0 ↔ x ∈ st.space
    rw [← hker]; rfl
  have hrn := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  rw [hsub, finrank_space st h, Module.finrank_fintype_fun_eq_card] at hrn
  rw [Matrix.rank]
  omega

end CryptoLean.Combinatorics.GainDsu
