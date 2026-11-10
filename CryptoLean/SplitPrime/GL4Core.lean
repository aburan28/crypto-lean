import Mathlib

universe u

namespace CryptoLean.SLP

/-! ### Syntax -/

/-- Linear layer. `wire k` is the result of the `k`-th nonlinear gate. -/
inductive LExp (F : Type u) (n : ℕ) : Type u where
  | inp   : Fin n → LExp F n
  | wire  : ℕ → LExp F n
  | const : F → LExp F n
  | add   : LExp F n → LExp F n → LExp F n
  | smul  : F → LExp F n → LExp F n

/-- Nonlinear gates: the M and S of the memo. -/
inductive Gate (F : Type u) (n : ℕ) : Type u where
  | mul : LExp F n → LExp F n → Gate F n
  | sq  : LExp F n → Gate F n

/-- Straight-line program with `n` inputs and `m` outputs. -/
structure Prog (F : Type u) (n m : ℕ) : Type u where
  gates : List (Gate F n)
  outs  : Fin m → LExp F n

section Syntax
variable {F : Type u} {n n' m : ℕ}

def LExp.subst (e : LExp F n) (σ : Fin n → LExp F n') : LExp F n' :=
  match e with
  | .inp i    => σ i
  | .wire k   => .wire k
  | .const c  => .const c
  | .add a b  => .add (a.subst σ) (b.subst σ)
  | .smul c a => .smul c (a.subst σ)

def Gate.subst (g : Gate F n) (σ : Fin n → LExp F n') : Gate F n' :=
  match g with
  | .mul a b => .mul (a.subst σ) (b.subst σ)
  | .sq a    => .sq (a.subst σ)

def Gate.isMul : Gate F n → Bool
  | .mul _ _ => true
  | .sq _    => false

def Gate.isSq : Gate F n → Bool
  | .mul _ _ => false
  | .sq _    => true

def Prog.mulCount (P : Prog F n m) : ℕ := P.gates.countP Gate.isMul
def Prog.sqCount  (P : Prog F n m) : ℕ := P.gates.countP Gate.isSq

/-- Substitute linear-layer expressions for the inputs. -/
def Prog.substIn (P : Prog F n m) (σ : Fin n → LExp F n') : Prog F n' m where
  gates := P.gates.map fun g => g.subst σ
  outs  := fun k => (P.outs k).subst σ

theorem countP_map_congr {α β : Type*} (p : β → Bool) (q : α → Bool) (f : α → β)
    (h : ∀ a, p (f a) = q a) (l : List α) :
    (l.map f).countP p = l.countP q := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.countP_cons, h, ih]

theorem Prog.mulCount_substIn (P : Prog F n m) (σ : Fin n → LExp F n') :
    (P.substIn σ).mulCount = P.mulCount :=
  countP_map_congr Gate.isMul Gate.isMul (fun g => g.subst σ)
    (fun g => by cases g <;> rfl) P.gates

theorem Prog.sqCount_substIn (P : Prog F n m) (σ : Fin n → LExp F n') :
    (P.substIn σ).sqCount = P.sqCount :=
  countP_map_congr Gate.isSq Gate.isSq (fun g => g.subst σ)
    (fun g => by cases g <;> rfl) P.gates

end Syntax

/-! ### Semantics -/

section Semantics
variable {F : Type u} [Field F] {n n' m m' : ℕ}

def LExp.eval (e : LExp F n) (x : Fin n → F) (env : List F) : F :=
  match e with
  | .inp i    => x i
  | .wire k   => env.getD k 0
  | .const c  => c
  | .add a b  => a.eval x env + b.eval x env
  | .smul c a => c * a.eval x env

def Gate.eval (g : Gate F n) (x : Fin n → F) (env : List F) : F :=
  match g with
  | .mul a b => a.eval x env * b.eval x env
  | .sq a    => a.eval x env * a.eval x env

/-- Run the gates in order; each appends its value to the wire environment. -/
def runGates (x : Fin n → F) : List (Gate F n) → List F → List F
  | [], env => env
  | g :: gs, env => runGates x gs (env ++ [g.eval x env])

def Prog.eval (P : Prog F n m) (x : Fin n → F) : Fin m → F :=
  fun k => (P.outs k).eval x (runGates x P.gates [])

theorem LExp.eval_subst (σ : Fin n → LExp F n') (w : Fin n' → F) (x : Fin n → F)
    (env : List F) (hσ : ∀ i, (σ i).eval w env = x i) (e : LExp F n) :
    (e.subst σ).eval w env = e.eval x env := by
  induction e with
  | inp i => simpa only [LExp.subst, LExp.eval] using hσ i
  | wire k => simp only [LExp.subst, LExp.eval]
  | const c => simp only [LExp.subst, LExp.eval]
  | add a b iha ihb => simp only [LExp.subst, LExp.eval, iha, ihb]
  | smul c a ih => simp only [LExp.subst, LExp.eval, ih]

theorem Gate.eval_subst (σ : Fin n → LExp F n') (w : Fin n' → F) (x : Fin n → F)
    (env : List F) (hσ : ∀ i, (σ i).eval w env = x i) (g : Gate F n) :
    (g.subst σ).eval w env = g.eval x env := by
  cases g with
  | mul a b => simp only [Gate.subst, Gate.eval, LExp.eval_subst σ w x env hσ]
  | sq a => simp only [Gate.subst, Gate.eval, LExp.eval_subst σ w x env hσ]

theorem runGates_subst (σ : Fin n → LExp F n') (w : Fin n' → F) (x : Fin n → F)
    (hσ : ∀ env i, (σ i).eval w env = x i) (gs : List (Gate F n)) (env : List F) :
    runGates w (gs.map fun g => g.subst σ) env = runGates x gs env := by
  induction gs generalizing env with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, runGates]
    rw [Gate.eval_subst σ w x env (hσ env) g]
    exact ih _

theorem Prog.eval_substIn (P : Prog F n m) (σ : Fin n → LExp F n') (w : Fin n' → F)
    (x : Fin n → F) (hσ : ∀ env i, (σ i).eval w env = x i) :
    (P.substIn σ).eval w = P.eval x := by
  funext k
  show ((P.outs k).subst σ).eval w (runGates w (P.gates.map fun g => g.subst σ) []) =
      (P.outs k).eval x (runGates x P.gates [])
  rw [runGates_subst σ w x hσ]
  exact LExp.eval_subst σ w x _ (hσ _) _

/-! ### Linear combinations as linear-layer syntax -/

/-- `Σ_{j ∈ l} c j • e j` as a right-nested chain of `add`/`smul`. -/
def LExp.lin {ι : Type} (c : ι → F) (e : ι → LExp F n) : List ι → LExp F n
  | [] => .const 0
  | j :: l => .add (.smul (c j) (e j)) (LExp.lin c e l)

theorem LExp.eval_lin {ι : Type} (c : ι → F) (e : ι → LExp F n) (x : Fin n → F)
    (env : List F) (l : List ι) :
    (LExp.lin c e l).eval x env = (l.map fun j => c j * (e j).eval x env).sum := by
  induction l with
  | nil => simp [LExp.lin, LExp.eval]
  | cons j l ih => simp [LExp.lin, LExp.eval, ih]

/-- List-based matrix action. Equal to `Matrix.mulVec` (File 2). -/
def rowApply (A : Matrix (Fin m) (Fin n) F) (w : Fin n → F) : Fin m → F :=
  fun i => ((List.finRange n).map fun j => A i j * w j).sum

/-- Old input `i` expressed in the new inputs: `Σ_j A i j • inp j`. -/
def linSubst (A : Matrix (Fin n) (Fin n') F) : Fin n → LExp F n' :=
  fun i => LExp.lin (A i) LExp.inp (List.finRange n')

theorem eval_linSubst (A : Matrix (Fin n) (Fin n') F) (w : Fin n' → F)
    (env : List F) (i : Fin n) :
    (linSubst A i).eval w env = rowApply A w i :=
  LExp.eval_lin (A i) LExp.inp w env (List.finRange n')

/-- Post-compose the outputs with a matrix. Gates are untouched. -/
def Prog.linOut (P : Prog F n m) (B : Matrix (Fin m') (Fin m) F) : Prog F n m' where
  gates := P.gates
  outs  := fun k => LExp.lin (B k) P.outs (List.finRange m)

theorem Prog.eval_linOut (P : Prog F n m) (B : Matrix (Fin m') (Fin m) F)
    (x : Fin n → F) : (P.linOut B).eval x = rowApply B (P.eval x) := by
  funext k
  exact LExp.eval_lin (B k) P.outs x (runGates x P.gates []) (List.finRange m)

/-! ### Reparameterization: the one-step lemma -/

/-- The program for `w ↦ B · P(A · w)`. -/
def Prog.reparam (P : Prog F n m) (A : Matrix (Fin n) (Fin n') F)
    (B : Matrix (Fin m') (Fin m) F) : Prog F n' m' :=
  (P.substIn (linSubst A)).linOut B

/-- Strongest syntactic form: same gates in the same order, operands substituted. -/
theorem Prog.gates_reparam (P : Prog F n m) (A : Matrix (Fin n) (Fin n') F)
    (B : Matrix (Fin m') (Fin m) F) :
    (P.reparam A B).gates = P.gates.map fun g => g.subst (linSubst A) := rfl

theorem Prog.mulCount_reparam (P : Prog F n m) (A : Matrix (Fin n) (Fin n') F)
    (B : Matrix (Fin m') (Fin m) F) : (P.reparam A B).mulCount = P.mulCount :=
  Prog.mulCount_substIn P (linSubst A)

theorem Prog.sqCount_reparam (P : Prog F n m) (A : Matrix (Fin n) (Fin n') F)
    (B : Matrix (Fin m') (Fin m) F) : (P.reparam A B).sqCount = P.sqCount :=
  Prog.sqCount_substIn P (linSubst A)

theorem Prog.eval_reparam (P : Prog F n m) (A : Matrix (Fin n) (Fin n') F)
    (B : Matrix (Fin m') (Fin m) F) (w : Fin n' → F) :
    (P.reparam A B).eval w = rowApply B (P.eval (rowApply A w)) := by
  unfold Prog.reparam
  rw [Prog.eval_linOut,
    Prog.eval_substIn P (linSubst A) w (rowApply A w)
      (fun env i => eval_linSubst A w env i)]

/-! ### Iteration -/

theorem mulCount_foldl_reparam
    (steps : List (Matrix (Fin n) (Fin n) F × Matrix (Fin m) (Fin m) F))
    (P : Prog F n m) :
    (steps.foldl (fun Q s => Q.reparam s.1 s.2) P).mulCount = P.mulCount := by
  induction steps generalizing P with
  | nil => rfl
  | cons s steps ih => simp only [List.foldl_cons, ih, Prog.mulCount_reparam]

theorem sqCount_foldl_reparam
    (steps : List (Matrix (Fin n) (Fin n) F × Matrix (Fin m) (Fin m) F))
    (P : Prog F n m) :
    (steps.foldl (fun Q s => Q.reparam s.1 s.2) P).sqCount = P.sqCount := by
  induction steps generalizing P with
  | nil => rfl
  | cons s steps ih => simp only [List.foldl_cons, ih, Prog.sqCount_reparam]

/-! ### "And conversely": achievable (M, S) profiles are invariant -/

theorem exists_prog_iff
    (A : Matrix (Fin n) (Fin n') F) (A' : Matrix (Fin n') (Fin n) F)
    (B : Matrix (Fin m') (Fin m) F) (B' : Matrix (Fin m) (Fin m') F)
    (hA : ∀ x : Fin n → F, rowApply A (rowApply A' x) = x)
    (hB : ∀ y : Fin m → F, rowApply B' (rowApply B y) = y)
    (f : (Fin n → F) → (Fin m → F)) (a s : ℕ) :
    (∃ P : Prog F n m, (∀ x, P.eval x = f x) ∧ P.mulCount = a ∧ P.sqCount = s) ↔
    (∃ Q : Prog F n' m', (∀ w, Q.eval w = rowApply B (f (rowApply A w))) ∧
        Q.mulCount = a ∧ Q.sqCount = s) := by
  constructor
  · rintro ⟨P, hP, ha, hs⟩
    refine ⟨P.reparam A B, ?_, (Prog.mulCount_reparam P A B).trans ha,
      (Prog.sqCount_reparam P A B).trans hs⟩
    intro w
    rw [Prog.eval_reparam, hP]
  · rintro ⟨Q, hQ, ha, hs⟩
    refine ⟨Q.reparam A' B', ?_, (Prog.mulCount_reparam Q A' B').trans ha,
      (Prog.sqCount_reparam Q A' B').trans hs⟩
    intro x
    rw [Prog.eval_reparam, hQ, hA, hB]

end Semantics
end CryptoLean.SLP
