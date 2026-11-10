import Mathlib

namespace CryptoLean.SLP

/-- `ZMod p` has no nontrivial ring endomorphism. -/
-- NAME CHECK: relies on the instance I believe is `ZMod.subsingleton_ringHom`.
-- Fallback I believe exists: `RingHom.ext_zmod σ _`.
theorem ringHom_zmod_eq_id (p : ℕ) (σ : ZMod p →+* ZMod p) :
    σ = RingHom.id (ZMod p) :=
  Subsingleton.elim _ _

/-- **Lemma 1.** A `σ`-semilinear map between `ZMod p`-modules is linear. -/
theorem semilinear_zmod_map_smul (p : ℕ) {V W : Type*}
    [AddCommMonoid V] [AddCommMonoid W] [Module (ZMod p) V] [Module (ZMod p) W]
    {σ : ZMod p →+* ZMod p} (f : V →ₛₗ[σ] W) (c : ZMod p) (x : V) :
    f (c • x) = c • f x := by
  have hσ : σ c = c := by rw [ringHom_zmod_eq_id p σ]; rfl
  rw [f.map_smulₛₗ c x, hσ]

/-- Bundled form. Memo case: `V = W = Fin 4 → ZMod p`. -/
def semilinearToLinear (p : ℕ) {V W : Type*}
    [AddCommMonoid V] [AddCommMonoid W] [Module (ZMod p) V] [Module (ZMod p) W]
    {σ : ZMod p →+* ZMod p} (f : V →ₛₗ[σ] W) : V →ₗ[ZMod p] W where
  toFun := f
  map_add' := f.map_add
  map_smul' := fun c x => by simpa using semilinear_zmod_map_smul p f c x

end CryptoLean.SLP
