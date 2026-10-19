import CryptoLean.Group.CyclicEncoding
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
namespace CryptoLean.Cyclic
variable {A : Type*} [AddCommGroup A] {p : ℕ} [Fact p.Prime]

theorem collision_recover (P : A) (hp : addOrderOf P = p)
    (a₁ b₁ a₂ b₂ x : ZMod p)
    (h : walkPoint P (encode (n := p) P (by rw [← hp]; exact addOrderOf_nsmul_eq_zero P) x) a₁ b₁ =
      walkPoint P (encode (n := p) P (by rw [← hp]; exact addOrderOf_nsmul_eq_zero P) x) a₂ b₂)
    (hb : b₁ ≠ b₂) : x = (a₂ - a₁) / (b₁ - b₂) := by
  rw [walkPoint_eq_encode, walkPoint_eq_encode] at h
  have hs := encode_injective P hp h
  apply (eq_div_iff (sub_ne_zero.mpr hb)).mpr
  calc
    x * (b₁ - b₂) = (a₁ + b₁ * x) - (a₂ + b₂ * x) + (a₂ - a₁) := by ring
    _ = a₂ - a₁ := by rw [hs]; ring

theorem negated_collision_recover (P : A) (hp : addOrderOf P = p)
    (a₁ b₁ a₂ b₂ x : ZMod p)
    (h : walkPoint P (encode (n := p) P (by rw [← hp]; exact addOrderOf_nsmul_eq_zero P) x) a₁ b₁ =
      -walkPoint P (encode (n := p) P (by rw [← hp]; exact addOrderOf_nsmul_eq_zero P) x) a₂ b₂)
    (hb : b₁ + b₂ ≠ 0) : x = -(a₁ + a₂) / (b₁ + b₂) := by
  rw [walkPoint_eq_encode, walkPoint_eq_encode, ← map_neg] at h
  have hs := encode_injective P hp h
  apply (eq_div_iff hb).mpr
  calc
    x * (b₁ + b₂) = (a₁ + b₁ * x) + (a₂ + b₂ * x) - (a₁ + a₂) := by ring
    _ = -(a₁ + a₂) := by rw [hs]; ring
end CryptoLean.Cyclic
