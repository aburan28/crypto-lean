/-!
# `GF(2)[t]` on `Nat` bit patterns

Bit `i` of a `Nat` is the coefficient of `t^i`. These are the computational
definitions used by `decide` replays (promoted from
`crypto/research/ic_tree_split_structured_v_20261011/lean/TreeSplit/Replay.lean`).

`mod` reduces with a fixed budget of 130 steps, as the source's `polyMod`
does, so certificates keep their meaning. The source writes it as a `for` loop,
which the kernel cannot evaluate (hence its `native_decide`). Here both
functions recurse structurally on an explicit fuel argument, so kernel `decide`
checks them and no compiler trust is needed. `mod` does the same steps in the
same order as the source loop. Each step clears the leading term, so the
result is the true remainder whenever `deg a − deg b < 130`. The proof that
`polyMod` matches `Polynomial (ZMod 2)` reduction is a planned
`CryptoLean.Bridge` theorem, not yet proved.
-/

namespace CryptoLeanCore.GF2Poly

/-- Carry-less product, one bit of `b` per unit of fuel. -/
def mulFuel : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | n + 1, a, b => (if b % 2 = 1 then a else 0) ^^^ mulFuel n (a <<< 1) (b >>> 1)

/-- Carry-less product. `b.log2 + 1` steps consume every bit of `b`. -/
def mul (a b : Nat) : Nat := mulFuel (b.log2 + 1) a b

/-- One reduction step of the source loop: clear `a`'s leading term with a shift of `b`. -/
def modStep (a b : Nat) : Nat :=
  if a != 0 && a.log2 ≥ b.log2 then a ^^^ (b <<< (a.log2 - b.log2)) else a

def modFuel : Nat → Nat → Nat → Nat
  | 0, a, _ => a
  | n + 1, a, b => modFuel n (modStep a b) b

/-- Remainder of `a` by `b ≠ 0`, 130-step budget (see module docstring). -/
def mod (a b : Nat) : Nat := modFuel 130 a b

/-- `(t^2+1) = (t+1)^2` in `GF(2)[t]`. -/
example : mul 3 3 = 5 := by decide +kernel
/-- `t^7 − 1 = (t+1)(t^3+t+1)(t^3+t^2+1)` in `GF(2)[t]`. -/
example : mul 3 (mul 11 13) = 129 := by decide +kernel
example : mod 129 11 = 0 := by decide +kernel
example : mod 129 7 ≠ 0 := by decide +kernel

end CryptoLeanCore.GF2Poly
