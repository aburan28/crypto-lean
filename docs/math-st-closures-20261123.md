# math-st closures: formal parts

23 November 2026. Consumer: isogeny-labs/crypto,
`research/math_st_open_problems_20261119/` (A1 report and A3 note). Source:
`CryptoLean/Group/MathStClosures.lean`.

| consumer claim | theorem | statement |
|---|---|---|
| A3 (A), core | `normSq_pow_sub_one_le` | `normSq (α^m - 1) ≤ (√(normSq α)^m + 1)^2` |
| A3 (A) | `orbit_divisor_le` | `normSq α = d`, `N = normSq (α^m - 1) ≠ 0`, `r ∣ N` ⇒ `r ≤ (√d^m + 1)^2` |
| A3 (A), `N ≠ 0` | `normSq_pow_sub_one_ne_zero` | `d ≥ 2`, `m ≥ 1` ⇒ `normSq (α^m - 1) ≠ 0` |
| A3 (B) | `same_orbit_iff_char_eq` | `χ.ker = zpowers λ` ⇒ (`∃ i, t = λ^i * s` ↔ `χ t = χ s`) |
| A3 (B), existence | `exists_char_ker_eq` | the quotient map by `zpowers λ` has that kernel |
| A1 envelope | `card_roots_X_pow_sub_one` | over `ZMod n`, `n` prime, `d ≥ 1`: `#{x : x^d = 1} = gcd(n-1, d)` |
| A1 envelope | `card_roots_X_pow_sub_X` | `d ≥ 2`: `#{x : x^d = x} = 1 + gcd(n-1, d-1)` |

**Hypotheses the consumer carries.** Mathlib has no embedding of `End(E)`
into an imaginary-quadratic order with `deg = normSq`. The consumer supplies
it as `normSq α = d` and `N = normSq (α^m - 1)`.

**Not formalized.** A3 (C), the generic-group lower bound, because this library
has no generic-group-model framework. The A1 upper bound `R ≤ L + 10` is
measured, not proved.

**Gate.** `tools/proof-gate.sh` passed on the whole repository: 348 theorems,
0 failing, 0 trusted native exceptions. Each new theorem uses only `propext`,
`Classical.choice` and `Quot.sound`, and `same_orbit_iff_char_eq` uses only
`propext`. Receipt: `receipts/MathStClosures20261123/gate-audit.txt`. The only
build warning is Lake's module-system advisory for `import Mathlib`. Other
files get it too.
