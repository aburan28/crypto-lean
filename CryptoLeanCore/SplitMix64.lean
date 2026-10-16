/-!
# SplitMix64

The 64-bit mixer the `aburan28/crypto` harnesses use for seeded streams
(Steele, Lea and Flood, OOPSLA 2014). `step s` returns the next state and the
output. Promoted from `TreeSplit/Replay.lean` (`mix`).
-/

namespace CryptoLeanCore.SplitMix64

def step (s : UInt64) : UInt64 × UInt64 :=
  let s' := s + 0x9E3779B97F4A7C15
  let z := (s' ^^^ (s' >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (s', z ^^^ (z >>> 31))

/-- Reference value: the first output for seed 0 is `0xE220A8397B1DCDAF`. -/
theorem first_output_seed_zero : (step 0).2 = 0xE220A8397B1DCDAF := by decide

end CryptoLeanCore.SplitMix64
