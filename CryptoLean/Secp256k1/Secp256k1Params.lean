import CryptoLean.Secp256k1.Verified

-- Ported from KeyAIGit/ecdlp-lean-verification Ecdlp/Proved/Secp256k1Params.lean at 0a47cd62f43d (PR #347).
/-! secp256k1 number-theoretic parameter facts behind real design choices. -/

namespace CryptoLean.Secp256k1.Curve

/-- `p ≡ 3 (mod 4)`: enables point decompression via `√a = a^((p+1)/4)`. -/
theorem p_mod_four : Secp256k1.p % 4 = 3 := by native_decide

/-- `3 ∣ (p − 1)`: `𝔽_p` has a primitive cube root of unity (the GLV field factor `β`). -/
theorem three_dvd_p_sub_one : (Secp256k1.p - 1) % 3 = 0 := by native_decide

/-- `3 ∣ (n − 1)`: `ℤ/n` has a primitive cube root of unity (the GLV eigenvalue `λ`),
making the GLV scalar decomposition possible. -/
theorem three_dvd_n_sub_one : (Secp256k1.n - 1) % 3 = 0 := by native_decide

end CryptoLean.Secp256k1.Curve
