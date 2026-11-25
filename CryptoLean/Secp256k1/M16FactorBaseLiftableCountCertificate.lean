import CryptoLean.Secp256k1.M16FactorBaseLiftableGeneratorCertificate

-- Ported from KeyAIGit/ecdlp-lean-verification Ecdlp/Proved/M16FactorBaseLiftableCountCertificate.lean at 0a47cd62f43d (PR #347).
/-!
# Isolated native certificate for the M16 liftable representative census

This is intentionally the only native leaf for the representative count.
The tail-recursive accumulator keeps native evaluation resource bounded; the
second theorem bridges its result to the mathematical `Nat.count` by a kernel
proof from `boolCountAcc_eq`.
-/

namespace CryptoLean.Secp256k1.M16FactorBaseLiftable.Certificates

/-- A closed no-inline boundary keeps native compilation from specializing the
entire census loop at its concrete bound. -/
@[noinline] def representativeCountRuntime : ℕ :=
  boolCountAcc representativeEulerPositive 0 factorBaseOrbitCount 0

theorem representative_count_native :
    representativeCountRuntime = 94509 := by
  native_decide

theorem representativeEulerPositive_count :
    Nat.count (fun k ↦ representativeEulerPositive k = true)
      factorBaseOrbitCount = 94509 := by
  simpa only [representativeCountRuntime, boolCountAcc_eq, Nat.zero_add] using
    representative_count_native

end CryptoLean.Secp256k1.M16FactorBaseLiftable.Certificates
