import CryptoLean.Secp256k1.M16FactorBaseLiftableDefs

-- Ported from KeyAIGit/ecdlp-lean-verification Ecdlp/Proved/M16FactorBaseLiftableGeneratorCertificate.lean at 0a47cd62f43d (PR #347).
/-! Isolated native certificate for the M16 generator order and GLV powers. -/

namespace CryptoLean.Secp256k1.M16FactorBaseLiftable.Certificates

theorem factorBaseGenerator_certificate :
    factorBaseGenerator ^ 564522 = 1 ∧
    factorBaseGenerator ^ 282261 ≠ 1 ∧
    factorBaseGenerator ^ 188174 ≠ 1 ∧
    factorBaseGenerator ^ 80646 ≠ 1 ∧
    factorBaseGenerator ^ 42 ≠ 1 ∧
    factorBaseGenerator ^ 188174 = (Secp256k1.beta : Fp) ^ 2 ∧
    factorBaseGenerator ^ 376348 = (Secp256k1.beta : Fp) := by
  native_decide

end CryptoLean.Secp256k1.M16FactorBaseLiftable.Certificates
