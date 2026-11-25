# Proof-carrying post-quantum KEM: design and the ML-KEM / SQIsign proof inventory

2026-11-25 · crypto-lean branch `claude/pq-kem-proofs-20261125` · trunk PR isogeny-labs/workspace#151

## 1. Design: a KEM that ships its proofs

A *proof-carrying KEM* (PC-KEM) is a KEM specification plus a manifest. Every property a
deployment relies on appears in the manifest with one of three statuses:

| Status | Meaning | Check |
|---|---|---|
| **L** (Lean) | Theorem in `crypto-lean`, standard axioms only | `tools/proof-gate.sh`, `#print axioms` |
| **C** (computed) | Number produced by a script in this directory, with its model stated | re-run the script |
| **A** (assumption) | Named hardness or idealisation assumption, with the reduction that uses it | none: it is an assumption |

The design rule is that **no property sits in prose only**. An implementation (for example
the `velu` library) cites manifest rows, never "the paper". Each row also says what the
formal statement *does not* cover, so the formal result is never read as stronger than it
is.

The construction is the standard modular one, chosen because each layer has a small,
separately checkable proof obligation:

1. **K-PKE** (Regev/LPR/Kyber over `R_q^k`): correctness identity plus a rounding bound
   (L), a failure probability δ (C), and IND-CPA from decision MLWE (L, with MLWE as A).
2. **FO transform with implicit rejection** (`FO^⊥̸`, `m ‖ H(ek)` variant, FIPS 203
   Alg. 17/18): correctness (L), failure transfer δ_KEM ≤ δ_PKE in the ROM (L), and
   IND-CCA in the (Q)ROM (open, see §4).
3. **Hybrid combiner** for deployment (X25519 + ML-KEM, `K = KDF(K₁ ‖ K₂ ‖ transcript)`):
   IND-CCA if either component is (open; next obligation, §4).

ML-KEM is the first instance. §2 is its manifest.

## 2. ML-KEM manifest

| # | Property | Status | Where |
|---|---|---|---|
| 1 | `Decompress_d ∘ Compress_d` moves `x` by ≤ ⌈q/2^(d+1)⌋ for d ∈ {1,4,5,10,11} (832, 104, 52, 2, 1) | L | `Lattice/Rounding.lean` `mlkem_decompress_compress_error` (kernel `decide`, all 3329 inputs) |
| 2 | 1-bit decoding is correct when the centred noise is below 832 | L | `Lattice/Rounding.lean` `mlkem_decode_correct` |
| 3 | Decryption = message + `⟪e,r⟫ − ⟪e₁,s⟫ + e₂` | L | `PQ/KPKE.lean` `decrypt_encrypt` |
| 4 | q = 3329 is prime, ζ = 17 is a primitive 256th root, there is no 512th root (why the NTT is incomplete) | L | `Lattice/NTT.lean` |
| 5 | CBD_η has support [−η, η], mean 0 and variance η/2 | L | `Lattice/CBD.lean` |
| 6 | δ = 2⁻¹³⁸·⁸ / 2⁻¹⁶⁴·⁸ / 2⁻¹⁷⁴·⁸ (512/768/1024) | C | `failure_prob.py`; reproduces FIPS 203 Table 1 to 0.1 bit |
| 7 | **IND-CPA(K-PKE) ≤ Σ four decision-MLWE advantages**, with explicit reductions `B₁`, `B₂`; adaptive message choice allowed | L | `PQ/KPKE.lean` `indcpa_le_mlwe`; ML-KEM instance `PQ/MLKEM.lean` `mlkem{512,768,1024}_indcpa` |
| 8 | FO correctness: K-PKE correct ⇒ `Decaps(Encaps) = K` | L | `PQ/FO.lean` `decaps_encaps` |
| 9 | KEM failure ⊆ PKE failure at the derived coins; in the ROM, δ_KEM ≤ δ_PKE | L | `PQ/FO.lean` `kemFail_imp_pkeFail`, `kemFail_le_pkeFail_rom` |
| 10 | Decision MLWE (k×k, χ₁, χ₁) and ((k+1)×k, χ₁, χ₂) is hard | A | used by row 7 |
| 11 | `SampleNTT(XOF(ρ))` yields a uniform matrix `A`; `G`, `H`, `J` are random oracles | A | used by rows 7 and 9 |
| 12 | IND-CCA of ML-KEM (FO in the QROM) | **open** | HHK17; Bindel et al. 2019; Don–Fehr–Majenz–Schaffner 2022 (pen and paper) |

**What the formal statements do not cover** (read before citing rows 7 to 9):

* *Running time is not modelled.* Advantages are exact rationals of finite uniform
  experiments. `B₁` and `B₂` visibly run the adversary once plus one encryption, but
  "efficient" is not a Lean theorem.
* The ciphertext in row 7 is uncompressed. Compression and encoding are public
  deterministic maps, so an attack on the compressed ciphertext is an attack in the model
  composed with them. This step is argued in prose, not stated in Lean.
* Row 6 uses the standard independence heuristic for coefficients of polynomial products
  and models `u` and `v` as uniform before compression, the same model as the Kyber team's
  script. It is not a proved bound.
* Row 9 models `G(· ‖ h)` as a uniformly random function of `m` for the fixed `h = H(ek)`.

## 3. SQIsign manifest

SQIsign's verifier trusts the quaternion side of the Deuring correspondence. The table
shows what is formal today.

| # | Property | Status | Where |
|---|---|---|---|
| S1 | `nrd` is multiplicative on any quaternion algebra | L | `Quaternion/ReducedNorm.lean` `nrd_mul` |
| S2 | `O₀ = ℤ⟨1, i, (i+j)/2, (1+k)/2⟩` is a subring of `B_{p,∞}` (p = 4m+3), with norm form `a²+ad+b²+bc+(m+1)(c²+d²)`, positive definite and integral | L | `Quaternion/MaximalOrderO0.lean` |
| S3 | Gram determinant −p², so disc(O₀) = p | L | `gram_det` |
| S4 | **`B_{p,∞}` is a division algebra**: `nrd` is positive definite and every `x ≠ 0` is a unit with inverse `x̄ / nrd x` (needed for every ideal-equivalence step `I ↦ I ᾱ / nrd I`) | L (new) | `Quaternion/Division.lean` `nrd_bp_pos`, `bp_isUnit` |
| S5 | `ι² = −1` and `π ∘ ι = −ι ∘ π` on `E₀ : y² = x³ + x` | L | `Quaternion/E0Maps.lean` |
| S6 | O₀ is maximal (disc = disc(B) ⇒ maximal; Voight Thm 15.5.5) | open | needs discriminants of orders in Mathlib |
| S7 | Deuring: `deg φ_I = nrd(I)`, `End(E₀) ≅ O₀` | open | needs an isogeny layer (no elliptic-curve isogenies in Mathlib) |
| S8 | Kani's lemma (2D/HD verification: the (2ᵉ,2ᵉ)-isogeny of E × E′ embedding the response) | open | needs abelian surfaces and polarisations |
| S9 | Σ-protocol special soundness and HVZK; EUF-CMA from the One-Endomorphism problem | open; A | SQIsign round-2 specification |

## 4. Next obligations, in order

1. **FO IND-CCA in the ROM** (row 12, classical first): oracle adversaries with query
   counting over the `pr` kernel, giving the HHK17 `U^⊥̸` bound `Adv ≤ 2·Adv_CPA + q_G·δ + …`
   with the plaintext-checking and decryption-failure terms written out.
2. **Hybrid combiner** (§1 item 3): IND-CCA if either component KEM is, in the ROM.
3. **Compression as post-processing**: state in Lean the corollary of row 7 for
   `Compress_du × Compress_dv` (the formal composition is a one-line instance of
   `CPAAdversary`).
4. **S6**: maximality from the discriminant, once orders and discriminants are in place.
5. **Bind to code**: the `velu` ML-KEM implementation cites rows 1 to 9 per function, and
   its KAT/ACVP tests close the gap between the Lean spec and the bytes.

## 5. Reproduce

```bash
lake build CryptoLean.PQ CryptoLean.Quaternion.Division
lake env lean --run tools/AuditAxioms.lean CryptoLean.PQ CryptoLean.Quaternion.Division
python3 docs/pq-kem-20261125/failure_prob.py
```

Audit result (2026-11-25): 44 theorems in the new modules, 0 failing, all within
`propext`, `Classical.choice` and `Quot.sound`; no `sorry`, no `native_decide`.
Failure-probability script output:

```
set           log2 P[coef]  log2 delta (union)  FIPS 203
ML-KEM-512          -146.8              -138.8    -138.8
ML-KEM-768          -172.8              -164.8    -164.8
ML-KEM-1024         -182.8              -174.8    -174.8
```
