# Review notes for `manuscript.pdf` (internal; not part of the note)

## Review history

1. **Round 1** (independent reviewer agent, 2026-11-21). Found:
   - Corollary 4.4(c) false as stated. Counterexample `p = 1531, t = −43`:
     crater `ℤ/15 × ℤ/105`, floor `ℤ/1575`. Replaced by Proposition 3.4.
   - The "`o(√q)`" evaluation claim was unproved.
   - Height-one Lean lemmas were cited for statements at all heights.
   - The check script mislabelled its counts and listed a vacuous prediction.
   - Several citations needed fixing.

   All fixed. Added: Kohel's bound between arbitrary levels, floor and
   above-floor criteria at any height, the criterion stated inside `ℤ[ω]`,
   height ≥ 2 in the check, and the scope section.
2. **Round 2** (fresh reviewer agent). Confirmed:
   - Proposition 3.4 by brute force over 1,094 classes, including
     `d_K ∈ {−3, −4}`, with 0 mismatches.
   - Theorems 2.3, 3.2, 3.6 and 4.3, and the Section 5 numbers.

   Found:
   - The cost discussion wrongly said `N`-isogeny kernels are non-rational.
     They are `F_p`-rational above the floor; the cost is in finding them.
   - The abstract overclaimed what is in Lean.
   - "directly" in Corollary 4.4(b) was misleading.
   - The archive for Example 3.5 was missing.
   - Several imprecisions and citation issues.

   All fixed. Added `HasDual.comp` (chains of any length) and
   `check_example35.py`.

## Errata to earlier internal notes

- The 2026-11-21 proof-map note said the crater side always has full rational
  `N`-torsion on `E` or its twist. That holds only for `t ≡ ±2 (mod N)`
  (Theorem 3.2(3)).
- Earlier lab Lean (2026-10 studies) stated the transfer over structures
  without group laws. Theorem 4.2 replaces it.

## Not independently verified (check before external circulation)

- Pinpoints: Cox 2013 Cor. 7.17; Lenstra 1996 Thm. 1; Waterhouse 1969
  Thm. 4.2 and §5; Schoof 1987 §4; Silverman III.4.11, III.5.5, III.6.1,
  III.6.2(a), III.6.4(b), III.9.4; Kohel 1996 Ch. 4.
- [MMSTV08] bibliographic details. [KKM11] has no page pinpoint for the
  "weakness beyond a gap" discussion.
- The Gal25 journal details are taken from the IACR ePrint page: the Springer
  page needs a login.
- The rho measurement (0.9958, CI [0.966, 1.026]) lives in `isogeny-labs/crypto`
  and was not re-checked here.
- The library-wide proof-gate receipt's `source-target.log` contains an
  unrelated pre-existing message about `SelectorTree20261116/FloorProbe.lean`.
  It does not affect the audit (`audit.log`: 0 failing, 0 trusted).
