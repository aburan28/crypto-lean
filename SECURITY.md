<!--
Canonical security, disclosure and acceptable-use policy for isogeny-labs
repositories (action plan F4, docs/strategy/2026-11-21-action-plan.md).
Copy it into a repository as SECURITY.md, then fill the two marked sections.
Owner actions before the first copy merges:
  1. enable GitHub private vulnerability reporting on each public repository
     (Settings > Code security > Private vulnerability reporting);
  2. create the security@isogenylabs.io mailbox, or replace the address below.
This is a policy draft, not legal advice. Counsel reviews it with F6 and F9.
-->

# Security policy

## Reporting a vulnerability

Please report security problems privately. Do not open a public issue.

- **GitHub:** use "Report a vulnerability" on this repository's Security tab.
- **Email:** security@isogenylabs.io

Tell us what you found, how to reproduce it, and what you think the impact
is. We confirm receipt within 3 business days and tell you what we will do
within 10 business days. Our default is coordinated disclosure after
90 days, or sooner once a fix is released. We credit reporters who want to be
credited.

We will not pursue legal action against good-faith research that stays
within this policy: it avoids privacy violations, data destruction and
service disruption, uses only accounts and data you own or are authorised
to use, and gives us reasonable time to respond before anything is made
public.

## What this repository is, and what it is not

CryptoLean is a Lean 4 library of definitions and machine-checked proofs
about elliptic curves, their twists and torsion, finite-field polynomials,
Semaev's summation polynomial and the counting bounds behind the lab's
discrete-log research, together with the proof gate that audits each
theorem's axioms (`tools/proof-gate.sh`). It is a mathematics library: it
contains no executable attack, recovers no keys, touches no network and
handles no secrets. A security problem here most likely means a proof gate
that accepts an unsound proof (an unlisted axiom, `sorry` or
`native_decide` that the audit misses); please report that privately too.

## Acceptable use

Some code here implements published cryptanalytic techniques: attacks on
weak parameters, key recovery from flawed signatures or leakage, and network
probes that read how a system negotiates cryptography. We publish it for
research, education, and defensive assessment.

- Use it only on systems, keys, signatures and data that you own, or that
  you have written authorisation to test.
- Do not use it to obtain anyone else's keys, funds, messages or data, or to
  get into systems you are not authorised to access.
- Network probes complete ordinary handshakes and read what the server
  offers. Do not point them at networks you do not operate or have
  permission to assess, and respect the target's rate limits.
- If you recover key material that is not yours, stop. Do not use it or
  share it; report it privately as above.

## How Isogeny Labs runs client engagements

When we assess a client's systems, these rules hold whatever the contract
says on top of them:

1. **Written authorisation first.** No active test starts before a signed
   authorisation that names the systems, the adversary model, what counts as
   a finding, the testing window and the client's emergency contact.
2. **Public data by default.** We analyse public material (signatures, public
   keys, certificates, handshakes) unless the client agrees in writing to
   provide more.
3. **Recovered key material.** If an analysis recovers a private key or
   other secret, we tell the client's named contact at once through the
   agreed secure channel. We never store it in plaintext, never put it in a
   repository, ticket, report or log, and delete it at the end of the
   engagement, confirming the deletion in writing.
4. **Evidence, not exploitation.** We show a finding with the smallest proof
   that establishes it: a verified result, a test, a signed evidence record.
   We do not use it beyond that.
5. **Third parties.** A weakness found in someone else's product is reported
   to that vendor under coordinated disclosure (90 days by default), with
   the client's agreement where the client's data was involved.

## Ethics

We build attacks so that their cost is measured rather than guessed, and so
that weak deployments are found by their owners first. We do not sell attack
capability, target individuals, or take work whose purpose is to defeat
security that people rely on without their owner's consent.

## Components with dual-use capability

No component attacks a system, recovers keys or probes networks.

| Path | What it does | Intended use | Safeguards |
|:--|:--|:--|:--|
| `CryptoLean/`, `CryptoLeanCore/` | States and proves facts about curve structure that cryptanalysis relies on (twists, torsion, Semaev's S₃, relation-count bounds) | Checking the mathematics behind published measurements and research notes | Proofs only; no algorithm here runs against a key or a target |
| `tools/proof-gate.sh`, `tools/AuditAxioms.lean`, `tools/selftest/` | Builds every Lean target and audits each theorem's transitive axioms | Making a proof claim checkable by someone who did not write it | Only `propext`, `Classical.choice` and `Quot.sound` pass; the self-test must reject each failure fixture for the expected reason |
