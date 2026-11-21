#set document(title: "ECDLP across a prime conductor gap")
#set page(paper: "a4", margin: 2.2cm, numbering: "1")
#set text(size: 10.5pt)
#set par(justify: true)
#set heading(numbering: "1.1")
#set math.equation(numbering: none)

#let thm(kind, name, body) = block(width: 100%, inset: (y: 4pt))[
  *#kind* #if name != none [(#name)]. #emph(body)
]
#let src(t) = text(size: 9pt, fill: rgb("#444"))[\[#t\]]
#let lean(t) = text(size: 9pt, fill: rgb("#0a5"))[\[Lean: #raw(t)\]]

#align(center)[
  #text(size: 15pt, weight: "bold")[ECDLP on the floor and the crater of an isogeny volcano\ across a prime conductor gap]

  #v(4pt)
  Technical note with machine-checked algebra, isogeny-labs, 21 November 2026 (draft for expert review)
]

#v(6pt)
*Abstract.* Let $E$ be an ordinary elliptic curve over $FF_p$ with Frobenius
discriminant $t^2 - 4p = f^2 d_K$, and let $N$ be a prime dividing $f$. The
$FF_p$-isogeny class of $E$ splits into the curves whose endomorphism ring
has conductor prime to $N$ (the crater side of the $N$-volcano) and those
whose conductor is divisible by $N$ (the floor side). We record precise
statements, with complete proofs, of what does and does not differ between the
two sides for the elliptic curve discrete logarithm problem (ECDLP). (i) Every
$FF_p$-isogeny from level $0$ to level $k$ of the $N$-volcano has degree
divisible by $N^k$. (ii) $E[N] subset.eq E(FF_p)$ if and only if $N divides f slash c$
and $t equiv 2 med (mod N)$; in particular floor curves always have cyclic
$E(FF_p)[N]$. (iii) If $N$ also divides $\#E(FF_p)$ then $N | p - 1$,
$t equiv 2 med (mod N)$ and $N^2 | \#E(FF_p)$, so such an $N$ is never a
"cryptographic" subgroup order and its DLP has embedding degree one on every
curve of the class. (iv) For a prime $n$ with $n | \#E$ and $n^2 divides.not \#E$,
$n divides.not f$, and any two curves of the class are joined by an
$FF_p$-isogeny of degree prime to $n p$; along it the ECDLP in the order-$n$
subgroup transfers in both directions with the answer preserved. Hence there
is no ECDLP hardness gap between floor and crater beyond the cost of
computing a connecting isogeny, which is the subject of [Gal99, JMV05, Gal25].
All algebraic steps are verified in Lean 4 / Mathlib; the remaining inputs are
standard facts about elliptic curves, each stated as an explicit hypothesis
and cited.

= Setting, conventions and what is machine-checked

Throughout, $p > 3$ is prime, $E slash FF_p$ is ordinary with trace $t$ and
Frobenius endomorphism $pi$, so $p divides.not t$ and
$Delta_pi = t^2 - 4p < 0$. Write $Delta_pi = f^2 d_K$ with $d_K$ a fundamental
discriminant, $K = QQ(sqrt(d_K))$ and $cal(O)_K = ZZ[omega]$ with
$omega^2 = a + b omega$ ($a, b in ZZ$). For $c in ZZ$ let
$ cal(O)_c = ZZ[c omega] = { x + y omega : c | y } $
(`conductorOrder c` in Lean; for $c >= 1$ this is the order of conductor $c$).
Then $ZZ[pi] = cal(O)_f$ and, writing $pi = x_0 + f omega$, every curve in the
isogeny class has the same $t$, $f$, $d_K$.

For a prime $N$ and $h = v_N (f) >= 1$, the $N$-*volcano* of the class has
levels $0, dots, h$; a curve with $"End"(E) tilde.equiv cal(O)_c$ is on level
$v_N (c)$, the *crater* is level $0$ and the *floor* is level $h$. "Large prime
conductor gap" means $h >= 1$ for a large prime $N$; most statements are for
general $h$.

*Labels.* #lean("name") marks a statement proved in Lean 4 (v4.35.0, Mathlib
`cfc55fc`) in `aburan28/crypto-lean`, modules `CryptoLean.Curve.ConductorGap`
and `CryptoLean.Curve.ConductorGapBridges`; every such declaration depends only
on `propext`, `Classical.choice`, `Quot.sound` (proof-gate receipt in
`docs/receipts/ConductorGap20261121/`, 281 theorems, 0 trusted). #src("F_i")
marks one of the standard facts below, which Mathlib does not yet contain
(it has Weierstrass curves and their point groups but no isogenies or
endomorphism rings); in Lean they appear as hypotheses of the theorems that
use them. Pinpoint references (theorem numbers) are given to the best of
our knowledge and should be checked against the editions cited.

== Standard facts used (not formalized)

/ F1 (Deuring, Waterhouse): $"End"(E)$ is an order of $K$ containing $ZZ[pi]$, and all endomorphisms of an ordinary $E$ are defined over $FF_p$ #src("Sil09, III.9.4; Wat69, Ch. 4").
/ F2 (normalized embedding): there is a unique ring embedding $iota_E : "End"(E) arrow.r.hook cal(O)_K$ with $iota_E (pi_E) = pi$; for $FF_p$-isogenous $E, E'$ use the same $pi in cal(O)_K$.
/ F3 (duals): an $FF_p$-isogeny $phi : E -> E'$ of degree $d$ has a dual $hat(phi)$ with $hat(phi) phi = [d]_E$, $phi hat(phi) = [d]_(E')$, defined over $FF_p$, and $phi compose pi_E = pi_(E') compose phi$ because $phi$ is defined over $FF_p$ #src("Sil09, III.6.1").
/ F4 (factorization): for $N != p$ ($[N]$ separable), if $psi : E -> E$ is an isogeny and $E[N] subset.eq ker psi$, then $psi = lambda compose [N]$ for an endomorphism $lambda$ #src("Sil09, III.4.11").
/ F5 (torsion): $E[N] tilde.equiv (ZZ slash N)^2$ for $N != p$ #src("Sil09, III.6.4").
/ F6 (Tate): $FF_p$-isogenous curves have the same $\#E(FF_p) = p + 1 - t$ #src("Tat66").
/ F7 (volcano structure): if $ell | c$ is prime, $E$ has an $FF_p$-rational $ell$-isogeny to a curve with endomorphism ring $cal(O)_(c slash ell)$ (the ascending edge) #src("Koh96, Ch. 4; FM02; Sut13, §2").
/ F8 (CM torsor): the $FF_p$-isomorphism classes of curves with trace $t$ and endomorphism ring $cal(O)$ form a principal homogeneous space under $"Pic"(cal(O))$; an invertible integral ideal $frak(a)$ gives an $FF_p$-isogeny $E -> frak(a) * E$ of degree $N(frak(a))$ #src("Wat69, §5; Sch87, §4").
/ F9 (ideals prime to $M$): every class of $"Pic"(cal(O))$ contains an invertible integral ideal of norm prime to any given $M != 0$ #src("Cox13, Cor. 7.17").

= The order lattice and Kohel's degree lemma

#thm("Lemma 2.1", [order classification], [Every subring $S$ of $cal(O)_K = ZZ[omega]$ with $cal(O)_f subset.eq S$ equals $cal(O)_c$ for some $c | f$.]) #lean("subring_eq_conductorOrder")

_Proof._ The imaginary parts of $S$ form an ideal $(c)$ of $ZZ$. Then
$S subset.eq cal(O)_c$. Conversely, take $s in S$ with $"im" s = c$; for
$z$ with $"im" z = c k$, $z - k s in ZZ subset.eq S$. Finally
$f omega in S$ gives $c | f$. #h(1fr) $square$

With F1 and F2, $iota_E ("End" E) = cal(O)_c$ for a unique $c | f$, $c >= 1$:
the conductor $c(E)$.

#thm("Lemma 2.2", [conjugation multiplies by the degree], [Let $cal(C)$ be a preadditive category, $phi : X -> Y$, $psi : Y -> X$ where composites are written in diagrammatic order ($psi ; phi$ means first $psi$, then $phi$), with $psi ; phi = d dot bb(1)_Y$, $pi in "End" X$, $pi' in "End" Y$ with $pi ; phi = phi ; pi'$, and suppose that for every $alpha in "End" X$ there are $m != 0$, $u, v in ZZ$ with $m alpha = u + v pi$. Let $iota : "End" X -> cal(O)_K$, $iota' : "End" Y -> cal(O)_K$ be additive with $iota(bb(1)) = iota'(bb(1)) = 1$ and $iota(pi) = iota'(pi') = pi_K$. Then $iota'(psi ; alpha ; phi) = d dot iota(alpha)$ for all $alpha$.]) #lean("hom_conj_eq_smul")

_Proof._ $psi ; (u + v pi) ; phi = u (psi ; phi) + v (psi ; phi ; pi') = d(u + v pi')$,
so $m iota'(psi ; alpha ; phi) = d(u + v pi_K) = m d iota(alpha)$; cancel $m$
in the torsion-free group $cal(O)_K$. #h(1fr) $square$

The hypotheses hold for elliptic curves over $FF_p$ and $FF_p$-isogenies by
F1–F3 ($m = [cal(O)_c : ZZ[pi]] = f slash c$ works for every $alpha$).

#thm("Theorem 2.3", [Kohel's degree lemma], [Let $phi : E -> E'$ be an $FF_p$-isogeny of degree $d$, $c = c(E)$, $c' = c(E')$. Then $d cal(O)_c subset.eq cal(O)_(c')$, $d cal(O)_(c') subset.eq cal(O)_c$, equivalently $c' | d c$ and $c | d c'$. If $N$ is prime, $N^k | c'$ and $N divides.not c$, then $N^k | d$.]) #lean("kohel_smul_le, smul_conductorOrder_le_iff, prime_pow_dvd_degree_of_gap, gap_prime_dvd_isogeny_degree")

_Proof._ Lemma 2.2 with $X = E$, $Y = E'$, $psi = hat(phi)$ (so $psi ; phi = phi compose hat(phi) = [d]_(E')$), and the same
argument with $(hat(phi), phi)$ in place of $(phi, hat(phi))$. $d cal(O)_c subset.eq cal(O)_(c')$ iff
$c' | d c$ (test on $c omega$). If $N^k | c' | d c$ and $gcd(N, c) = 1$ then
$N^k | d$. #h(1fr) $square$

This is [Koh96, Ch. 4]; the proof is recorded because the Lean statement
makes all of its inputs explicit. Consequently every $FF_p$-isogeny from the
crater to level $k$ of the $N$-volcano has degree divisible by $N^k$.

= Rational $N$-torsion: what separates floor from crater

#thm("Lemma 3.1", none, [For $N != p$: $E[N] subset.eq E(FF_p)$ iff $pi - 1 in N dot "End"(E)$.])

_Proof._ If $pi - 1 = N lambda$ then $(pi - 1)(E[N]) = lambda(N E[N]) = 0$.
Conversely $E(FF_p) = ker(pi - 1)$ and $pi - 1 != 0$, so F4 gives
$pi - 1 = lambda compose [N]$ with $lambda in "End"(E)$. #h(1fr) $square$

Write $cal(O)_c = ZZ[omega_c]$, $omega_c = c omega$,
$omega_c^2 = c^2 a + c b omega_c$ (`orderEmbed`, `range_orderEmbed`), and
$pi = x + e omega_c$ with $e = f slash c$. Then $"tr" pi = t = 2x + c b e$.

#thm("Theorem 3.2", [floor/crater torsion], [Let $N$ be an odd prime, $N | f$, and $E$ a curve with conductor $c$, $e = f slash c$.
1. $E[N] subset.eq E(FF_p)$ iff $N | e$ and $x equiv 1 med (mod N)$.
2. *Floor* ($v_N (c) = v_N (f)$, i.e. $N divides.not e$): $E[N] subset.eq.not E(FF_p)$, so $E(FF_p)[N]$ is cyclic (of order $1$ or $N$).
3. *Above the floor* ($N | e$; in particular the crater when $N | f$): $t equiv 2x med (mod N)$, and $E[N] subset.eq E(FF_p)$ iff $t equiv 2 med (mod N)$; for the quadratic twist, iff $t equiv -2$. If $t equiv.not plus.minus 2$, neither $E$ nor its twist has full rational $N$-torsion.]) #lean("sub_one_mem_smul_iff, floor_not_full, crater_full_iff, crater_trace_congr")

_Proof._ (1) Lemma 3.1 and $(x - 1) + e omega_c in N cal(O)_c$ iff
$N | x - 1$ and $N | e$. (2) By (1); a subgroup of $E[N] tilde.equiv (ZZ slash N)^2$
(F5) that is not all of it is cyclic. (3) $t - 2x = c b e equiv 0$; $N$ odd. The
twist has Frobenius $-pi$, trace $-t$. #h(1fr) $square$

*Remark 3.3 (module structure).* With Lenstra's theorem
$E[N] tilde.equiv cal(O)_c slash N cal(O)_c$ as $cal(O)_c$-modules [Len96],
the algebra gives more: above the floor $pi$ acts on $E[N]$ as the scalar
$x equiv t slash 2$, so its eigenspace is all $N^2$ points
#lean("frobenius_scalar_iff, frobenius_eigen_card_full, scalar_trace_congr, crater_side_full");
on the floor every eigenspace of $pi$ on $E[N]$ has at most $N$ points
#lean("frobenius_eigen_card_le, floor_side_line"). Theorem 3.2 does not need this.

#thm("Theorem 3.4", [the gap prime as a subgroup order], [If $t^2 - 4p = D f^2$, $N$ is an odd prime with $N | f$ and $N | \#E(FF_p) = p + 1 - t$, then $N | p - 1$, $t equiv 2 med (mod N)$ and $N^2 | \#E(FF_p)$.]) #lean("gap_prime_dvd_order")

_Proof._ $t equiv p + 1$ gives $(p - 1)^2 equiv t^2 - 4p equiv 0$, so
$N | p - 1$ and $t equiv 2$. Then $4 \#E = (t - 2)^2 - D f^2 equiv 0 med (mod N^2)$
and $N$ is odd. #h(1fr) $square$

So a gap prime is a subgroup order only with embedding degree $1$, where the
Frey–Rück/Tate pairing maps the DLP in $E(FF_p)[N]$ into $mu_N subset FF_p^*$
[FR94]; this holds on *every* curve of the class, floor and crater alike
(F6). Moreover $N^2 | \#E$ forces $N <= sqrt(\#E) < sqrt(p) + 1$.

= Transfer of the ECDLP across the gap

#thm("Corollary 4.1", [cryptographic subgroups avoid the conductor], [If $n$ is an odd prime with $n | \#E(FF_p)$ and $n^2 divides.not \#E(FF_p)$ (e.g. $n > sqrt(\#E)$), then $n divides.not f$. Hence $n$ divides no conductor $c(E')$ and is different from every gap prime.]) #lean("dlp_prime_not_dvd_conductor")

#thm("Theorem 4.2", [transfer], [Let $phi : G -> H$, $psi : H -> G$ be homomorphisms of abelian groups with $psi compose phi = [d]$, and $P in G$ of order $n$ with $gcd(d, n) = 1$. Then $phi(P)$ has order $n$, and for $Q in chevron.l P chevron.r$ and $k in ZZ$: $phi(Q) = k phi(P) arrow.r.double Q = k P$. The same holds for a chain $phi_r compose dots.c compose phi_1$ with duals of degrees $d_i$ prime to $n$.]) #lean("dlog_transfer, addOrderOf_map_eq, dual_comp, dlog_transfer_comp")

Applied to $G = E(FF_p)$, $H = E'(FF_p)$ (Mathlib's `WeierstrassCurve.Affine.Point`
groups; instance probe `InstanceProbe.lean`) and an $FF_p$-isogeny with its
dual (F3), any algorithm for the ECDLP in the order-$n$ subgroup of $E'$
solves it on $E$ with overhead two evaluations of $phi$, whatever the
algorithm (generic or not).

#thm("Theorem 4.3", [connecting isogenies of degree prime to $n$], [Let $n$ be as in Corollary 4.1, $n != p$. For any two curves $E, E'$ in the $FF_p$-isogeny class there is an $FF_p$-isogeny $E -> E'$ of degree prime to $n p$. Consequently the ECDLP in the order-$n$ subgroups of $E$ and $E'$ are mutually reducible, with the same answer, at the cost of evaluating that isogeny and its dual chain.])

_Proof._ Let $c = c(E)$, $c' = c(E')$; both divide $f$ (Lemma 2.1), so all
their prime factors are prime to $n$ (Corollary 4.1) and to $p$ ($p divides.not f$
since $p divides.not Delta_pi$ for ordinary $E$). By F7, ascending edges give
$FF_p$-isogenies $E -> E_0$ of degree $c$ and $E' -> E'_0$ of degree $c'$ with
$"End"(E_0) tilde.equiv "End"(E'_0) tilde.equiv cal(O)_K$. By F8 and F9,
$E'_0 tilde.equiv frak(a) * E_0$ with $N(frak(a))$ prime to $n p$, giving
$E_0 -> E'_0$ of that degree; compose with the dual of $E' -> E'_0$ (degree $c'$, F3).
The total degree $c N(frak(a)) c'$ is prime to $n p$. Theorem 4.2 for the chain
gives the reductions. #h(1fr) $square$

#thm("Corollary 4.4", [no floor/crater ECDLP gap], [Let $N$ be a prime with $v_N (f) >= 1$, $E$ on the crater and $E'$ on the floor of the $N$-volcano, and $n$ as in Corollary 4.1. Then: (a) $\#E(FF_p) = \#E'(FF_p)$, both order-$n$ subgroups are cyclic of order $n$, and the embedding degree $"ord"_n (p)$ and anomalousness coincide, so every attack whose applicability and cost depend only on $(p, \#E, n)$ — Pohlig–Hellman on the $n$-part, MOV/Frey–Rück, Smart–Satoh–Araki–Semaev, and generic algorithms with the $Omega(sqrt(n))$ lower bound of [Sho97] — is identical; (b) for every algorithm $A'$ on $E'$ there is $A$ on $E$ with $T_A <= T_(A') + 2 C(phi)$, and conversely, where $phi$ is a connecting isogeny of degree prime to $n$ (Theorem 4.3), which necessarily has degree divisible by $N^(v_N (f))$ when it goes directly from crater to floor (Theorem 2.3); (c) the two sides differ, as groups, only in their $N$-primary parts (Theorem 3.2), which are coprime to $n$.])

_Proof._ (a) F6; $n^2 > \#E$ or $n^2 divides.not \#E$ makes the $n$-part
cyclic of order $n$; $"ord"_n (p)$ depends on $n, p$ only. (b) Theorems 4.2,
4.3 and 2.3. (c) Theorem 3.2 and Corollary 4.1. #h(1fr) $square$

*What is not claimed.* Theorem 4.3 asserts existence; it says nothing about
the cost of *finding* or *evaluating* a connecting isogeny. For two given
curves of an ordinary isogeny class, [Gal25] (Research in Number Theory 11,
2025; ePrint 2024/924) gives, by its abstract, a rigorous $tilde(O)(q^(1 slash 4))$
algorithm to compute an isogeny between any two curves of the class for flat
volcanoes and for tall volcanoes with crater of constant or polynomial size,
and a heuristic $tilde(O)(q^(0.4))$ general bound, improving [Gal99]; see also
[JMV05]. Combined with Corollary 4.4(b), the best ECDLP costs on floor and
crater curves differ by at most that amount plus the cost of evaluating the
isogeny it returns on two points, which is $o(sqrt(q))$. Whether a
weakness held by a positive fraction of floor curves could be kept from a
*given* crater curve faster than this (the setting of [KKM11]) is not
addressed here. A particular implementation's constant (e.g. a hashed rho
walk) is an empirical question; the lab's measurement on a $52$-bit class
with $N = 631409$ found the floor/crater ratio of mean counted cost
$0.9958$ (95% CI $[0.966, 1.026]$).

= Independent exact check

`check_gap.py` (deterministic, no dependencies) enumerates, for every prime
$p <= 1500$, all ordinary $FF_p$-isogeny classes with $d_K in.not {-3, -4}$ and
every odd prime $N$ with $N parallel f$ and $N | \#E$, and counts
$\#E(FF_p)[N]$ by brute force on every curve (one model per $j$-invariant).
Predictions: Theorem 3.4 on every class; $\#E(FF_p)[N] in {N, N^2}$ on every
curve (Theorems 3.2, 3.4); and the class-number relation
$\#{"floor"} = (N - (d_K slash N)) dot \#{"crater"}$ between curves with cyclic and with
full $N$-torsion. Result: 1,233/1,233 classes and 24,300/24,300 curves agree;
a negative control (the wrong relation $\#{"floor"} = N dot \#{"crater"}$) fails
on 144 of 171 classes with $p <= 400$ (the others have $(d_K slash N) = 0$).

= Errata to earlier internal notes

- The 2026-11-21 PR note stated that on the crater side "$E(FF_p)[N]$ or its twist's is all of $(ZZ slash N)^2$". This is true only when $t equiv plus.minus 2 med (mod N)$; Theorem 3.2(3) is the correct statement. (The 2026-10-22 class had $t equiv -2$, where the statement holds for the twist.)
- Earlier Lean transfer statements used structures without group laws; Theorem 4.2 replaces them with statements over abelian groups and Mathlib's point groups.

= References

#set text(size: 9.5pt)
/ [Cox13]: D. A. Cox, _Primes of the form $x^2 + n y^2$_, 2nd ed., Wiley, 2013.
/ [FM02]: M. Fouquet, F. Morain, Isogeny volcanoes and the SEA algorithm, ANTS-V, LNCS 2369, 2002.
/ [FR94]: G. Frey, H.-G. Rück, A remark concerning $m$-divisibility and the discrete logarithm in the divisor class group of curves, Math. Comp. 62 (1994).
/ [Gal99]: S. D. Galbraith, Constructing isogenies between elliptic curves over finite fields, LMS J. Comput. Math. 2 (1999).
/ [Gal25]: S. D. Galbraith, Climbing and descending tall isogeny volcanos, Research in Number Theory 11, no. 7 (2025); extended version IACR ePrint 2024/924.
/ [JMV05]: D. Jao, S. D. Miller, R. Venkatesan, Do all elliptic curves of the same order have the same difficulty of discrete log?, ASIACRYPT 2005.
/ [KKM11]: A. H. Koblitz, N. Koblitz, A. Menezes, Elliptic curve cryptography: the serpentine course of a paradigm shift, J. Number Theory 131 (2011).
/ [Koh96]: D. Kohel, Endomorphism rings of elliptic curves over finite fields, PhD thesis, UC Berkeley, 1996.
/ [Len96]: H. W. Lenstra Jr., Complex multiplication structure of elliptic curves, J. Number Theory 56 (1996).
/ [Sch87]: R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987).
/ [Sho97]: V. Shoup, Lower bounds for discrete logarithms and related problems, EUROCRYPT 1997.
/ [Sil09]: J. H. Silverman, _The Arithmetic of Elliptic Curves_, 2nd ed., GTM 106, Springer, 2009.
/ [Sut13]: A. V. Sutherland, Isogeny volcanoes, ANTS-X, Open Book Series 1 (2013).
/ [Tat66]: J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966).
/ [Wat69]: W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. ÉNS 2 (1969).
