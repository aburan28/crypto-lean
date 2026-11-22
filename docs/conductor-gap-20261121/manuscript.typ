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
discriminant $t^2 - 4p = f^2 d_K$, and let $N$ be an odd prime dividing $f$,
$h = v_N (f)$. The $FF_p$-isogeny class of $E$ is stratified by the
$N$-volcano: curves whose endomorphism ring has conductor $c$ with
$v_N (c) = 0$ form the crater, those with $v_N (c) = h$ the floor. We give precise
statements, with complete proofs, of what does and does not differ between
floor and crater for the elliptic curve discrete logarithm problem (ECDLP).
(i) An $FF_p$-isogeny between curves on levels $k$ and $k'$ has degree divisible
by $N^(|k - k'|)$. (ii) $E[N] subset.eq E(FF_p)$ iff $E$ is above the floor and
$t equiv 2 med (mod N)$; floor curves always have cyclic $E(FF_p)[N]$; more
generally the groups $E(FF_p)$ in the class differ only at primes dividing $f$.
(iii) If $N$ also divides $\#E(FF_p)$ then $N | p - 1$, $t equiv 2 med (mod N)$ and
$N^2 | \#E(FF_p)$. (iv) For an odd prime $n$ with $n parallel \#E(FF_p)$ we have
$n divides.not f$, and any two curves of the class are joined by an $FF_p$-isogeny
of degree prime to $n p$, along which the ECDLP in the order-$n$ subgroup
transfers in both directions with the answer preserved. Consequently, for such
$n$, floor and crater are equally hard up to the cost of computing and
evaluating a connecting isogeny (a non-uniform reduction); bounding that
cost is the subject of [Gal99, JMV05, Gal25, GGR25] and is not addressed here.
The order-theoretic and group-theoretic steps marked [Lean] are verified in
Lean 4 / Mathlib; Lemma 3.1 and Proposition 3.4 are proved on paper only; the
inputs about elliptic curves (F1–F10 below) are standard, stated as explicit
hypotheses and cited.

= Setting, conventions and what is machine-checked

Throughout, $p > 3$ is prime, $E slash FF_p$ is ordinary with trace $t$ and
Frobenius endomorphism $pi$, so $p divides.not t$ and
$Delta_pi = t^2 - 4p < 0$. Write $Delta_pi = f^2 d_K$ with $d_K$ a fundamental
discriminant, $K = QQ(sqrt(d_K))$ and $cal(O)_K = ZZ[omega]$ with
$omega^2 = a + b omega$ ($a, b in ZZ$). For $c in ZZ$ let
$ cal(O)_c = ZZ[c omega] = { x + y omega : c | y } $
(`conductorOrder c` in Lean; for $c >= 1$ this is the order of conductor $c$).
Then $d_K = b^2 + 4a$, $ZZ[pi] = cal(O)_f$, and after replacing $omega$ by its conjugate if necessary
$pi = x_0 + f omega$ with $f >= 1$; every curve in the isogeny class has the same $t$, $f$, $d_K$.

For a prime $N$ and $h = v_N (f) >= 1$, the $N$-isogeny graph of the class is a
union of $N$-volcanoes (one family for each $N$-free part of the conductor).
We define the *level* of a curve with $"End"(E) tilde.equiv cal(O)_c$ as $v_N (c) in {0, dots, h}$;
the *crater* side is level $0$ and the *floor* is level $h$. "Large prime
conductor gap" means $h >= 1$ for a large prime $N$; most statements are for
general $h$.

*Labels.* #lean("name") marks a statement proved in Lean 4 (v4.35.0, Mathlib
`cfc55fc`) in `aburan28/crypto-lean`, modules `CryptoLean.Curve.ConductorGap`
and `CryptoLean.Curve.ConductorGapBridges`; every such declaration depends only
on `propext`, `Classical.choice`, `Quot.sound` (library-wide proof-gate receipt in
`docs/receipts/ConductorGap20261121/`: PASS, 0 trusted; the two modules contribute 42 theorems and 2 equation lemmas). #src("F_i")
marks one of the standard facts below, which Mathlib does not yet contain
(it has Weierstrass curves and their point groups but no isogenies or
endomorphism rings); in Lean they appear as hypotheses of the theorems that
use them.

== Standard facts used (not formalized)

/ F1 (Deuring, Waterhouse): $"End"(E)$ is an order of $K$ containing $ZZ[pi]$ #src("Wat69, Thm. 4.2; Sil09, III.9.4"); since it is commutative, every endomorphism commutes with $pi$ and is therefore defined over $FF_p$.
/ F2 (normalized embedding): there is a unique ring embedding $iota_E : "End"(E) arrow.r.hook cal(O)_K$ with $iota_E (pi_E) = pi$; for $FF_p$-isogenous $E, E'$ use the same $pi in cal(O)_K$.
/ F3 (duals): an $FF_p$-isogeny $phi : E -> E'$ of degree $d$ has a dual $hat(phi)$ with $hat(phi) phi = [d]_E$ #src("Sil09, III.6.1") and $phi hat(phi) = [d]_(E')$ #src("Sil09, III.6.2(a)"); $phi pi_E = pi_(E') phi$ because $phi$ is defined over $FF_p$; then $(hat(phi) pi_(E') - pi_E hat(phi)) phi = hat(phi) phi pi_E - pi_E hat(phi) phi = 0$, so $hat(phi) pi_(E') = pi_E hat(phi)$ (as $phi$ is surjective on $overline(FF)_p$-points) and $hat(phi)$ is defined over $FF_p$.
/ F4 (factorization): for $N != p$ ($[N]$ separable), if $psi : E -> E$ is an isogeny and $E[N] subset.eq ker psi$, then $psi = lambda compose [N]$ for an endomorphism $lambda$ #src("Sil09, III.4.11").
/ F5 (torsion): $E[N] tilde.equiv (ZZ slash N)^2$ for $N != p$ #src("Sil09, III.6.4(b)").
/ F6 (equal point counts): $FF_p$-isogenous curves have the same $\#E(FF_p) = p + 1 - t$: from $phi (1 - pi_E) = (1 - pi_(E')) phi$ and multiplicativity of degrees, $deg(1 - pi_E) = deg(1 - pi_(E'))$, and $\#E(FF_p) = deg(1 - pi_E)$ since $1 - pi_E$ is separable #src("Sil09, III.5.5"). (The converse is Tate's theorem [Tat66].)
/ F7 (volcano structure): if $ell | c$ is prime, $E$ has an $FF_p$-rational $ell$-isogeny to a curve with endomorphism ring $cal(O)_(c slash ell)$ (the ascending edge) #src("Koh96, Ch. 4; FM02; Sut13, §2").
/ F8 (CM torsor): the $FF_p$-isomorphism classes of curves with trace $t$ and endomorphism ring $cal(O)$ form a principal homogeneous space under $"Pic"(cal(O))$; an invertible integral ideal $frak(a)$ gives an $FF_p$-isogeny $E -> frak(a) * E$ of degree $"Nm"(frak(a))$ #src("Wat69, §5; Sch87, §4").
/ F9 (ideals prime to $M$): every class of $"Pic"(cal(O))$ contains an invertible integral ideal of norm prime to any given $M != 0$ #src("Cox13, Cor. 7.17").
/ F10 (Lenstra): $E(FF_p) tilde.equiv "End"(E) slash (pi - 1)"End"(E)$ as $"End"(E)$-modules #src("Len96, Thm. 1").

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

#thm("Theorem 2.3", [Kohel's degree lemma], [Let $phi : E -> E'$ be an $FF_p$-isogeny of degree $d$, $c = c(E)$, $c' = c(E')$. Then $d cal(O)_c subset.eq cal(O)_(c')$, $d cal(O)_(c') subset.eq cal(O)_c$, equivalently $c' | d c$ and $c | d c'$. Hence $|v_N (c) - v_N (c')| <= v_N (d)$ for every prime $N$; in particular $N^k | c'$, $N divides.not c$ imply $N^k | d$.]) #lean("kohel_smul_le, smul_conductorOrder_le_iff, level_difference_le_degree, prime_pow_dvd_degree_of_gap, gap_prime_dvd_isogeny_degree")

_Proof._ Lemma 2.2 with $X = E$, $Y = E'$, $psi = hat(phi)$ (so $psi ; phi = phi compose hat(phi) = [d]_(E')$), and the same
argument with $(hat(phi), phi)$ in place of $(phi, hat(phi))$. $d cal(O)_c subset.eq cal(O)_(c')$ iff
$c' | d c$ (test on $c omega$). If $N^k | c' | d c$ and $gcd(N, c) = 1$ then
$N^k | d$; in general $v_N (c') <= v_N (d) + v_N (c)$ and symmetrically. #h(1fr) $square$

This is [Koh96, Ch. 4]; the proof is recorded because the Lean statement
makes all of its inputs explicit. Consequently every $FF_p$-isogeny between levels $k$ and $k'$ of the
$N$-volcano has degree divisible by $N^(|k - k'|)$.

= Rational $N$-torsion: what separates floor from crater

#thm("Lemma 3.1", none, [For a prime $N != p$: $E[N] subset.eq E(FF_p)$ iff $pi - 1 in N dot "End"(E)$.])

_Proof._ If $pi - 1 = N lambda$ then $(pi - 1)(E[N]) = lambda(N E[N]) = 0$.
Conversely $E(FF_p) = ker(pi - 1)$ and $pi - 1 != 0$, so F4 gives
$pi - 1 = lambda compose [N]$ with $lambda in "End"(E)$. #h(1fr) $square$

Write $cal(O)_c = ZZ[omega_c]$, $omega_c = c omega$,
$omega_c^2 = c^2 a + c b omega_c$ (`orderEmbed`, `range_orderEmbed`), and
$pi = x + e omega_c$ with $e = f slash c$. Then $"tr" pi = t = 2x + c b e$.

#thm("Theorem 3.2", [floor/crater torsion], [Let $N$ be an odd prime, $N | f$ (so $N != p$, as $p divides.not f$), and $E$ a curve with conductor $c$, $e = f slash c$.
1. $E[N] subset.eq E(FF_p)$ iff $N | e$ and $x equiv 1 med (mod N)$.
2. *Floor* ($v_N (c) = v_N (f)$, i.e. $N divides.not e$): $E[N] subset.eq.not E(FF_p)$, so $E(FF_p)[N]$ is cyclic (of order $1$ or $N$).
3. *Above the floor* ($N | e$, any level $< h$; in particular the crater): $t equiv 2x med (mod N)$, and $E[N] subset.eq E(FF_p)$ iff $t equiv 2 med (mod N)$; for the quadratic twist, iff $t equiv -2$. If $t equiv.not plus.minus 2$, neither $E$ nor its twist has full rational $N$-torsion.]) #lean("algebraic criterion only: sub_one_mem_smul_iff, sub_one_mem_smul_conductorOrder_iff, floor_not_full_of_not_dvd, above_floor_full_iff, crater_trace_congr")

_Proof._ (1) Lemma 3.1 and $(x - 1) + e omega_c in N cal(O)_c$ iff
$N | x - 1$ and $N | e$. (2) By (1); a subgroup of $E[N] tilde.equiv (ZZ slash N)^2$
(F5) that is not all of it is cyclic. (3) $t - 2x = c b e equiv 0$; $N$ odd. The
twist has Frobenius $-pi$, trace $-t$. #h(1fr) $square$

The link between the level of a curve and its rational $ell$-power torsion is
classical (it follows from F10 [Len96]) and is used to compute volcano heights
and to walk volcanoes [MMSTV08, IJ13]; Theorem 3.2 is recorded here for its
formal proof and its exact hypotheses.

*Remark 3.3 (module structure).* Applying F10 over $FF_(p^k)$ with $E[N] subset.eq E(FF_(p^k))$
(Frobenius $pi^k$) gives $E[N] tilde.equiv cal(O)_c slash N cal(O)_c$ as $cal(O)_c$-modules [Len96]. With this,
the algebra gives more: above the floor $pi$ acts on $E[N]$ as the scalar
$x equiv t slash 2$, so its eigenspace is all $N^2$ points
#lean("frobenius_scalar_iff, frobenius_eigen_card_full, scalar_trace_congr, crater_side_full");
on the floor every eigenspace of $pi$ on $E[N]$ has at most $N$ points
#lean("frobenius_eigen_card_le"). Theorem 3.2 does not need this. (`crater_side_full` and `floor_side_line` are the special cases $v_N (c) = 0$ and $h = 1$.)

#thm("Proposition 3.4", [group structure by level], [Let $pi = x + e omega_c$ in $cal(O)_c$ and $g = gcd(x - 1, e)$. Then $E(FF_p) tilde.equiv ZZ slash g times ZZ slash (\#E(FF_p) slash g)$. In particular, for a prime $ell$, the $ell$-primary parts of $E(FF_p)$ and $E'(FF_p)$ for two curves of the class can differ only if $ell | f$.])

This is classical: by [Len96], $E(FF_p) tilde.equiv ZZ slash n_1 times ZZ slash n_2$ with $n_1$ the largest
integer such that $(pi - 1) slash n_1 in "End"(E)$; see also [MMSTV08, IJ13]. We record the
explicit form and a proof.

_Proof._ By F10, $E(FF_p) tilde.equiv cal(O)_c slash (pi - 1) cal(O)_c$ as groups. Write
$cal(O)_c = ZZ[omega_c]$, $omega_c^2 = A + B omega_c$, and $pi - 1 = g beta$ with
$beta = u + v omega_c$, $gcd(u, v) = 1$, so $\#E = "Nm"(pi - 1) = g^2 "Nm"(beta)$.
(1) $cal(O)_c slash beta cal(O)_c$ is cyclic of order $"Nm"(beta)$: $"Nm"(beta) = beta overline(beta) in beta cal(O)_c$ and
$gcd(v, "Nm"(beta)) = gcd(v, u^2) = 1$, so from $v omega_c equiv -u med (mod beta)$ we get
$omega_c equiv -u v^(-1)$ modulo $beta$; hence $ZZ$ surjects onto the quotient,
whose order is the index $"Nm"(beta)$ of $beta cal(O)_c$.
(2) In $G = cal(O)_c slash g beta cal(O)_c$ the class of $1$ has order $g "Nm"(beta)$: an integer
$m$ lies in $g beta cal(O)_c$ iff $g | m$ and $m slash g in beta cal(O)_c inter ZZ = "Nm"(beta) ZZ$ by (1).
(3) $G slash g G = cal(O)_c slash g cal(O)_c tilde.equiv (ZZ slash g)^2$, so in
$G tilde.equiv ZZ slash m_1 times ZZ slash m_2$ ($m_1 | m_2$) we have $g | m_1$. With
$m_2 >= g "Nm"(beta)$ from (2) and $m_1 m_2 = g^2 "Nm"(beta)$ this forces $m_1 = g$,
$m_2 = \#E slash g$. Finally $g | e = f slash c$ and $c | f$, so every prime
dividing $g$ divides $f$; the second invariant is $\#E slash g$ on every curve. #h(1fr) $square$

*Example 3.5 (the groups really differ away from $N$).* $p = 1531$,
$t = -43$, $d_K = -19$ ($a = -5$, $b = 1$), $f = 15$, $\#E = 1575 = 3^2 dot 5^2 dot 7$.
On the crater ($c = 1$, $x = -29$, $e = 15$, $g = 15$) Proposition 3.4 gives
$ZZ slash 15 times ZZ slash 105$; on the common floor of the $3$- and $5$-volcanoes
($c = 15$, $e = 1$) it gives $ZZ slash 1575$. Brute force on $j = 182$ and $j = 51$
confirms both. Floor and crater of the $3$-volcano thus differ also in their
$5$-primary parts; all differences are at primes dividing $f$, hence prime to
any $n$ as in Corollary 4.1.

#thm("Theorem 3.6", [the gap prime as a subgroup order], [If $t^2 - 4p = D f^2$, $N$ is an odd prime with $N | f$ and $N | \#E(FF_p) = p + 1 - t$, then $N | p - 1$, $t equiv 2 med (mod N)$ and $N^2 | \#E(FF_p)$.]) #lean("gap_prime_dvd_order")

_Proof._ $t equiv p + 1$ gives $(p - 1)^2 equiv t^2 - 4p equiv 0$, so
$N | p - 1$ and $t equiv 2$. Then $4 \#E = (t - 2)^2 - D f^2 equiv 0 med (mod N^2)$
and $N$ is odd. #h(1fr) $square$

So a gap prime is a subgroup order only with embedding degree $1$. Since
$N | p - 1$, the Tate pairing $E(FF_p)[N] times E(FF_p) slash N E(FF_p) -> mu_N$ is
non-degenerate [FR94], which reduces the DLP in $E(FF_p)[N]$ to $mu_N subset FF_p^*$
also on the floor, where the $N$-part is cyclic of order $N^k$, $k >= 2$; this
holds on every curve of the class (F6). In any case $N^2 | \#E$ forces
$N^2 <= \#E <= (sqrt(p) + 1)^2$, i.e. $N <= sqrt(p) + 1$, so this DLP is also easy by generic means.

= Transfer of the ECDLP across the gap

#thm("Corollary 4.1", [cryptographic subgroups avoid the conductor], [If $n$ is an odd prime with $n | \#E(FF_p)$ and $n^2 divides.not \#E(FF_p)$ (e.g. $n > sqrt(\#E)$), then $n divides.not f$. Hence $n$ divides no conductor $c(E')$ and is different from every gap prime.]) #lean("dlp_prime_not_dvd_conductor")

#thm("Theorem 4.2", [transfer], [Let $phi : G -> H$, $psi : H -> G$ be homomorphisms of abelian groups with $psi compose phi = [d]$, and $P in G$ of order $n$ with $gcd(d, n) = 1$. Then $phi(P)$ has order $n$, and for $Q in chevron.l P chevron.r$ and $k in ZZ$: $phi(Q) = k phi(P) arrow.r.double Q = k P$. The same holds for a chain $phi_r compose dots.c compose phi_1$ with duals of degrees $d_i$ prime to $n$, since maps with duals of degree $d_i$ compose to a map with a dual of degree $product d_i$.]) #lean("dlog_transfer, addOrderOf_map_eq, HasDual.comp, HasDual.id, dlog_transfer_of_hasDual, addOrderOf_map_eq_of_hasDual")

Transferring ECDLP instances along isogenies is classical (e.g. [Gal99, JMV05, GHS02]).
Applied to $G = E(FF_p)$, $H = E'(FF_p)$ (Mathlib's `WeierstrassCurve.Affine.Point`
groups; instance probe `InstanceProbe.lean`) and an $FF_p$-isogeny with its
dual (F3), any algorithm for the ECDLP in the order-$n$ subgroup of $E'$
solves it on $E$ with overhead two evaluations of $phi$, whatever the
algorithm (generic or not).

#thm("Theorem 4.3", [connecting isogenies of degree prime to $n$], [Let $n$ be as in Corollary 4.1. For any two curves $E, E'$ in the $FF_p$-isogeny class there is an $FF_p$-isogeny $E -> E'$ of degree prime to $n p$. Consequently the ECDLP in the order-$n$ subgroups of $E$ and $E'$ are mutually reducible, with the same answer, at the cost of evaluating that isogeny and its dual chain.])

_Proof._ Let $c = c(E)$, $c' = c(E')$; both divide $f$ (Lemma 2.1), so all
their prime factors are prime to $n$ (Corollary 4.1) and to $p$ ($p divides.not f$
since $p divides.not Delta_pi$ for ordinary $E$). By F7, ascending edges give
$FF_p$-isogenies $E -> E_0$ of degree $c$ and $E' -> E'_0$ of degree $c'$ with
$"End"(E_0) tilde.equiv "End"(E'_0) tilde.equiv cal(O)_K$. By F8 and F9,
$E'_0 tilde.equiv frak(a) * E_0$ with $"Nm"(frak(a))$ prime to $n p$, giving
$E_0 -> E'_0$ of that degree; compose with the dual of $E' -> E'_0$ (degree $c'$, F3).
The total degree $c "Nm"(frak(a)) c'$ is prime to $n p$. Theorem 4.2 for the chain
gives the reductions. #h(1fr) $square$

#thm("Corollary 4.4", [no floor/crater ECDLP gap], [Let $N$ be a prime with $v_N (f) >= 1$, $E$ on the crater and $E'$ on the floor of the $N$-volcano, and $n$ as in Corollary 4.1. Then: (a) $\#E(FF_p) = \#E'(FF_p)$, both order-$n$ subgroups are cyclic of order $n$, and the embedding degree $"ord"_n (p)$ and anomalousness coincide, so every attack whose applicability and cost depend only on $(p, \#E, n)$ — Pohlig–Hellman on the $n$-part, MOV/Frey–Rück, Smart–Satoh–Araki–Semaev, and generic algorithms with the $Omega(sqrt(n))$ lower bound of [Sho97] — is identical; (b) for every algorithm $A'$ on $E'$ there is $A$ on $E$, given $phi$ as advice (a non-uniform reduction), with $T_A <= T_(A') + 2 C(phi)$ and the same success probability on uniformly random instances ($phi$ is a bijection between the order-$n$ subgroups), and conversely with $C(hat(phi))$ in place of $C(phi)$, where $phi$ is a connecting isogeny of degree prime to $n$ (Theorem 4.3); every $FF_p$-isogeny between $E$ and $E'$, composite or not, has degree divisible by $N^(v_N (f))$ (Theorem 2.3); (c) the groups $E(FF_p)$ and $E'(FF_p)$ differ only in their $ell$-primary parts for primes $ell | f$ (Proposition 3.4; not only at $ell = N$, see Example 3.5), all of which are prime to $n$.])

_Proof._ (a) F6; $n^2 > \#E$ or $n^2 divides.not \#E$ makes the $n$-part
cyclic of order $n$; $"ord"_n (p)$ depends on $n, p$ only. (b) Theorems 4.2,
4.3 and 2.3. (c) Proposition 3.4 and Corollary 4.1. #h(1fr) $square$

Nothing in Corollary 4.4 uses that $E$ is on the crater and $E'$ on the floor:
it holds for any two curves of the class. The floor/crater case is the one
where the connecting isogenies are forced to have large degree.

*Scope and what is not claimed.*
- The statements concern a prime $n$ with $n parallel \#E(FF_p)$. Theorem 4.3 asserts
  *existence* of a connecting isogeny. It says nothing about the cost of finding
  or evaluating one, and Corollary 4.4(b) is non-uniform: $phi$ is given to $A$.
- Moving between levels costs at least one $N$-isogeny step per level (Theorem 2.3:
  degree divisible by $N^h$ between crater and floor), and $N$ can be large:
  $N^2 | t^2 - 4p$ gives only $N <= 2 sqrt(p)$. Above the floor $pi$ acts on $E[N]$
  as the scalar $x equiv t slash 2$ (Remark 3.3), so every subgroup of order $N$ is
  $pi$-stable and all $N + 1$ $N$-isogenies are $FF_p$-rational, with kernel
  polynomials over $FF_p$; given a kernel polynomial, Kohel's formulas evaluate
  the isogeny in $O(N)$ operations in $FF_p$. The expensive part is *finding* the
  kernel: its points lie in $E[N] subset.eq E(FF_(p^k))$ with $k = "ord"_N (x)$, which may
  be as large as $N - 1$, and the alternative, factoring the modular polynomial
  $Phi_N$, is out of reach for $N$ of cryptographic interest. When
  $t equiv plus.minus 2 med (mod N)$ the kernel points are rational on $E$ or its twist,
  and the whole step costs $O(N)$ (the lab's 52-bit class is of this kind).
  For large $N$ this cost can be comparable to $sqrt(n)$.
- For two given curves of an ordinary isogeny class, [Gal25] gives (according to
  its abstract) a rigorous $tilde(O)(q^(1 slash 4))$ algorithm to compute an isogeny
  between any two curves of the class for flat volcanoes and for tall volcanoes
  with crater of constant or polynomial size, and heuristically $tilde(O)(q^(0.4))$ in
  general, improving [Gal99]; [GGR25] improves ascending tall volcanoes. We do
  not restate their output representation or its evaluation cost. A uniform
  "no gap" statement for given floor and crater curves therefore follows from
  Corollary 4.4 only to the extent that such an isogeny can be found *and
  evaluated* in time well below $sqrt(n)$; with a $q^(0.4)$ bound this requires
  roughly $n >> q^(0.8)$.
- [JMV05] proves random self-reducibility (under GRH) among curves with the
  *same* endomorphism ring, i.e. on one level of the volcano; it does not
  connect levels separated by a large prime $N$. That is exactly the gap
  considered here; the possibility that a weakness might be confined to
  curves beyond such a gap is discussed in [KKM11]. Corollary 4.4 shows that no such
  weakness can come from the group order, the order-$n$ subgroup, the embedding
  degree, or (via any isogeny of degree prime to $n$) from any algorithm applied
  to a curve on the other side; it does not bound the cost of reaching that curve.
- A particular implementation's constant (e.g. a hashed rho walk) is an
  empirical question. The lab measured, on a $52$-bit class with $N = 631409$, a
  floor/crater ratio of mean counted rho cost of $0.9958$ (95% CI $[0.966, 1.026]$);
  protocol and data: `isogeny-labs/crypto`, `research/deep_volcano_prime_gap_20261022/`.

= Independent exact check

`docs/checks/conductor-gap-20261121/check_gap.py` (deterministic, standard
library only), run as `python3 check_gap.py 5 1500`, enumerates for every prime
$p <= 1500$ all ordinary $FF_p$-isogeny classes with $d_K in.not {-3, -4}$ (both
$E$ and its twist for every $j != 0, 1728$; one model per $j$ is one
$FF_p$-isomorphism class of trace $t$, since $t != 0$), and every odd prime $N$
with $h = v_N (f) >= 1$ and $N | \#E$. It counts $\#E(FF_p)[N]$ by brute force on
every curve and tests:
(A) Theorem 3.6 on every class;
(C) Theorem 3.2 jointly with F8 and the class-number formula
$h(cal(O)_(c N^k)) = h(cal(O)_c) N^(k-1) (N - (d_K slash N))$, valid for $N divides.not c$,
$k >= 1$ and $cal(O)_c^times = cal(O)_(c N^k)^times = {plus.minus 1}$ (guaranteed by $d_K in.not {-3, -4}$), for
any height $h$: the numbers of curves with full rational $N$-torsion (levels $< h$)
and with cyclic $N$-torsion (level $h$) must satisfy
$\#"cyc" dot (1 + (N - chi)(N^(h-1) - 1) slash (N - 1)) = \#"full" dot N^(h-1) (N - chi)$, $chi = (d_K slash N)$.
Result: 1,324 (class, $N$) pairs over 1,316 distinct classes (heights $h = 1, 2, 3$:
1,233, 89 and 2 pairs), 26,339 curve checks; (A) and (C) hold in every case.
As a non-vacuity check, the false closed form $\#"cyc" = N^h dot \#"full"$
fails on all 1,070 pairs with $chi != 0$; this shows that (C) has content, not that
the check would detect every false variant of Theorem 3.2.

Limits of this check. (C) is an aggregate count per class, so compensating
per-curve errors are not excluded; levels are not computed independently of
torsion. $N | \#E$ forces $t equiv 2 med (mod N)$, so only that branch of
Theorem 3.2(3) is exercised: the twist branch is not tested independently (the
twist's own class has trace $-t equiv 2$), and the branch $t equiv.not plus.minus 2$ is trivially
true over $FF_p$ and not exercised. That $\#E(FF_p)[N] in {N, N^2}$ is automatic
(F5 and $N | \#E$). Theorems 2.3 and 4.3 are not tested. Example 3.5 is
reproduced by `check_example35.py` (output `example35.txt`).

#heading(numbering: none)[References]

#set text(size: 9.5pt)
/ [Cox13]: D. A. Cox, _Primes of the form $x^2 + n y^2$_, 2nd ed., Wiley, 2013.
/ [FM02]: M. Fouquet, F. Morain, Isogeny volcanoes and the SEA algorithm, ANTS-V, LNCS 2369, 2002.
/ [FR94]: G. Frey, H.-G. Rück, A remark concerning $m$-divisibility and the discrete logarithm in the divisor class group of curves, Math. Comp. 62 (1994).
/ [Gal99]: S. D. Galbraith, Constructing isogenies between elliptic curves over finite fields, LMS J. Comput. Math. 2 (1999).
/ [Gal25]: S. D. Galbraith, Climbing and descending tall isogeny volcanos, IACR ePrint 2024/924 (rev. 2025); the ePrint page lists publication in Research in Number Theory 11, no. 7 (2025), doi:10.1007/s40993-024-00586-7.
/ [GGR25]: S. D. Galbraith, V. Gilchrist, D. Robert, Improved algorithms for ascending isogeny volcanoes, and applications, LATINCRYPT 2025; IACR ePrint 2025/1243.
/ [GHS02]: S. D. Galbraith, F. Hess, N. P. Smart, Extending the GHS Weil descent attack, EUROCRYPT 2002.
/ [IJ13]: S. Ionica, A. Joux, Pairing the volcano, Math. Comp. 82 (2013).
/ [JMV05]: D. Jao, S. D. Miller, R. Venkatesan, Do all elliptic curves of the same order have the same difficulty of discrete log?, ASIACRYPT 2005.
/ [KKM11]: A. H. Koblitz, N. Koblitz, A. Menezes, Elliptic curve cryptography: the serpentine course of a paradigm shift, J. Number Theory 131 (2011).
/ [Koh96]: D. Kohel, Endomorphism rings of elliptic curves over finite fields, PhD thesis, UC Berkeley, 1996.
/ [Len96]: H. W. Lenstra Jr., Complex multiplication structure of elliptic curves, J. Number Theory 56 (1996).
/ [MMSTV08]: J. Miret, R. Moreno, D. Sadornil, J. Tena, M. Valls, Computing the height of volcanoes of $ell$-isogenies of elliptic curves over finite fields, Appl. Math. Comput. 196 (2008).
/ [Sch87]: R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987).
/ [Sho97]: V. Shoup, Lower bounds for discrete logarithms and related problems, EUROCRYPT 1997.
/ [Sil09]: J. H. Silverman, _The Arithmetic of Elliptic Curves_, 2nd ed., GTM 106, Springer, 2009.
/ [Sut13]: A. V. Sutherland, Isogeny volcanoes, ANTS-X, Open Book Series 1 (2013).
/ [Tat66]: J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966).
/ [Wat69]: W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. ÉNS 2 (1969).
