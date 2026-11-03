# 7. Computation, databases and software

## 7.1 Verification of the full formula for individual curves

| Work | Scope | Keys |
|---|---|---|
| Buhler–Gross–Zagier | rank 3 curve 5077a1: $r_{\mathrm{an}}=r_{\mathrm{alg}}=3$ | BuhlerGrossZagier1985 |
| Grigorov–Jorza–Patrikis–Stein–Tarniţă | conductor $\le1000$, rank $\le1$, $Ш$ bounded prime by prime; full BSD for most | GJPST2009 |
| Miller | conductor $<5000$, rank $\le1$, except a few curves | Miller2011 |
| Creutz–Miller | completes conductor $<5000$, rank $\le1$, via second isogeny descents | CreutzMiller2012 |
| Agashe–Stein | modular abelian varieties of rank 0, visible $Ш$ | AgasheStein2005 |
| Stein–Wuthrich | rank $\ge2$, conductor $\le30\,000$: $Ш[p]=0$ for good ordinary $5\le p<1000$ | SteinWuthrich2013 |
| Coates–Liang–Sujatha; Banwait | five rank-2 CM curves, $p<30\,000$ | CoatesLiangSujatha2010, Banwait2026 |
| van Bommel | hyperelliptic Jacobians of genus $\ge2$, numerically up to squares | vanBommel2022 |
| Keller–Stoll | strong BSD proved for many modular abelian surfaces over $\mathbf{Q}$ | KellerStoll2022, KellerStoll2025 |

Tools inside these verifications: Heegner-index bounds and Kolyvagin bounds
(Cha2005, Jetchev2008), explicit Heegner points and non-trivial $Ш$
(JetchevLauterStein2009), image of Galois (Serre1972, Mazur1978), $p$-adic
$L$-functions by modular symbols (PollackStevens2011, Wuthrich2018).

## 7.2 Databases

* **Cremona database** (CremonaEcdata): all elliptic curves over $\mathbf{Q}$ of conductor
  $<500\,000$ with ranks, generators, torsion, Tamagawa numbers, analytic $Ш$
  (`allbsd`), curves with large analytic $Ш$ (`allbigsha`), Iwasawa invariants
  (`iwasawa`, conductor $<150\,000$), Galois images. GitHub `JohnCremona/ecdata`.
* **LMFDB** (LMFDB): curves over $\mathbf{Q}$ (Cremona range and more), over number fields,
  with BSD invariants; GitHub `LMFDB/lmfdb`.
* **Stein–Watkins database** and curves ordered by height (BHKSSW2016).
* Rank records: Dujella's tables (Dujella).

## 7.3 Software

| Package | Relevant functions | Location |
|---|---|---|
| PARI/GP 2.17 (PARI) | `ellanalyticrank`, `ellbsd`, `ellrank` (2-descent), `ellsaturation`, `ellheegner`, `ellpadicL`, `ellpadicheight`, `ellpadicregulator`, `ellpadicbsd`, `elltamagawa`, `msinit` | pari.math.u-bordeaux.fr |
| SageMath | `E.sha().an()`, `E.sha().p_primary_bound()`, `E.padic_lseries(p)`, `E.prove_BSD()` (Miller's algorithm) | github.com/sagemath/sage |
| eclib (Cremona) | `mwrank` 2-descent, modular symbols | github.com/JohnCremona/eclib |
| Magma | 2-, 3-, 4-, 8-descent, `ThreeSelmerGroup`, `MordellWeilShaInformation` | commercial |
| Lean 4 / Mathlib | Weierstrass curves and the group law; no BSD statement yet | github.com/leanprover-community/mathlib4 |

A list of public GitHub repositories found by searching is in
[`../catalogue/github_repositories.md`](../catalogue/github_repositories.md).

## 7.4 A reproducible check in this repository

[`../checks/analytic_sha.py`](../checks/analytic_sha.py) computes, with PARI/GP,
the analytic order of $Ш$ for 11a1, 37a1, 389a1, 5077a1, 571a1, 681b1, 960d1 and
234446a1 (ranks 0 to 4). Output in [`../checks/analytic_sha.out`](../checks/analytic_sha.out):
$Ш_{\mathrm{an}}=1,1,1,1,4,9,4,1$ to ten decimal places. This is a numerical
check of the formula, not a proof.
