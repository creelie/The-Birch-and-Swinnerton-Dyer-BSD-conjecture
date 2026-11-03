# 8. Generalisations

## 8.1 Abelian varieties over number fields

Tate1966 states the conjecture for an abelian variety $A$ over a number field $K$:

$$\frac{L^{(r)}(A/K,1)}{r!}=\frac{\#Ш(A/K)\,\Omega_A\,R_A\,\prod_v c_v}{\#A(K)_{\mathrm{tors}}\,\#A^\vee(K)_{\mathrm{tors}}}\cdot(\text{discriminant factor}),$$

with $r=\operatorname{rank}A(K)$. Known cases:

* Modular abelian varieties $A_f$ of $\mathrm{GL}_2$-type over $\mathbf Q$ with analytic rank
  $\le1$: rank equality and finiteness of $Ш$ by Gross–Zagier–Kolyvagin–Logachev
  (see Gross1991). Visible-$Ш$ evidence: AgasheStein2005.
* Modular abelian surfaces (GSp$_4$): LoefflerZerbes2021 prove rank-0 cases of BSD (finiteness
  of $A(\mathbf Q)$ and of $Ш[p^\infty]$ for many $p$) via an Euler system for GSp$_4$.
* Exact verification of the full (strong) formula for individual abelian surfaces:
  KellerStoll2022, KellerStoll2025 (all modular abelian surfaces of a large class over
  $\mathbf Q$); numerical verification for Jacobians of hyperelliptic curves: vanBommel2022;
  strong BSD in genus 2 code: repository `TimoKellerMath/strongBSDgenus2`.

## 8.2 Function fields

Over a global function field $K=\mathbf F_q(C)$ the analogue is much better understood
(Tate1966, Milne1975, KatoTrihan2003):

* $\operatorname{ord}_{s=1}L(A,s)\ge\operatorname{rank}A(K)$ always;
* equality holds iff $Ш(A/K)[\ell^\infty]$ is finite for one prime $\ell$ (any $\ell$, including
  $\ell=p$ by KatoTrihan2003), and then the full formula holds;
* for an elliptic surface this is equivalent to the Tate conjecture for the surface (Tate
  conjecture for divisors), known for many classes, e.g. rational and K3 elliptic surfaces.

Unbounded ranks over $\mathbf F_p(t)$ with BSD proved: Ulmer2002. Higher derivatives:
YunZhang2017 express the $r$-th Taylor coefficient of an $L$-function over a function field
as an intersection number of Heegner–Drinfeld cycles on moduli of shtukas, a function-field
analogue of Gross–Zagier in every order of vanishing.

## 8.3 Motives: Bloch–Kato and Beilinson

* Bloch1980 recast the formula through height pairings and Tamagawa numbers.
* BlochKato1990: the Tamagawa number conjecture for motives, of which BSD is the case
  $h^1(E)(1)$; Fontaine–Perrin-Riou and Kato's equivariant refinements follow.
* KimPollack2025: a refined BSD-type formula for Bloch–Kato Selmer groups of modular forms
  via Kolyvagin derivatives, determining rank and module structure at ordinary $p\ge3$ with
  large image, in every analytic rank (conditional on a localised main conjecture).
* Nekovar2006: Selmer complexes, the framework for the Iwasawa and parity results.

## 8.4 Heegner cycles, Shimura curves, triple products

* Zhang1997 (Heegner cycles, higher weight), Zhang2001 (Shimura curves),
  YuanZhangZhang2013 (the Gross–Zagier formula in full generality on Shimura curves).
* DarmonRotger2017: BSD in analytic rank 0 for elliptic curves twisted by two-dimensional odd
  Artin representations (diagonal cycles, Euler systems).
* Darmon2004 surveys Heegner points, Stark–Heegner points and the conjectural constructions
  beyond analytic rank one.

## 8.5 Number fields other than $\mathbf Q$

Over totally real fields the GZK theorem holds for modular curves under a Jacquet–Langlands
hypothesis (Zhang2001, YuanZhangZhang2013). Over imaginary quadratic fields even modularity was
open until recently; an unrefereed OpenAI preprint (October 2026) claims modularity of every
elliptic curve over an imaginary quadratic field (see chapter 11).
