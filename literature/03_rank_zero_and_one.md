# 3. Analytic rank zero and one: what is proved

Throughout, $E/\mathbf{Q}$ is an elliptic curve (modular by
BreuilConradDiamondTaylor2001).

## 3.1 Rank and finiteness

**Theorem (Gross–Zagier, Kolyvagin; GrossZagier1986, Kolyvagin1989, Kolyvagin1990, with BumpFriedbergHoffstein1990, MurtyMurty1991).**
If $r_{\mathrm{an}}(E)\le1$ then $r_{\mathrm{alg}}(E)=r_{\mathrm{an}}(E)$ and
$Ш(E/\mathbf{Q})$ is finite.

Proof outline. Choose an imaginary quadratic field $K$ satisfying the Heegner
hypothesis such that the twist $E^K$ has analytic rank $1-r_{\mathrm{an}}(E)$
(possible by Bump–Friedberg–Hoffstein / Murty–Murty / Waldspurger). Then
$\operatorname{ord}_{s=1}L(E/K,s)=1$, and by Gross–Zagier the Heegner point
$y_K\in E(K)$ has non-zero height. Kolyvagin's Euler system of Heegner points
over ring class fields bounds the Selmer group of $E/K$ by the index of
$y_K$; projecting to the $\pm$ eigenspaces gives the theorem. Expositions:
Gross1991, Darmon2004, Rubin2000, MazurRubin2004.

Earlier and independent routes in rank 0: Coates–Wiles and Rubin for CM curves
(CoatesWiles1977, Rubin1987); Kato's Euler system (Kato2004) gives
$L(E,1)\ne0\Rightarrow E(\mathbf{Q})$ and $Ш[p^\infty]$ finite for suitable $p$.

## 3.2 Converse theorems

The converse direction ("Selmer corank $r\le1$ ⇒ analytic rank $r$") is known
for one prime $p$ at a time, under hypotheses that have been steadily removed.

| Statement | Hypotheses (abbreviated) | Keys |
|---|---|---|
| corank $\operatorname{Sel}_{p^\infty}=0$ ⇒ $L(E,1)\ne0$ | $p$ good ordinary, $E[p]$ irreducible with ramification condition (SU); without the ramification condition (BCS 2024) | SkinnerUrban2014, BurungaleCastellaSkinner2024 |
| corank $=1$ and $Ш[p^\infty]$ finite ⇒ $r_{\mathrm{an}}=1$ | $p$ good ordinary, $E[p]$ surjective plus conditions | Zhang2014, Skinner2020 |
| same, multiplicative $p$ | $p>3$ multiplicative | SkinnerZhang2014, Castella2018, Castella2024, Venerucci2016 |
| same, CM curves | $p$ split or inert in the CM field, various | BurungaleTian2020, BurungaleTian2025 |
| same, supersingular $p$ | semistable $E$, $p$ supersingular | BSTW2024 |
| Eisenstein primes ($E[p]$ reducible) | $p$ good ordinary, $p$ Eisenstein | CastellaGrossiLeeSkinner2022, KellerYin2024 |

A pointwise converse at every prime $p$ with no hypotheses is not in the refereed
literature; it is among the unrefereed 2026 claims
([11_unrefereed_claims_2026.md](11_unrefereed_claims_2026.md)).

## 3.3 The $p$-part of the formula

For $r_{\mathrm{an}}\le1$, $Ш$ is finite and $L^{(r)}(E,1)/(r!\,\Omega_E\operatorname{Reg})\in\mathbf{Q}^\times$
(rationality: Gross–Zagier and Manin–Drinfeld), so full BSD is the
statement that for every prime $p$ the $p$-adic valuations agree.

| Range | Proved for | Keys |
|---|---|---|
| $r_{\mathrm{an}}=0$, CM | $p\nmid\#\mathcal{O}_K^\times$ (Rubin); all $p$ including 2 and 3 when $\mathbf{Q}(E_{\mathrm{tors}})/K$ is abelian (Burungale–Flach) | Rubin1991, BurungaleFlach2024 |
| $r_{\mathrm{an}}=0$, non-CM | $p\ge3$ good ordinary, $E[p]$ irreducible (+ ramification, removed in BCS 2024); multiplicative $p$ (Skinner 2016); supersingular semistable (BSTW 2024) | SkinnerUrban2014, Skinner2016, BurungaleCastellaSkinner2024, BSTW2024 |
| $r_{\mathrm{an}}=1$, CM | $p$ potentially good ordinary, $p\nmid\#\mathcal{O}_K^\times$ | LiLiuTian2016 |
| $r_{\mathrm{an}}=1$, non-CM | odd good $p$, semistable $E$, $E[p]$ irreducible, with further conditions (JSW); multiplicative (Castella); without ramification hypotheses and supersingular (BCS, BSTW) | JetchevSkinnerWan2017, Castella2018, BurungaleCastellaSkinner2024, BSTW2024 |
| $p=2$ | Special families only (e.g. congruent number and cube-sum curves via 2- and 3-descent together with Tian–Yuan–Zhang type explicit Gross–Zagier); no general theorem in the refereed literature | Tian2014, TianYuanZhang2017, CoatesLiTianZhai2015 |

**Consequences.**

* BSTW2024 exhibits the first infinite families of non-CM elliptic curves over
  $\mathbf{Q}$ for which the full BSD conjecture is proved.
* Computationally, full BSD is verified curve by curve: all curves of conductor
  $<5000$ of rank $\le1$ (Miller2011, CreutzMiller2012, building on GJPST2009);
  the method combines the theorems above for $p\ge3$ (or $p\ge5$) with explicit
  2- and 3-descents and Heegner-index or Kolyvagin bounds (Cha2005, Jetchev2008).

## 3.4 What is still missing in rank $\le1$ (refereed literature)

* The 2-part (and in some reduction types the 3-part) of the formula for
  general curves.
* Primes $p$ of additive reduction, in general.
* Hence: full BSD is not known for every curve of analytic rank $\le1$, although
  it is known for very many explicit curves and for infinite families.
