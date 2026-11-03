# 4. Iwasawa theory and $p$-adic BSD

## 4.1 Cyclotomic main conjecture

Let $p$ be a prime of good ordinary reduction, $\Lambda=\mathbf{Z}_p[[T]]$,
$X_\infty$ the Pontryagin dual of $\operatorname{Sel}_{p^\infty}(E/\mathbf{Q}_\infty)$
over the cyclotomic $\mathbf{Z}_p$-extension (Mazur1972), and $L_p(E,T)\in\Lambda$
the Mazur–Swinnerton-Dyer / Mazur–Tate–Teitelbaum $p$-adic $L$-function
(MazurTateTeitelbaum1986). The main conjecture says
$\operatorname{char}_\Lambda X_\infty=(L_p(E,T))$.

* Kato2004: $X_\infty$ is $\Lambda$-torsion and $\operatorname{char}X_\infty\supseteq(L_p)$
  up to powers of $p$ (integrally, when the image of $G_\mathbf{Q}$ on $T_pE$ contains $\mathrm{SL}_2(\mathbf{Z}_p)$).
* SkinnerUrban2014: the opposite divisibility for $p\ge3$, $E[p]$ irreducible and
  a ramification hypothesis; Wan2015, Skinner2016 (multiplicative), BurungaleCastellaSkinner2024
  (ramification hypothesis removed).
* Supersingular $p$: signed main conjectures of Kobayashi2003 (and Pollack2003,
  Sprung2012 for $a_p\neq0$); one divisibility from Kato; Wan, Castella–Çiperiani–Skinner–Sprung,
  Sprung (odd supersingular); Kobayashi's conjecture for semistable curves in BSTW2024.
* CM curves: Rubin1991 (two-variable main conjecture over $K$).

## 4.2 From the main conjecture to BSD

Schneider1985 and PerrinRiou1993 relate the order of vanishing and the
leading coefficient of $\operatorname{char}X_\infty$ at $T=0$ to the
Selmer corank, the $p$-adic height regulator $\operatorname{Reg}_p$ and
$\#Ш[p^\infty]$. Consequences:

* **Finiteness of $Ш[p^\infty]$ in any rank (one-sided).** One always has
  $\operatorname{ord}_{T=0}\operatorname{char}X_\infty\ge\operatorname{corank}\operatorname{Sel}_{p^\infty}(E/\mathbf{Q})$
  (Schneider, Perrin-Riou), and Kato's divisibility gives
  $\operatorname{ord}_{T=0}\operatorname{char}X_\infty\le\operatorname{ord}_{T=0}L_p(E,T)$.
  So if a computation shows $\operatorname{ord}_{T=0}L_p(E,T)=r_{\mathrm{alg}}$ (the
  $r$-th coefficient is non-zero), then $\operatorname{corank}\operatorname{Sel}_{p^\infty}=r_{\mathrm{alg}}$
  and $Ш(E/\mathbf{Q})[p^\infty]$ is finite, in any rank. With the $p$-adic regulator
  $\operatorname{Reg}_p$ and the leading coefficient one also bounds $\#Ш[p^\infty]$,
  and often proves $Ш[p^\infty]=0$. This is the method of SteinWuthrich2013 (see §6)
  and of BalakrishnanMullerStein2016.
* **$p$-adic BSD.** MazurTateTeitelbaum1986: $\operatorname{ord}_{T=0}L_p=r$ and
  $L_p^*=\epsilon_p\operatorname{Reg}_p\#Ш\prod c_\ell/\#\mathrm{tors}^2$ with the Euler factor
  $\epsilon_p=(1-\alpha^{-1})^2$, plus an extra zero and the $\mathcal{L}$-invariant for split
  multiplicative $p$ (GreenbergStevens1993). Known consequences of the main conjecture
  for $p$-adic BSD are surveyed in Greenberg1999 and BurungaleSkinnerTian2021.

## 4.3 Anticyclotomic theory and Heegner points

* BertoliniDarmon2005: anticyclotomic main conjecture in the definite case, one divisibility.
* Perrin-Riou's Heegner point main conjecture: BurungaleCastellaKim2021.
* BertoliniDarmonPrasanna2013: $p$-adic Rankin $L$-function whose value is the
  $p$-adic logarithm of a Heegner point (BDP formula); used in most recent converse theorems.
* Kolyvagin's conjecture (non-vanishing of the Kolyvagin system): Zhang2014 under hypotheses;
  BCGS2023 for good ordinary $p$ split in $K$; refined form with Tamagawa factors.
* Two-variable zeta elements over imaginary quadratic fields: BSTW2024.

## 4.4 $p$-adic Gross–Zagier formulas

PerrinRiou1987 (ordinary), Kobayashi2013 (supersingular), Disegni2017
(Shimura curves), and the exceptional-zero formula of Venerucci2016.
