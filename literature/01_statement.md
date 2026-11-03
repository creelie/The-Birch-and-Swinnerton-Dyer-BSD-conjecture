# 1. The conjecture

## 1.1 Setting

Let $E/\mathbf{Q}$ be an elliptic curve with conductor $N$ and global minimal
Weierstrass model with Néron differential $\omega$. The Hasse–Weil
$L$-function

$$L(E,s)=\prod_{p\nmid N}\bigl(1-a_pp^{-s}+p^{1-2s}\bigr)^{-1}\prod_{p\mid N}\bigl(1-a_pp^{-s}\bigr)^{-1},\qquad a_p=p+1-\#E(\mathbf{F}_p),$$

converges for $\operatorname{Re}s>3/2$. By modularity
(Wiles1995, TaylorWiles1995, BreuilConradDiamondTaylor2001) it is the
$L$-function of a weight-two newform of level $N$, so it continues to an
entire function and satisfies $\Lambda(E,s)=w_E\Lambda(E,2-s)$ with
$\Lambda(E,s)=N^{s/2}(2\pi)^{-s}\Gamma(s)L(E,s)$ and root number $w_E=\pm1$.

The Mordell–Weil theorem gives $E(\mathbf{Q})\cong\mathbf{Z}^{r}\oplus E(\mathbf{Q})_{\mathrm{tors}}$.
Put $r_{\mathrm{an}}=\operatorname{ord}_{s=1}L(E,s)$, the analytic rank, and
$r=r_{\mathrm{alg}}$, the algebraic rank.

## 1.2 Statement

**Conjecture (Birch and Swinnerton-Dyer; BirchSwinnertonDyer1963, BirchSwinnertonDyer1965, Tate1966).**

1. (Rank part, "weak BSD".) $r_{\mathrm{an}}=r_{\mathrm{alg}}$.
2. (Finiteness.) The Tate–Shafarevich group
   $Ш(E/\mathbf{Q})=\ker\bigl(H^1(\mathbf{Q},E)\to\prod_vH^1(\mathbf{Q}_v,E)\bigr)$ is finite.
3. (Leading term, "strong BSD".) With $r=r_{\mathrm{an}}$,

$$\frac{L^{(r)}(E,1)}{r!}=\frac{\Omega_E\cdot\operatorname{Reg}(E/\mathbf{Q})\cdot\#Ш(E/\mathbf{Q})\cdot\prod_{p\mid N}c_p}{\#E(\mathbf{Q})_{\mathrm{tors}}^2}.$$

Here $\Omega_E=\int_{E(\mathbf{R})}|\omega|$ (both real components counted),
$c_p=[E(\mathbf{Q}_p):E_0(\mathbf{Q}_p)]$ are the Tamagawa numbers, and
$\operatorname{Reg}$ is the determinant of the Néron–Tate height pairing on a
basis of $E(\mathbf{Q})/E(\mathbf{Q})_{\mathrm{tors}}$ (normalisation: the
canonical height with $\hat h(P)\approx\log|x(P)|$; with the other common
normalisation $\hat h$ is halved and the regulator changes by $2^{-r}$).

The Clay Mathematics Institute's official problem description is Wiles2006.
It states the rank equality as the problem and records the full leading-term
formula as the refined form of the conjecture.

## 1.3 Standard reformulations

* **$p$-part.** For a prime $p$, "the $p$-part of the BSD formula" means:
  $r_{\mathrm{an}}=r_{\mathrm{alg}}$, $Ш(E/\mathbf{Q})[p^\infty]$ is finite, and
  the two sides of the formula have the same $p$-adic valuation when
  $\#Ш$ is replaced by $\#Ш[p^\infty]$. Full BSD for $E$ in rank $\le1$ is
  equivalent to the $p$-part for every $p$, since in that range
  $Ш$ is known to be finite and the ratio $L^{(r)}(E,1)/(r!\,\Omega_E\operatorname{Reg})$
  is known to be rational (Gross–Zagier and Kolyvagin; see §3).
* **Selmer corank.** $\operatorname{corank}_{\mathbf{Z}_p}\operatorname{Sel}_{p^\infty}(E/\mathbf{Q})=r_{\mathrm{alg}}+\operatorname{corank}Ш[p^\infty]$.
  So finiteness of $Ш[p^\infty]$ is equivalent to "Selmer corank = Mordell–Weil rank".
* **Parity.** The functional equation gives $(-1)^{r_{\mathrm{an}}}=w_E$, so the
  conjecture predicts $(-1)^{r_{\mathrm{alg}}}=w_E$ (parity conjecture). The
  $p$-Selmer version, $(-1)^{\operatorname{corank}\operatorname{Sel}_{p^\infty}}=w_E$, is a theorem
  for all $p$ (DokchitserDokchitser2010, building on Nekovář, Kim, Monsky1996).
* **Isogeny invariance.** The quotient $\#Ш\cdot\operatorname{Reg}\cdot\prod c_p\cdot\Omega/\#\mathrm{tors}^2$
  is an isogeny invariant (Cassels1965), so the formula holds for $E$ if and only if
  it holds for any curve isogenous to $E$.
* **Cassels–Tate pairing.** If $Ш$ is finite, its order is a square (Cassels1962, Tate1966).

## 1.4 Variants and generalisations (details in [08_generalisations.md](08_generalisations.md))

* Abelian varieties over number fields (Tate1966; Bloch1980 reformulates with Tamagawa numbers).
* Function fields of curves over finite fields (Tate1966, Milne1975, KatoTrihan2003): here
  the rank part implies everything else.
* $p$-adic analogues: MazurTateTeitelbaum1986 (good ordinary and multiplicative $p$,
  with the exceptional-zero $\mathcal{L}$-invariant), BertoliniDarmon/Bernardi–Perrin-Riou
  and Pollack2003, Sprung2012, Kobayashi2003 at supersingular primes.
* Twists by Artin representations (DarmonRotger2017) and the equivariant
  Tamagawa number conjecture; motives in general: Bloch–Kato (BlochKato1990).
