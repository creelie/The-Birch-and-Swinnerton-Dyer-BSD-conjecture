# 6. Rank two and higher: the frontier

For curves of analytic rank $\ge2$ the conjecture is far from known.

* **Rank equality.** For an individual curve of rank 2 or 3 the equality
  $r_{\mathrm{an}}=r_{\mathrm{alg}}$ can be proved: $r_{\mathrm{alg}}$ by descent, and
  $r_{\mathrm{an}}$ because the vanishing of the lower derivatives is exact (for rank 2,
  $L(E,1)=0$ is an exact modular-symbol computation; for rank 3, $L'(E,1)=0$ follows from
  Gross–Zagier and the vanishing of a Heegner point height, as for 5077a1 in
  BuhlerGrossZagier1985), while the next derivative is non-zero numerically. For rank $\ge4$
  no curve is known to have $r_{\mathrm{an}}\ge4$, since $L''(E,1)=0$ or $L'''(E,1)=0$
  cannot be certified.
* **Finiteness of $Ш$** is unknown for every curve with $r_{\mathrm{an}}\ge2$.
* **No case of the leading-term formula** is known in rank $\ge2$.

What is known is partial information prime by prime.

## 6.1 Finiteness and vanishing of $Ш[p^\infty]$ for individual primes

* SteinWuthrich2013: using Kato's divisibility and computed $p$-adic $L$-functions and
  $p$-adic regulators, $Ш(E/\mathbf{Q})[p]=0$ for all 1,534,422 pairs $(E,p)$ with $E$ non-CM,
  conductor $\le30\,000$, rank $\ge2$, and $p$ a good ordinary prime with $5\le p<1000$
  (plus image-of-Galois conditions).
* CoatesLiangSujatha2009, CoatesLiangSujatha2010: for CM curves of rank 2, a criterion for
  $Ш[p^\infty]=0$ at good ordinary $p$, applied to five curves for $p<30\,000$.
* Banwait2026: a cyclotomic criterion via the second Taylor coefficient of the $p$-adic
  $L$-function; the regulator is a unit at all but three of 8,050 primes for the same five CM
  curves; settles $p=577$ for $y^2=x^3+34x$. Lean formalisation of the first equivalence.
* Kim2026Sha: Heegner points detect finiteness of $Ш[p^\infty]$ for semistable curves of
  arbitrary rank at good $p\ge5$ with irreducible $E[p]$, via Kolyvagin's conjecture.
* BalakrishnanMullerStein2016: numerical $p$-adic BSD for modular abelian varieties including
  rank $\ge2$.
* Darmon–Rotger diagonal classes and generalized Kato classes: Castella–Hsieh
  (CastellaHsieh2018) give non-vanishing of generalized Kato classes for rank-2 curves, a
  candidate Euler-system input for rank 2.

## 6.2 Higher derivatives

* GrossKohnenZagier1987: positions of Heegner points; YunZhang2017: Taylor expansion of
  $L$-functions over function fields in terms of intersection numbers of Heegner–Drinfeld
  cycles on moduli of shtukas (all higher derivatives, function field case).
* No analogue over number fields of a formula for $L''(E,1)$ in terms of rational points is known.

## 6.3 Why rank $\ge2$ is hard

Every proof of finiteness of $Ш$ uses an Euler system whose bottom class is
non-zero: Heegner points (rank 1 over $K$), Kato or Beilinson–Flach elements
(rank 0). In rank $\ge2$ the bottom classes vanish and their derivatives
(Kolyvagin derivatives, derived heights) only control Selmer groups up to the
rank, not $Ш$ itself. Determining $Ш[p^\infty]$ prime by prime, as in 6.1, cannot
reach all $p$ at once.

## 6.4 Natural next targets (in increasing difficulty)

1. Extend the Stein–Wuthrich computation (conductor $\le30\,000$, $p<1000$, ordinary)
   to larger conductors, larger $p$, supersingular primes (now that signed main
   conjectures are available in more cases) and to rank 3 and 4 curves.
2. Prove $Ш(E/\mathbf{Q})[p^\infty]=0$ for **all** $p$ in an explicit set of positive
   density for one rank-2 curve.
3. Prove finiteness of $Ш(E/\mathbf{Q})$ for one curve of rank 2. This is open and would be a
   major result.
