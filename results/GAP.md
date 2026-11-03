# What is missing for BSD, and what would fill it

The conjecture has two parts: (R) $\operatorname{ord}_{s=1}L(E,s)=\operatorname{rank}E(\mathbf Q)$,
and (F) the leading-term formula, which needs Ш finite. For analytic rank $\le1$ both parts
reduce to theorems (Gross–Zagier, Kolyvagin, Kato, Skinner–Urban and successors). The gap
is analytic rank $r\ge2$. It splits into three precise statements.

## Target 1: an upper bound for the Selmer group from $L^{(r)}(E,1)\neq0$

Needed: if $L^{(r)}(E,1)\ne0$ then $\operatorname{corank}\mathrm{Sel}_{p^\infty}(E/\mathbf Q)\le r$.
This alone gives (R) together with the finiteness of Ш[$p^\infty$], once $r$ independent
points are known.

* *What exists.* Kolyvagin's Euler system of Heegner points bounds the Selmer group only
  when the basic Heegner point is non-torsion, which by Gross–Zagier means
  $\operatorname{ord}L(E/K,s)=1$. Kato's Euler system bounds it by the order of the
  $p$-adic $L$-function, not of the complex one.
* *Construction that would fill it.* A **higher Gross–Zagier formula over $\mathbf Q$**:
  cycles whose height is $L^{(r)}(E,1)$, as Yun and Zhang built over function fields
  from moduli of shtukas with $r$ legs (Ann. of Math. 186 (2017)). Over number fields
  there are no shtukas with several legs, and no substitute is known.
* *Alternative.* A **rank-$r$ Kolyvagin system** (Mazur–Rubin, Burns–Sakamoto–Sano)
  together with a theorem that its leading class is nonzero when $L^{(r)}(E,1)\ne0$. The
  systems exist; the nonvanishing theorem is the missing piece.

## Target 2: the $p$-adic regulator is nonzero (Schneider's conjecture)

Needed for the Iwasawa route: $\operatorname{Reg}_p(E/\mathbf Q)\ne0$, i.e. the
cyclotomic $p$-adic height pairing is nondegenerate.

* *What exists.* Nothing in general. For $r=1$ it says $h_p(P)\ne0$ for the generator,
  already open in general.
* *Construction that would fill it.* A $p$-adic transcendence theorem for values of
  the $p$-adic sigma function at algebraic points (an analogue of Baker's theorem for
  heights). Bertrand proved the CM case for $r=1$.

## Target 3: the $p$-adic and the complex $L$-functions vanish to the same order

Needed: $\operatorname{ord}_TL_p(E,T)=\operatorname{ord}_{s=1}L(E,s)$. With Targets 1–2
on the $p$-adic side (where Kato and Skinner–Urban give the main conjecture), this
transfers the $p$-adic statement to the complex one.

* *Construction that would fill it.* A $p$-adic higher Gross–Zagier formula
  (Perrin-Riou proved the $r=1$ case), or an interpolation linking the derivatives of
  both functions.

## What can be done now, and is done here

For a *given* curve and prime the three targets can be bypassed: the computation of
$L_p(E,T)$ shows $\operatorname{ord}_TL_p=r$, which by Kato and Schneider proves at once
that the regulator is nonzero (Target 2 for that $p$), that Ш[$p^\infty$] is finite, and
its order. That is the construction carried out in this folder, for curves of rank 3, 4,
5 and 6. It proves the $p$-part, not the conjecture: Target 3 stays open for each of
these curves (no curve is proved to have analytic rank $\ge4$), and covering all primes
would need Target 1 or 2 in general.
