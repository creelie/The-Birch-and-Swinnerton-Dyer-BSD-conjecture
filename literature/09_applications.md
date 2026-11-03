# 9. Applications

## 9.1 Congruent numbers

A squarefree $n$ is congruent (the area of a right triangle with rational sides) iff
$E_n:y^2=x^3-n^2x$ has positive rank.

* Tunnell1983: if $n$ is congruent then a ternary-form count vanishes; the converse holds
  under weak BSD for $E_n$. So BSD decides the problem by a finite computation.
* $n\equiv5,6,7\pmod 8$: root number $-1$; BSD predicts every such $n$ is congruent. Known for
  many families: Tian2014 (infinitely many congruent $n$ with any prescribed number of prime
  factors in each class, via Heegner points),
  TianYuanZhang2017 (genus periods and genus points).
* Densities: HeathBrown1994 (distribution of 2-Selmer sizes). SmithCongruent: full BSD for
  $E_n$ for at least 41.9% of squarefree $n\equiv1,2,3\pmod8$, and weak BSD (so congruence) for
  at least 55.9% of $n\equiv5,6,7\pmod8$, completing an argument of Tian, Yuan and Zhang.
  Smith2017: Delaunay's distribution for $2^\infty$-Selmer groups in quadratic twist families
  of curves with full rational 2-torsion and no rational cyclic 4-subgroup; rank $\ge2$ occurs
  for $o(N)$ twists.
* BurungaleTian2021: an expository account of the even parity Goldfeld conjecture, first for the
  congruent number family.

## 9.2 Sums of two cubes (Sylvester's problem)

A prime $p\equiv4,7,8\pmod9$ should be a sum of two rational cubes (Sylvester).

* DasguptaVoight2018: mock Heegner points prove it for $p\equiv4,7\pmod9$ under a
  3-adic condition.
* AlpogeBhargavaShnidman2022: a positive proportion of integers are, and are not, sums of two
  cubes.
* Elkies announced the classes $4,7$ in 1994; Yin constructed CM points on
  $y^2=x^3+p^{2i}/4$ settling them, and Yin2026 (arXiv 2607.01744) proves the matching explicit
  Gross–Zagier formula.
* BurungaleTian2026 (arXiv 2609.14893, preprint): the class $p\equiv8\pmod9$, by showing that
  $y^2=x^3+p^2/4$ has analytic rank one (an auxiliary Rankin–Selberg $L$-function, Chan's
  3-isogeny descent and the rank-zero converse). With Yin this completes Sylvester's conjecture.
* The unrefereed OpenAI Selmer-converse preprint also claims the $p\equiv4,7,8$ statement as an
  application (chapter 11).

## 9.3 Hilbert's tenth problem

Ranks of elliptic curves in field extensions give Diophantine definitions of $\mathbf Z$.

* MazurRubin2010: under $Ш[2]$ parity hypotheses, Hilbert's tenth problem is undecidable over
  the ring of integers of every number field.
* KoymansPagano2024arxiv / KoymansPagano2026: unconditional undecidability over every ring of
  integers, by additive combinatorics and 2-descent; ABHS2025 (Alpöge–Bhargava–Ho–Shnidman):
  the same via rank stability in quadratic extensions.
* Over $\mathbf Q$ itself the problem is classically open; an unrefereed OpenAI preprint
  (October 2026) claims a negative answer using rank-one elliptic curves (chapter 11).

## 9.4 Other

* The class number problem: Goldfeld's effective lower bound uses an elliptic curve of
  analytic rank 3 (5077a1, proved by BuhlerGrossZagier1985 via Gross–Zagier).
* Rational points on curves: Chabauty–Coleman and quadratic Chabauty need rank information
  supplied by BSD-type theorems (repository `jbalakrishnan/AWS`).
