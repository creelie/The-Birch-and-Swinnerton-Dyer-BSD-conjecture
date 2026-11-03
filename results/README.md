# The $p$-primary part of the Tate–Shafarevich group in ranks three to six

Deep Bhattacharjee, November 2026. Paper: [`../paper/main.pdf`](../paper/main.pdf)
(LaTeX source [`../paper/main.tex`](../paper/main.tex)).

## Results

* **Theorem A.** The curve 234446a1, $y^2+xy=x^3-x^2-79x+289$, the only curve of rank four
  of conductor below $500\,000$, has $E(\mathbf Q)\cong\mathbf Z^4$ and
  $Ш(E/\mathbf Q)[p^\infty]=0$ for every prime $5\le p<1000$ with $p\ne337$, and
  $Ш(E/\mathbf Q)[2]=0$. At the ordinary primes among them $L_p(E,T)$ vanishes to order
  exactly four and the $p$-adic height pairing is nondegenerate.
* **Theorem B.** For the 494 isogeny classes of rank three with conductor
  $30\,000<N\le100\,000$, the rank is three and $Ш(E/\mathbf Q)[p^\infty]=0$ at every good
  ordinary prime $5\le p<100$ (10,404 pairs), with the same two statements on $L_p$ and
  the height pairing.
* **Theorems C and D.** The rank-five curve 19047851a1 (Elkies–Watkins) has
  $Ш[p^\infty]=0$ for $p=7,11,13,17,19$; the rank-six curve 5187563742a1 has
  $Ш[7^\infty]=0$.
* **Leading coefficient.** For all 1,717 pairs of Theorem B with $p\le13$ the coefficient
  $a_3$ of $L_p(E,T)$ and $S_p=(1-\alpha^{-1})^2\prod c_v\operatorname{Reg}_\gamma/\#E_{\rm tors}^2$
  agree modulo $p^{v+2}$, $v=v_p(S_p)$: the $p$-adic BSD formula of Mazur–Tate–Teitelbaum
  holds to that precision with $\#Ш=1$, the value predicted by the (numerically computed)
  analytic order of Ш.

None of this proves the Birch and Swinnerton-Dyer conjecture or the finiteness of Ш for
any curve of rank $\ge2$: every statement concerns one prime at a time. See
[`GAP.md`](GAP.md) for what is missing.

## Method

Kato's divisibility and the theorem of Schneider and Perrin-Riou turn one congruence
$v_p(a_r)=v_p(S_p)<\infty$ into the rank, the vanishing of $Ш[p^\infty]$, the
nondegeneracy of the $p$-adic height and the main conjecture at $(E,p)$ (Theorem 5.1 of
the paper), provided $\bar\rho_{E,p}$ is surjective and the points are $p$-saturated. Both
side conditions are checked by counting points on reductions (Sections 7 and 8).

## Files

| Path | Content |
|---|---|
| `data/rank3.jsonl.gz` | one record per pair of Theorem B: $a_p$, surjectivity witnesses, $a_3$, $v_p(S_p)$, status |
| `data/rank3_refine.jsonl` | the 419 irregular pairs, settled at levels 3 to 5 |
| `data/rank3_curves.txt` | the 8,862 rank-three classes of conductor $30\,000$–$500\,000$ with generators |
| `data/rank4.jsonl`, `data/rank4_refine.jsonl`, `data/rank4_supersingular.jsonl` | Theorem A |
| `data/rank5.jsonl`, `data/rank6.jsonl`, `data/rank5_curve.txt`, `data/rank6_curve.txt` | Theorems C and D |
| `data/saturation.jsonl.gz` | auxiliary primes of the saturation sieve for every pair |
| `data/leading.jsonl` | $a_3$ and $S_p$ modulo $p^{v+2}$ for the 1,717 pairs with $p\le13$ |
| `data/sha_an.jsonl.gz` | analytic order of Ш for the rank-three classes and the curves of rank 5, 6 |
| `scripts/certify.py`, `scripts/refine.py` | the certificates (levels 2 and $\ge3$) |
| `scripts/fastsum.py`, `scripts/leading.py` | Riemann sums at high level; the leading-coefficient check |
| `scripts/ss.py` | supersingular primes ($D_p$-valued $L$-function) |
| `scripts/sat.py`, `scripts/sieve/` | $p$-saturation (eclib; reduction sieve) |
| `scripts/shaan.py`, `scripts/shacert.py`, `scripts/assemble.py` | analytic Ш; single-pair driver; summary |
| `scripts/gen/` | the worked examples and the tables of the paper |
| `scripts/mklean.py`, `lean/` | Lean 4 files and their generator |

The Lean files (`Rank3.lean`: 1,482 theorems; `Rank4.lean`) check by kernel evaluation
(`decide +kernel`, Lean 4.34, no Mathlib), for every certified pair, the finite arithmetic
of the certificate: $p$ and the witness primes are good, $a_p\not\equiv0\pmod p$, the three
surjectivity conditions with every $a_q$ computed by counting points, and that the
generators lie on the curve. `#print axioms` reports no axioms. The values of $a_r$ and
of the $p$-adic regulator are not checked in Lean.

## Reproducing

The computations use SageMath 10.8 modules (`passagemath`, with `eclib`), PARI/GP 2.17.4
through `cypari2`, and Lean 4.34. Each script states its usage and input files in its
first lines; they are run from a working directory holding those inputs (the curve lists
of `data/` under the names `rank3.txt`, `r5.txt`, `r6.txt`).

The figures of the paper are drawn by `../paper/figures/make_figures.py DATA_DIR`.
