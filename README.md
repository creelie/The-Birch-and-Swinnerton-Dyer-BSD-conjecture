# The Birch and Swinnerton-Dyer conjecture

A curated, checked record of what is known about the Birch and Swinnerton-Dyer (BSD)
conjecture, kept up to date, and the base for new results on it.

Maintainer: Deep Bhattacharjee. Last updated 3 November 2026.

## Releases

| Release | Content | DOI |
|---|---|---|
| v1.0.0 | paper on the $p$-primary part of Ш in ranks three to six, data and certificates | [10.5281/zenodo.23931964](https://doi.org/10.5281/zenodo.23931964) |
| v1.0.1 | declarations, keywords and MSC under the abstract, tables before the references | [10.5281/zenodo.23933186](https://doi.org/10.5281/zenodo.23933186) |
| v1.0.2 | every reference checked against Crossref and the publishers | [10.5281/zenodo.23933270](https://doi.org/10.5281/zenodo.23933270) |

Concept DOI of all versions: [10.5281/zenodo.23931963](https://doi.org/10.5281/zenodo.23931963).

## The conjecture

For an elliptic curve $E/\mathbf Q$ with $L$-function $L(E,s)$,

$$\operatorname{ord}_{s=1}L(E,s)=\operatorname{rank}E(\mathbf Q),\qquad
\lim_{s\to1}\frac{L(E,s)}{(s-1)^r}=\frac{\#Ш(E/\mathbf Q)\,\Omega_E\,R_E\,\prod_pc_p}{\#E(\mathbf Q)_{\mathrm{tors}}^2}.$$

It is one of the seven Clay Millennium Problems.

## Status in one paragraph

For analytic rank $0$ or $1$ the rank equality and finiteness of $Ш$ are theorems
(Gross–Zagier, Kolyvagin, with modularity), and the leading-term formula is proved
prime by prime for a large class of curves; an unrefereed release of October 2026
claims it in full. For analytic rank $\ge2$ finiteness of $Ш$ is not known for a single
curve, only the vanishing or finiteness of $Ш[p^\infty]$ for explicit pairs $(E,p)$;
no curve is proved to have analytic rank $\ge4$. On average, a positive proportion of
curves satisfy the rank part. The conjecture is open.

## Contents

| Path | Content |
|---|---|
| [`literature/01_statement.md`](literature/01_statement.md) | Statement, reformulations, generalisations |
| [`literature/02_timeline.md`](literature/02_timeline.md) | Timeline 1922–2026 |
| [`literature/03_rank_zero_and_one.md`](literature/03_rank_zero_and_one.md) | Gross–Zagier–Kolyvagin, converse theorems, the $p$-part of the formula |
| [`literature/04_iwasawa_padic.md`](literature/04_iwasawa_padic.md) | Main conjectures, $p$-adic BSD |
| [`literature/05_ranks_statistics_heuristics.md`](literature/05_ranks_statistics_heuristics.md) | Average ranks, Goldfeld, heuristics, records |
| [`literature/06_rank_two_and_higher.md`](literature/06_rank_two_and_higher.md) | The rank $\ge2$ frontier |
| [`literature/07_computation_databases_software.md`](literature/07_computation_databases_software.md) | Numerical evidence, databases, software |
| [`literature/08_generalisations.md`](literature/08_generalisations.md) | Abelian varieties, function fields, Bloch–Kato |
| [`literature/09_applications.md`](literature/09_applications.md) | Congruent numbers, sums of two cubes, Hilbert's tenth problem |
| [`literature/10_books_surveys.md`](literature/10_books_surveys.md) | Books and surveys |
| [`literature/11_unrefereed_claims_2026.md`](literature/11_unrefereed_claims_2026.md) | Unrefereed claims of 2026 |
| [`literature/12_open_problems.md`](literature/12_open_problems.md) | Open problems and targets |
| [`paper/`](paper/) | Paper: *The $p$-primary part of the Tate–Shafarevich group in ranks three to six* (36 pp.) |
| [`results/`](results/) | Its data, programs and Lean 4 certificates |
| [`references.bib`](references.bib) | 162 references, DOIs checked against Crossref |
| [`catalogue/`](catalogue/) | 1,438 arXiv records (TSV and JSON), repositories, announced proofs |
| [`checks/`](checks/) | Numerical BSD check of eight curves of ranks 0–4 (PARI/GP) |
| [`tools/`](tools/) | Scripts that build the catalogue and the bibliography |

Citations in the chapters use the BibTeX keys of `references.bib`.

## Reproducing

```
pip install cypari2           # PARI/GP 2.17
python3 checks/analytic_sha.py
python3 tools/arxiv_cat.py raw.json                 # harvests the arXiv API
python3 tools/build_catalogue.py raw.json catalogue # filters it into the catalogue
python3 tools/mkbib.py tools/dois.txt out.bib       # BibTeX for the DOI entries via Crossref
```

## Licence

See [`LICENSE`](LICENSE).
