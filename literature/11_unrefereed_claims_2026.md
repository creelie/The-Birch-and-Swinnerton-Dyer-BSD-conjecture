# 11. Unrefereed claims (as of 3 November 2026)

These manuscripts are **not refereed**. They are recorded so that this repository is complete
and so that no later work here duplicates or silently relies on them. Nothing in this
repository uses them as a proved input; where a later chapter or result is conditional on one
of them, it says so.

## 11.1 The OpenAI Math release (github.com/openai/math, October 2026)

Manuscripts authored "OpenAI", released September–October 2026; the latest versions:

| Key | Title | Claim (from the abstract) |
|---|---|---|
| OpenAI2026BSD | Exact Birch–Swinnerton-Dyer formula from low Selmer corank (7 Oct) | The full leading-term formula, with every prime factor and no hypothesis on reduction, torsion, isogenies, CM or residual images, for every $E/\mathbf Q$ whose $q^\infty$-Selmer group has corank $0$ or $1$ at some prime $q$; then $r_{\mathrm{an}}=r_{\mathrm{alg}}$ equals that corank and $Ш$ is finite. |
| OpenAI2026SelmerConverse | The Selmer converse for elliptic curves at every prime (7 Oct) | If the $p^\infty$-Selmer corank is $r\in\{0,1\}$ for some $p$, then $r_{\mathrm{an}}=r_{\mathrm{alg}}=r$ and $Ш$ is finite. Application: $X^3+Y^3=\ell Z^3$ has rank one for primes $\ell\equiv4,7,8\pmod9$. |
| OpenAI2026TwoPrimary | The two-primary BSD formula in Selmer corank at most one (6 Oct) | The 2-part of the formula when the $2^\infty$-Selmer corank is $\le1$. |
| OpenAI2026TwoTorsion | A pointwise 2-converse for elliptic curves with rational two-torsion (7 Oct) | The 2-converse in corank $\le1$ when $E(\mathbf Q)[2]\ne0$, any reduction at 2. |
| OpenAI2026Goldfeld | Goldfeld's analytic density conjecture and the 2-converse (7 Oct) | In every quadratic twist family, analytic ranks 0 and 1 each have density 1/2. |
| OpenAI2026MeanRank | The mean analytic rank of quadratic twists (6 Oct) | The average analytic rank of twists tends to 1/2. |
| OpenAI2026H10 | Hilbert's tenth problem over the rational numbers (6 Oct) | No algorithm decides whether an integer polynomial has a rational zero (via rank-one elliptic curves and elliptic logarithms). |

Related claims in the same release: modularity of elliptic curves over imaginary quadratic
fields (4 Oct), Fontaine–Mazur modularity at the prime 2, unrestricted pro-modularity at 2,
Milne's rationality conjecture for abelian varieties.

**What would follow if they hold.** Together they would give BSD in full for every curve of
analytic rank $\le1$ and, by Bhargava–Shankar-type averages and the Goldfeld density claim, for
100% of curves in every twist family. They do not touch rank $\ge2$: no claim in the release
gives finiteness of $Ш$, or the leading term, for a single curve with $r_{\mathrm{an}}\ge2$.
This is why the research part of this repository aims at rank $\ge2$ (chapter 12).

## 11.2 Claimed proofs of the full conjecture

Several arXiv (mostly math.GM) and GitHub manuscripts announce a proof of the conjecture in
general. None has been accepted by the community, none is in a refereed venue, and the ones
checked here rest on an unproved step or a misreading of the statement. They are listed in
[`../catalogue/claimed_proofs.md`](../catalogue/claimed_proofs.md) without comment on each.
