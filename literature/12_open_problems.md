# 12. Open problems and the frontier

Status on 3 November 2026, refereed results only unless marked.

## 12.1 What is open

1. **The conjecture itself** (Clay problem): $r_{\mathrm{an}}=r_{\mathrm{alg}}$ and the
   leading-term formula for every $E/\mathbf Q$.
2. **Finiteness of $Ш$ in rank $\ge2$.** Not known for a single curve with $r_{\mathrm{an}}\ge2$.
   Known only prime by prime: $Ш[p^\infty]$ finite (often zero) for explicit $(E,p)$
   (SteinWuthrich2013, CoatesLiangSujatha2009/2010, Banwait2026, Kim2026Sha).
3. **The leading term in rank $\ge2$.** No case known; even its $p$-part is known only for
   finitely many explicit $(E,p)$ through $p$-adic BSD and Kato.
4. **Certifying $r_{\mathrm{an}}\ge4$.** No curve is proved to have analytic rank $\ge4$; the
   vanishing of $L''(E,1)$ or $L'''(E,1)$ cannot be decided by known methods (no Gross–Zagier
   formula for higher derivatives over $\mathbf Q$).
5. **Rank $\le1$, all primes (refereed).** The full formula is proved for a large but
   restricted class; the open cases are the 2-part with additive reduction or bad
   residual images, and some additive primes $p\ge3$ (chapter 3). Claimed in full by the
   unrefereed OpenAI release (chapter 11).
6. **Goldfeld's conjecture** for every twist family (proved for many families with a
   2-isogeny or full 2-torsion; claimed in general by unrefereed work).
7. **Boundedness of ranks** (Park–Poonen–Voight–Wood heuristic predicts finitely many curves of
   rank $>21$; the record is $\ge32$, exact rank 22 known).
8. **Main conjectures** at additive primes and at $p=2$; Kolyvagin's conjecture (non-vanishing
   of the Kolyvagin system) in general.
9. **Higher Gross–Zagier over number fields**: a number-field analogue of YunZhang2017.

## 12.2 Concrete targets for this repository

Ranked by what can be proved with current methods plus computation.

* **(A) Vanishing of $Ш[p^\infty]$ for rank-2 and rank-3 curves beyond the Stein–Wuthrich
  range.** Method: Kato's divisibility + the inequality
  $\operatorname{corank}\mathrm{Sel}_{p^\infty}\le\operatorname{ord}_TL_p$ + an exact computation
  showing $\operatorname{ord}_TL_p=r_{\mathrm{alg}}$ and the $p$-adic regulator, so that the
  $p$-adic BSD quotient is a unit. New ranges: conductor above 30 000, rank 3 and 4 curves,
  primes $p\ge1000$.
* **(B) Supersingular primes** via Kobayashi's signed Selmer groups and the signed main
  conjecture divisibility (Kato + Kobayashi), where SteinWuthrich2013 do not apply.
* **(C) The leading term $p$-adically**: verify the $p$-adic BSD formula
  (MazurTateTeitelbaum1986) for rank-2/3 curves to high $p$-adic precision, which together with
  (A) gives the $p$-part of the classical formula conditional only on $Ш[p^\infty]$ finiteness,
  which (A) supplies.
* **(D) Rank-4 curves** (e.g. 234446a1): every result of (A) holds without knowing
  $r_{\mathrm{an}}=4$, since the $p$-adic argument uses $r_{\mathrm{alg}}$ only.

Each such result is a theorem about specific $(E,p)$, not a closure of the conjecture.
