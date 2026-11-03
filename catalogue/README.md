# Catalogue

Collected on 3 November 2026.

## arXiv (`arxiv_bsd_catalogue.tsv`, `arxiv_bsd_catalogue.json`)

1,438 arXiv records on the conjecture and the mathematics around it, newest first. The TSV has
one line per paper (id, dates, primary class, authors, title, DOI, journal reference, query
topics, flag); the JSON adds the abstract.

Built from the arXiv API with these queries (full text of title and abstract, all categories),
deduplicated, then kept only if the title or abstract names one of the objects of the
conjecture (Selmer, Shafarevich–Tate, Heegner, Kolyvagin, Gross–Zagier, Iwasawa, elliptic
curve, abelian variety, Euler system in the arithmetic sense, congruent number, Bloch–Kato,
Tamagawa, $p$-adic $L$-function, Mordell–Weil, modular form, motive):

| topic | query |
|---|---|
| bsd, bsd2 | "Birch and Swinnerton-Dyer", "BSD conjecture" |
| sha, sha2 | "Tate-Shafarevich", "Shafarevich-Tate" |
| heegner, kolyvagin, gz | Heegner points; Kolyvagin; Gross–Zagier |
| imc, eulersys | Iwasawa main conjecture elliptic; Euler system |
| selmer, parity | Selmer group elliptic; parity conjecture |
| padicL | $p$-adic $L$-function elliptic curve |
| rankavg, goldfeld, rankrecord | average rank; Goldfeld conjecture; rank records |
| congruent | congruent number |
| bloch_kato | Bloch–Kato conjecture |

407 records carry a DOI or journal reference. The 14 records with primary class `math.GM`
(general mathematics, where claims are not screened) are flagged.

The scripts are `../tools/arxiv_cat.py` (harvest) and `../tools/build_catalogue.py` (filter).

## Other lists

* [`github_repositories.md`](github_repositories.md): software, data and research code.
* [`claimed_proofs.md`](claimed_proofs.md): announced proofs of the full conjecture, none accepted.
* Refereed papers and books: [`../references.bib`](../references.bib), 162 entries.
