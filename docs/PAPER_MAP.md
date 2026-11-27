# Paper-to-Lean Correspondence

This document tracks the formalization status of the results in:

> **Three-Block Bounds for the Asymptotic Rank of Weighted Graph Tensors**
> Zhengyang Wang, Yichuan Cao, Hongbo Li, Xiao-Shan Gao

This repository is intended to house the Lean 4 formalization of the full paper.
**Currently, only the uniform odd-cycle theorem ($C_m$, Corollary 17) is formalized and kernel-checked.**
The remaining theorems are established by written proofs in the manuscript and will be added incrementally.

## Formalized Results (Uniform Odd Cycles $C_m$)

| Manuscript reference | Mathematical statement | Lean declaration | Module | Status |
|---|---|---|---|---|
| Eq. (2.4)–(2.5) | $m$-factor cycle tensor $T_F(C_m, n)$, exact rank $r_F(m,n)$, dyadic exponent $\Gamma_F(C_m)$ | `OddCycleTarget.coeff`, `HasDecomposition`, `exactRank`, `exponent` | `OddCycleTarget.lean` | Verified |
| Corollary 17(i) | $\Gamma_F(C_m) = (2m-3)^2 / [4(m-2)]$ for every field $F$ and odd $m \ge 3$ | `OddCycleTarget.odd_equality_all` | `OddCycleTarget/Equality.lean` | Verified |
| Corollary 17(i) (limit) | $\lim_{t\to\infty} t^{-1} \log_2 r_F(m, 2^t) = (2m-3)^2 / [4(m-2)]$ | `OddCycleTarget.odd_limit` | `OddCycleTarget/Equality.lean` | Verified |
| Corollary 17(i) (excess) | $(m-2)(\Gamma_F(C_m) - (m-1)) = 1/4$ | `OddCycleTarget.odd_normalized_excess` | `OddCycleTarget/Equality.lean` | Verified |
| Corollary 17(ii) | Finite-rank lower bound $r_F(m,n)^{4(m-2)} \ge n^{(2m-3)^2}$ for $n \ge 2$ and $\Gamma_F(C_m) \ge (2m-3)^2/[4(m-2)]$ | `OddCycleTarget.oddFiniteLower`, `oddExponentLower`, `oddRankAndExponentLower` | `OddCycleTarget/LowerConclusion.lean` | Verified |
| Corollary 17(iii) | Explicit dyadic decomposition witnesses $r^{4(m-2)q} \le 2^{((2m-3)^2 q + 1)t}$ | `OddCycleTarget.odd_upper_all` | `OddRoot.lean` | Verified |
| Internal lower reduction | Three-block $(m-2,1,1)$ specialization to rectangular matrix multiplication | `OddCycleTarget.groupOddRectangle`, `rectanglePowerLower` | `OddCycleTarget/RectGrouping.lean`, `RectangleInput.lean` | Verified |
| Internal spectral bridge | $\mathrm{CAT}(0)$ Ptolemy inequality and Zhou quadratic mass inequality | `OddCycleTarget.Spectrum.actual_wire_ptolemy`, `binaryClique_upper_step`, `exists_maximizing_ptolemy_table` | `OddCycleTarget/SpectrumGeometry.lean`, `OddRoot.lean`, `MassTests.lean` | Verified |
| Internal odd-cycle geometry | Sharp perimeter bound $4(m-2) \sum_{i=0}^{m-1} d(i,i+1) \le (2m-3)^2$ | `OddCycleOffset.universalPrice`, `OddCycleTarget.sharp_perimeter` | `OddCycleTarget/UniversalPrice.lean`, `SharpPerimeter.lean` | Verified |

## Remaining Paper Results (Planned)

| Manuscript section | Topic | Status |
|---|---|---|
| Section 2.2 (Proposition 2) | Uniform complete graphs $K_m$ | Planned (written proof in paper) |
| Section 3 (Theorem 4, Corollary 6, Proposition 7) | Two-tree metric characterization, four active vertices, consistent representatives | Planned (written proof in paper) |
| Section 4 (Theorem 8) | Exactness on at most five active vertices | Planned (written proof in paper) |
| Section 5.1–5.2, 5.4 (Theorems 11, 13, 19; Propositions 12, 18; Corollaries 20–22) | General odd Ptolemy polygon inequality, arbitrarily weighted cycles, rigidity, cut chambers, attachments, layered cycles | Planned (written proof in paper) |
| Section 6 (Theorems 23, 25, 26, 29, 30, 32; Proposition 24; Lemma 28) | Fractional odd-cycle packings, single-deletion classification, $100/93$ two-deletion comparison, triangle-indicator cone, two-distance tables | Planned (written proof in paper) |
| Section 7 (Proposition 33, Theorem 34, Corollary 35) | Semidefinite cut comparison, inertia bounds, dominant-edge asymptotics | Planned (written proof in paper) |
| Section 8 (Propositions 36–38) | Division-free arithmetic circuits for tensor contractions | Planned (written proof in paper) |
| Appendices A–C (Proposition 40, Theorem 41) | Local integer-mass certificate, six-position two-book inequality, six uniform rows | Planned (written proof in paper) |
