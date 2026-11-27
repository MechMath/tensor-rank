# Three-Block Bounds for the Asymptotic Rank of Weighted Graph Tensors in Lean 4

[中文说明](README.zh-CN.md) · [Paper correspondence](docs/PAPER_MAP.md) · [Third-party licenses](licenses/)

This repository hosts the Lean 4 formalization of the paper:

> **Three-Block Bounds for the Asymptotic Rank of Weighted Graph Tensors**
> Zhengyang Wang, Yichuan Cao, Hongbo Li, Xiao-Shan Gao

This repository is designed to collect the Lean 4 formalizations of all theorems in the paper. **At present, only the uniform odd-cycle theorem ($C_m$, Corollary 17) is formalized and kernel-checked**; formalizations of the remaining theorems in the manuscript will be added in future updates.

## Formalized main results (Uniform odd cycles $C_m$)

| Manuscript | Lean entry point | Assumptions |
|---|---|---|
| Exact odd-cycle exponent (Corollary 17(i)) | `OddCycleTarget.odd_equality_all` | None (unconditional over every field $F$ and odd $m \ge 3$). |
| Dyadic rank-exponent limit (Corollary 17(i)) | `OddCycleTarget.odd_limit` | None. |
| Normalized excess identity $(m-2)(\Gamma_F(C_m)-(m-1))=1/4$ | `OddCycleTarget.odd_normalized_excess` | None. |
| Finite-rank lower bound $r_F(m,n)^{4(m-2)} \ge n^{(2m-3)^2}$ (Corollary 17(ii)) | `OddCycleTarget.oddRankAndExponentLower` | None (all fields $F$, odd $m \ge 3$, $n \ge 2$). |
| Explicit integer decomposition witnesses (Corollary 17(iii)) | `OddCycleTarget.odd_upper_all` | None. |

```lean
import OddCycleTarget.Equality

#check OddCycleTarget.odd_equality_all
#check OddCycleTarget.odd_upper_all
#check OddCycleTarget.odd_limit
#check OddCycleTarget.oddRankAndExponentLower
```

## Build and verify

Install [elan](https://github.com/leanprover/elan), Git, Bash, and Python 3. The Lean toolchain and Mathlib revision are pinned in `lean-toolchain` and `lake-manifest.json`; do not run `lake update` when reproducing this snapshot.

```sh
git clone https://github.com/MechMath/tensor-rank.git
cd tensor-rank
lake exe cache get
lake build +OddCycleTarget.Equality
lake env leanchecker OddRoot OddCycleTarget.Equality
lake env lean VerifyResults.lean
```

Alternatively, run the full build, kernel check, and source scan via:

```sh
bash scripts/audit.sh
```

The toolchain is **Lean `v4.35.0`** (`leanprover/lean4:v4.35.0`) with **Mathlib** pinned at commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. All transitive dependencies are locked in [`lake-manifest.json`](lake-manifest.json).

## Scope and axiom boundary

- **Scope:** Only the uniform odd-cycle theorem ($C_m$, Corollary 17) is currently formalized in Lean. All other theorems in the paper (arbitrarily weighted cycles, complete graphs $K_m$, two-tree metrics, five active vertices, near-bipartite bounds, dominant-edge asymptotics, and arithmetic circuits) are proved on paper and planned for future additions; see [`docs/PAPER_MAP.md`](docs/PAPER_MAP.md).
- **No custom axioms or `sorry`:** All proofs in the uniform odd-cycle development are free of `sorry`, `admit`, and project-specific axioms. Running `VerifyResults.lean` reports only Lean's three standard axioms for `odd_equality_all`, `odd_upper_all`, `odd_limit`, and `oddRankAndExponentLower`:
  ```text
  propext, Classical.choice, Quot.sound
  ```
- **Independent kernel check:** Both `OddRoot` and `OddCycleTarget.Equality` pass verification under `leanchecker`.

## Repository layout

- `OddCycleTarget.lean`: exact $m$-factor cycle tensor definition (`coeff`, `HasDecomposition`, `exactRank`, `exponent`), rational target constants `A m`, `D m`, and target predicates.
- `OddCycleTarget/RectGrouping.lean`, `RectangleFormula.lean`, `RectangleInput.lean`, `RankBridge.lean`, `LowerTransfer.lean`, `LowerConclusion.lean`: $(m-2,1,1)$ three-block grouping reduction and finite-rank / exponent lower bounds.
- `OddCycleTarget/SpectrumBridge.lean`, `SpectrumGeometry.lean`, `CliqueRankBridge.lean`, `MassTests.lean`, `Assembly.lean`: spectral representation of $\Gamma_F(C_m)$, $\mathrm{CAT}(0)$ Ptolemy inequality, and Zhou's quadratic mass inequality.
- `OddCycleTarget/OffsetSharp.lean`, `OddCube.lean`, `UniversalPrice.lean`, `PacketPrice.lean`, `SharpPerimeter.lean`: sharp odd-cycle perimeter bound for Ptolemy--Zhou pseudometrics.
- `OddRoot.lean`, `OddCycleTarget/Equality.lean`, `VerifyResults.lean`: top-level assembly, final theorems, and axiom checks.
- `OddCycleTarget/C5Target/` and `OddCycleTarget/Lemmata/`: self-contained vendored upstream Lean libraries (see attribution below).
- `docs/PAPER_MAP.md`: correspondence between paper statements and Lean declarations.
- `scripts/audit.sh`: reproducible build, `leanchecker` replay, and axiom audit script.

## Attribution and licensing

This repository is licensed under the **Apache License, Version 2.0** (see [`LICENSE`](LICENSE)).

The uniform odd-cycle formalization builds on Lean 4 and Mathlib together with vendored upstream Lean developments whose licenses and notices are preserved in [`licenses/`](licenses/):

- OpenAI's tensor-spectrum ($\mathrm{CAT}(0)$ geometry) and rectangular matrix multiplication Lean libraries ([`licenses/OpenAI-LICENSE.txt`](licenses/OpenAI-LICENSE.txt), Apache-2.0).
- Kirill Khoruzhii's tensor-rank Lean library building on Jeroen Zuiddam's formalizations ([`licenses/Lemmata-LICENSE.txt`](licenses/Lemmata-LICENSE.txt), [`licenses/Lemmata-NOTICE.txt`](licenses/Lemmata-NOTICE.txt), Apache-2.0).
- Brouwer fixed-point formalization by `harfe` ([`licenses/FixedPointTheorems-LICENSE.txt`](licenses/FixedPointTheorems-LICENSE.txt), MIT).
