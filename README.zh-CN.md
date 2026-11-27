# 加权图张量渐近秩的三块界（Lean 4 形式化）

[English](README.md) · [论文全文 (PDF)](paper/Three_Block_Bounds_for_the_Asymptotic_Rank_of_Weighted_Graph_Tensors.pdf) · [论文定理对照表](docs/PAPER_MAP.md) · [第三方许可证](licenses/)

本仓库用于存放论文的 Lean 4 形式化代码：

> **Three-Block Bounds for the Asymptotic Rank of Weighted Graph Tensors**
> Zhengyang Wang, Yichuan Cao, Hongbo Li, Xiao-Shan Gao

本仓库的长期目标是存放该论文全部定理的 Lean 4 形式化证明。**目前已完成并通过内核验证的部分为单位权奇圈 $C_m$ 的精确渐近秩指数与有限秩下界定理（Corollary 17）**，论文其余定理的形式化将在后续逐步补全。

## 当前已完成形式化的主结果（单位权奇圈 $C_m$）

| 论文位置 | Lean 入口声明 | 额外数学假设 |
|---|---|---|
| 单位权奇圈精确指数（Corollary 17(i)） | `OddCycleTarget.odd_equality_all` | 无（对任意域 $F$ 与任意奇数 $m \ge 3$ 无条件成立） |
| 二进渐近秩极限（Corollary 17(i)） | `OddCycleTarget.odd_limit` | 无 |
| 归一化超额恒等式 $(m-2)(\Gamma_F(C_m)-(m-1))=1/4$ | `OddCycleTarget.odd_normalized_excess` | 无 |
| 有限秩下界 $r_F(m,n)^{4(m-2)} \ge n^{(2m-3)^2}$（Corollary 17(ii)） | `OddCycleTarget.oddRankAndExponentLower` | 无（任意域 $F$、奇数 $m \ge 3$、整数 $n \ge 2$） |
| 显式整数分解见证（Corollary 17(iii)） | `OddCycleTarget.odd_upper_all` | 无 |

## 编译与验证

安装 [elan](https://github.com/leanprover/elan)、Git、Bash 与 Python 3。工具链固定为 **Lean `v4.35.0`**，Mathlib 固定在提交 `56a005855ea17e0b0958f73ec801ae140b0a1679`（复现时请勿执行 `lake update`）：

```sh
git clone https://github.com/MechMath/tensor-rank.git
cd tensor-rank
lake exe cache get
lake build +OddCycleTarget.Equality
lake env leanchecker OddRoot OddCycleTarget.Equality
lake env lean VerifyResults.lean
```

或直接运行完整审计脚本：

```sh
bash scripts/audit.sh
```

所有主要声明均不含 `sorry`、`admit` 或自定义公理，公理依赖审计仅报告 Lean 标准公理 `propext`、`Classical.choice` 与 `Quot.sound`，且通过独立内核检查器 `leanchecker` 重放校验。

## 许可证与上游致谢

本仓库采用 **Apache License 2.0** 协议（见 [`LICENSE`](LICENSE)）。仓库内嵌的上游 Lean 形式化库（OpenAI 谱几何与矩形矩阵乘法库、Kirill Khoruzhii / Jeroen Zuiddam 张量秩库及 `harfe` 不动点库）的完整许可证与声明均保留在 [`licenses/`](licenses/) 目录中。
