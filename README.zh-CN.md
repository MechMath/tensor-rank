# 加权图张量渐近秩的三块界（论文与 Lean 4 形式化）

[English](README.md) · [论文全文 (PDF)](paper/Three_Block_Bounds_for_the_Asymptotic_Rank_of_Weighted_Graph_Tensors.pdf) · [论文定理对照表](docs/PAPER_MAP.md) · [第三方许可证](licenses/)

本仓库用于统一存放以下论文的**全文稿件**及其**全部定理的完整 Lean 4 形式化证明**：

> **Three-Block Bounds for the Asymptotic Rank of Weighted Graph Tensors**
> Zhengyang Wang, Yichuan Cao, Hongbo Li, Xiao-Shan Gao
> 论文 PDF：[`paper/Three_Block_Bounds_for_the_Asymptotic_Rank_of_Weighted_Graph_Tensors.pdf`](paper/Three_Block_Bounds_for_the_Asymptotic_Rank_of_Weighted_Graph_Tensors.pdf)

**目前已完成并通过内核验证的形式化部分为单位权奇圈 $C_m$ 的精确渐近秩指数与有限秩下界定理（Corollary 17）**，论文其余定理的 Lean 4 形式化将在后续逐步补全。

## 论文简介与主要成果

给定加权图 $(G,w)$ 与固定域 $F$，每个顶点对应一个张量因子、每条边对应维数为 $2^{\lfloor t w_e \rfloor}$ 的缩并指标，由此定义加权图张量及其渐近秩指数 $\Gamma_F(G,w)$。将顶点划分为至多三块并限制到所得矩形矩阵乘法张量（指数记为 $U$），可得到精细化最大割（$\mathrm{MaxCut}$）压平界的**三块下界** $L_3(G,w)$；另一方面，在满足 $\mathrm{CAT}(0)$ 托勒密（Ptolemy）不等式与 Zhou 二次质量不等式的伪度量 $d$ 上最大化加权边长和，得到几何上界 $B_{\mathrm{PZ}}(G,w)$，从而有基本夹逼关系：

$$\mathrm{MaxCut}(G,w) \le L_3(G,w) \le \Gamma_F(G,w) \le B_{\mathrm{PZ}}(G,w).$$

本文围绕“$L_3(G,w)$ 何时精确刻画 $\Gamma_F(G,w)$，以及在近二分图上对 $\Gamma_F(G,w)$ 的控制有多紧”展开研究，主要成果分为四个部分：

1. **双树度量几何刻画与至多五个活动顶点的精确性（Theorems 4 & 8，Corollary 6，Proposition 7）**
   对任意加权图 $(G,w)$，证明 $L_3(G,w)$ 恰好等于所有满足 Zhou 二次质量不等式的**至多两棵树度量之和**的最大加权边长和，且“两棵树”这一阈值是紧的（三棵树即可在 $C_5$ 上违背托勒密不等式并严格超过真实指数）。结合托勒密几何与二阶变分分析，证明在任意域 $F$ 与任意非负实边权下，只要与正权边关联的顶点不超过 $5$ 个，恒有 $\Gamma_F(G,w) = B_{\mathrm{PZ}}(G,w) = L_3(G,w)$；并给出一致随机代表提升定理，可将小图精确性推广到任意规模的图。

2. **奇托勒密多边形不等式与任意权圈的精确指数（Theorems 11 & 13，Corollaries 17 & 20）**
   对任意托勒密伪度量空间中的奇多边形建立无条件周长–距离和不等式，进而对任意长度的圈与任意非负实权完全确定其渐近秩指数：对任意奇数 $m$（总权 $W$，下标模 $m$），

   $$
   \Gamma_F(C_m,w) = B_{\mathrm{PZ}}(C_m,w) = L_3(C_m,w) = \max_{0 \le i < m} U(W - w_{i-1} - w_i,\, w_{i-1},\, w_i),
   $$

   其最优三块划分总由孤立一个顶点、在余路径上交替排列另外两块实现。在单位权下给出 $\Gamma_F(C_m) = m - 1 + \frac{1}{4(m-2)}$（$m \ge 3$ 为奇数），并刻画极值谱度量的刚性、精确退化为最大割的参数室，以及带二分附件图与分层圈图的推广。

3. **近二分图：奇圈打包、一致比值界与精确子类（Theorems 23, 25, 26, 29, 30 & 32；Conjecture 39）**
   针对正权支集删除至多两条边即可变为二分图的图类，结合分数奇圈打包与 Hu 双商品流定理，证明：
   - 对任意域与任意非负实权，成立一致比较界 $L_3(G,w) \le \Gamma_F(G,w) \le \frac{100}{93}\,L_3(G,w)$，当正权支集不含 $K_4$ 时进一步改进为 $\frac{19}{18}$；
   - 在三角形边指示向量生成的非负锥上，$\Gamma_F(G,w) = L_3(G,w)$ 对任意顶点数与三角形数均精确成立；
   - 完全分类“删去一条单位权边即成二分图”的正整数权图的 $\Gamma_F$，给出任意权 $k$-页书图的 $O(k^2)$ 精确公式，并证明两距离托勒密–Zhou 表的精确控制。该二删边图类在一般权下是否恒有 $\Gamma_F = L_3$ 仍为开放问题（Conjecture 39）。

4. **完全图、主导边渐近修正、SDP 边界与算术电路对比（Propositions 2, 33 & 36–38；Theorem 34）**
   记录单位权完全图 $K_m$ 的精确律 $\Gamma_F(K_m) = m^2/4$ 与有限秩下界 $r^4 \ge n^{m^2}$；将 $B_{\mathrm{PZ}}$ 与 Goemans–Williamson 半定规划割界对比，并构造 6 顶点三删边反例给出 $B_{\mathrm{PZ}} - L_3 = 27/1846 > 0$；对任意图上单条主导边权 $q \to \infty$ 时的渐近行为确定一阶精确修正 $\lim_{q\to\infty} q(\Gamma_F(q) - q - M) = H^2/4$；最后将分离张量秩与允许复用中间乘积的无除法算术电路对比，证明任意加权矩阵圈 $C_m$ 的电路指数为 $\tau_F(C_m,w) = \max_i U(\min_j w_j, w_i, w_{i+1})$（单位权下对所有 $m$ 均为 $9/4$），并对单位四面体 $K_4$ 给出 $27/8 \le \tau_F(K_4) \le 4 - 23/120000$。

## Lean 4 形式化进展

### 当前已完成形式化的主结果（单位权奇圈 $C_m$）

| 论文位置 | Lean 入口声明 | 额外数学假设 |
|---|---|---|
| 单位权奇圈精确指数（Corollary 17(i)） | `OddCycleTarget.odd_equality_all` | 无（对任意域 $F$ 与任意奇数 $m \ge 3$ 无条件成立） |
| 二进渐近秩极限（Corollary 17(i)） | `OddCycleTarget.odd_limit` | 无 |
| 归一化超额恒等式 $(m-2)(\Gamma_F(C_m)-(m-1))=1/4$ | `OddCycleTarget.odd_normalized_excess` | 无 |
| 有限秩下界 $r_F(m,n)^{4(m-2)} \ge n^{(2m-3)^2}$（Corollary 17(ii)） | `OddCycleTarget.oddRankAndExponentLower` | 无（任意域 $F$、奇数 $m \ge 3$、整数 $n \ge 2$） |
| 显式整数分解见证（Corollary 17(iii)） | `OddCycleTarget.odd_upper_all` | 无 |

完整论文定理与 Lean 声明对照（含后续待补全计划）见 [`docs/PAPER_MAP.md`](docs/PAPER_MAP.md)。

### 编译与验证

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
