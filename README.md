# 冗余机械臂控制公式 Lean 形式化验证

[![Lean 4.32.2](https://img.shields.io/badge/Lean%204.32.2-Mathlib%20v4.32.2-blue)](https://lean-lang.org)
[![Build](https://img.shields.io/badge/build-8663%20jobs%20%E2%9C%93-brightgreen)]()
[![Sorry](https://img.shields.io/badge/sorry-0-red)]()
[![Axioms](https://img.shields.io/badge/axioms-3%20documented-orange)]()

用 **Lean 4 + Mathlib** 对冗余机械臂神经网络运动学控制的核心公式进行**机器验证**——不是仿真、不是数值实验，而是逐条定理的严格形式化证明。所有定理可被计算机独立检查。

## 验证范围

| 来源 | 内容 | 模块 |
|---|---|---|
| 推导文档 · 速度级 | 伪逆 `J† = Jᵀ(JJᵀ)⁻¹` 与最小范数性质、零空间投影 `P₀ = I − J†J`、通解结构、误差动态、关节极限分段梯度 | `Velocity.lean` |
| 推导文档 · 加速度级 | 乘积法则 `p̈ = Jθ̈ + J̇θ̇`、加速度伪逆解、PD 误差动态、恒定加速度欧拉积分 | `Accel.lean` |
| 求解器数学核心 | QP 凸性/一阶最优性、LVI/不动点等价 `y = P(y−Fy)`、连续/离散投影神经网络收敛 | `QP_LVI_PNN.lean`、`ConvergenceAxioms.lean` |
| 避障几何 | 最近点配平方 `‖tv−w‖² = ‖v‖²(t−t*)² + ⋯`、Li 函数梯度 | `Obstacle.lean` |
| **Li, Zhang & Jin (2017) TNNLS** | 控制律 (19) 的 **Theorem 1** 与控制律 (41) 速度补偿的 **Theorem 2**：投影最小距离性质链、Lyapunov 导数、LaSalle/Gronwall 收敛、**非凸投影集**（论文核心贡献） | `LiZhangJin.lean` |

## 核心成果

- **控制律 (19) `u = P_Ω(Jᵀ(r_d−r)/γ)`（Theorem 1）**：`0 ∈ int(Ω)`、`J` 行满秩 ⟹ 误差 `e → 0`。完整验证了投影平方不等式 `‖Pz‖² ≤ 2⟨Pz,z⟩`、不变集分析 `P(−Jᵀe/γ)=0 ⟹ Jᵀe=0 ⟹ e=0`（论文 (23)–(37)），组装 LaSalle 收敛
- **控制律 (41) 速度补偿（Theorem 2）**：`J⁺ṙ_d ∈ int(Ω)` ⟹ 误差 `e → 0`。两步验证——Step 1 强单调条件 `⟨x,JJᵀx⟩ ≥ c‖x‖²` 下 `JJᵀw` 指数收敛到 `ṙ_d`（Gronwall，(42)）；Step 2 平移版不变集（论文 (46)–(51)，`z = −Jᵀe/γ + y` 处 `Pz = y ⟹ e = 0`）
- **投影集 Ω 无需凸性**：全部论证只依赖投影最小距离性质 `‖Pz−z‖ ≤ ‖y−z‖`（`hPdist` 假设）与内部点条件，与论文"任意集（非凸）"贡献一致
- **QP/KKT/LVI 不动点等价**：`LVI ⟺ y = P(y−Fy)`（论文 (8) 两方向）、RNN 平衡点（论文 (9)）、框投影实例化
- 8663 个构建任务全绿，**零 `sorry`/`admit`**

## 假设策略：仅 3 个 axiom

机器验证的边界是动力系统定理本体（超出代数层，均引用文献），**其前提与应用链全部严格验证**：

| Axiom | 内容 | 引用 |
|---|---|---|
| `pnn_global_exponential_convergence` | 投影动力系统 `ẏ = γ(P_Ω(y−F(y))−y)` 在 F 强单调时全局指数收敛 | Gao (2003) IEEE TNN；Friesz et al. (1999) |
| `lasalle_global_convergence` | `V̇ ≤ 0` 且 `V̇=0 ⟹ e=0` ⟹ `e(t) → 0` | LaSalle (1960)；Khalil, *Nonlinear Systems* |
| `exp_convergence` | `V̇ ≤ −cV`（Gronwall 比较引理）⟹ 指数收敛 | Khalil, *Nonlinear Systems* 定理 3.4 |

## Lean 抓到的数学问题（勘误实绩）

形式化验证不是复述公式——它把论文里的隐含假设与笔误暴露出来：

| # | 问题 | 处理 |
|---|---|---|
| 1 | 分段梯度端点性质缺前提 `θl < θu`（无反例为假） | 补正 |
| 2 | 一阶最优性⟹VI 需 Q 对称（非对称时不可归并） | 补假设 |
| 3 | 文档 (31) 的谱界 `β < 2/‖M‖` 仅对谱范数成立，l∞ 范数下有反例 | 验证表述修正 |
| 4 | Li 函数梯度符号与常规链式法则相反 | 按链式法则版验证（待与原文比对） |
| 5 | 论文 (35) 的 `−J_E` 与 (34) 不符 | 以 (34) 为准 |
| 6 | **论文 (46) 丢失 γ 因子**：`V̇₂` 应为 `−γ⟨z−y, Pz−y⟩`（γ > 0 不影响结论） | 按正确版验证 |

## 快速开始

```bash
# 工具链位于 D:\AI\lean\elan（Windows；ELAN_HOME=D:/AI/lean/elan）
export ELAN_HOME="D:/AI/lean/elan"
cd project
lake build                          # 8663 jobs 全绿
grep -rn "sorry\|admit" LeanVerify/ # 应为空
grep -rn "^axiom" LeanVerify/       # 应仅 3 个
```

## 项目结构

```
project/LeanVerify/
├── Core.lean               # 基础引理：eNorm 欧氏范数、内积、伪逆、零空间投影
├── Velocity.lean           # 速度级：控制律/误差动态/分段梯度
├── Accel.lean              # 加速度级：乘积法则/PD 误差动态/欧拉积分
├── QP_LVI_PNN.lean         # QP 凸性/KKT/LVI/不动点等价
├── ConvergenceAxioms.lean  # 收敛 axiom（Gao 2003）
├── Paper.lean              # Ma et al. TSMC 2023：(7)–(36)
├── Obstacle.lean           # 避障几何与 Li 函数
└── LiZhangJin.lean         # LZJ 2017 TNNLS：Theorem 1 & 2 完整验证
docs/
├── formula-mapping.md      # 公式 ↔ 定理对照表（§4 = Li-Zhang-Jin）
├── VERIFICATION.md         # 验证报告（范围/假设/缺口/勘误）
├── lean-work-notes.md      # 执行期环境实证与数学发现
└── 完整公式推导_速度级与加速度级_修正版.md  # Lean 验证发现的 6 处问题修正版
```

## 文档

- [公式 ↔ 定理对照表](docs/formula-mapping.md) —— 每条公式对应哪个 Lean 定理、验证状态
- [验证报告](docs/VERIFICATION.md) —— 范围、axiom 清单、已知缺口、勘误记录
- [工作笔记](docs/lean-work-notes.md) —— 环境实证与数学发现
- [推导文档修正版](docs/完整公式推导_速度级与加速度级_修正版.md) —— 推导文档 + Lean 修正

## 参考论文

- S. Li, Y. Zhang, L. Jin, "Kinematic Control of Redundant Manipulators Using Neural Networks," *IEEE TNNLS*, 28(10), 2017.
- Ma et al., *IEEE TSMC: Systems*, 2023（ALMM+ASOA 求解器，验证于 `Paper.lean`）
