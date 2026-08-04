# 验证报告

生成日期：2026-08-04。Lean 4.32.2 + Mathlib v4.32.2，项目 `D:\AI\lean\project`。

## 1. 验证范围

对冗余机械臂神经网络运动学控制的三份公式源进行机器验证：

1. **推导文档上篇**（速度级 42 公式）：伪逆/零空间/通解/误差动态/关节极限/分段梯度（`Velocity.lean`）
2. **推导文档下篇**（加速度级推广）：乘积法则/加速度伪逆/通解/PD 误差动态/欧拉积分（`Accel.lean`）
3. **源论文 Ma et al. TSMC 2023**：(7)–(9) 限位统一化、(13)–(17) ASOA、(18)–(26) VAM Theorem 1、(29)–(36) 拉格朗日/RNN/单调性（`Paper.lean`）
4. 求解器数学核心：QP 凸性/一阶最优性、LVI、不动点等价、连续/离散投影神经网络（`QP_LVI_PNN.lean`、`ConvergenceAxioms.lean`）
5. 避障几何与 Li 函数（`Obstacle.lean`）
6. **源论文 Li, Zhang & Jin (2017) TNNLS**：控制律 (19)/Theorem 1 与速度补偿控制律 (41)/Theorem 2 的稳定性定理（`LiZhangJin.lean`）——投影最小距离性质链、Lyapunov 导数、不变集分析（0 ∈ int(Ω) 与平移版 J⁺ṙ_d ∈ int(Ω)）、LaSalle/Gronwall 组装

完整公式↔定理对照见 `formula-mapping.md`。

## 2. 验证状态

- 全部 `lake build` 通过（8663 jobs），**零 `sorry`/`admit`**
- 全库 **axiom 仅 3 个**（均为动力系统定理本体，见 §3）：`pnn_global_exponential_convergence`（Gao 2003）、`lasalle_global_convergence`（LaSalle 1960 / Khalil）、`exp_convergence`（Gronwall / Khalil）
- 定理 doc-comment 均标注来源（文档 (n)/论文 (n)）与验证假设
- **工作包 B 已全部完成**（2026-08-04 第二轮）：Theorem 1（控制律 (19)）与 Theorem 2（控制律 (41)）的验证链（含 6 个新定理 `proj_sq_ineq_at`/`V2_dot_algebra`/`V2dot_zero_implies_Pzero_at`/`proj_eq_y_implies_z_eq_y`/`theorem2_step1`/`theorem2`）已合并，`V1_dot_algebra` 的 2 个遗留 `sorry` 已消除

## 3. 假设清单（axiom）

| 假设 | 内容 | 引用来源 | 理由 |
|---|---|---|---|
| `pnn_global_exponential_convergence` | 投影动力系统 ẏ = γ(P_Ω(y−F(y))−y) 在 F 强单调（⟨x−y, Fx−Fy⟩ ≥ η‖x−y‖ₑ²）时全局指数收敛（eNorm 范数） | 论文 Lemma 1，引用 Gao (2003) IEEE TNN 14(2):426–431；Friesz et al. (1999) OR 42(6) | 定理本体需 Hilbert 空间单调算子 + 指数稳定性理论，超出本项目范围；**应用链全部机器验证**（F 构造、单调性、不动点等价、框投影实例化） |
| `lasalle_global_convergence` | V = ½‖e‖² 满足 V̇ = Vdot(e(t)) ≤ 0 且 V̇=0 ⟹ e=0 时，e(t) → 0（t → ∞） | LaSalle (1960) "Some extensions of Lyapunov's second method"；Khalil, Nonlinear Systems | 动力系统理论标准结果；**Theorem 1/2 的前提链全部机器验证**（`Vdot_nonpos`/`Vdot_zero_implies_Pzero`/`proj_zero_implies_JTe_zero`/`JTe_zero_implies_e_zero` 与平移版 (46)–(51)） |
| `exp_convergence` | V = ½‖x−x*‖² 满足 V̇ = Vdot(x(t)) ≤ −cV（c > 0）时，x(t) → x*（指数衰减） | Gronwall 不等式 / 比较引理（Khalil, Nonlinear Systems 定理 3.4） | 经典微分方程比较定理；**Theorem 2 Step 1 应用链全部机器验证**（`V1_dot_algebra`/`V1_decay`/`Vdot_deriv_comp`） |

## 4. 已知缺口（未验证项）

| 缺口 | 原因 | 处理 |
|---|---|---|
| 文档 (26) 原-对偶 LVI 一般情形（含不等式）的 KKT⟹LVI | 依赖凸函数一阶条件引理（Mathlib 对自定义内积实例支持有限） | 等式约束特例已证（`kkt_eq_only_implies_vi`）；一般情形记录为缺口 |
| 文档 (23) 反向（VI ⟹ QP 最优） | 同凸一阶条件 | 正向（最优⟹VI）已证 |
| 文档 (31) 的 β 谱界（β < 2/λ_max ⟹ ‖I−βM‖ < 1） | 谱理论（对称矩阵谱定理）；且该蕴含仅对谱范数成立（l∞ 范数有反例） | 离散收敛以 `‖I−βM‖ < 1`（l∞ 算子范数）为假设陈述，谱界推导记录为缺口 |
| 文档 (30) 的"矩阵不等式"一步 | Lyapunov 指数衰减的完整推导 | 由 §3 axiom 覆盖；代数应用链已证 |
| KKT ⟹ QP 最优（论文 Theorem 2 的收口） | 凸性 + 约束规格（强对偶） | `paper_theorem2_assembly` 以 hKKTopt 假设收口 |
| 文档 (32)(33) 预条件 RNN 的正定性论证 | 块矩阵 (I+Hᵀ) 的谱论证 | 未形式化（记录） |
| 文档 (36) 避障雅可比的链式法则梯度 | 依赖范数梯度 FDeriv 引理（自定义内积实例下受限） | 未形式化（记录） |
| 文档 (12)–(15) 连杆运动学、论文 GJK 算法本体 | 抽象层决定：运动学实体作符号；GJK 为迭代算法 | 明确不在验证范围 |
| 二阶 ODE 显式解（文档 (B.4) 后半） | 超出代数层 | 代数闭合已证，解形式记录 |
| LZJ 论文 (42) 的 λ_min(JJᵀ) > 0（rank JJᵀ = m ⟹ 正定） | 谱理论（对称矩阵特征值） | 以强单调假设 hmono（⟨x, JJᵀx⟩ ≥ c‖x‖ₑ²）陈述，`theorem2_step1` 依赖该假设 |
| LZJ 论文 "V̇₂ ≤ −(1/2)‖Pz−y‖²" 的投影平方下界 | (48) 配平方给出 ‖Pz−y‖² ≤ 2⟨z−y, Pz−y⟩，但 (46) 的 γ 因子丢失使论文 (49) 定量形式不精确 | `theorem2` 只断言 V̇₂ ≤ 0（LaSalle 需要），定量衰减率不验证 |

## 5. 验证中发现的数学问题（Lean 抓错实绩）

1. 文档 (19) `piecewiseGrad_endpoints` 缺前提 `θl < θu`（补正）
2. 文档 (23) 需 Q 对称假设（补正）
3. 文档 (39) Li 函数梯度符号与常规链式法则相反（勘误候选，待与 ALMM 原文比对）
4. 论文 (35) ∇F 的 −J_E 与 (34) 不一致（以 (34) 为准验证）
5. 文档 (31) β 条件为谱范数陈述，l∞ 范数下不成立（验证表述已修正）
6. **论文 (46) 丢失 γ 因子**：V̇₂ = eᵀJ(Pz−y) 应为 −γ⟨z−y, Pz−y⟩（伴随 + z = −Jᵀe/γ + y），论文原文写作 −⟨z−y, Pz−y⟩；γ > 0 不影响 V̇₂ ≤ 0 的结论，`V2_dot_algebra` 按正确版验证（Lean 抓错实绩）
7. **Theorem 2 的不变集论证需平移版 int(Ω)**：Theorem 1 用 0 ∈ int(Ω) 沿 −Jᵀe 方向取小步；Theorem 2 用 J⁺ṙ_d ∈ int(Ω)，沿 z−y 方向取小步 y' = y + ρ(z−y)/(2‖z−y‖) 得 ‖y'−z‖ = ‖z−y‖ − ρ/2 直接矛盾（`proj_eq_y_implies_z_eq_y`），不需 proj_zero_ineq 的二次型下界

## 6. 记号约定

- `Vec n = Fin n → ℝ`；`Mat m n`；矩阵×向量用 `*ᵥ`
- `inner ℝ x y` 欧氏内积（自定义实例，Mathlib 对 `Fin n → ℝ` 无 Inner）
- `‖·‖` = Mathlib sup 范数；`eNorm` = 欧氏范数（sqrt(Σxᵢ²)）
- 矩阵范数 = l∞ 算子范数（`open scoped Matrix.Norms.Operator`）

## 7. 复现

```bash
export ELAN_HOME="D:/AI/lean/elan"
cd "D:/AI/lean/project"
"D:/AI/lean/elan/bin/lake.exe" build          # 全量构建（8663 jobs）
grep -rn "sorry\|admit" LeanVerify/            # 应为空
# 唯一 axiom：
grep -rn "^axiom" LeanVerify/
```

## 8. 审查记录

- Task 1–7：每任务独立规格审查 + 代码质量审查（子代理）
- Task 8–11：内联执行后集中独立审查（2026-08-04），发现并修复 `linear_part_contraction` 空转定理及 l∞ 范数谱界注释错误
- Task 12–16：内联执行（自查：build 绿 + 零 sorry + git 干净）
- 建议：最终交付前可由审稿人/合作者通读各模块 doc-comment 与对照表
