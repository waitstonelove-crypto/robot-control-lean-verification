# 公式 ↔ Lean 定理对照表

生成日期：2026-08-04。对照关系：推导文档《完整公式推导_速度级与加速度级.md》（下称"文档"）与源论文 Ma et al. IEEE TSMC 2023（下称"论文"）的公式，对应 `D:\AI\lean\project\LeanVerify\` 中的 Lean 定理。

状态图例：✅ 已机器验证 / ⚠ 部分验证或依赖假设（见备注）/ 📌 假设（axiom）/ ❌ 未覆盖（明确记录）

## 1. 文档上篇：速度级（42 公式）

| 公式 | 内容摘要 | Lean 定理 | 状态 |
|---|---|---|---|
| (1) 正运动学 | p = f(θ) | —（抽象层：f 为符号映射，链式法则作为假设 hpd/hp 使用） | ⚠ 定义层 |
| (2) 微分运动学 | ṗ = Jθ̇ | 以 FDeriv 假设形式嵌入 `error_dynamics` 的 hp | ⚠ 定义层 |
| (3) 雅可比列向量 | 旋量理论列 | —（与论文 (3) 无关，见核对记录） | ❌ 未形式化 |
| (4) 伪逆解 | J† = Jᵀ(JJᵀ)⁻¹，最小范数 | `rpinv`, `rpinv_mul_self_mul`（MP1）, `rpinv_self_mul_self`（MP2）, `rpinv_mul_conjTranspose`（MP3）, `rpinv_self_conjTranspose`（MP4）, `rpinv_min_norm` | ✅ |
| (5) 伪逆性质 | JJ† = I_m；J†J ≠ I_n（m<n） | `rpinv_mul_eq_one`；"≠"未证（秩论证） | ✅ / ⚠ |
| (6) 零空间投影 | P₀ = I − J†J，幂等，JP₀ = 0 | `nullProj`, `nullProj_idempotent`, `nullProj_symmetric`, `jacobian_mul_nullProj`, `nullProj_in_nullspace`, `nullProj_eq_self_of_mem_nullspace`, `nullProj_inner_nonneg` | ✅ |
| (7) 梯度投影法 | dH/dt = ∇HᵀJ†ṗ_d + α‖P₀∇H‖² | `nullspace_gradient_contrib`（零空间项非负部分） | ⚠ 非负项已证，全式依赖链式法则假设 |
| (8) 完整控制方案 | θ̇ = J†(c+ke) + P₀φ | `control_law_apply` | ✅ |
| (9) 通解 | J(J†v + P₀φ) = v | `general_solution` | ✅ |
| (10) 位置误差 | e = p_d − p | —（定义层，嵌入 `error_dynamics` 的 he） | ⚠ 定义层 |
| (11) 误差动态 | ė = −ke，解 e(0)e^{−kt} | `error_dynamics`, `exp_solution_ode`, `exp_decay` | ✅ |
| (12)(13) 连杆位置 | p_e/p_i = f_i(θ) | —（抽象层） | ❌ 未形式化 |
| (14)(15) 连杆雅可比/速度 | J_i 截断、ṗ_i = J_iθ̇ | — | ❌ 未形式化 |
| (16) 关节中间值 | θ_M = (θ⁺+θ⁻)/2 | `hFunc_max_at_mid` 内使用 | ⚠ 定义层 |
| (17) 极限函数 | h(θ)，最大值 1/4 在 θ_M | `hFunc`, `hFunc_max_at_mid` | ✅ |
| (18) 梯度向量 | ∂h/∂θ_i = (∏_{j≠i}h_j)·h'_i | `hFunc_partial_deriv` | ✅ |
| (19) 分段梯度 | 双向势场，θ_M 处不连续 | `piecewiseGrad`, `piecewiseGrad_lower`, `piecewiseGrad_upper`, `piecewiseGrad_endpoints`, `piecewiseGrad_jump_at_mid` | ✅（endpoints 需 θl < θu，已补前提） |
| (20)(21) QP 形式 | min ½xᵀQx + cᵀx，Ax ≤ b, Ex = d | `feasibleSet`（可行域）、`KKT`（最优性条件载体） | ⚠ 定义层 |
| (22) 可行域凸性 | Ω 凸 | `feasibleSet_convex`, `feasibleSetBox_convex` | ✅ |
| (23) VI | 最优 ⟹ ⟨x−x*, Qx*+c⟩ ≥ 0 | `qp_optimal_implies_vi`（需 Q 对称，见备注） | ✅（Q 对称假设） |
| (24) LVI | F = Qx + c | `VI` 定义 | ⚠ 定义层 |
| (25) 框约束 | l ≤ y ≤ h | `feasibleSetBox`, `boxProj` | ✅ |
| (26) 原-对偶 LVI | KKT ⟹ 分量不等式 | `kkt_eq_only_implies_vi`（等式约束特例） | ⚠ 一般情形未证（凸一阶条件） |
| (27) 投影算子 | P_Ω = max(l, min(y, h)) | `boxProj`, `boxProj_mem`, `boxProj_fixedPoint`, `boxProj_char` | ✅ |
| (28) 不动点等价 | LVI ⟺ y = P(y−Fy) | `fixed_point_implies_VI`, `VI_implies_fixed_point`, `VI_iff_fixed_point_box` | ✅ |
| (29) 连续 RNN | ẏ = γ(P(y−Fy) − y) | `pnn_equilibrium`, `box_pnn_equilibrium_implies_VI` | ✅ |
| (30) Lyapunov 收敛 | 全局指数收敛 | `ConvergenceAxioms.pnn_global_exponential_convergence`（📌 引用 Gao 2003）+ 应用链 `lyapunov_deriv`, `affine_F_diff`, `nonexpansive_step`, `nonexpansive_step_affine`, `smul_identity_strong_monotone`（标量情形） | 📌 + ✅ 应用链 |
| (31) 离散 RNN | y_{k+1} = P(y_k − βF(y_k)) | `discIter`, `discIter_converges`（Banach） | ✅（β 谱界为假设 hLin，见备注） |
| (32)(33) 预条件 | (I+Hᵀ) 加速 | — | ❌ 未形式化（正定性论证见备注） |
| (34) RNN 最终形式 | = (29) | `pnn_convergence`（框投影实例化） | ✅ |
| (35) 最小距离 | d = min‖q−q'‖ | `linkSphereDist`（球障碍简化） | ⚠ 定义层 |
| (36) 避障雅可比 | ∂d/∂θ = nᵀJ | —（链式法则，依赖范数梯度引理） | ❌ 未形式化 |
| (37) 最近点 | t* = ⟨v,w⟩/‖v‖² | `norm_sq_complete_square`, `closest_point_param` | ✅ |
| (38) 最小距离值 | d = ‖q_si−c‖ − r | `linkSphereDist`, `safety_sign` | ✅ |
| (39) Li 函数 | L_i = w₁‖p_E−p‖² + w₂⟨p_E−p, ṗ_E⟩ | `liFunc`, `liFunc_grad_algebra` | ✅（梯度符号勘误，见 §3） |

## 2. 文档下篇：加速度级推广

| 公式 | 内容摘要 | Lean 定理 | 状态 |
|---|---|---|---|
| (A.1) 正运动学 | 不变 | — | ⚠ 定义层 |
| (A.2a) 速度级 | ṗ = Jθ̇ | — | ⚠ 定义层 |
| (A.2b) 加速度级 | p̈ = Jθ̈ + J̇θ̇ | `accel_kinematics_prodRule` | ✅ |
| (B.1) 伪逆解 | θ̈ = J†(p̈_d − J̇θ̇) | `accel_pinv_solves`, `accel_pinv_min_norm` | ✅ |
| (B.2) 通解 | + P₀φ | `accel_general_solution` | ✅ |
| (B.3) 零空间优化 | + αP₀∇H | 同 (B.2) + (7) 的组合 | ⚠ 组合未单列 |
| (B.4) PD 误差动态 | ë + k_dė + k_p e = 0 | `pd_error_algebra`（代数闭合） | ⚠ 二阶 ODE 显式解不在范围 |
| (B.5) 完整控制律 | p̈ = p̈_d + k_dė + k_p e | `pd_control_law_closed` | ✅ |
| (C.1) 加速度 QP | 结构不变，右端替换 | 同 (20)(21) 定义层 | ⚠ 定义层 |
| (D.1) 加速度 RNN | 结构不变 | `pnn_convergence`（通用 M） | ✅ |
| (E) 积分链 | 恒定加速度二阶欧拉 | `euler_constant_accel` | ✅ |
| (F) 对照表 | — | —（文档性） | — |

## 3. 论文公式（Ma et al. TSMC 2023）

| 公式 | 内容摘要 | Lean 定理 | 状态 |
|---|---|---|---|
| (1)(2)(3) 运动学 | 速度/加速度级 | `accel_kinematics_prodRule`（(3)） | ✅ (3)；⚠ (1)(2) 定义层 |
| (4)(5)(6) 误差反馈 | J_Eθ̈ = r̈_G | `pd_control_law_closed`（同型代数） | ✅（记号对齐见备注） |
| (7)(8)(9) 限位统一化 | η⁻/η⁺ | `etaLow`, `etaHigh`, `eta_bounds`, `eta_tightening`, `etaLow_le_iff`, `etaHigh_ge_iff` | ✅ |
| (10)(11)(12) GJK 距离 | 定义层 | —（GJK 算法本身不形式化） | ⚠ 定义层 |
| (13)–(17) ASOA | 逃逸加速度不等式 | `asoa_basic_ineq`, `asoaB`, `asoa_constraint` + `otimes`, `otimes_mul` | ✅（u 单位/非负投影假设注明） |
| (18)–(26) VAM + Theorem 1 | min ½(α‖θ̇‖²+β‖θ̈‖²) ⟺ min ½θ̈ᵀθ̈ + αζθ̇ᵀθ̈ | `vam_expand`, `vam_equiv`, `vam_equiv_minimizer` | ✅ |
| (27)(28) QP | 最终 QP 形式 | `feasibleSet`/`KKT` 定义层 | ⚠ 定义层 |
| (29) 拉格朗日 | L(θ̈, ϑ, ν) | `lagrangian` | ✅ |
| (30) KKT 投影形式 | θ̈ = P_V(θ̈−∂L/∂θ̈) 等 | `lagrangian_quadratic`（∂L/∂θ̈ 代数层）、`fixed_point_iff_first_order`（(30a) 等价）、`nonneg_proj_fixed_point`（(30c) 互补） | ✅（FDeriv 封装降级为代数层） |
| (31) RNN 动力学 | 三分量 | `paper_theorem2_assembly` 组装 | ✅ |
| (32)(33) 收敛引理 | Lemma 1（Gao 2003） | `pnn_global_exponential_convergence`（📌） | 📌 |
| (34)(35)(36) 单调性 | ∇F+∇Fᵀ = diag(2I,0,0) ⪰ 0 | `F_monotone`, `F_monotone_nonneg` | ✅（注：论文 (35) 的 −J_E 与 (34) 不符，以 (34) 为准） |
| Theorem 2 | RNN 收敛到 QP 最优 | `paper_theorem2_assembly` + 📌 收敛 axiom + hKKTopt 假设 | ⚠ 骨架（KKT⟹最优为假设） |

## 4. Li, Zhang & Jin (2017) TNNLS 稳定性定理（工作包 B）

来源：Li, Zhang & Jin, "Kinematic Control of Redundant Manipulators Using Neural Networks", IEEE TNNLS 28(10), 2017（`LiZhangJin.lean`）。核心贡献点：投影集 Ω 任意（非凸），无需凸性。

| 论文公式 | 内容摘要 | Lean 定理 | 状态 |
|---|---|---|---|
| 控制律 (19) | u = P_Ω(Jᵀ(r_d−r)/γ) | —（控制律本体，嵌入 theorem1 前提） | ⚠ 前提层 |
| 误差动态 (21) | ė = JP_Ω(−Jᵀe/γ) | —（嵌入 theorem1 的 hflow） | ⚠ 前提层 |
| (23) 投影最小距离 | y ∈ Ω ⟹ ‖Pz−z‖ₑ ≤ ‖y−z‖ₑ | `proj_dist_le_norm`（hPdist 假设）、0 ∈ Ω 特例 | ✅（hPdist 为公理化假设） |
| (25) 投影平方不等式 | 0 ∈ Ω ⟹ ‖Pz‖ₑ² ≤ 2⟨Pz, z⟩ | `proj_sq_ineq` | ✅ |
| (26) V̇ ≤ 0 | V = ½‖e‖²，V̇ = ⟨e, JP(−Jᵀe/γ)⟩ ≤ 0 | `Vdot_nonpos` | ✅ |
| (28)(29) V̇=0 ⟹ Pz=0 | ‖Pz‖² ≤ 2⟨Pz,z⟩ 与 ⟨e,JPz⟩ = −γ⟨z,Pz⟩ | `Vdot_zero_implies_Pzero` | ✅ |
| (30)–(33) 投影零点引理 | Pz = 0 时 ∀y ∈ Ω, ‖y‖² + (2/γ)⟨Jᵀe,y⟩ ≥ 0 | `proj_zero_ineq` | ✅ |
| (34)–(36) 0 ∈ int(Ω) ⟹ Jᵀe = 0 | 沿 −Jᵀe 取小步 y ∈ Ω 得 ρ ≥ 4‖Jᵀe‖/γ，取 ρ = min(ρ₀/2, c/2) 矛盾 | `proj_zero_implies_JTe_zero` | ✅ |
| (37) 行满秩 ⟹ e = 0 | Jᵀe = 0 且 JJᵀ 可逆 ⟹ e = 0 | `JTe_zero_implies_e_zero` | ✅ |
| Theorem 1 | 控制律 (19)、0 ∈ int(Ω)、J 行满秩 ⟹ e → 0 | `theorem1`（Vdot_deriv + LaSalle axiom 组装） | ✅（LaSalle 本体为 📌，前提链全机器验证） |
| (40) costate 动态 | ẇ = (ṙ_d − JJᵀw)/γ，v = Jᵀw | —（嵌入 theorem2_step1 的 hflow） | ⚠ 前提层 |
| (41) 控制律 | u = P(Jᵀ(r_d−r)/γ + Jᵀw) | —（嵌入 theorem2 的 hflow） | ⚠ 前提层 |
| (42) V₁ 衰减代数 | V̇₁ = −(1/γ)⟨x, JJᵀx⟩，x = JJᵀw − ṙ_d | `V1_dot_algebra`, `V1_decay`（强单调 c ⟹ ≤ −(2c/γ)V₁） | ✅ |
| Theorem 2 Step 1 | JJᵀw 指数收敛到 ṙ_d | `theorem2_step1`（Vdot_deriv_comp + exp_convergence axiom） | ✅（Gronwall 本体为 📌） |
| (43) 不变集控制律 | w = (JJᵀ)⁻¹ṙ_d ⟹ u = P(Jᵀ(r_d−r)/γ + J⁺ṙ_d) | —（J⁺ = rpinv 已在 Core 验证；嵌入 theorem2 的 hflow） | ⚠ 前提层 |
| (46) V₂ 代数 | z = −Jᵀe/γ + y ⟹ ⟨e, J(Pz−y)⟩ = −γ⟨z−y, Pz−y⟩ | `V2_dot_algebra`（注：论文原文丢失 γ 因子，见 §5） | ✅ |
| (48) 平移投影不等式 | y ∈ Ω ⟹ ‖Pz−y‖ₑ² ≤ 2⟨z−y, Pz−y⟩ | `proj_sq_ineq_at` | ✅ |
| (49) V̇₂ ≤ 0 | V̇₂ = −γ⟨z−y, Pz−y⟩ ≤ 0 | 组装在 `theorem2` 的 hneg | ✅ |
| (50) V̇₂=0 ⟹ Pz=y | 从 (48) 与 (46) | `V2dot_zero_implies_Pzero_at` | ✅ |
| (51) y ∈ int(Ω) ⟹ Jᵀe = 0 | 沿 z−y 方向取小步 y' ∈ Ω 得 ‖y'−z‖ < ‖y−z‖ 矛盾（平移版不变集） | `proj_eq_y_implies_z_eq_y`, `proj_eq_y_implies_JTe_zero` | ✅ |
| Theorem 2 | 控制律 (41)、J⁺ṙ_d ∈ int(Ω)、J 行满秩 ⟹ e → 0 | `theorem2`（LaSalle axiom 组装） | ✅（LaSalle/Gronwall 本体为 📌，前提链全机器验证） |

## 5. 核对发现与勘误记录

1. **文档 ≠ 论文转写**：文档 (3)–(9)、(16)–(19)、(20)–(34)、(35)–(38)、(39) 与论文对应公式不同源（详见 `lean-work-notes.md` §1 与设计文档 §3）
2. **文档 (19) `piecewiseGrad_endpoints`** 需前提 `θl < θu`（无反例为假），已补
3. **文档 (23) 一阶最优性** 需 Q 对称（非对称时第一阶项含 ⟨x*,Qδ⟩ 不可归并），已补假设
4. **文档 (31) β < 2/‖M‖** 为谱范数陈述；本验证用 l∞ 算子范数（Mathlib 默认矩阵范数），该蕴含对 l∞ 不成立（有反例），离散收敛以 `‖I−βM‖ < 1` 为假设陈述
5. **文档 (39) Li 函数梯度符号**：文档写正号；常规约定（p_E、ṗ_E 与 θ 无关）下链式法则给负号，`liFunc_grad_algebra` 按负号版验证，符号约定待与 ALMM 原文（Yang et al. TII 2024）比对
6. **论文 (35) ∇F 的 (2,1) 块 −J_E** 与 (34) 的 F₂ = J_Eθ̈ − r̈G 不符（∂F₂/∂θ̈ = +J_E）；本验证以 (34) 为准，单调性结论 ‖δx‖² 与 (36) 的 diag(2I,0,0) 一致
7. **范数记号**：`‖·‖` = Mathlib sup 范数（boxProj_nonexpansive 等），`eNorm` = 欧氏范数（最小范数/配平方/VAM 等）——各定理 doc-comment 已注明
