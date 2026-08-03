# Lean 验证项目工作笔记

最后更新：2026-08-04（Task 8 完成）。本文件是执行期经验与状态的"作战手册"，供后续任务与未来会话直接使用。

## 1. 项目状态

- 仓库：`D:\AI\lean`（git，分支 `feat/lean-verification`），lake 项目 `D:\AI\lean\project`（Lean 4.32.2 + Mathlib v4.32.2）
- 工具链：`ELAN_HOME=D:/AI/lean/elan`；构建：`cd "D:/AI/lean/project" && "D:/AI/lean/elan/bin/lake.exe" build`
- 提交惯例：`cd "D:/AI/lean" && git add -A && git -c user.name="wj" -c user.email="wj@local" commit -m "<msg>"`

### 模块与定理（截至 Task 8）

| 文件 | 内容 | 状态 |
|---|---|---|
| `LeanVerify/Core.lean` | Vec/Mat、instInnerVec（欧氏内积）、boxProj 族（含非扩张）、eNorm 族、rpinv+MP4、nullProj 族、general_solution、rpinv_min_norm、vec_inner_{add,symm,smul,neg}_*、vec_mulVec_adjoint | ✅ |
| `LeanVerify/Velocity.lean` | control_law_apply、nullspace_gradient_contrib、error_dynamics、exp_solution_ode、exp_decay、hFunc + max_at_mid、hFunc_partial_deriv、piecewiseGrad 族 | ✅ |
| `LeanVerify/Accel.lean` | accel_kinematics_prodRule（乘积法则）、accel_pinv_solves/min_norm、accel_general_solution、pd_error_algebra、pd_control_law_closed、euler_constant_accel | ✅ |
| `LeanVerify/QP_LVI_PNN.lean` | feasibleSet + 凸性、feasibleSetBox、VI、KKT、qp_optimal_implies_vi（需 Q 对称）、kkt_eq_only_implies_vi | ✅ |

**已完成任务：0-8**（Task 9-17 待办）。

## 2. 环境实证（Mathlib v4.32.2 踩坑记录，违反必卡）

1. **矩阵运算语句必须用 `Matrix (Fin m) (Fin n) ℝ` 拼写**——`Mat m n` 缩写使类型类实例检索失败（DiscrTree 按头部常量匹配）。`Mat` 只用于逐点运算
2. **矩阵×向量没有 `*` 记号**：一律 `J *ᵥ x`（`Matrix.mulVec`）；`M.mulVec (N.mulVec x) = (M*N).mulVec x` 用 `Matrix.mulVec_mulVec`
3. **`inner ℝ x y` 显式场参数**（裸 `inner` 失败）；内积展开用 `inner_vec_eq_sum`（@[simp]）
4. **Mathlib 对 `Vec n = Fin n → ℝ` 的范数是 sup 范数**，与内积不相容（‖x‖² ≠ ⟨x,x⟩）。欧氏范数 = `eNorm`（Core 定义，eNorm² = inner self）。最小范数/配平方/VAM 展开类定理**必须用 eNorm**
5. **`[LinearOrder]` 类引理（le_max_left 等）裸调用卡死类型合成**——显式传参数
6. **`½` 记号本工具链解析失败**（"unexpected token"）——用 `(1 / 2)`
7. **`x*` 不是合法标识符**（`*` 不能进标识符）——用 `xstar`
8. **`λ` 是保留字**——用 `lam`
9. **HasFDerivAt 的线性映射参数**：`fun x => x • v` 无法类型检查，必须用 `ContinuousLinearMap.toSpanSingleton ℝ v`（定义相等于 `fun x => x • v`，`toSpanSingleton_apply : toSpanSingleton R x r = r • x := rfl`）
10. **`fun_prop` 不处理 HasDerivAt 目标**（4.32.2）——手工组合 `hasDerivAt_id`/`.const_smul`/`.const_mul`/`.mul`/`.div_const` + `convert` + `ring`/`simp [div_eq_mul_inv, mul_comm]`（ring_nf 不化简 1/2 类数值系数）
11. **有限乘积导数**：`HasDerivAt.finsetProd`（`finset_prod` 已废弃）；和式坍缩 `smul_ite` + `Finset.sum_ite_eq'` + `Finset.prod_filter`
12. **可逆矩阵引理族**：`Matrix.mul_nonsing_inv`/`nonsing_inv_mul`（需 `IsUnit A.det`）+ 无条件 `Matrix.transpose_nonsing_inv`，经 `Matrix.isUnit_iff_isUnit_det` 转换
13. **向量加法重排**：`abel`（含标量 • 项当原子）；`ring_nf`/`linarith` 处理向量等式会失败
14. **`(a • x) i` 需 `simp` 展开为 `a * x i` 后再 ring**
15. **内积伴随**：`vec_mulVec_adjoint : inner ℝ (A *ᵥ x) y = inner ℝ x (Aᵀ *ᵥ y)`（Core，自定义实例下自行硬算）
16. **极限/邻域**：`Tendsto` 需 `open Filter`；`𝓝[>]` 需 `open scoped Topology`；`mem_nhdsWithin_iff_exists_mem_nhds_inter` 在**根命名空间**；`nhdsWithin_le_nhds` 隐式参数（不要显式传）；`Ioi_mem_nhds (h : a < b) : Ioi a ∈ 𝓝 b`、`Iio_mem_nhds` 同型；`inter_mem_iff` 拼 filter 隶属交集；`ge_of_tendsto h h' : b ≤ a`（h' : ∀ᶠ x, b ≤ f x）——注意方向是 `ge_of_tendsto`
17. **`div_le_iff` 已改名 `div_le_iff₀`**；`HasDerivAt.comp` 第一显式参数是点 t
18. **`IsOpen.mem_nhds hs hx`**（两个参数）；`isOpen_Ioo` 参数隐式
19. **ext 对连续线性映射等式**：显式 `apply ContinuousLinearMap.ext`；`simp` 会把 `x • a` 重写为乘法并触发 `mul_eq_mul_left_iff` 析取——用 `rw` 链 + 定向 `simp [Matrix.mulVec, dotProduct, Finset.sum_add_distrib]`

## 3. 数学事实（执行期发现，写入对照表/VERIFICATION.md）

- **文档 (39) Li 函数梯度符号待核对**（文档写正号；p_E、ṗ_E 与 θ 无关时链式法则给负号）——Task 16 处理，需与 ALMM 原文比对
- **`qp_optimal_implies_vi` 需要 Q 对称假设**（计划原文漏了；非对称 Q 下第一阶项含 ⟨x*,Qδ⟩ 无法归并）
- **`piecewiseGrad_endpoints` 需要 `θl < θu` 前提**
- 文档 (30) Lyapunov 的"矩阵不等式"步骤 → Task 10 的 axiom
- 文档 (28) 不动点等价 → Task 9 用投影特征不等式证（比文档的"方向极限"论证更干净）

## 4. 已知缺口（对照表 ⚠ 条目）

1. 文档 (26) 一般情形（含不等式）的 KKT⟹LVI：依赖凸一阶条件引理；当前只有 `kkt_eq_only_implies_vi`（等式特例）
2. 收敛性：Gao 2003 Lemma 1 / 文档 (30) → Task 10 axiom（ConvergenceAxioms.lean）
3. 离散 RNN (31) 的谱界（β < 2/‖M‖ ⟹ 压缩）依赖谱理论，可能标注
4. 二阶 ODE 显式解（文档 (B.4) 后半）不在验证范围（已注明）
5. Task 8 为内联执行（自查），未独立审查——Task 11 后集中审查

## 5. 后续任务风险点（Task 9-17）

- **Task 9**（不动点等价）：投影特征不等式（Core boxProj_char 已有）两方向拼装；`boxProj` 的最近点唯一性（严格凸）——注意 sup 范数下 boxProj 仍是最近点吗？**不是**！框投影的"最近点"性质是欧氏意义——Task 9 若用 `hPdist`（距离最优性）需欧氏范数版本或改用特征不等式直接证（**推荐：全程只用 boxProj_char，不用距离**）
- **Task 10**（收敛 axiom）：语句用 boxProj + VI；`symm_pos_strong_monotone` 依赖谱理论（Mathlib `Matrix.PosSemidef` 探索；不行降级为条件传递）
- **Task 11**（离散）：Banach 不动点（`#find Contraction`/`Banach.fixed_point`）；谱界可能标注
- **Task 12**（⊗ 算子）：`otimes s h := fun j => inner ℝ (fun i => s i j) h`；`otimes_mul` 用 `Finset.sum_comm` 硬算；ASOA 不等式 `nlinarith` + `field_simp`（τ > 0）
- **Task 13**（η 统一化）：`max_le_iff`/`le_min_iff` 平凡部分 + 单调性 linarith
- **Task 14**（VAM 等价）：`norm_sq_add_real` 展开 + ring；注意 ½ 用 (1/2)
- **Task 15**（RNN/KKT）：拉格朗日梯度验证 FDeriv 链（参考 Task 4 error_dynamics 模式）；互补松弛 `max` 不动点分情况；`F_monotone` 展开硬算（伴随一次 + ring）——注意论文 (34) F₃ = b − JC⊗uCOθ̈ 的负号
- **Task 16**（最近点/Li）：配平方 `‖tv−w‖² = ‖v‖²(t−t*)² + ...` 用 `norm_sq_eq_inner` + `field_simp`；Li 函数先核对符号（见 §3）
- **Task 17**（文档）：formula-mapping.md 逐公式状态 + VERIFICATION.md axiom 清单；全量 build 收尾

## 6. 工作流备忘

- 每个任务完成后：`lake build` 全绿 + `grep -rn "sorry" LeanVerify/` 无输出 + git 干净
- 新模块需在 `LeanVerify.lean` 加 `import`
- 模块名 = 文件名（`lake build LeanVerify.QP_LVI_PNN` 而不是缩写）
- 定理语句与计划不一致时必须报告（如 Q 对称假设）；doc-comment 公式编号（文档 (n)/论文 (n)）
