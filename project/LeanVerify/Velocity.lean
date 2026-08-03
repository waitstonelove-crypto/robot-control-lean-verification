/-
Copyright (c) 2026 wj. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: wj
-/
import LeanVerify.Core

/-!
# Velocity：上篇核心链 —— 控制律 / 误差动态 / 梯度投影 / 关节极限 h 函数

对应文档第 2 章「速度层」：控制律 (8)、零空间项非负贡献 (7)、误差动态 (11)、
关节极限 h 函数 (17)。矩阵运算一律使用 `Matrix` 拼写与 `*ᵥ`，欧氏范数用 `eNorm`。
-/

namespace Velocity

open Filter
open Matrix
open scoped BigOperators
open scoped Topology

/-- 控制律代入验证：θ̇ = J†(c + ke) + P₀φ ⟹ ṗ = c + ke —— 文档 (8) -/
theorem control_law_apply {m n : ℕ} (J : Matrix (Fin m) (Fin n) ℝ) (h : IsUnit (J * Jᵀ))
    (c e : Vec m) (φ : Vec n) :
    J *ᵥ (rpinv J h *ᵥ (c + e) + nullProj J h *ᵥ φ) = c + e := by
  exact general_solution J h (c + e) φ

/-- 零空间项对 H 变化率的贡献非负：α·∇Hᵀ·P₀·∇H ≥ 0（α ≥ 0） —— 文档 (7) -/
theorem nullspace_gradient_contrib {m n : ℕ} (J : Matrix (Fin m) (Fin n) ℝ) (h : IsUnit (J * Jᵀ))
    (g : Vec n) (α : ℝ) (hα : 0 ≤ α) :
    0 ≤ α * inner ℝ g (nullProj J h *ᵥ g) := by
  exact mul_nonneg hα (nullProj_inner_nonneg J h g)

/-- 误差动态：控制律 (8)（θ̇ = J†(ṗ_d + ke) + P₀φ）下，e = p_d − p 满足 ė = −ke
   —— 文档 (11)（代数代入 + 导数封装）。
   记号说明：FDeriv 要求连续线性映射，`u ↦ u • v` 的捆绑形式用
   `ContinuousLinearMap.toSpanSingleton ℝ v`（逐点定义为 `fun u ↦ u • v`）。 -/
theorem error_dynamics {m n : ℕ} (J : Matrix (Fin m) (Fin n) ℝ) (h : IsUnit (J * Jᵀ)) (k : ℝ)
    (pd p e : ℝ → Vec m) (pd' : ℝ → Vec m) (φ : Vec n)
    (he : ∀ t, e t = pd t - p t)
    (hpd : ∀ t, HasDerivAt pd (pd' t) t)
    (hp : ∀ t, HasFDerivAt p (ContinuousLinearMap.toSpanSingleton ℝ
      (J *ᵥ (rpinv J h *ᵥ (pd' t + k • e t) + nullProj J h *ᵥ φ))) t) :
    ∀ t, HasDerivAt e (-k • e t) t := by
  intro t
  let v := J *ᵥ (rpinv J h *ᵥ (pd' t + k • e t) + nullProj J h *ᵥ φ)
  -- 速度代入：ṗ = J·(J†(ṗ_d + ke) + P₀φ) = ṗ_d + ke（通解结构 general_solution）
  have hpD : HasDerivAt p v t := by
    simpa [v] using (hp t).hasDerivAt
  -- ė = ṗ_d − ṗ（e = p_d − p 逐点成立，代入导数）
  have hsub : HasDerivAt (pd - p) (pd' t - v) t := (hpd t).sub hpD
  -- 代数核心：ṗ_d − (ṗ_d + ke) = −ke
  have hval : pd' t - v = -k • e t := by
    dsimp [v]
    rw [general_solution J h (pd' t + k • e t) φ]
    ext i
    simp
  have hfinal : HasDerivAt (pd - p) (-k • e t) t := by
    simpa [hval] using hsub
  -- 由 he 把函数 pd − p 还原为 e
  exact hfinal.congr_of_eventuallyEq (Eventually.of_forall he)

/-- ė = −ke 的解验证：e(t) := e0·exp(−kt) 满足微分方程 —— 文档 (11) -/
theorem exp_solution_ode {n : ℕ} (e0 : Vec n) (k : ℝ) (t : ℝ) :
    ∀ i : Fin n, HasDerivAt (fun s : ℝ => e0 i * Real.exp (-k * s))
      (-k * (e0 i * Real.exp (-k * t))) t := by
  intro i
  -- 内部导数：d/dt [−k·t] = −k
  have h1 : HasDerivAt (fun s : ℝ => -k * s) (-k) t := by
    simpa using (hasDerivAt_id t).const_mul (-k)
  -- 链式法则 + 常数乘：d/dt [e0_i·exp(−kt)] = e0_i·(exp(−kt)·(−k))
  have hh : HasDerivAt (fun s : ℝ => e0 i * Real.exp (-k * s))
      (e0 i * (Real.exp (-k * t) * (-k))) t := by
    exact ((Real.hasDerivAt_exp (-k * t)).comp t h1).const_mul (e0 i)
  rw [show e0 i * (Real.exp (-k * t) * (-k)) = -k * (e0 i * Real.exp (-k * t)) by ring] at hh
  exact hh

/-- k > 0 时指数衰减：exp(−kt) → 0 (t → ∞) —— 文档 (11) 收敛性 -/
theorem exp_decay (k : ℝ) (hk : 0 < k) :
    Tendsto (fun t : ℝ => Real.exp (-k * t)) atTop (𝓝 0) := by
  -- k·t → +∞（k > 0），再取负得 −k·t → −∞，exp 在 −∞ 处趋于 0
  have hkpos : Tendsto (fun t : ℝ => k * t) atTop atTop := by
    have h := tendsto_const_mul_atTop_of_pos (r := k) (f := id) (l := atTop) hk
    exact h.2 tendsto_id
  have hnegt : Tendsto (fun t : ℝ => -(k * t)) atTop atBot :=
    Tendsto.comp tendsto_neg_atTop_atBot hkpos
  have h1 : Tendsto (fun t : ℝ => -k * t) atTop atBot := by
    simpa [neg_mul] using hnegt
  exact Real.tendsto_exp_atBot.comp h1

/-- 单关节 h 函数：h_i(θ) = (θ−θ⁻)(θ⁺−θ)/(θ⁺−θ⁻)² —— 文档 (17) -/
noncomputable def hFunc (θl θu θ : ℝ) : ℝ := (θ - θl) * (θu - θ) / (θu - θl) ^ 2

/-- AM-GM 二元形式：(ab ≤ ((a+b)/2)² —— (a+b)² − 4ab = (a−b)² ≥ 0 -/
private lemma amgm2 (a b : ℝ) : a * b ≤ ((a + b) / 2) ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- h 在 θ_M = (θ⁻+θ⁺)/2 处取最大值 1/4 —— 文档 (17) -/
theorem hFunc_max_at_mid {θl θu : ℝ} (hl : θl < θu) :
    hFunc θl θu ((θl + θu) / 2) = 1 / 4 ∧ ∀ θ, hFunc θl θu θ ≤ 1 / 4 := by
  constructor
  · -- 中点处取值：Δ = θu − θl，(Δ/2)(Δ/2)/Δ² = 1/4
    unfold hFunc
    have hΔ : θu - θl ≠ 0 := by linarith
    field_simp [hΔ]
    ring_nf
  · intro θ
    unfold hFunc
    -- a = θ − θ⁻，b = θ⁺ − θ，则 a + b = θ⁺ − θ⁻，ab ≤ ((a+b)/2)²
    have hineq : (θ - θl) * (θu - θ) ≤ ((θu - θl) / 2) ^ 2 := by
      have ham := amgm2 (θ - θl) (θu - θ)
      have hsum : (θ - θl) + (θu - θ) = θu - θl := by ring
      rw [hsum] at ham
      exact ham
    -- 除以正分母 (θu − θl)² > 0
    have hden : 0 < (θu - θl) ^ 2 := by positivity
    rw [div_le_iff₀ hden]
    -- ((θu − θl)/2)² = 1/4·(θu − θl)²
    have hineq2 : ((θu - θl) / 2) ^ 2 ≤ 1 / 4 * (θu - θl) ^ 2 := by
      nlinarith
    exact le_trans hineq hineq2

/-- 单因子导数：h'_i(x) = (θ⁺ + θ⁻ − 2x)/(θ⁺ − θ⁻)² —— 文档 (18) 的分量形式。
   hFunc 展开为多项式 (x−θ⁻)(θ⁺−x)/(θ⁺−θ⁻)²，分子导数为 θ⁺ + θ⁻ − 2x。 -/
private lemma hFunc_deriv (θl θu x : ℝ) :
    HasDerivAt (fun y : ℝ => hFunc θl θu y) ((θu + θl - 2 * x) / (θu - θl) ^ 2) x := by
  unfold hFunc
  have hA : HasDerivAt (fun y : ℝ => y - θl) 1 x := by
    simpa using (hasDerivAt_id x).sub_const θl
  have hB : HasDerivAt (fun y : ℝ => θu - y) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub θu
  have hD : HasDerivAt (fun y : ℝ => (y - θl) * (θu - y) / (θu - θl) ^ 2)
      ((1 * (θu - x) + (x - θl) * -1) / (θu - θl) ^ 2) x := (hA.mul hB).div_const ((θu - θl) ^ 2)
  convert hD using 1
  ring

/-- h(θ) = ∏ h_i(θ_i) 对 θ_i 的偏导：∂h/∂θ_i = (∏_{j≠i} h_j(θ_j)) · h'_i(θ_i)
   —— 文档 (18)。乘积法则下除 j = i 外各因子均为常数（导数 0），和式中仅剩一项。 -/
theorem hFunc_partial_deriv {n : ℕ} (θl θu θ : Vec n) (i : Fin n) :
    HasDerivAt (fun x : ℝ => ∏ j : Fin n, hFunc (θl j) (θu j) (if j = i then x else θ j))
      ((∏ j : Fin n, if j = i then 1 else hFunc (θl j) (θu j) (θ j)) *
        ((θu i + θl i - 2 * θ i) / (θu i - θl i) ^ 2)) (θ i) := by
  let f : Fin n → ℝ → ℝ := fun j x => hFunc (θl j) (θu j) (if j = i then x else θ j)
  let v : ℝ := (θu i + θl i - 2 * θ i) / (θu i - θl i) ^ 2
  let f' : Fin n → ℝ := fun j => if j = i then v else 0
  -- j = i 时是 hFunc (θl i) (θu i)，用单因子导数；j ≠ i 时为常数（导数 0）
  have hfi : HasDerivAt (f i) v (θ i) := by
    simpa [f, v] using hFunc_deriv (θl i) (θu i) (θ i)
  have hfne : ∀ j, j ≠ i → HasDerivAt (f j) 0 (θ i) := by
    intro j hji
    have hc : f j = fun _ : ℝ => hFunc (θl j) (θu j) (θ j) := by
      funext x
      simp [f, hji]
    rw [hc]
    exact hasDerivAt_const (θ i) (hFunc (θl j) (θu j) (θ j))
  -- 乘积法则组装：d/dθ_i ∏ f_j = ∑_j (∏_{k≠j} f_k) · f'_j，仅 j = i 项非零
  have hf : ∀ j ∈ (Finset.univ : Finset (Fin n)), HasDerivAt (f j) (f' j) (θ i) := by
    intro j hj
    by_cases hji : j = i
    · subst hji
      simpa [f'] using hfi
    · simpa [f', hji] using hfne j hji
  have hprod : HasDerivAt (∏ j ∈ (Finset.univ : Finset (Fin n)), f j)
      (∑ j ∈ (Finset.univ : Finset (Fin n)),
        (∏ k ∈ (Finset.univ : Finset (Fin n)).erase j, f k (θ i)) • f' j) (θ i) := by
    exact HasDerivAt.finsetProd (u := (Finset.univ : Finset (Fin n))) (f := f) (f' := f') hf
  have hprod' : HasDerivAt (fun x : ℝ => ∏ j : Fin n, f j x)
      (∑ j ∈ (Finset.univ : Finset (Fin n)),
        (∏ k ∈ (Finset.univ : Finset (Fin n)).erase j, f k (θ i)) • f' j) (θ i) := by
    convert hprod using 1
    funext x
    rw [Finset.prod_apply]
  -- ∏_{k≠i} h_k(θ_k) 化为带 if 的整积：i 因子为 1（消失）
  have herase : (∏ k ∈ (Finset.univ : Finset (Fin n)).erase i,
        hFunc (θl k) (θu k) (if k = i then θ i else θ k)) =
      ∏ k : Fin n, if k = i then 1 else hFunc (θl k) (θu k) (θ k) := by
    rw [← Finset.filter_ne']
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro k hk
    by_cases hki : k = i
    · simp [hki]
    · simp [hki]
  -- 和式坍缩到 j = i 一项（f' 其余为 0），乘积替换为 herase，即可闭合
  simpa [f, f', herase, smul_ite, smul_eq_mul, Finset.sum_ite_eq', v] using hprod'

/-- 分段梯度（简化版）：θ < θ_M 时取第一分支（v ≥ 0，推向上限），否则取第二分支
   （v ≤ 0，推向下限）—— 文档 (19)。 -/
noncomputable def piecewiseGrad (θl θu θ : ℝ) : ℝ :=
  if θ < (θl + θu) / 2 then (θ - θl) / (θu - θl) ^ 2 else (θ - θu) / (θu - θl) ^ 2

/-- 区间 1 性质：θ < θ_M 时 v ≥ 0（推向上限），θ ≥ θ⁻ 保证分子非负 —— 文档 (19) -/
theorem piecewiseGrad_lower {θl θu θ : ℝ} (hl : θl < θu) (hθ : θl ≤ θ) (hθm : θ < (θl + θu) / 2) :
    0 ≤ piecewiseGrad θl θu θ := by
  rw [piecewiseGrad, if_pos hθm]
  have hΔ : 0 < θu - θl := by linarith
  exact div_nonneg (by linarith) (le_of_lt (sq_pos_of_pos hΔ))

/-- 区间 2 性质：θ > θ_M 时 v ≤ 0（推向下限），θ ≤ θ⁺ 保证分子非正 —— 文档 (19) -/
theorem piecewiseGrad_upper {θl θu θ : ℝ} (hl : θl < θu) (hθ : θ ≤ θu) (hθm : (θl + θu) / 2 < θ) :
    piecewiseGrad θl θu θ ≤ 0 := by
  rw [piecewiseGrad, if_neg (not_lt_of_gt hθm)]
  have hden : 0 < (θu - θl) ^ 2 := sq_pos_of_pos (by linarith)
  rw [div_le_iff₀ hden]
  linarith

/-- 端点值：v(θ⁻) = 0，v(θ⁺) = 0 —— 文档 (19)。
   注意：需 θ⁻ < θ⁺（hl），否则 θ⁻ ≥ θ_M 时首分支不成立，端点值公式退化。 -/
theorem piecewiseGrad_endpoints {θl θu : ℝ} (hl : θl < θu) :
    piecewiseGrad θl θu θl = 0 ∧ piecewiseGrad θl θu θu = 0 := by
  constructor
  · rw [piecewiseGrad]
    rw [if_pos (by linarith : θl < (θl + θu) / 2)]
    simp
  · rw [piecewiseGrad]
    rw [if_neg (not_lt_of_gt (by linarith : (θl + θu) / 2 < θu))]
    simp

/-- θ_M 处不连续：左分支值 (θ_M − θ⁻)/Δ² > 0 而右分支值 (θ_M − θ⁺)/Δ² < 0
   （Δ = θ⁺ − θ⁻ > 0）—— 文档 (19) 注明的不连续。
   注：piecewiseGrad 在 θ_M 处取第二分支（if 条件 θ_M < θ_M 为假），
   故「跳跃」表现为：左分支在 θ_M 的值 > 0，而实际取值（右分支）< 0。 -/
theorem piecewiseGrad_jump_at_mid {θl θu : ℝ} (hl : θl < θu) :
    0 < ((θl + θu) / 2 - θl) / (θu - θl) ^ 2 ∧ ((θl + θu) / 2 - θu) / (θu - θl) ^ 2 < 0 := by
  have hΔ : 0 < θu - θl := by linarith
  constructor
  · exact div_pos (by linarith) (sq_pos_of_pos hΔ)
  · have hden : 0 < (θu - θl) ^ 2 := sq_pos_of_pos hΔ
    rw [div_lt_iff₀ hden]
    linarith

end Velocity
