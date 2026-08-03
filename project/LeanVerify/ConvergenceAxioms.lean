import LeanVerify.QP_LVI_PNN
/-! # 收敛性假设与应用链：投影动力系统全局指数收敛（axiom，引用 Gao 2003）与 Lyapunov 应用链。 -/

open Matrix
open scoped Topology

/--
投影动力系统的全局指数收敛 —— 本文件为假设来源（axiom）：
- 论文 Ma et al. 2023 的 Lemma 1（引用 [38] X.-B. Gao, "Exponential stability of globally
  projected dynamic systems", IEEE TNN 2003 与 [39] Friesz et al., Operations Research 1999）
- 文档公式 (30) 的 Lyapunov 结论（文档中"经过适当的矩阵不等式推导"一步未给出完整证明，
  本 axiom 将其显式化；应用链（F 构造、单调性、不动点等价）在 QP_LVI_PNN.lean 中严格证明）
- 说明：定理本体需要 Hilbert 空间单调算子 + 指数稳定性理论，超出本项目范围
  （见 docs/VERIFICATION.md §假设清单）。
-/
axiom pnn_global_exponential_convergence {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} {κ : Vec n}
    {Ω : Set (Vec n)} {P : Vec n → Vec n} {γ : ℝ}
    (hγ : 0 < γ)
    (hΩc : Convex ℝ Ω)
    (hPmem : ∀ y, P y ∈ Ω)
    (hPchar : ∀ a z, z ∈ Ω → inner ℝ (a - P a) (z - P a) ≤ 0)
    (hStrongMon : ∃ η > 0, ∀ x y : Vec n, inner ℝ (x - y) (M *ᵥ x - M *ᵥ y) ≥ η * eNorm (x - y) ^ 2) :
    ∀ (y : ℝ → Vec n) (ystar : Vec n)
      (hflow : ∀ t, HasFDerivAt y
        (ContinuousLinearMap.toSpanSingleton ℝ (γ • (P (y t - (M *ᵥ y t + κ)) - y t))) t)
      (hystar : QPLVI.VI (fun z => M *ᵥ z + κ) Ω ystar),
    eNorm (y 0 - ystar) > 0 →
    ∃ c > 0, ∀ t, 0 ≤ t → eNorm (y t - ystar) ≤ eNorm (y 0 - ystar) * Real.exp (-c * t)

namespace ConvergenceAxioms

open QPLVI

/-- 强单调的充分条件（标量情形）：M = c·I（c > 0）时 ⟨x−y, M(x−y)⟩ = c·‖x−y‖ₑ²
   —— 文档 (30) 前件的可证实例（一般对称正定情形依赖谱理论，见 VERIFICATION.md） -/
theorem smul_identity_strong_monotone {n : ℕ} (c : ℝ) (hc : 0 < c) :
    ∃ η > 0, ∀ x y : Vec n, inner ℝ (x - y) ((c • 1) *ᵥ (x - y)) ≥ η * eNorm (x - y) ^ 2 := by
  refine ⟨c, hc, ?_⟩
  intro x y
  have hmul : (c • 1) *ᵥ (x - y) = c • (x - y) := by
    ext i
    rw [Matrix.mulVec]
    simp [dotProduct, Matrix.one_apply, Finset.sum_ite_eq']
  calc
    inner ℝ (x - y) ((c • 1) *ᵥ (x - y)) = inner ℝ (x - y) (c • (x - y)) := by rw [hmul]
    _ = c * inner ℝ (x - y) (x - y) := by rw [vec_inner_smul_right]
    _ = c * eNorm (x - y) ^ 2 := by rw [eNorm_sq_eq_inner]
    _ ≥ c * eNorm (x - y) ^ 2 := le_rfl

/-- 主定理：F(y) = My + κ 强单调时，框约束 RNN 轨迹全局指数收敛到 LVI 解
   —— 文档 (29)(30)(34) 组合（axiom 对框投影的实例化） -/
theorem pnn_convergence {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} {κ : Vec n} {γ : ℝ} {l h : Vec n}
    (hlh : ∀ i, l i ≤ h i) (hγ : 0 < γ)
    (hStrong : ∃ η > 0, ∀ x y : Vec n, inner ℝ (x - y) (M *ᵥ x - M *ᵥ y) ≥ η * eNorm (x - y) ^ 2) :
    ∀ (y : ℝ → Vec n) (ystar : Vec n)
      (hystar : VI (fun z => M *ᵥ z + κ) (feasibleSetBox l h) ystar)
      (hflow : ∀ t, HasFDerivAt y
        (ContinuousLinearMap.toSpanSingleton ℝ (γ • (boxProj l h (y t - (M *ᵥ y t + κ)) - y t))) t),
    eNorm (y 0 - ystar) > 0 →
    ∃ c > 0, ∀ t, 0 ≤ t → eNorm (y t - ystar) ≤ eNorm (y 0 - ystar) * Real.exp (-c * t) := by
  exact fun y ystar hystar hflow h0 =>
    pnn_global_exponential_convergence (M := M) (κ := κ) (γ := γ)
      (P := boxProj l h) (Ω := feasibleSetBox l h)
      hγ (feasibleSetBox_convex l h)
      (fun y => fun i => ⟨(boxProj_mem hlh y).1 i, (boxProj_mem hlh y).2 i⟩)
      (fun a z hz => @boxProj_char n l h a z (by simpa [feasibleSetBox] using hz))
      hStrong y ystar hflow hystar h0

/-- V̇ 的代数展开：⟨y − y*, γ(P(y−Fy) − y)⟩ = γ·⟨y − y*, P(y−Fy) − y⟩ —— 文档 (30) 代数层 -/
theorem lyapunov_deriv {n : ℕ} (F : Vec n → Vec n) (P : Vec n → Vec n) (γ : ℝ) (y ystar : Vec n) :
    inner ℝ (y - ystar) (γ • (P (y - F y) - y)) = γ * inner ℝ (y - ystar) (P (y - F y) - y) := by
  rw [vec_inner_smul_right]

/-- 仿射 F 的线性差：F(y) − F(y*) = M(y − y*)（F = My + κ） —— 文档 (30) 应用步骤 -/
theorem affine_F_diff {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (κ : Vec n) (y ystar : Vec n) :
    (M *ᵥ y + κ) - (M *ᵥ ystar + κ) = M *ᵥ (y - ystar) := by
  rw [Matrix.mulVec_sub]
  abel

/-- 非扩张性上界：‖P(y−Fy) − y*‖ ≤ ‖(y−y*) − (Fy − Fy*)‖ —— 文档 (30) 应用步骤 -/
theorem nonexpansive_step {n : ℕ} (F : Vec n → Vec n) (P : Vec n → Vec n) (y ystar : Vec n)
    (hP : ∀ a b, ‖P a - P b‖ ≤ ‖a - b‖) (hystar : ystar = P (ystar - F ystar)) :
    ‖P (y - F y) - ystar‖ ≤ ‖(y - ystar) - (F y - F ystar)‖ := by
  calc
    ‖P (y - F y) - ystar‖ ≤ ‖(y - F y) - (ystar - F ystar)‖ := by
      have hsub : P (y - F y) - P (ystar - F ystar) = P (y - F y) - ystar := by
        congr 1
        exact hystar.symm
      rw [← hsub]
      exact hP (y - F y) (ystar - F ystar)
    _ = ‖(y - ystar) - (F y - F ystar)‖ := by
      congr 1
      abel

/-- 应用链组合：非扩张 + 仿射差 ⟹ ‖P(y−Fy) − y*‖ ≤ ‖(I−M)(y−y*)‖ —— 文档 (30) -/
theorem nonexpansive_step_affine {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (κ : Vec n)
    (P : Vec n → Vec n) (y ystar : Vec n)
    (hP : ∀ a b, ‖P a - P b‖ ≤ ‖a - b‖) (hystar : ystar = P (ystar - (M *ᵥ ystar + κ))) :
    ‖P (y - (M *ᵥ y + κ)) - ystar‖ ≤ ‖(y - ystar) - M *ᵥ (y - ystar)‖ := by
  calc
    ‖P (y - (M *ᵥ y + κ)) - ystar‖
        ≤ ‖(y - ystar) - ((M *ᵥ y + κ) - (M *ᵥ ystar + κ))‖ :=
          nonexpansive_step (fun z => M *ᵥ z + κ) P y ystar hP hystar
    _ = ‖(y - ystar) - M *ᵥ (y - ystar)‖ := by
      rw [affine_F_diff M κ y ystar]

end ConvergenceAxioms
