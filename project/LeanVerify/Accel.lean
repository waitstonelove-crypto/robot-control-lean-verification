/-
Copyright (c) 2026 wj. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: wj
-/
import LeanVerify.Core

/-!
# Accel：加速度级运动学与逆解（下篇）

对应文档第 A/B 章（下篇）：乘积法则 (A.2b)、加速度级伪逆解 (B.1)、
加速度级通解 (B.2)。矩阵运算一律使用 `Matrix` 拼写与 `*ᵥ`，欧氏范数用 `eNorm`。
-/

namespace Accel

open Matrix
open scoped BigOperators
open scoped Topology

/-- 乘积法则：d/dt(J·θ̇) = J·θ̈ + J̇·θ̇ —— 文档 (A.2b) 核心。
   Jdot、θdd 是给定的导数数据（记号上 Jdot t = fderiv J t 1、θdd t = fderiv θd t 1），
   hJ/hθd 声明 J、θd 可微且导数为 `x ↦ x • Jdot t` / `x ↦ x • θdd t`。
   注：`HasFDerivAt` 的导数参数须为连续线性映射，`x ↦ x • v` 不能直接作为
   `ℝ →L[ℝ] E` 型项书写（无函数到线性映射的自动提升），须写
   `ContinuousLinearMap.toSpanSingleton ℝ v`（逐点定义为 `fun x ↦ x • v`），
   与 Velocity.error_dynamics 同款（执行期实证 3）。
   证明路线：对结果逐坐标 i，把 `(J s *ᵥ θd s) i` 展开为 `∑ k, J s i k * θd s k`，
   坐标投影（hasFDerivAt_pi'）给出形如 `proj k ∘SL proj i ∘SL toSpanSingleton` 的
   导数，经 `rw [ContinuousLinearMap.comp_apply]` + `dsimp [ContinuousLinearMap.proj, LinearMap.proj]`
   归约为逐分量值（rw 无法直接处理 proj 应用，其隐式 Module 参数在重写时不可合成）；
   再用标量乘积法则 `HasDerivAt.mul` + 求和 `HasDerivAt.fun_sum` 组装，
   `hasFDerivAt_pi.mpr` 还原整个向量函数，最后用 `ContinuousLinearMap.ext` 归一化
   导数映射（toSpanSingleton 对 pi 的分解；注意 `Matrix.mulVec`/`dotProduct` 展开
   是定义相等，而 toSpanSingleton/pi 的消去须显式 `rw`）。 -/
theorem accel_kinematics_prodRule {m n : ℕ} (J : ℝ → Matrix (Fin m) (Fin n) ℝ) (θd : ℝ → Vec n)
    (Jdot : ℝ → Matrix (Fin m) (Fin n) ℝ) (θdd : ℝ → Vec n)
    (hJ : ∀ t, HasFDerivAt J (ContinuousLinearMap.toSpanSingleton ℝ (Jdot t)) t)
    (hθd : ∀ t, HasFDerivAt θd (ContinuousLinearMap.toSpanSingleton ℝ (θdd t)) t) :
    ∀ t, HasFDerivAt (fun s => J s *ᵥ θd s)
      (ContinuousLinearMap.toSpanSingleton ℝ (Jdot t *ᵥ θd t + J t *ᵥ θdd t)) t := by
  intro t
  -- 逐坐标：对每行 i，标量函数 s ↦ (J s *ᵥ θd s) i = ∑ k, J s i k * θd s k 可微
  have hrow : ∀ i, HasDerivAt (fun s : ℝ => (J s *ᵥ θd s) i)
      (∑ k : Fin n, (Jdot t i k * θd t k + J t i k * θdd t k)) t := by
    intro i
    -- J 的行元导数：由 hJ t 经两层坐标投影（hasFDerivAt_pi'），导数形如
    -- `proj k ∘SL proj i ∘SL toSpanSingleton ℝ (Jdot t)`；复合在 1 处的值逐分量
    -- 归约为 Jdot t i k（comp_apply 展开 + dsimp 展开 proj 的 toFun 后 rfl）。
    have hJ2 : ∀ k, HasDerivAt (fun x : ℝ => J x i k) (Jdot t i k) t := by
      intro k
      have h2 := hasFDerivAt_pi'.1 (hasFDerivAt_pi'.1 (hJ t) i) k
      have hval : ((ContinuousLinearMap.proj k ∘SL ContinuousLinearMap.proj i ∘SL
          ContinuousLinearMap.toSpanSingleton ℝ (Jdot t)) 1) = Jdot t i k := by
        rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
        dsimp [ContinuousLinearMap.proj, LinearMap.proj]
        simp
        rfl
      have hd : HasDerivAt (fun x : ℝ => J x i k)
          ((ContinuousLinearMap.proj k ∘SL ContinuousLinearMap.proj i ∘SL
            ContinuousLinearMap.toSpanSingleton ℝ (Jdot t)) 1) t := h2.hasDerivAt
      rw [hval] at hd
      exact hd
    -- θd 的分量导数：由 hθd t 经一层坐标投影
    have hθd2 : ∀ k, HasDerivAt (fun x : ℝ => θd x k) (θdd t k) t := by
      intro k
      have h2 := hasFDerivAt_pi'.1 (hθd t) k
      have hval : ((ContinuousLinearMap.proj k ∘SL
          ContinuousLinearMap.toSpanSingleton ℝ (θdd t)) 1) = θdd t k := by
        rw [ContinuousLinearMap.comp_apply]
        dsimp [ContinuousLinearMap.proj, LinearMap.proj]
        simp
      have hd : HasDerivAt (fun x : ℝ => θd x k)
          ((ContinuousLinearMap.proj k ∘SL
            ContinuousLinearMap.toSpanSingleton ℝ (θdd t)) 1) t := h2.hasDerivAt
      rw [hval] at hd
      exact hd
    -- 标量乘积法则 (A.2b) 的逐项形式：d/dt(J_ik·θ̇_k) = J̇_ik·θ̇_k + J_ik·θ̈_k
    have hfk : ∀ k : Fin n, HasDerivAt (fun s : ℝ => J s i k * θd s k)
        (Jdot t i k * θd t k + J t i k * θdd t k) t := by
      intro k
      exact (hJ2 k).mul (hθd2 k)
    -- Finset 求和组装（fun_sum 的函数形式与目标逐定义相等）
    have hsum : HasDerivAt (fun s : ℝ => ∑ k : Fin n, J s i k * θd s k)
        (∑ k : Fin n, (Jdot t i k * θd t k + J t i k * θdd t k)) t := by
      exact HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin n)))
        (A := fun k s => J s i k * θd s k) (A' := fun k => Jdot t i k * θd t k + J t i k * θdd t k)
        (fun k hk => hfk k)
    -- 还原 mulVec 定义（∑ k, J s i k * θd s k = (J s *ᵥ θd s) i，定义相等）
    exact hsum
  -- hasFDerivAt_pi 从逐坐标可微组装出整个向量函数的可微性
  have hpi := hasFDerivAt_pi.mpr (fun i => (hrow i).hasFDerivAt)
  -- 归一化导数映射：toSpanSingleton A = pi (toSpanSingleton ∘ B_i)，其中
  -- A = Jdot t *ᵥ θd t + J t *ᵥ θdd t 且 A_i = B_i（mulVec/dotProduct 定义展开）。
  -- 注意：不能把 `ext` 用于该线性映射等式（会生成 Module 实例相等目标），
  -- 须显式 `apply ContinuousLinearMap.ext`；smul 在 `x • A i` 处不做乘法重写
  -- （`smul_eq_mul` 会引出 `mul_eq_mul_left_iff` 的析取），故收尾用 `congr` + `simp`。
  have hnorm : ContinuousLinearMap.toSpanSingleton ℝ (Jdot t *ᵥ θd t + J t *ᵥ θdd t) =
      ContinuousLinearMap.pi (fun i => ContinuousLinearMap.toSpanSingleton ℝ
        (∑ k : Fin n, (Jdot t i k * θd t k + J t i k * θdd t k))) := by
    apply ContinuousLinearMap.ext
    intro x
    funext i
    rw [ContinuousLinearMap.pi_apply, ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearMap.toSpanSingleton_apply, Pi.smul_apply]
    congr 1
    simp [Matrix.mulVec, dotProduct, Finset.sum_add_distrib]
  rw [hnorm]
  exact hpi

/-- 加速度级伪逆解满足等式约束：J·J†w = w（w = p̈_d − J̇θ̇） —— 文档 (B.1)。
   由 (J·J†)·w = 1·w = w：`mulVec_mulVec` 结合矩阵乘法 + `rpinv_mul_eq_one` (JJ† = I)。 -/
theorem accel_pinv_solves {m n : ℕ} (J : Matrix (Fin m) (Fin n) ℝ) (h : IsUnit (J * Jᵀ))
    (w : Vec m) :
    J *ᵥ (rpinv J h *ᵥ w) = w := by
  simp [Matrix.mulVec_mulVec, rpinv_mul_eq_one J h, Matrix.one_mulVec]

/-- 加速度级最小范数解：‖J†w‖ₑ ≤ ‖x‖ₑ（∀x，Jx = w） —— 文档 (B.1)（复用 (4)） -/
theorem accel_pinv_min_norm {m n : ℕ} (J : Matrix (Fin m) (Fin n) ℝ) (h : IsUnit (J * Jᵀ))
    (w : Vec m) (x : Vec n) (hx : J *ᵥ x = w) :
    eNorm (rpinv J h *ᵥ w) ≤ eNorm x := by
  exact rpinv_min_norm J h w x hx

/-- 加速度级通解：J(θ̈p + P₀φ) = w —— 文档 (B.2)，复用 general_solution -/
theorem accel_general_solution {m n : ℕ} (J : Matrix (Fin m) (Fin n) ℝ) (h : IsUnit (J * Jᵀ))
    (w : Vec m) (φ : Vec n) :
    J *ᵥ (rpinv J h *ᵥ w + nullProj J h *ᵥ φ) = w := by
  exact general_solution J h w φ

end Accel
