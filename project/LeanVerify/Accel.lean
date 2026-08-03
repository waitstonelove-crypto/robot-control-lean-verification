/-
Copyright (c) 2026 wj. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: wj
-/
import LeanVerify.Core
/-! # Accel 加速度级推广：乘积法则、加速度伪逆/通解、PD 误差动态、欧拉积分（文档 (A)-(F)）。 -/

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

/-- PD 期望加速度的代数闭合：p̈_des = p̈_d + k_d ė + k_p e 时，
   p̈_des − p̈_d = k_d ė + k_p e —— 文档 (B.4)（代数层；二阶 ODE 显式解不在验证范围） -/
theorem pd_error_algebra {m : ℕ} (edd edd_des e ed : Vec m) (kd kp : ℝ)
    (hpd : edd_des = edd + kd • ed + kp • e) :
    edd_des - edd = kd • ed + kp • e := by
  rw [hpd]
  abel

/-- 完整加速度级控制律闭环验证：p̈ = p̈_d + k_d ė + k_p e
   —— 文档 (B.5)（p̈ = Jθ̈ + J̇θ̇ 的代数展开 + 通解 (B.2) 组合）。
   记号：Jdot 即 J̇（带结合符的标识符 Lean 词法器不接受，故用 Jdot）。 -/
theorem pd_control_law_closed {m n : ℕ} (J Jdot : Matrix (Fin m) (Fin n) ℝ) (h : IsUnit (J * Jᵀ))
    (pdd ed e : Vec m) (θd : Vec n) (kd kp : ℝ) (φ : Vec n) :
    Jdot *ᵥ θd +
        J *ᵥ (rpinv J h *ᵥ (pdd + kd • ed + kp • e - Jdot *ᵥ θd) +
          nullProj J h *ᵥ φ) =
      pdd + kd • ed + kp • e := by
  rw [accel_general_solution J h (pdd + kd • ed + kp • e - Jdot *ᵥ θd) φ]
  abel

/-- 恒定加速度下二阶欧拉精确性：θ̇(t) = θ̇₀ + θ̈t 且 θ(t) = θ₀ + θ̇₀t + ½θ̈t²
   满足各自的导数关系 —— 文档 (E) -/
theorem euler_constant_accel {n : ℕ} (θ0 θd0 θdd : Vec n) :
    (∀ t, HasDerivAt (fun s : ℝ => θd0 + s • θdd) θdd t) ∧
    (∀ t, HasDerivAt (fun s : ℝ => θ0 + s • θd0 + (s ^ 2 / 2) • θdd) (θd0 + t • θdd) t) := by
  constructor
  · intro t
    -- θd0 常数（导数 0）+ s ↦ s•θdd 导数 θdd（id 的导数 1，1•θdd = θdd）。
    -- 注：不能 simpa —— simp 引理 hasDerivAt_const_add_iff 会把目标中 `θd0 +` 吸收掉
    -- （函数侧是逐点 λ 和形式时不匹配），故用 convert 展开逐点加后只剩导数方程 0 + θdd = θdd。
    have h1 : HasDerivAt (fun s : ℝ => θd0) 0 t := hasDerivAt_const t θd0
    have h2 : HasDerivAt (fun s : ℝ => s • θdd) θdd t := by
      simpa using (hasDerivAt_id t).smul_const θdd
    have hboth : HasDerivAt (fun s : ℝ => θd0 + s • θdd) (0 + θdd) t := h1.add h2
    convert hboth using 1
    simp
  · intro t
    -- s ↦ s•θd0 导数 θd0
    have h1 : HasDerivAt (fun s : ℝ => s • θd0) θd0 t := by
      simpa using (hasDerivAt_id t).smul_const θd0
    -- 标量导数：d/dt (s²/2) = t。
    -- 注：HasDerivAt.pow/.mul 走 NormedAlgebra 模实例，与语句目标的标准模实例不定义相等，
    -- 故 s² 的导数用 hasDerivAt_pow（标准实例）；div_const 的结论（代数实例）经 convert
    -- 桥接回标准实例，剩余算术 2t/2 = t 由 simp [div_eq_mul_inv, mul_comm] 归一化
    -- （mul_comm 非默认 simp 引理，须显式给出）。
    have hpow : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have hdiv : HasDerivAt (fun s : ℝ => s ^ 2 / 2) (2 * t / 2) t := hpow.div_const 2
    have hsc : HasDerivAt (fun s : ℝ => (s ^ 2) / 2) t t := by
      convert hdiv using 1
      simp [div_eq_mul_inv, mul_comm]
    -- s ↦ (s²/2)•θdd 导数 t•θdd（smul_const：标量函数乘常数向量，Vec 模实例唯一）
    have h2 : HasDerivAt (fun s : ℝ => (s ^ 2 / 2) • θdd) (t • θdd) t :=
      hsc.smul_const θdd
    -- 组装：θ0 常数 + 两项，导数 (0 + θd0) + t•θdd = θd0 + t•θdd（convert 同第一分支）
    have hboth : HasDerivAt (fun s : ℝ => θ0 + s • θd0 + (s ^ 2 / 2) • θdd)
        ((0 + θd0) + t • θdd) t := ((hasDerivAt_const t θ0).add h1).add h2
    convert hboth using 1
    simp

end Accel
