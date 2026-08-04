import LeanVerify.Core
import LeanVerify.QP_LVI_PNN

open Matrix

/-! # Li-Zhang-Jin (2017) 稳定性定理验证
控制律 (19) u = P_Ω(Jᵀ(r_d−r)/γ) 的 Theorem 1 与控制律 (41) 速度补偿的 Theorem 2。
核心：投影最小距离性质（任意集 Ω，无需凸性——论文贡献点）+ Lyapunov/LaSalle 论证。
记号：u = θ̇ ∈ Rⁿ，J ∈ R^{m×n}，P_Ω 为投影，γ > 0 缩放，e = r − r_d。
误差动态 (21)：ė = J P_Ω(−Jᵀe/γ)。 -/

namespace LiZhangJin

/-- 向量逐分量除以标量（保持论文记号 u/γ；`Vec n → ℝ` 无标量除法实例） -/
noncomputable def vecDiv {n : ℕ} (x : Vec n) (c : ℝ) : Vec n := fun i => x i / c

/-- 论文 (23) 的 y=0 特例：0 ∈ Ω ⟹ ‖P z − z‖ₑ ≤ ‖z‖ₑ -/
theorem proj_dist_le_norm {n : ℕ} (P : Vec n → Vec n) (Ω : Set (Vec n))
    (hPdist : ∀ z y : Vec n, y ∈ Ω → eNorm (P z - z) ≤ eNorm (y - z))
    (h0 : (0 : Vec n) ∈ Ω) (z : Vec n) :
    eNorm (P z - z) ≤ eNorm z := by
  simpa [eNorm_neg] using hPdist z 0 h0

/-- 论文 (23)(24)(25)：0 ∈ Ω ⟹ ‖P z‖ₑ² ≤ 2⟨P z, z⟩（配平方展开后移项） -/
theorem proj_sq_ineq {n : ℕ} (P : Vec n → Vec n) (Ω : Set (Vec n))
    (hPdist : ∀ z y : Vec n, y ∈ Ω → eNorm (P z - z) ≤ eNorm (y - z))
    (h0 : (0 : Vec n) ∈ Ω) (z : Vec n) :
    eNorm (P z) ^ 2 ≤ 2 * inner ℝ (P z) z := by
  have h1 : eNorm (P z - z) ≤ eNorm z := proj_dist_le_norm P Ω hPdist h0 z
  have h1sq : eNorm (P z - z) ^ 2 ≤ eNorm z ^ 2 := by
    nlinarith [h1, eNorm_nonneg (P z - z), eNorm_nonneg z]
  have hsq := eNorm_sub_sq (P z) z
  nlinarith [h1sq, hsq]

/-- 论文 (26)：V̇ = ⟨e, J P_Ω(−Jᵀe/γ)⟩ ≤ 0（Lyapunov 导数非正，V = ‖e‖²/2） -/
theorem Vdot_nonpos {n m : ℕ} (P : Vec n → Vec n) (Ω : Set (Vec n))
    (hPdist : ∀ z y : Vec n, y ∈ Ω → eNorm (P z - z) ≤ eNorm (y - z))
    (h0 : (0 : Vec n) ∈ Ω) (J : Matrix (Fin m) (Fin n) ℝ) (γ : ℝ) (hγ : 0 < γ) (e : Vec m) :
    inner ℝ e (J *ᵥ P (vecDiv (-((Jᵀ) *ᵥ e)) γ)) ≤ 0 := by
  let z : Vec n := vecDiv (-((Jᵀ) *ᵥ e)) γ
  have hineq : eNorm (P z) ^ 2 ≤ 2 * inner ℝ (P z) z := proj_sq_ineq P Ω hPdist h0 z
  have hzpos : 0 ≤ inner ℝ (P z) z := by
    have : 0 ≤ eNorm (P z) ^ 2 := sq_nonneg (eNorm (P z))
    nlinarith [hineq]
  have hz : (Jᵀ) *ᵥ e = -(γ • z) := by
    ext i
    change (Jᵀ *ᵥ e) i = -(γ * (z i))
    dsimp [z, vecDiv]
    field_simp [hγ.ne']
  have hadj : inner ℝ e (J *ᵥ P z) = -γ * inner ℝ (P z) z := by
    have h1 : inner ℝ e (J *ᵥ P z) = inner ℝ ((Jᵀ) *ᵥ e) (P z) := by
      rw [vec_inner_symm e (J *ᵥ P z)]
      rw [vec_mulVec_adjoint J (P z) e]
      rw [vec_inner_symm (P z) ((Jᵀ) *ᵥ e)]
    rw [h1, hz]
    rw [vec_inner_neg_left, vec_inner_smul_left]
    rw [vec_inner_symm z (P z)]
    ring
  rw [hadj]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (le_of_lt hγ)) hzpos

end LiZhangJin
