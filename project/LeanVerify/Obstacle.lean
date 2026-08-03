import LeanVerify.Core

open Matrix

namespace Obstacle

/-- 配平方恒等式：‖t•v − w‖ₑ² = ‖v‖ₑ²(t − ⟨v,w⟩/‖v‖ₑ²)² + ‖w‖ₑ² − ⟨v,w⟩²/‖v‖ₑ² —— 文档 (37) 推导基础 -/
theorem norm_sq_complete_square {n : ℕ} (v w : Vec n) (t : ℝ) (hv : v ≠ 0) :
    eNorm (t • v - w) ^ 2 = eNorm v ^ 2 * (t - inner ℝ v w / eNorm v ^ 2) ^ 2 + eNorm w ^ 2
      - (inner ℝ v w) ^ 2 / eNorm v ^ 2 := by
  have hv0 : eNorm v ≠ 0 := fun hv0 => hv ((eNorm_eq_zero_iff v).mp hv0)
  have hv2 : eNorm v ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 hv0
  have hleft : eNorm (t • v - w) ^ 2 = eNorm v ^ 2 * t ^ 2 - 2 * t * inner ℝ v w + eNorm w ^ 2 := by
    rw [eNorm_sq_eq_inner, eNorm_sq_eq_inner, eNorm_sq_eq_inner]
    simp only [vec_inner_sub_left, vec_inner_sub_right, vec_inner_smul_left, vec_inner_smul_right]
    rw [vec_inner_symm w v]
    ring
  have hright : eNorm v ^ 2 * (t - inner ℝ v w / eNorm v ^ 2) ^ 2 + eNorm w ^ 2
      - (inner ℝ v w) ^ 2 / eNorm v ^ 2
      = eNorm v ^ 2 * t ^ 2 - 2 * t * inner ℝ v w + eNorm w ^ 2 := by
    have hE1 : ∀ a : ℝ, eNorm v ^ 2 * (a * (inner ℝ v w / eNorm v ^ 2)) = a * inner ℝ v w := by
      intro a
      field_simp [hv0]
    have hE2 : eNorm v ^ 2 * (inner ℝ v w / eNorm v ^ 2) ^ 2 = (inner ℝ v w) ^ 2 / eNorm v ^ 2 := by
      field_simp [hv0]
    have hsq : (t - inner ℝ v w / eNorm v ^ 2) ^ 2 =
        t ^ 2 - 2 * t * (inner ℝ v w / eNorm v ^ 2) + (inner ℝ v w / eNorm v ^ 2) ^ 2 := by ring
    rw [hsq]
    rw [mul_add, mul_sub]
    rw [hE1 (2 * t), hE2]
    ring
  rw [hleft, hright]

/-- t* = ⟨v,w⟩/‖v‖ₑ² 是 ½‖t•v − w‖ₑ² 的全局最小点（连杆上最近点参数） —— 文档 (37) -/
theorem closest_point_param {n : ℕ} (v w : Vec n) (hv : v ≠ 0) (t : ℝ) :
    (1 / 2) * eNorm (t • v - w) ^ 2 ≥ (1 / 2) * eNorm ((inner ℝ v w / eNorm v ^ 2) • v - w) ^ 2 := by
  have hsq : eNorm (t • v - w) ^ 2 - eNorm ((inner ℝ v w / eNorm v ^ 2) • v - w) ^ 2
      = eNorm v ^ 2 * (t - inner ℝ v w / eNorm v ^ 2) ^ 2 := by
    rw [norm_sq_complete_square v w t hv, norm_sq_complete_square v w (inner ℝ v w / eNorm v ^ 2) hv]
    ring
  have hge : 0 ≤ eNorm v ^ 2 * (t - inner ℝ v w / eNorm v ^ 2) ^ 2 := by
    exact mul_nonneg (sq_nonneg (eNorm v)) (sq_nonneg _)
  nlinarith [hsq, hge]

/-- 连杆-球最小距离：d_i = ‖q_si − c_obs‖ − r_obs，q_si = p_si + t_i(p_ei − p_si) —— 文档 (38)(37) -/
noncomputable def linkSphereDist {n : ℕ} (ps pe c : Vec n) (r t : ℝ) : ℝ :=
  eNorm (ps + t • (pe - ps) - c) - r

/-- 安全判定：d_i > 0 无碰撞、= 0 接触、< 0 碰撞 —— 文档 (38) -/
theorem safety_sign {n : ℕ} (ps pe c : Vec n) (r t : ℝ) :
    (linkSphereDist ps pe c r t > 0 ↔ eNorm (ps + t • (pe - ps) - c) > r) ∧
    (linkSphereDist ps pe c r t = 0 ↔ eNorm (ps + t • (pe - ps) - c) = r) ∧
    (linkSphereDist ps pe c r t < 0 ↔ eNorm (ps + t • (pe - ps) - c) < r) := by
  constructor
  · constructor
    · intro h
      unfold linkSphereDist at h
      linarith
    · intro h
      unfold linkSphereDist
      linarith
  · constructor
    · constructor
      · intro h
        unfold linkSphereDist at h
        linarith
      · intro h
        unfold linkSphereDist
        linarith
    · constructor
      · intro h
        unfold linkSphereDist at h
        linarith
      · intro h
        unfold linkSphereDist
        linarith

/-- Li 函数：L_i = w₁‖p_E − p_i‖² + w₂⟨p_E − p_i, ṗ_E⟩ —— 文档 (39)（p_E、ṗ_E 与 θ 无关的常规约定）。
   注：文档 (39) 的梯度写为 +2w₁(p_E−p_i)ᵀJ_i + w₂ṗ_EᵀJ_i；在 p_E、ṗ_E 与 θ 无关的常规约定下
   链式法则给出负号（∂‖p_E−f(θ)‖²/∂θ = −2(p_E−p)ᵀJ）。符号约定待与 ALMM 原文（Yang et al.）
   比对后定夺，见 lean-work-notes §3 与 formula-mapping.md。 -/
noncomputable def liFunc {m n : ℕ} (w1 w2 : ℝ) (pE pEd : Vec m) (θ : Vec n)
    (f : Vec n → Vec m) : ℝ :=
  w1 * eNorm (pE - f θ) ^ 2 + w2 * inner ℝ (pE - f θ) pEd

/-- 梯度公式（代数版，负号版）：f 仿射（f(x) = f(θ) + J(x−θ)）时，L 沿方向 g 的差 =
   ⟨−2w₁(p_E−p) − w₂ṗ_E, J·g⟩ + w₁‖J·g‖² —— 文档 (39) 勘误候选
   （一阶项为 −2w₁(p_E−p)ᵀJ − w₂ṗ_EᵀJ，与文档的正号版本符号相反） -/
theorem liFunc_grad_algebra {m n : ℕ} (w1 w2 : ℝ) (pE pEd : Vec m) (θ : Vec n)
    (f : Vec n → Vec m) (J : Matrix (Fin m) (Fin n) ℝ)
    (hf : ∀ x, f x = f θ + J *ᵥ (x - θ)) (g : Vec n) :
    liFunc w1 w2 pE pEd (θ + g) f - liFunc w1 w2 pE pEd θ f
      = inner ℝ (((-2 * w1) • (pE - f θ)) - w2 • pEd) (J *ᵥ g) + w1 * eNorm (J *ᵥ g) ^ 2 := by
  have hfθ : f (θ + g) = f θ + J *ᵥ g := by
    rw [hf (θ + g)]
    abel
  have hsub : pE - f (θ + g) = (pE - f θ) - J *ᵥ g := by
    rw [hfθ]
    abel
  have h1 : w1 * eNorm (pE - f (θ + g)) ^ 2 - w1 * eNorm (pE - f θ) ^ 2
      = -2 * w1 * inner ℝ (pE - f θ) (J *ᵥ g) + w1 * eNorm (J *ᵥ g) ^ 2 := by
    rw [hsub]
    have hsqgen : ∀ X B : Vec m, eNorm (X - B) ^ 2
        = eNorm X ^ 2 - 2 * inner ℝ X B + eNorm B ^ 2 := by
      intro X B
      rw [eNorm_sq_eq_inner, eNorm_sq_eq_inner, eNorm_sq_eq_inner]
      rw [vec_inner_sub_left]
      rw [vec_inner_sub_right]
      rw [vec_inner_sub_right]
      rw [vec_inner_symm B X]
      ring
    have hsq : eNorm ((pE - f θ) - J *ᵥ g) ^ 2
        = eNorm (pE - f θ) ^ 2 - 2 * inner ℝ (pE - f θ) (J *ᵥ g) + eNorm (J *ᵥ g) ^ 2 :=
      hsqgen (pE - f θ) (J *ᵥ g)
    rw [hsq]
    ring
  have h2 : w2 * inner ℝ (pE - f (θ + g)) pEd - w2 * inner ℝ (pE - f θ) pEd
      = -w2 * inner ℝ (J *ᵥ g) pEd := by
    rw [hsub]
    rw [vec_inner_sub_left]
    ring
  rw [show liFunc w1 w2 pE pEd (θ + g) f - liFunc w1 w2 pE pEd θ f =
      (w1 * eNorm (pE - f (θ + g)) ^ 2 - w1 * eNorm (pE - f θ) ^ 2) +
      (w2 * inner ℝ (pE - f (θ + g)) pEd - w2 * inner ℝ (pE - f θ) pEd) by
        unfold liFunc
        abel]
  have hrhs : inner ℝ (((-2 * w1) • (pE - f θ)) - w2 • pEd) (J *ᵥ g)
      = -2 * w1 * inner ℝ (pE - f θ) (J *ᵥ g) - w2 * inner ℝ pEd (J *ᵥ g) := by
    calc
      inner ℝ (((-2 * w1) • (pE - f θ)) - w2 • pEd) (J *ᵥ g)
          = inner ℝ (((-2 * w1) • (pE - f θ))) (J *ᵥ g) - inner ℝ (w2 • pEd) (J *ᵥ g) := by
            rw [vec_inner_sub_left]
      _ = (-2 * w1) * inner ℝ (pE - f θ) (J *ᵥ g) - w2 * inner ℝ pEd (J *ᵥ g) := by
            have hs1 : inner ℝ (((-2 * w1) • (pE - f θ))) (J *ᵥ g) =
                (-2 * w1) * inner ℝ (pE - f θ) (J *ᵥ g) := by
              exact vec_inner_smul_left (-2 * w1) (pE - f θ) (J *ᵥ g)
            rw [hs1]
            rw [vec_inner_smul_left]
  rw [h1, h2, hrhs]
  rw [vec_inner_symm (J *ᵥ g) pEd]
  ring

end Obstacle
