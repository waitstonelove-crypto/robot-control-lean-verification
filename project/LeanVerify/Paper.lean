import LeanVerify.Core
import LeanVerify.QP_LVI_PNN

/-! # 论文公式验证：Ma et al. TSMC 2023 的 ⊗ 算子、ASOA、VAM、η 统一化、拉格朗日/RNN/单调性。 -/

open Matrix
open QPLVI

namespace Paper

/-- ⊗ 算子：s ⊗ h = [s₁·h, …, sₙ·h]（h 为 m 维列向量，sᵢ 为 s 的第 i 列） —— 论文 (15) -/
noncomputable def otimes {m n : ℕ} (s : Matrix (Fin m) (Fin n) ℝ) (h : Vec m) : Vec n :=
  fun j => inner ℝ (fun i => s i j) h

/-- 核心恒等式：(s ⊗ h)·x = hᵀ·(s·x) = ⟨h, sx⟩ —— 论文 (14)→(15) 的转换依据 -/
theorem otimes_mul {m n : ℕ} (s : Matrix (Fin m) (Fin n) ℝ) (h : Vec m) (x : Vec n) :
    inner ℝ (otimes s h) x = inner ℝ h (s *ᵥ x) := by
  rw [inner_vec_eq_sum, inner_vec_eq_sum]
  calc
    ∑ j, (∑ i, s i j * h i) * x j = ∑ j, ∑ i, s i j * h i * x j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_mul]
    _ = ∑ i, ∑ j, s i j * h i * x j := by rw [Finset.sum_comm]
    _ = ∑ i, h i * (∑ j, s i j * x j) := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        ∑ j, s i j * h i * x j = ∑ j, h i * (s i j * x j) := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = h i * ∑ j, s i j * x j := by rw [← Finset.mul_sum]
    _ = inner ℝ h (s *ᵥ x) := by
      simp [Matrix.mulVec, dotProduct]

/-- ASOA 约束推导（论文 (13)→(15)）：‖ṙ_CU‖τ + ‖r̈_CU‖τ²/2 ≤ d_GJK − d_2
   在 u_CO 单位且投影沿 u_CO 方向非负（‖ṙ_CU‖ = ṙ_C·u_CO，‖r̈_CU‖ = r̈_C·u_CO）下，
   代入 ṙ_C = J_Cθ̇、r̈_C = J̇_Cθ̇ + J_Cθ̈（论文 (14)），移项得 (J_C ⊗ u_CO)θ̈ ≤ b（论文 (15)(16)）。
   注：u 单位与非负投影假设由控制律保证，本定理以点积形式陈述其代数实质。 -/
theorem asoa_basic_ineq {m n : ℕ} (JC JdC : Matrix (Fin m) (Fin n) ℝ) (u : Vec m) (θd θdd : Vec n)
    (dGJK d2 τ : ℝ) (hτ : 0 < τ)
    (hineq : (inner ℝ (JC *ᵥ θd) u) * τ + (inner ℝ (JdC *ᵥ θd + JC *ᵥ θdd) u) * τ ^ 2 / 2 ≤ dGJK - d2) :
    inner ℝ (otimes JC u) θdd ≤ (2 * (dGJK - d2) - τ ^ 2 * inner ℝ (JdC *ᵥ θd) u - 2 * τ * inner ℝ (JC *ᵥ θd) u) / τ ^ 2 := by
  have hsplit : inner ℝ (JdC *ᵥ θd + JC *ᵥ θdd) u = inner ℝ (JdC *ᵥ θd) u + inner ℝ (JC *ᵥ θdd) u := by
    rw [vec_inner_add_left]
  have hineq' : (inner ℝ (JC *ᵥ θdd) u) * τ ^ 2 / 2 ≤
      dGJK - d2 - (inner ℝ (JdC *ᵥ θd) u) * τ ^ 2 / 2 - (inner ℝ (JC *ᵥ θd) u) * τ := by
    nlinarith [hineq, hsplit]
  have hmain : inner ℝ (JC *ᵥ θdd) u ≤
      (2 * (dGJK - d2) - τ ^ 2 * inner ℝ (JdC *ᵥ θd) u - 2 * τ * inner ℝ (JC *ᵥ θd) u) / τ ^ 2 := by
    rw [le_div_iff₀ (sq_pos_of_pos hτ)]
    nlinarith [hineq']
  rw [otimes_mul, vec_inner_symm]
  exact hmain

/-- b 的定义（论文 (16)）：b = [2(d_GJK − d_2) − τ²⟨J̇_Cθ̇,u⟩ − 2τ⟨J_Cθ̇,u⟩]/τ² -/
noncomputable def asoaB {m n : ℕ} (JC JdC : Matrix (Fin m) (Fin n) ℝ) (u : Vec m) (θd : Vec n)
    (dGJK d2 τ : ℝ) : ℝ :=
  (2 * (dGJK - d2) - τ ^ 2 * inner ℝ (JdC *ᵥ θd) u - 2 * τ * inner ℝ (JC *ᵥ θd) u) / τ ^ 2

/-- 最终 ASOA 约束（论文 (17)）：(J_C ⊗ u_CO)θ̈ ≤ b -/
theorem asoa_constraint {m n : ℕ} (JC JdC : Matrix (Fin m) (Fin n) ℝ) (u : Vec m) (θd θdd : Vec n)
    (dGJK d2 τ : ℝ) (hτ : 0 < τ)
    (hineq : (inner ℝ (JC *ᵥ θd) u) * τ + (inner ℝ (JdC *ᵥ θd + JC *ᵥ θdd) u) * τ ^ 2 / 2 ≤ dGJK - d2) :
    inner ℝ (otimes JC u) θdd ≤ asoaB JC JdC u θd dGJK d2 τ := by
  simpa [asoaB] using asoa_basic_ineq JC JdC u θd θdd dGJK d2 τ hτ hineq

/-- η⁻ = max(ϖp(μθ⁻−θ), ϖv(θ̇⁻−θ̇), θ̈⁻)，逐分量 —— 论文 (9a) -/
noncomputable def etaLow {n : ℕ} (ϖp ϖv μ : ℝ) (θ θd : Vec n) (θL θdL θddL : Vec n) : Vec n :=
  fun i => max (max (ϖp * (μ * θL i - θ i)) (ϖv * (θdL i - θd i))) (θddL i)

/-- η⁺ = min(ϖp(μθ⁺−θ), ϖv(θ̇⁺−θ̇), θ̈⁺)，逐分量 —— 论文 (9b) -/
noncomputable def etaHigh {n : ℕ} (ϖp ϖv μ : ℝ) (θ θd : Vec n) (θU θdU θddU : Vec n) : Vec n :=
  fun i => min (min (ϖp * (μ * θU i - θ i)) (ϖv * (θdU i - θd i))) (θddU i)

/-- 兼容性：η⁻ ≥ θ̈⁻、η⁺ ≤ θ̈⁺（逐分量），因此 [η⁻, η⁺] ⊆ [θ̈⁻, θ̈⁺] —— 论文 (8) 语义 -/
theorem eta_bounds {n : ℕ} (ϖp ϖv μ : ℝ) (θ θd θL θdL θddL θU θdU θddU : Vec n) :
    (∀ i, θddL i ≤ etaLow ϖp ϖv μ θ θd θL θdL θddL i) ∧
    (∀ i, etaHigh ϖp ϖv μ θ θd θU θdU θddU i ≤ θddU i) := by
  constructor
  · intro i
    exact le_max_of_le_right le_rfl
  · intro i
    exact min_le_right (min (ϖp * (μ * θU i - θ i)) (ϖv * (θdU i - θd i))) (θddU i)

/-- 临界收紧：ϖp > 0 时，θ 增大 ⟹ ϖp(μθ⁻−θ) 减小（θ 越靠近下限，η⁻ 的下限项越紧）
   —— 论文 Remark 1（该不等式与 μ 符号无关，μ 的正性用于保证 ϖp 项的物理方向） -/
theorem eta_tightening {n : ℕ} (ϖp μ : ℝ) (hϖ : 0 < ϖp)
    (θL : Vec n) (θ1 θ2 : Vec n) (i : Fin n) (hθ : θ1 i ≤ θ2 i) :
    ϖp * (μ * θL i - θ2 i) ≤ ϖp * (μ * θL i - θ1 i) := by
  have hle : μ * θL i - θ2 i ≤ μ * θL i - θ1 i := by linarith
  exact mul_le_mul_of_nonneg_left hle (le_of_lt hϖ)

/-- η⁻ 判定：η⁻_i ≤ x ⟺ 三项均 ≤ x（max 结构） —— 论文 (9a) -/
theorem etaLow_le_iff {n : ℕ} (ϖp ϖv μ : ℝ) (θ θd θL θdL θddL : Vec n) (i : Fin n) (x : ℝ) :
    etaLow ϖp ϖv μ θ θd θL θdL θddL i ≤ x ↔
      ϖp * (μ * θL i - θ i) ≤ x ∧ ϖv * (θdL i - θd i) ≤ x ∧ θddL i ≤ x := by
  simp [etaLow, max_le_iff, and_assoc]

/-- η⁺ 判定：x ≤ η⁺_i ⟺ x ≤ 三项（min 结构） —— 论文 (9b) -/
theorem etaHigh_ge_iff {n : ℕ} (ϖp ϖv μ : ℝ) (θ θd θU θdU θddU : Vec n) (i : Fin n) (x : ℝ) :
    x ≤ etaHigh ϖp ϖv μ θ θd θU θdU θddU i ↔
      x ≤ ϖp * (μ * θU i - θ i) ∧ x ≤ ϖv * (θdU i - θd i) ∧ x ≤ θddU i := by
  simp [etaHigh, le_min_iff, and_assoc]

/-- 展开恒等式：½(α‖θ̈+ζθ̇‖² + β‖θ̈‖²) = ½‖θ̈‖² + αζ⟨θ̇,θ̈⟩ + ½αζ²‖θ̇‖²（α+β=1）
   —— 论文 (24)(25)(26)。‖·‖ 为欧氏范数 eNorm。 -/
theorem vam_expand {n : ℕ} (α β ζ : ℝ) (hαβ : α + β = 1) (θd θdd : Vec n) :
    (1 / 2) * (α * eNorm (θdd + ζ • θd) ^ 2 + β * eNorm θdd ^ 2)
      = (1 / 2) * eNorm θdd ^ 2 + α * ζ * inner ℝ θd θdd + (1 / 2) * α * ζ ^ 2 * eNorm θd ^ 2 := by
  have hnorm : eNorm (θdd + ζ • θd) ^ 2 = eNorm θdd ^ 2 + 2 * ζ * inner ℝ θd θdd + ζ ^ 2 * eNorm θd ^ 2 := by
    rw [eNorm_sq_eq_inner, eNorm_sq_eq_inner, eNorm_sq_eq_inner]
    simp only [vec_inner_add_left, vec_inner_add_right, vec_inner_smul_left, vec_inner_smul_right]
    rw [vec_inner_symm θdd θd]
    ring
  rw [hnorm]
  have hβ : β = 1 - α := by linarith
  rw [hβ]
  ring

/-- 目标差恒等式：VAM 原目标与简化目标（对 θ̈）相差与 θ̈ 无关的常数 —— 论文 Theorem 1 -/
theorem vam_equiv {n : ℕ} (α β ζ : ℝ) (hαβ : α + β = 1) (θd θdd1 θdd2 : Vec n) :
    (1 / 2) * (α * eNorm (θdd1 + ζ • θd) ^ 2 + β * eNorm θdd1 ^ 2)
        - (1 / 2) * (α * eNorm (θdd2 + ζ • θd) ^ 2 + β * eNorm θdd2 ^ 2)
      = ((1 / 2) * eNorm θdd1 ^ 2 + α * ζ * inner ℝ θd θdd1)
        - ((1 / 2) * eNorm θdd2 ^ 2 + α * ζ * inner ℝ θd θdd2) := by
  rw [vam_expand α β ζ hαβ θd θdd1, vam_expand α β ζ hαβ θd θdd2]
  ring

/-- 最小化器集合等价：VAM 原目标与简化目标在 S 上有相同的最小点集 —— 论文 Theorem 1 结论 -/
theorem vam_equiv_minimizer {n : ℕ} (α β ζ : ℝ) (hαβ : α + β = 1) (θd : Vec n) (S : Set (Vec n)) :
    {x ∈ S | ∀ y ∈ S, (1 / 2) * (α * eNorm (y + ζ • θd) ^ 2 + β * eNorm y ^ 2) ≥
        (1 / 2) * (α * eNorm (x + ζ • θd) ^ 2 + β * eNorm x ^ 2)}
      = {x ∈ S | ∀ y ∈ S, (1 / 2) * eNorm y ^ 2 + α * ζ * inner ℝ θd y ≥
        (1 / 2) * eNorm x ^ 2 + α * ζ * inner ℝ θd x} := by
  ext x
  constructor <;> intro hx
  · constructor
    · exact hx.1
    · intro y hy
      have hd : (1 / 2) * (α * eNorm (y + ζ • θd) ^ 2 + β * eNorm y ^ 2)
            - (1 / 2) * (α * eNorm (x + ζ • θd) ^ 2 + β * eNorm x ^ 2)
          = ((1 / 2) * eNorm y ^ 2 + α * ζ * inner ℝ θd y)
            - ((1 / 2) * eNorm x ^ 2 + α * ζ * inner ℝ θd x) := vam_equiv α β ζ hαβ θd y x
      nlinarith [hx.2 y hy, hd]
  · constructor
    · exact hx.1
    · intro y hy
      have hd : (1 / 2) * (α * eNorm (y + ζ • θd) ^ 2 + β * eNorm y ^ 2)
            - (1 / 2) * (α * eNorm (x + ζ • θd) ^ 2 + β * eNorm x ^ 2)
          = ((1 / 2) * eNorm y ^ 2 + α * ζ * inner ℝ θd y)
            - ((1 / 2) * eNorm x ^ 2 + α * ζ * inner ℝ θd x) := vam_equiv α β ζ hαβ θd y x
      nlinarith [hx.2 y hy, hd]

/-- 拉格朗日函数 L(θ̈, ϑ, ν) = ½θ̈ᵀθ̈ + αζθ̇ᵀθ̈ + ϑᵀ(r̈G − J_Eθ̈) + ν(J_C⊗uθ̈ − b) —— 论文 (29) -/
noncomputable def lagrangian {n m : ℕ} (α ζ : ℝ) (θd : Vec n) (θdd : Vec n)
    (JE : Matrix (Fin m) (Fin n) ℝ) (rGd : Vec m) (lam : Vec m) (JC : Matrix (Fin m) (Fin n) ℝ)
    (u : Vec m) (b : ℝ) (nu : ℝ) : ℝ :=
  (1 / 2) * inner ℝ θdd θdd + α * ζ * inner ℝ θd θdd + inner ℝ lam (rGd - JE *ᵥ θdd) +
    nu * (inner ℝ (otimes JC u) θdd - b)

/-- 拉格朗日的二次结构：L(x1) − L(x2) = ⟨s, x1 − x2⟩ + ½‖x1−x2‖²，
   其中 s = θ̈ + αζθ̇ − J_Eᵀϑ + ν(J_C⊗u) 即论文 (30a) 的 ∂L/∂θ̈（代数层，替代 FDeriv 封装） -/
theorem lagrangian_quadratic {n m : ℕ} (α ζ : ℝ) (θd : Vec n) (JE : Matrix (Fin m) (Fin n) ℝ)
    (rGd : Vec m) (lam : Vec m) (JC : Matrix (Fin m) (Fin n) ℝ) (u : Vec m) (b : ℝ) (nu : ℝ)
    (x1 x2 : Vec n) :
    lagrangian α ζ θd x1 JE rGd lam JC u b nu - lagrangian α ζ θd x2 JE rGd lam JC u b nu
      = inner ℝ (x2 + (α * ζ) • θd - (JEᵀ) *ᵥ lam + nu • otimes JC u) (x1 - x2) +
        (1 / 2) * eNorm (x1 - x2) ^ 2 := by
  have h1 : (1 / 2) * inner ℝ x1 x1 - (1 / 2) * inner ℝ x2 x2
      = inner ℝ x2 (x1 - x2) + (1 / 2) * eNorm (x1 - x2) ^ 2 := by
    rw [eNorm_sq_eq_inner]
    have hx : x1 = x2 + (x1 - x2) := by abel
    have hinner : inner ℝ x1 x1 =
        inner ℝ x2 x2 + 2 * inner ℝ x2 (x1 - x2) + inner ℝ (x1 - x2) (x1 - x2) := by
      calc
        inner ℝ x1 x1 = inner ℝ (x2 + (x1 - x2)) (x2 + (x1 - x2)) := by
          congr 2 <;> exact hx
        _ = inner ℝ x2 x2 + 2 * inner ℝ x2 (x1 - x2) + inner ℝ (x1 - x2) (x1 - x2) := by
          simp only [vec_inner_add_left, vec_inner_add_right, vec_inner_symm x2 (x1 - x2)]
          ring
    rw [hinner]
    ring
  have h2 : α * ζ * inner ℝ θd x1 - α * ζ * inner ℝ θd x2 = α * ζ * inner ℝ θd (x1 - x2) := by
    have hsub : inner ℝ θd x1 - inner ℝ θd x2 = inner ℝ θd (x1 - x2) := by
      exact (vec_inner_sub_right θd x1 x2).symm
    rw [← mul_sub]
    rw [hsub]
  have h3 : inner ℝ lam (rGd - JE *ᵥ x1) - inner ℝ lam (rGd - JE *ᵥ x2)
      = -inner ℝ ((JEᵀ) *ᵥ lam) (x1 - x2) := by
    calc
      inner ℝ lam (rGd - JE *ᵥ x1) - inner ℝ lam (rGd - JE *ᵥ x2)
          = inner ℝ lam ((rGd - JE *ᵥ x1) - (rGd - JE *ᵥ x2)) := by
            rw [← vec_inner_sub_right lam (rGd - JE *ᵥ x1) (rGd - JE *ᵥ x2)]
      _ = inner ℝ lam (-(JE *ᵥ (x1 - x2))) := by
            congr 1
            rw [Matrix.mulVec_sub]
            abel
      _ = -inner ℝ lam (JE *ᵥ (x1 - x2)) := by rw [vec_inner_neg_right]
      _ = -inner ℝ ((JEᵀ) *ᵥ lam) (x1 - x2) := by
            rw [vec_inner_symm lam (JE *ᵥ (x1 - x2))]
            rw [vec_mulVec_adjoint JE (x1 - x2) lam]
            rw [vec_inner_symm (x1 - x2) ((JEᵀ) *ᵥ lam)]
  have h4 : nu * (inner ℝ (otimes JC u) x1 - b) - nu * (inner ℝ (otimes JC u) x2 - b)
      = nu * inner ℝ (otimes JC u) (x1 - x2) := by
    have hsub : inner ℝ (otimes JC u) x1 - inner ℝ (otimes JC u) x2 =
        inner ℝ (otimes JC u) (x1 - x2) := by
      exact (vec_inner_sub_right (otimes JC u) x1 x2).symm
    calc
      nu * (inner ℝ (otimes JC u) x1 - b) - nu * (inner ℝ (otimes JC u) x2 - b)
          = nu * ((inner ℝ (otimes JC u) x1 - b) - (inner ℝ (otimes JC u) x2 - b)) := by
            rw [← mul_sub]
      _ = nu * (inner ℝ (otimes JC u) x1 - inner ℝ (otimes JC u) x2) := by
            congr 1
            ring
      _ = nu * inner ℝ (otimes JC u) (x1 - x2) := by rw [hsub]
  rw [show lagrangian α ζ θd x1 JE rGd lam JC u b nu - lagrangian α ζ θd x2 JE rGd lam JC u b nu =
      ((1 / 2) * inner ℝ x1 x1 - (1 / 2) * inner ℝ x2 x2) +
      (α * ζ * inner ℝ θd x1 - α * ζ * inner ℝ θd x2) +
      (inner ℝ lam (rGd - JE *ᵥ x1) - inner ℝ lam (rGd - JE *ᵥ x2)) +
      (nu * (inner ℝ (otimes JC u) x1 - b) - nu * (inner ℝ (otimes JC u) x2 - b)) by
        unfold lagrangian
        abel]
  rw [h1, h2, h3, h4]
  rw [eNorm_sq_eq_inner]
  simp only [vec_inner_add_left, vec_inner_sub_left, vec_inner_smul_left, neg_smul]
  ring

/-- F 的单调性直接验证（论文 Definition 1 + (36) 的代数实质）：
   ⟨δ, F(λ+δ) − F(λ)⟩ = ‖δx‖² ≥ 0，对应论文 (34) 的 F₁ = θ̈ − J_Eᵀϑ + ϑ(J_C⊗u) + αζθ̇、
   F₂ = J_Eθ̈ − r̈G、F₃ = b − J_C⊗uθ̈（仿射部分，平移项 αζθ̇、r̈G、b 对差无贡献）。
   注：论文 (35) 的 ∇F 矩阵 (2,1) 块印为 −J_E，与 (34) 的 F₂ = J_Eθ̈ − r̈G 不符（∂F₂/∂θ̈ = J_E）；
   本验证以 (34) 为准，单调性结论 ‖δx‖² 与 (36) 的 diag(2I,0,0) 一致。 -/
theorem F_monotone {n m : ℕ} (JE : Matrix (Fin m) (Fin n) ℝ) (JC : Matrix (Fin m) (Fin n) ℝ)
    (u : Vec m) (δx : Vec n) (δlam : Vec m) (δnu : ℝ) :
    inner ℝ δx (δx - (JEᵀ) *ᵥ δlam + δnu • otimes JC u) +
    inner ℝ δlam (JE *ᵥ δx) + δnu * (-(inner ℝ (otimes JC u) δx)) = eNorm δx ^ 2 := by
  rw [eNorm_sq_eq_inner]
  rw [vec_inner_add_right, vec_inner_sub_right, vec_inner_smul_right]
  rw [← vec_mulVec_adjoint JE δx δlam]
  rw [vec_inner_symm δlam (JE *ᵥ δx)]
  rw [vec_inner_symm (otimes JC u) δx]
  ring

/-- F 单调非负（论文 Definition 1 验证完成） —— 供 Theorem 2 应用链引用 -/
theorem F_monotone_nonneg {n m : ℕ} (JE : Matrix (Fin m) (Fin n) ℝ) (JC : Matrix (Fin m) (Fin n) ℝ)
    (u : Vec m) (δx : Vec n) (δlam : Vec m) (δnu : ℝ) :
    0 ≤ inner ℝ δx (δx - (JEᵀ) *ᵥ δlam + δnu • otimes JC u) +
        inner ℝ δlam (JE *ᵥ δx) + δnu * (-(inner ℝ (otimes JC u) δx)) := by
  rw [F_monotone]
  exact sq_nonneg _

/-- 非负投影 (·)† = max(·,0) 的不动点刻画：ϑ = (ϑ+g)† ⟺ ϑ ≥ 0 ∧ g ≤ 0 ∧ (ϑ = 0 ∨ g = 0)
   —— 论文 (30c) 的互补松弛语义（单分量） -/
theorem nonneg_proj_fixed_point (nu g : ℝ) :
    nu = max (nu + g) 0 ↔ nu ≥ 0 ∧ g ≤ 0 ∧ (nu = 0 ∨ g = 0) := by
  constructor
  · intro h
    have h1 : nu ≥ 0 := by
      rw [h]
      exact le_max_of_le_right le_rfl
    have h2 : g ≤ 0 := by
      have : nu + g ≤ nu := (le_max_left (nu + g) 0).trans_eq h.symm
      linarith
    have h3 : nu = 0 ∨ g = 0 := by
      by_cases hnu0 : nu = 0
      · exact Or.inl hnu0
      · right
        have hpos : 0 < nu := lt_of_le_of_ne h1 (Ne.symm hnu0)
        have hge : 0 ≤ nu + g := by
          by_contra hlt
          have : nu + g < 0 := not_le.mp hlt
          have hmax : max (nu + g) 0 = 0 := max_eq_right (le_of_lt this)
          rw [h, hmax] at hpos
          linarith
        have hmax : max (nu + g) 0 = nu + g := max_eq_left hge
        have : nu = nu + g := by
          calc
            nu = max (nu + g) 0 := h
            _ = nu + g := hmax
        linarith
    exact ⟨h1, h2, h3⟩
  · intro h
    rcases h with ⟨hnu0, hg, hcases⟩
    rcases hcases with hnu | hg0
    · rw [hnu]
      simpa using (max_eq_right hg).symm
    · rw [hg0]
      simpa using (max_eq_left hnu0).symm

/-- 框内不动点 = 一阶条件：x = P_V(x − g) 且 x ∈ V ⟺ ∀ z ∈ V, ⟨z − x, g⟩ ≥ 0
   —— 论文 (30a)「θ̈ = P_V(θ̈ − ∂L/∂θ̈)」与 KKT 平稳性的等价（对任意梯度场 g；(28) 实例化） -/
theorem fixed_point_iff_first_order {n : ℕ} {l h : Vec n} (g : Vec n) (x : Vec n)
    (hlh : ∀ i, l i ≤ h i) (hx : ∀ i, l i ≤ x i ∧ x i ≤ h i) :
    (x = boxProj l h (x - g)) ↔ ∀ z : Vec n, (∀ i, l i ≤ z i ∧ z i ≤ h i) → 0 ≤ inner ℝ (z - x) g := by
  constructor
  · intro hfp
    have hVI := fixed_point_implies_VI (fun _ : Vec n => g) (feasibleSetBox l h) (boxProj l h)
      (fun y => fun i => ⟨(boxProj_mem hlh y).1 i, (boxProj_mem hlh y).2 i⟩)
      (fun a z hz => @boxProj_char n l h a z (by simpa [feasibleSetBox] using hz))
      x hx hfp
    intro z hz
    exact hVI.2 z (by simpa [feasibleSetBox] using hz)
  · intro hfirst
    exact VI_implies_fixed_point (fun _ : Vec n => g) (feasibleSetBox l h) (boxProj l h)
      (fun y => fun i => ⟨(boxProj_mem hlh y).1 i, (boxProj_mem hlh y).2 i⟩)
      (fun a z hz => @boxProj_char n l h a z (by simpa [feasibleSetBox] using hz))
      x hx ⟨hx, fun z hz => hfirst z (by simpa [feasibleSetBox] using hz)⟩

/-- Theorem 2 组装（论文 Theorem 2 的验证骨架）：
   ① 平稳性：θ̈ = P_V(θ̈ − ∂L/∂θ̈)（hfix）⟹ 框内 + 一阶条件（fixed_point_iff_first_order）
   ② 原始可行性：r̈G = J_Eθ̈（heq，RNN 的 ϑ̇ 平衡分量）
   ③ 互补松弛：ν = (ν + g)†（hnu）⟹ ν ≥ 0 ∧ g ≤ 0 ∧ (ν = 0 ∨ g = 0)（nonneg_proj_fixed_point）
   ④ F 单调（F_monotone_nonneg，论文 (36)）
   收敛到 QP (28) 最优解：「KKT ⟹ 最优」在凸性与约束规格下成立（假设，见 VERIFICATION.md），
   收敛速率由 ConvergenceAxioms.pnn_convergence 覆盖。 -/
theorem paper_theorem2_assembly {n m : ℕ} {l h : Vec n} (JE : Matrix (Fin m) (Fin n) ℝ)
    (JC : Matrix (Fin m) (Fin n) ℝ) (u : Vec m) (α ζ : ℝ) (θd θdd : Vec n)
    (rGd : Vec m) (b : ℝ) (lam : Vec m) (nu g : ℝ) (hlh : ∀ i, l i ≤ h i)
    (hfix : θdd = boxProj l h (θdd - (θdd + (α * ζ) • θd - (JEᵀ) *ᵥ lam + nu • otimes JC u)))
    (heq : rGd = JE *ᵥ θdd)
    (hnu : nu = max (nu + g) 0) :
    (∀ i, l i ≤ θdd i ∧ θdd i ≤ h i) ∧
    (∀ z : Vec n, (∀ i, l i ≤ z i ∧ z i ≤ h i) →
      0 ≤ inner ℝ (z - θdd) (θdd + (α * ζ) • θd - (JEᵀ) *ᵥ lam + nu • otimes JC u)) ∧
    (0 ≤ nu ∧ g ≤ 0 ∧ (nu = 0 ∨ g = 0)) := by
  have hin : ∀ i, l i ≤ θdd i ∧ θdd i ≤ h i := by
    intro i
    rw [hfix]
    exact ⟨(boxProj_mem hlh _).1 i, (boxProj_mem hlh _).2 i⟩
  have hfirst : ∀ z : Vec n, (∀ i, l i ≤ z i ∧ z i ≤ h i) →
      0 ≤ inner ℝ (z - θdd) (θdd + (α * ζ) • θd - (JEᵀ) *ᵥ lam + nu • otimes JC u) :=
    (fixed_point_iff_first_order (θdd + (α * ζ) • θd - (JEᵀ) *ᵥ lam + nu • otimes JC u) θdd hlh hin).1 hfix
  exact ⟨hin, hfirst, (nonneg_proj_fixed_point nu g).mp hnu⟩

end Paper
