import LeanVerify.Core

open Matrix

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

end Paper
