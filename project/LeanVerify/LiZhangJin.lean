import LeanVerify.Core
import LeanVerify.QP_LVI_PNN

open Matrix Filter
open scoped Topology

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

/-- 论文 (32)(33)：P(z) = 0 时（z = −Jᵀe/γ），投影最小距离给出
   ∀y ∈ Ω, ‖y‖² + (2/γ)⟨Jᵀe, y⟩ ≥ 0 -/
theorem proj_zero_ineq {n m : ℕ} (P : Vec n → Vec n) (Ω : Set (Vec n))
    (hPdist : ∀ z y : Vec n, y ∈ Ω → eNorm (P z - z) ≤ eNorm (y - z))
    (J : Matrix (Fin m) (Fin n) ℝ) (γ : ℝ) (hγ : 0 < γ) (e : Vec m)
    (hPz : P (vecDiv (-((Jᵀ) *ᵥ e)) γ) = 0) (y : Vec n) (hy : y ∈ Ω) :
    0 ≤ eNorm y ^ 2 + (2 / γ) * inner ℝ ((Jᵀ) *ᵥ e) y := by
  let z : Vec n := vecDiv (-((Jᵀ) *ᵥ e)) γ
  have hnorm : eNorm (P z - z) = eNorm z := by
    rw [hPz]
    simpa using eNorm_neg z
  have hdist : eNorm z ≤ eNorm (y - z) := by
    have h1 := hPdist z y hy
    simpa [hnorm] using h1
  have hsq1 : eNorm z ^ 2 ≤ eNorm (y - z) ^ 2 := by
    exact sq_le_sq_of_nonneg (eNorm_nonneg z) (eNorm_nonneg (y - z)) hdist
  have hsqz := eNorm_sub_sq y z
  have hineq : 2 * inner ℝ y z ≤ eNorm y ^ 2 := by
    nlinarith [hsq1, hsqz]
  have hzinner : inner ℝ y z = -(1 / γ) * inner ℝ ((Jᵀ) *ᵥ e) y := by
    rw [inner_vec_eq_sum, inner_vec_eq_sum]
    calc
      ∑ i, y i * (vecDiv (-((Jᵀ) *ᵥ e)) γ) i = ∑ i, y i * (-((Jᵀ) *ᵥ e) i / γ) := by
        apply Finset.sum_congr rfl
        intro i hi
        rfl
      _ = -(1 / γ) * ∑ i, ((Jᵀ) *ᵥ e) i * y i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = -(1 / γ) * inner ℝ ((Jᵀ) *ᵥ e) y := by
        rw [inner_vec_eq_sum]
  rw [hzinner] at hineq
  ring_nf at hineq ⊢
  nlinarith

/-- 论文 (30)-(37)：P(−Jᵀe/γ) = 0 且 0 ∈ int(Ω)（eNorm 球形式）⟹ Jᵀe = 0。
   论证：∀ρ ∈ (0, ρ₀]，取 y = −ρJᵀe/(2‖Jᵀe‖) ∈ Ω（范数 ρ/2），代入 (33) 得 ρ ≥ 4‖Jᵀe‖/γ；
   取 ρ = min(ρ₀/2, 2‖Jᵀe‖/γ) 得矛盾（无极限，纯代数）。 -/
theorem proj_zero_implies_JTe_zero {n m : ℕ} (P : Vec n → Vec n) (Ω : Set (Vec n))
    (hPdist : ∀ z y : Vec n, y ∈ Ω → eNorm (P z - z) ≤ eNorm (y - z))
    (J : Matrix (Fin m) (Fin n) ℝ) (γ : ℝ) (hγ : 0 < γ) (e : Vec m)
    (hIntBall : ∃ ρ₀ > 0, ∀ y : Vec n, eNorm y ≤ ρ₀ → y ∈ Ω)
    (hPz : P (vecDiv (-((Jᵀ) *ᵥ e)) γ) = 0) :
    (Jᵀ) *ᵥ e = 0 := by
  rcases hIntBall with ⟨ρ₀, hρ₀, hball⟩
  by_contra hne
  have hJTe : 0 < eNorm ((Jᵀ) *ᵥ e) :=
    lt_of_le_of_ne (eNorm_nonneg _) (fun h => hne ((eNorm_eq_zero_iff ((Jᵀ) *ᵥ e)).mp h.symm))
  let c : ℝ := 4 * eNorm ((Jᵀ) *ᵥ e) / γ
  have hc : 0 < c := by
    dsimp [c]
    exact div_pos (mul_pos (by norm_num) hJTe) hγ
  have hall : ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → c ≤ ρ := by
    intro ρ hρ hρle
    let y0 : Vec n := (-(ρ / (2 * eNorm ((Jᵀ) *ᵥ e)))) • ((Jᵀ) *ᵥ e)
    have hny : eNorm y0 = ρ / 2 := by
      dsimp [y0]
      rw [eNorm_smul]
      have hden : 0 < 2 * eNorm ((Jᵀ) *ᵥ e) := by positivity
      rw [abs_neg, abs_div, abs_of_pos hρ, abs_of_pos hden]
      field_simp [ne_of_gt hden]
    have hy0mem : y0 ∈ Ω := by
      apply hball
      have : ρ / 2 ≤ ρ := by linarith
      linarith [hny]
    have hineq := proj_zero_ineq P Ω hPdist J γ hγ e hPz y0 hy0mem
    have hinner : inner ℝ ((Jᵀ) *ᵥ e) y0 = -(ρ * eNorm ((Jᵀ) *ᵥ e) / 2) := by
      dsimp [y0]
      rw [vec_inner_smul_right]
      rw [← eNorm_sq_eq_inner]
      field_simp [ne_of_gt hJTe]
    have hny2 : eNorm y0 ^ 2 = (ρ / 2) ^ 2 := by nlinarith [hny]
    -- 0 ≤ ρ²/4 + (2/γ)(−ρ‖Jᵀe‖/2) = ρ²/4 − ρ‖Jᵀe‖/γ ⟹ ρ ≥ 4‖Jᵀe‖/γ = c
    rw [hinner, hny2] at hineq
    ring_nf at hineq
    have hineq4 : 4 * ρ * eNorm ((Jᵀ) *ᵥ e) ≤ ρ ^ 2 * γ := by
      have h4g : 0 ≤ 4 * γ := by positivity
      have hm := mul_nonneg hineq h4g
      field_simp [hγ.ne'] at hm
      nlinarith
    have hfinal : 4 * eNorm ((Jᵀ) *ᵥ e) / γ ≤ ρ := by
      rw [div_le_iff₀ hγ]
      have hrew : 4 * eNorm ((Jᵀ) *ᵥ e) = (1 / ρ) * (4 * ρ * eNorm ((Jᵀ) *ᵥ e)) := by
        field_simp [hρ.ne']
      rw [hrew]
      have h1r : 0 ≤ 1 / ρ := by positivity
      have hstep : (1 / ρ) * (4 * ρ * eNorm ((Jᵀ) *ᵥ e)) ≤ (1 / ρ) * (ρ ^ 2 * γ) :=
        mul_le_mul_of_nonneg_left hineq4 h1r
      field_simp [hρ.ne'] at hstep ⊢
      exact hstep
    simpa [c] using hfinal
  let ρ : ℝ := min (ρ₀ / 2) (c / 2)
  have hρ0 : 0 < ρ := by
    dsimp [ρ]
    exact lt_min (div_pos hρ₀ (by norm_num)) (div_pos hc (by norm_num))
  have hρle : ρ ≤ ρ₀ := by
    dsimp [ρ]
    linarith [min_le_left (ρ₀ / 2) (c / 2)]
  have hcρ : c ≤ ρ := hall ρ hρ0 hρle
  have hρlt : ρ < c := by
    dsimp [ρ]
    linarith [min_le_right (ρ₀ / 2) (c / 2)]
  linarith

/-- 论文 (37) 收口：J 行满秩（JJᵀ 可逆）时 Jᵀe = 0 ⟹ e = 0 -/
theorem JTe_zero_implies_e_zero {m n : ℕ} (J : Matrix (Fin m) (Fin n) ℝ)
    (h : IsUnit (J * Jᵀ)) (e : Vec m) (hJTe : (Jᵀ) *ᵥ e = 0) : e = 0 := by
  have hJJTe : (J * Jᵀ) *ᵥ e = 0 := by
    rw [← Matrix.mulVec_mulVec]
    rw [hJTe, Matrix.mulVec_zero]
  have hinv : (J * Jᵀ)⁻¹ * (J * Jᵀ) = 1 :=
    Matrix.nonsing_inv_mul (J * Jᵀ) ((Matrix.isUnit_iff_isUnit_det (J * Jᵀ)).1 h)
  calc
    e = 1 *ᵥ e := by simp
    _ = ((J * Jᵀ)⁻¹ * (J * Jᵀ)) *ᵥ e := by rw [hinv]
    _ = (J * Jᵀ)⁻¹ *ᵥ ((J * Jᵀ) *ᵥ e) := by rw [Matrix.mulVec_mulVec]
    _ = (J * Jᵀ)⁻¹ *ᵥ 0 := by rw [hJJTe]
    _ = 0 := by simp

/-- Theorem 1 的不变集分析（论文 (30)-(37) 组装）：
   P(−Jᵀe/γ) = 0 且 0 ∈ int(Ω) 且行满秩 ⟹ e = 0 -/
theorem theorem1_invariant_set {n m : ℕ} (P : Vec n → Vec n) (Ω : Set (Vec n))
    (hPdist : ∀ z y : Vec n, y ∈ Ω → eNorm (P z - z) ≤ eNorm (y - z))
    (J : Matrix (Fin m) (Fin n) ℝ) (hJ : IsUnit (J * Jᵀ))
    (γ : ℝ) (hγ : 0 < γ) (e : Vec m)
    (hIntBall : ∃ ρ₀ > 0, ∀ y : Vec n, eNorm y ≤ ρ₀ → y ∈ Ω)
    (hPz : P (vecDiv (-((Jᵀ) *ᵥ e)) γ) = 0) :
    e = 0 := by
  exact JTe_zero_implies_e_zero J hJ e (proj_zero_implies_JTe_zero P Ω hPdist J γ hγ e hIntBall hPz)

/-- 论文 (28)(29)(30)：V̇ = ⟨e, JP(−Jᵀe/γ)⟩ = 0 ⟹ P(−Jᵀe/γ) = 0
   （从 (25) ‖P z‖² ≤ 2⟨P z, z⟩ 与 ⟨e, JPz⟩ = −γ⟨z, Pz⟩） -/
theorem Vdot_zero_implies_Pzero {n m : ℕ} (P : Vec n → Vec n) (Ω : Set (Vec n))
    (hPdist : ∀ z y : Vec n, y ∈ Ω → eNorm (P z - z) ≤ eNorm (y - z))
    (h0 : (0 : Vec n) ∈ Ω)
    (J : Matrix (Fin m) (Fin n) ℝ) (γ : ℝ) (hγ : 0 < γ) (e : Vec m)
    (hV : inner ℝ e (J *ᵥ P (vecDiv (-((Jᵀ) *ᵥ e)) γ)) = 0) :
    P (vecDiv (-((Jᵀ) *ᵥ e)) γ) = 0 := by
  let z : Vec n := vecDiv (-((Jᵀ) *ᵥ e)) γ
  have hineq : eNorm (P z) ^ 2 ≤ 2 * inner ℝ (P z) z := proj_sq_ineq P Ω hPdist h0 z
  have hadj : inner ℝ e (J *ᵥ P z) = -γ * inner ℝ (P z) z := by
    have h1 : inner ℝ e (J *ᵥ P z) = inner ℝ ((Jᵀ) *ᵥ e) (P z) := by
      rw [vec_inner_symm e (J *ᵥ P z)]
      rw [vec_mulVec_adjoint J (P z) e]
      rw [vec_inner_symm (P z) ((Jᵀ) *ᵥ e)]
    have hz : (Jᵀ) *ᵥ e = -(γ • z) := by
      ext i
      change (Jᵀ *ᵥ e) i = -(γ * (z i))
      dsimp [z, vecDiv]
      field_simp [hγ.ne']
    rw [h1, hz]
    rw [vec_inner_neg_left, vec_inner_smul_left]
    rw [vec_inner_symm z (P z)]
    ring
  have hzz : inner ℝ (P z) z = 0 := by
    have hVz : inner ℝ e (J *ᵥ P z) = 0 := by simpa [z] using hV
    rw [hadj] at hVz
    nlinarith [hVz, hγ]
  have hsq : eNorm (P z) ^ 2 ≤ 0 := by nlinarith [hineq, hzz]
  have hPz0 : eNorm (P z) = 0 := sq_eq_zero_iff.mp (le_antisymm hsq (sq_nonneg _))
  exact (eNorm_eq_zero_iff (P z)).mp hPz0

/--
LaSalle 不变集原理（收敛收口，axiom）：
   若 V(t) = ‖e(t)‖²/2 沿误差动态满足 V̇ ≤ 0（hneg），且 V̇ = 0 蕴含 e = 0（hinv，
   即最大不变集仅含 {0}），则 e(t) → 0（t → ∞）。
   引用：LaSalle (1960) "Some extensions of Lyapunov's second method" / Khalil, Nonlinear Systems。
   说明：定理本体为动力系统理论标准结果，本项目严格验证其前提
   （hneg：B1 的 Vdot_nonpos；hinv：B2-B3 的不变集分析）与应用链。 -/
axiom lasalle_global_convergence {m : ℕ} (e : ℝ → Vec m)
    (Vdot : Vec m → ℝ)
    (hVdot : ∀ t, HasDerivAt (fun s : ℝ => (1 / 2) * eNorm (e s) ^ 2) (Vdot (e t)) t)
    (hneg : ∀ x : Vec m, Vdot x ≤ 0)
    (hinv : ∀ x : Vec m, Vdot x = 0 → x = 0) :
    Tendsto e atTop (𝓝 0)

/-- V = ‖e‖²/2 沿轨迹的导数（逐分量导数版本）：
   d/dt (½‖e(t)‖²) = ⟨e(t), ed⟩，前提是 e 的每个分量导数存在且为 ed i -/
theorem Vdot_deriv_comp {m : ℕ} (e : ℝ → Vec m) (ed : Vec m) (t : ℝ)
    (hcomp : ∀ i : Fin m, HasDerivAt (fun s : ℝ => (e s) i) (ed i) t) :
    HasDerivAt (fun s : ℝ => (1 / 2) * eNorm (e s) ^ 2) (inner ℝ (e t) ed) t := by
  have hmul : ∀ i : Fin m, HasDerivAt (fun s : ℝ => (e s) i * (e s) i) (2 * (e t) i * ed i) t := by
    intro i
    have hm := (hcomp i).mul (hcomp i)
    have hval : ed i * (e t) i + (e t) i * ed i = 2 * (e t) i * ed i := by ring
    convert hm using 1 <;> try rfl
    exact hval.symm
  have hsum : HasDerivAt (fun s : ℝ => ∑ i : Fin m, (e s) i * (e s) i)
      (∑ i : Fin m, 2 * (e t) i * ed i) t := by
    convert (HasDerivAt.sum (u := Finset.univ) (fun i hi => hmul i)) using 1 <;> try rfl
    · funext s
      rw [Finset.sum_apply]
  have hhalf := hsum.const_mul (1 / 2)
  have hsq : ∀ s : ℝ, eNorm (e s) ^ 2 = ∑ i : Fin m, (e s) i * (e s) i := by
    intro s
    rw [eNorm_sq_eq_inner, inner_vec_eq_sum]
  have hval : (1 / 2) * ∑ i : Fin m, 2 * (e t) i * ed i = inner ℝ (e t) ed := by
    rw [inner_vec_eq_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  convert hhalf using 1 <;> try rfl
  · funext s
    rw [hsq]
  · exact hval.symm

/-- HasFDerivAt 的分量导数：HasFDerivAt w (toSpanSingleton ed) t ⟹ 每分量 (w s) j 的导数为 ed j -/
lemma coord_deriv_of_span {m : ℕ} (w : ℝ → Vec m) (ed : Vec m) (t : ℝ)
    (hflow : HasFDerivAt w (ContinuousLinearMap.toSpanSingleton ℝ ed) t) :
    ∀ j : Fin m, HasDerivAt (fun s : ℝ => (w s) j) (ed j) t := by
  intro j
  let π : Vec m →L[ℝ] ℝ := ContinuousLinearMap.proj j
  have hgdiff : DifferentiableAt ℝ (fun v : Vec m => π v) (w t) := π.differentiableAt
  have hediff : DifferentiableAt ℝ w t := hflow.differentiableAt
  have hfc := fderiv_comp (g := fun v : Vec m => π v) (f := w) (x := t) hgdiff hediff
  have hπ : fderiv ℝ (fun v : Vec m => π v) (w t) = π := π.fderiv
  have hfe : fderiv ℝ w t = ContinuousLinearMap.toSpanSingleton ℝ ed := hflow.fderiv
  have hcoord : fderiv ℝ (fun s : ℝ => (w s) j) t = ContinuousLinearMap.toSpanSingleton ℝ (ed j) := by
    calc
      fderiv ℝ (fun s : ℝ => (w s) j) t = fderiv ℝ (fun s : ℝ => π (w s)) t := by rfl
      _ = (fderiv ℝ (fun v : Vec m => π v) (w t)).comp (fderiv ℝ w t) := hfc
      _ = π.comp (ContinuousLinearMap.toSpanSingleton ℝ ed) := by rw [hπ, hfe]
      _ = ContinuousLinearMap.toSpanSingleton ℝ (ed j) := by
        ext u
        simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply, π]
  have hdiff : DifferentiableAt ℝ (fun s : ℝ => (w s) j) t := by
    fun_prop
  have hder : deriv (fun s : ℝ => (w s) j) t = ed j := by
    rw [show deriv (fun s : ℝ => (w s) j) t = (fderiv ℝ (fun s : ℝ => (w s) j) t) 1 by
      rfl]
    rw [hcoord]
    simp [ContinuousLinearMap.toSpanSingleton_apply]
  simpa [hder] using hdiff.hasDerivAt

/-- V = ‖e‖²/2 沿轨迹的导数：d/dt (½‖e(t)‖²) = ⟨e(t), ė(t)⟩（HasFDerivAt 版本） -/
theorem Vdot_deriv {m : ℕ} (e : ℝ → Vec m) (ed : Vec m) (t : ℝ)
    (hflow : HasFDerivAt e (ContinuousLinearMap.toSpanSingleton ℝ ed) t) :
    HasDerivAt (fun s : ℝ => (1 / 2) * eNorm (e s) ^ 2) (inner ℝ (e t) ed) t := by
  exact Vdot_deriv_comp e ed t (coord_deriv_of_span e ed t hflow)

/-- Theorem 1（论文）：控制律 (19) u = P_Ω(Jᵀ(r_d−r)/γ) 下，误差 e = r − r_d 全局收敛到 0。
   前提：0 ∈ int(Ω)（eNorm 球形式，任意集无需凸性）、J 行满秩。
   组装：B1（V̇ ≤ 0）+ V̇=0⟹e=0（B2-B3）+ LaSalle axiom。 -/
theorem theorem1 {n m : ℕ} (P : Vec n → Vec n) (Ω : Set (Vec n))
    (hPdist : ∀ z y : Vec n, y ∈ Ω → eNorm (P z - z) ≤ eNorm (y - z))
    (J : Matrix (Fin m) (Fin n) ℝ) (hJ : IsUnit (J * Jᵀ))
    (γ : ℝ) (hγ : 0 < γ)
    (hIntBall : ∃ ρ₀ > 0, ∀ y : Vec n, eNorm y ≤ ρ₀ → y ∈ Ω)
    (e : ℝ → Vec m)
    (hflow : ∀ t, HasFDerivAt e (ContinuousLinearMap.toSpanSingleton ℝ
      (J *ᵥ P (vecDiv (-((Jᵀ) *ᵥ (e t))) γ))) t) :
    Tendsto e atTop (𝓝 0) := by
  rcases hIntBall with ⟨ρ₀, hρ₀, hball⟩
  have h0 : (0 : Vec n) ∈ Ω := hball 0 (by simp [eNorm]; linarith)
  let Vdot : Vec m → ℝ := fun x => inner ℝ x (J *ᵥ P (vecDiv (-((Jᵀ) *ᵥ x)) γ))
  have hneg : ∀ x : Vec m, Vdot x ≤ 0 := by
    intro x
    unfold Vdot
    exact Vdot_nonpos P Ω hPdist h0 J γ hγ x
  have hinv : ∀ x : Vec m, Vdot x = 0 → x = 0 := by
    intro x hx
    have hPz : P (vecDiv (-((Jᵀ) *ᵥ x)) γ) = 0 := by
      unfold Vdot at hx
      exact Vdot_zero_implies_Pzero P Ω hPdist h0 J γ hγ x hx
    have hJTe : (Jᵀ) *ᵥ x = 0 := proj_zero_implies_JTe_zero P Ω hPdist J γ hγ x ⟨ρ₀, hρ₀, hball⟩ hPz
    exact JTe_zero_implies_e_zero J hJ x hJTe
  have hVd : ∀ t, HasDerivAt (fun s : ℝ => (1 / 2) * eNorm (e s) ^ 2) (Vdot (e t)) t := by
    intro t
    have hd := Vdot_deriv e (J *ᵥ P (vecDiv (-((Jᵀ) *ᵥ (e t))) γ)) t (hflow t)
    simpa [Vdot] using hd
  exact lasalle_global_convergence e Vdot hVd hneg hinv

end LiZhangJin

/-- 论文 (42) 的代数核心：x = JJᵀw − ṙ_d 时，⟨x, JJᵀ·((ṙ_d − JJᵀw)/ζ)⟩ = −(1/ζ)⟨x, JJᵀ·x⟩
   （(41b) ẇ = (ṙ_d − JJᵀw)/γ，故 V̇₁ = ⟨JJᵀw − ṙ_d, JJᵀẇ⟩ = −(1/γ)⟨x, JJᵀx⟩） -/
theorem V1_dot_algebra {m : ℕ} (JJt : Matrix (Fin m) (Fin m) ℝ) (rd w : Vec m) (ζ : ℝ) :
    inner ℝ (JJt *ᵥ w - rd) (JJt *ᵥ (vecDiv (rd - JJt *ᵥ w) ζ)) =
      -(1 / ζ) * inner ℝ (JJt *ᵥ w - rd) (JJt *ᵥ (JJt *ᵥ w - rd)) := by
  let x : Vec m := JJt *ᵥ w - rd
  have hx : JJt *ᵥ w - rd = x := rfl
  have hneg : rd - JJt *ᵥ w = -x := by
    ext i
    dsimp [x]
    ring
  have hmul : ∀ y : Vec m, JJt *ᵥ (vecDiv y ζ) = vecDiv (JJt *ᵥ y) ζ := by
    intro y
    ext i
    simp [vecDiv, Matrix.mulVec]
    rw [← Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hmulneg : JJt *ᵥ (-x) = -(JJt *ᵥ x) := by
    ext i
    simp [Matrix.mulVec, Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have h1 : JJt *ᵥ (vecDiv (rd - JJt *ᵥ w) ζ) = vecDiv (JJt *ᵥ (-x)) ζ := by
    rw [hneg, hmul]
  have hinner : inner ℝ x (vecDiv (JJt *ᵥ (-x)) ζ) = -(1 / ζ) * inner ℝ x (JJt *ᵥ x) := by
    rw [inner_vec_eq_sum, inner_vec_eq_sum]
    calc
      ∑ i, x i * (vecDiv (JJt *ᵥ (-x)) ζ) i = ∑ i, x i * ((JJt *ᵥ (-x)) i / ζ) := by
        apply Finset.sum_congr rfl
        intro i hi
        rfl
      _ = (1 / ζ) * ∑ i, x i * (JJt *ᵥ (-x)) i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (1 / ζ) * inner ℝ x (JJt *ᵥ (-x)) := by rw [inner_vec_eq_sum]
      _ = -(1 / ζ) * inner ℝ x (JJt *ᵥ x) := by
        rw [hmulneg, vec_inner_neg_right]
  calc
    inner ℝ (JJt *ᵥ w - rd) (JJt *ᵥ (vecDiv (rd - JJt *ᵥ w) ζ))
        = inner ℝ x (JJt *ᵥ (vecDiv (rd - JJt *ᵥ w) ζ)) := by rw [hx]
    _ = inner ℝ x (vecDiv (JJt *ᵥ (-x)) ζ) := by rw [h1]
    _ = -(1 / ζ) * inner ℝ x (JJt *ᵥ x) := hinner
    _ = -(1 / ζ) * inner ℝ (JJt *ᵥ w - rd) (JJt *ᵥ (JJt *ᵥ w - rd)) := by rw [hx]

/-- 论文 (42)：V₁ 衰减（强单调条件 c：⟨x, JJᵀx⟩ ≥ c‖x‖²）⟹ −(1/ζ)⟨x, JJᵀx⟩ ≤ −(2c/ζ)·½‖x‖² -/
theorem V1_decay {m : ℕ} (JJt : Matrix (Fin m) (Fin m) ℝ) (x : Vec m) (ζ c : ℝ)
    (hζ : 0 < ζ) (hmono : c * eNorm x ^ 2 ≤ inner ℝ x (JJt *ᵥ x)) :
    -(1 / ζ) * inner ℝ x (JJt *ᵥ x) ≤ -(2 * c / ζ) * ((1 / 2) * eNorm x ^ 2) := by
  nlinarith [hmono, hζ]

/-- Gronwall 型指数收敛（axiom）：V = ½‖x − x*‖² 满足 V̇ = Vdot(x(t)) 且 V̇ ≤ −cV
   ⟹ x(t) → x*（t → ∞，指数衰减）。
   引用：Gronwall 不等式 / 比较引理（经典微分方程理论，见 Khalil, Nonlinear Systems 定理 3.4）。 -/
axiom exp_convergence {m : ℕ} (x : ℝ → Vec m) (xstar : Vec m) (Vdot : Vec m → ℝ) (c : ℝ)
    (hc : 0 < c)
    (hVdot : ∀ t, HasDerivAt (fun s : ℝ => (1 / 2) * eNorm (x s - xstar) ^ 2) (Vdot (x t)) t)
    (hdec : ∀ t, Vdot (x t) ≤ -c * ((1 / 2) * eNorm (x t - xstar) ^ 2)) :
    Tendsto x atTop (𝓝 xstar)

/-- 论文 (48)（平移版投影不等式）：y ∈ Ω 时 ‖P z − y‖ₑ² ≤ 2⟨z − y, P z − y⟩
   （从 ‖Pz − z‖ ≤ ‖y − z‖ 配平方；y = 0 特例即 (25)） -/
theorem proj_sq_ineq_at {n : ℕ} (P : Vec n → Vec n) (Ω : Set (Vec n))
    (hPdist : ∀ z y : Vec n, y ∈ Ω → eNorm (P z - z) ≤ eNorm (y - z))
    (y0 : Vec n) (hy0 : y0 ∈ Ω) (z : Vec n) :
    eNorm (P z - y0) ^ 2 ≤ 2 * inner ℝ (z - y0) (P z - y0) := by
  have h1 : eNorm (P z - z) ≤ eNorm (y0 - z) := hPdist z y0 hy0
  have h1sq : eNorm (P z - z) ^ 2 ≤ eNorm (y0 - z) ^ 2 := by
    exact sq_le_sq_of_nonneg (eNorm_nonneg (P z - z)) (eNorm_nonneg (y0 - z)) h1
  have hsub : P z - z = (P z - y0) - (z - y0) := by abel
  have hsq := eNorm_sub_sq (P z - y0) (z - y0)
  have hsq' : eNorm (P z - z) ^ 2 = eNorm (P z - y0) ^ 2 - 2 * inner ℝ (P z - y0) (z - y0) + eNorm (z - y0) ^ 2 := by
    simpa [hsub] using hsq
  have hyn : eNorm (y0 - z) = eNorm (z - y0) := by
    simpa using eNorm_neg (z - y0)
  have hsq2 : eNorm (P z - y0) ^ 2 - 2 * inner ℝ (P z - y0) (z - y0) + eNorm (z - y0) ^ 2 ≤ eNorm (z - y0) ^ 2 := by
    rw [← hsq']
    rw [hyn] at h1sq
    exact h1sq
  have hcore : eNorm (P z - y0) ^ 2 ≤ 2 * inner ℝ (P z - y0) (z - y0) := by
    nlinarith
  rw [vec_inner_symm (P z - y0) (z - y0)]
  exact hcore

/-- 论文 (46) 的代数核心：z = −Jᵀe/γ + y 时，⟨e, J(P z − y)⟩ = −γ⟨z − y, P z − y⟩
   （伴随 + z 定义；论文原文此处丢失 γ 因子，不影响 V̇₂ ≤ 0 结论，按正确版验证） -/
theorem V2_dot_algebra {n m : ℕ} (P : Vec n → Vec n) (J : Matrix (Fin m) (Fin n) ℝ)
    (y : Vec n) (γ : ℝ) (hγ : 0 < γ) (e : Vec m) :
    inner ℝ e (J *ᵥ (P (vecDiv (-((Jᵀ) *ᵥ e)) γ + y) - y)) =
      -γ * inner ℝ (vecDiv (-((Jᵀ) *ᵥ e)) γ) (P (vecDiv (-((Jᵀ) *ᵥ e)) γ + y) - y) := by
  let z : Vec n := vecDiv (-((Jᵀ) *ᵥ e)) γ + y
  have hJTe : (Jᵀ) *ᵥ e = -(γ • (z - y)) := by
    ext i
    dsimp [z, vecDiv]
    field_simp [hγ.ne']
  have h1 : inner ℝ e (J *ᵥ (P z - y)) = inner ℝ ((Jᵀ) *ᵥ e) (P z - y) := by
    rw [vec_inner_symm e (J *ᵥ (P z - y))]
    rw [vec_mulVec_adjoint J (P z - y) e]
    rw [vec_inner_symm (P z - y) ((Jᵀ) *ᵥ e)]
  calc
    inner ℝ e (J *ᵥ (P (vecDiv (-((Jᵀ) *ᵥ e)) γ + y) - y))
        = inner ℝ e (J *ᵥ (P z - y)) := by rfl
    _ = inner ℝ ((Jᵀ) *ᵥ e) (P z - y) := h1
    _ = -γ * inner ℝ (z - y) (P z - y) := by
      rw [hJTe]
      rw [vec_inner_neg_left, vec_inner_smul_left]
    _ = -γ * inner ℝ (vecDiv (-((Jᵀ) *ᵥ e)) γ) (P (vecDiv (-((Jᵀ) *ᵥ e)) γ + y) - y) := by
      congr 1
      · congr 1
        dsimp [z]
        abel
      · rfl

/-- 论文 (50)：V̇₂ = 0 ⟹ P(z) = y（y ∈ Ω 时；从 (48) 与 (46) 的代数） -/
theorem V2dot_zero_implies_Pzero_at {n m : ℕ} (P : Vec n → Vec n) (Ω : Set (Vec n))
    (hPdist : ∀ z y : Vec n, y ∈ Ω → eNorm (P z - z) ≤ eNorm (y - z))
    (y : Vec n) (hy : y ∈ Ω) (J : Matrix (Fin m) (Fin n) ℝ) (γ : ℝ) (hγ : 0 < γ) (e : Vec m)
    (hV : inner ℝ e (J *ᵥ (P (vecDiv (-((Jᵀ) *ᵥ e)) γ + y) - y)) = 0) :
    P (vecDiv (-((Jᵀ) *ᵥ e)) γ + y) = y := by
  let z : Vec n := vecDiv (-((Jᵀ) *ᵥ e)) γ + y
  have hineq : eNorm (P z - y) ^ 2 ≤ 2 * inner ℝ (z - y) (P z - y) := proj_sq_ineq_at P Ω hPdist y hy z
  have hinner : inner ℝ e (J *ᵥ (P z - y)) = -γ * inner ℝ (z - y) (P z - y) := by
    simpa [z] using V2_dot_algebra P J y γ hγ e
  have hVz : inner ℝ e (J *ᵥ (P z - y)) = 0 := by simpa [z] using hV
  have hzz : inner ℝ (z - y) (P z - y) = 0 := by
    rw [hinner] at hVz
    nlinarith [hVz, hγ]
  have hsq : eNorm (P z - y) ^ 2 ≤ 0 := by nlinarith [hineq, hzz]
  have hPz0 : eNorm (P z - y) = 0 := sq_eq_zero_iff.mp (le_antisymm hsq (sq_nonneg _))
  have hPzy : P z - y = 0 := (eNorm_eq_zero_iff (P z - y)).mp hPz0
  simpa [z] using (sub_eq_zero.mp hPzy)

/-- 论文 (51) 的核心（平移版）：P(z) = y 且 y ∈ int(Ω)（eNorm 球形式，球心 y）⟹ z = y。
   论证：z ≠ y 时取 y' = y + ρ(z−y)/(2‖z−y‖) ∈ Ω（y 的球邻域内，沿 z−y 方向离开 y），
   得 ‖y'−z‖ = ‖z−y‖ − ρ/2 < ‖y−z‖，与投影最小距离 ‖y−z‖ ≤ ‖y'−z‖ 矛盾（无极限，纯代数）。 -/
theorem proj_eq_y_implies_z_eq_y {n : ℕ} (P : Vec n → Vec n) (Ω : Set (Vec n))
    (hPdist : ∀ z y : Vec n, y ∈ Ω → eNorm (P z - z) ≤ eNorm (y - z))
    (y : Vec n) (hIntBall : ∃ ρ₀ > 0, ∀ y' : Vec n, eNorm (y' - y) ≤ ρ₀ → y' ∈ Ω)
    (z : Vec n) (hPz : P z = y) :
    z = y := by
  rcases hIntBall with ⟨ρ₀, hρ₀, hball⟩
  by_contra hne
  have hw0 : 0 < eNorm (z - y) :=
    lt_of_le_of_ne (eNorm_nonneg _) (fun h => hne ((eNorm_eq_zero_iff (z - y)).mp h))
  let ρ : ℝ := min (ρ₀ / 2) (eNorm (z - y) / 2)
  have hρ0 : 0 < ρ := by
    dsimp [ρ]
    exact lt_min (div_pos hρ₀ (by norm_num)) (div_pos hw0 (by norm_num))
  have hρle : ρ ≤ ρ₀ := by
    dsimp [ρ]
    linarith [min_le_left (ρ₀ / 2) (eNorm (z - y) / 2)]
  have hρlt : ρ < 2 * eNorm (z - y) := by
    dsimp [ρ]
    linarith [min_le_right (ρ₀ / 2) (eNorm (z - y) / 2), hw0]
  let y0 : Vec n := y + (ρ / (2 * eNorm (z - y))) • (z - y)
  have hny : eNorm (y0 - y) = ρ / 2 := by
    dsimp [y0]
    rw [eNorm_smul]
    have hden : 0 < 2 * eNorm (z - y) := by positivity
    rw [abs_div, abs_of_pos hρ, abs_of_pos hden]
    field_simp [ne_of_gt hden]
  have hy0mem : y0 ∈ Ω := by
    apply hball
    linarith [hny]
  have hdist : eNorm (y - z) ≤ eNorm (y0 - z) := by
    have h1 := hPdist z y0 hy0mem
    simpa [hPz] using h1
  have hstep : y0 - z = (-1 + ρ / (2 * eNorm (z - y))) • (z - y) := by
    dsimp [y0]
    ext i
    simp
    ring
  have hnorm0 : eNorm (y0 - z) = eNorm (z - y) - ρ / 2 := by
    rw [hstep]
    rw [eNorm_smul]
    have hden : 0 < 2 * eNorm (z - y) := by positivity
    have hlt1 : ρ / (2 * eNorm (z - y)) < 1 := by
      rw [div_lt_one hden]
      exact hρlt
    have hneg : -1 + ρ / (2 * eNorm (z - y)) < 0 := by
      linarith
    have habs : |(-1 + ρ / (2 * eNorm (z - y)))| = 1 - ρ / (2 * eNorm (z - y)) := by
      rw [abs_of_neg hneg]
      ring
    rw [habs]
    field_simp [ne_of_gt hden]
    ring
  have hyn : eNorm (y - z) = eNorm (z - y) := by
    simpa using eNorm_neg (z - y)
  have hcontra : eNorm (z - y) - ρ / 2 < eNorm (z - y) := by
    linarith [hρ0]
  nlinarith [hdist, hnorm0, hyn]

/-- 论文 (51) 收口：P(z) = y、y ∈ int(Ω)、z = −Jᵀe/γ + y ⟹ Jᵀe = 0 -/
theorem proj_eq_y_implies_JTe_zero {n m : ℕ} (P : Vec n → Vec n) (Ω : Set (Vec n))
    (hPdist : ∀ z y : Vec n, y ∈ Ω → eNorm (P z - z) ≤ eNorm (y - z))
    (J : Matrix (Fin m) (Fin n) ℝ) (γ : ℝ) (hγ : 0 < γ) (e : Vec m)
    (y : Vec n) (hIntBall : ∃ ρ₀ > 0, ∀ y' : Vec n, eNorm (y' - y) ≤ ρ₀ → y' ∈ Ω)
    (hPz : P (vecDiv (-((Jᵀ) *ᵥ e)) γ + y) = y) :
    (Jᵀ) *ᵥ e = 0 := by
  have hz : vecDiv (-((Jᵀ) *ᵥ e)) γ + y = y :=
    proj_eq_y_implies_z_eq_y P Ω hPdist y hIntBall (vecDiv (-((Jᵀ) *ᵥ e)) γ + y) hPz
  have hdiv0 : vecDiv (-((Jᵀ) *ᵥ e)) γ = 0 := by
    apply_fun (fun v : Vec n => v - y) at hz
    simpa using hz
  ext i
  have hi := congrFun hdiv0 i
  dsimp [vecDiv] at hi
  have hnum : -((Jᵀ *ᵥ e) i) = 0 := by
    exact (div_eq_zero_iff hγ.ne').mp hi
  exact neg_eq_zero.mp hnum

/-- Theorem 2 Step 1（论文 (42) 组装）：(41b) ẇ = (ṙ_d − JJᵀw)/γ 下，
   x(t) = JJᵀw(t) − ṙ_d 指数收敛到 0，即 JJᵀw(t) → ṙ_d（t → ∞）。
   前提：强单调 ⟨x, JJᵀx⟩ ≥ c‖x‖ₑ²（rank JJᵀ = m，c = λ_min(JJᵀ) > 0）。 -/
theorem theorem2_step1 {m : ℕ} (JJt : Matrix (Fin m) (Fin m) ℝ) (rd : Vec m)
    (w : ℝ → Vec m) (γ c : ℝ) (hγ : 0 < γ) (hc : 0 < c)
    (hmono : ∀ x : Vec m, c * eNorm x ^ 2 ≤ inner ℝ x (JJt *ᵥ x))
    (hflow : ∀ t, HasFDerivAt w (ContinuousLinearMap.toSpanSingleton ℝ
      (vecDiv (rd - JJt *ᵥ (w t)) γ)) t) :
    Tendsto (fun t => JJt *ᵥ (w t) - rd) atTop (𝓝 0) := by
  let x : ℝ → Vec m := fun t => JJt *ᵥ (w t) - rd
  let Vdot : Vec m → ℝ := fun xv => inner ℝ xv (JJt *ᵥ (vecDiv (-xv) γ))
  have hxcomp : ∀ t, ∀ i : Fin m,
      HasDerivAt (fun s => (x s) i) ((JJt *ᵥ (vecDiv (rd - JJt *ᵥ (w t)) γ)) i) t := by
    intro t i
    have hwj : ∀ j : Fin m, HasDerivAt (fun s => (w s) j)
        ((vecDiv (rd - JJt *ᵥ (w t)) γ) j) t :=
      coord_deriv_of_span w (vecDiv (rd - JJt *ᵥ (w t)) γ) t (hflow t)
    have hterm : ∀ j : Fin m, HasDerivAt (fun s => JJt i j * (w s) j)
        (JJt i j * (vecDiv (rd - JJt *ᵥ (w t)) γ) j) t := by
      intro j
      exact (hwj j).const_mul (JJt i j)
    have hsum := HasDerivAt.sum (u := Finset.univ) (fun j hj => hterm j)
    have hminus : HasDerivAt (fun s => (∑ j, JJt i j * (w s) j) - rd i)
        (∑ j, JJt i j * (vecDiv (rd - JJt *ᵥ (w t)) γ) j) t := by
      simpa using hsum.sub (hasDerivAt_const t (rd i))
    convert hminus using 1 <;> try rfl
    · funext s
      simp [x, Matrix.mulVec]
  have hVd : ∀ t, HasDerivAt (fun s : ℝ => (1 / 2) * eNorm (x s) ^ 2) (Vdot (x t)) t := by
    intro t
    have hneg : rd - JJt *ᵥ (w t) = -(x t) := by
      dsimp [x]
      ext i
      ring
    have hed : JJt *ᵥ (vecDiv (rd - JJt *ᵥ (w t)) γ) = JJt *ᵥ (vecDiv (-(x t)) γ) := by
      rw [hneg]
    have hd := Vdot_deriv_comp x (JJt *ᵥ (vecDiv (-(x t)) γ)) t (by
      intro i
      simpa [hed] using hxcomp t i)
    simpa [Vdot] using hd
  have hVneg : ∀ t, Vdot (x t) ≤ -(2 * c / γ) * ((1 / 2) * eNorm (x t) ^ 2) := by
    intro t
    have ha := V1_dot_algebra JJt rd (w t) γ
    have hdec := V1_decay JJt (x t) γ c hγ (hmono (x t))
    have hneg : rd - JJt *ᵥ (w t) = -(x t) := by
      dsimp [x]
      ext i
      ring
    unfold Vdot
    rw [show vecDiv (-(x t)) γ = vecDiv (rd - JJt *ᵥ (w t)) γ by rw [← hneg]]
    rw [show x t = JJt *ᵥ (w t) - rd by rfl]
    rw [ha]
    rw [show JJt *ᵥ (w t) - rd = x t by rfl]
    exact hdec
  exact exp_convergence x 0 Vdot (2 * c / γ) (by positivity) hVd hVneg

/-- Theorem 2（论文）：控制律 (41)（u = P(Jᵀ(r_d−r)/γ + Jᵀw)，ẇ = (ṙ_d − JJᵀw)/γ）下，
   Step 1 证明 JJᵀw 指数收敛到 ṙ_d（theorem2_step1）；Step 2 在不变集
   w = (JJᵀ)⁻¹ṙ_d 中，误差 e = r − r_d 全局收敛到 0（LaSalle）。
   前提：J⁺ṙ_d ∈ int(Ω)（eNorm 球形式，任意集无需凸性）、J 行满秩。
   此处验证 Step 2 的代数链（(46)-(51)）：V̇₂ = −γ⟨z−y, Pz−y⟩ ≤ 0、
   V̇₂=0 ⟹ Pz=y ⟹ Jᵀe=0 ⟹ e=0，组装 LaSalle axiom。 -/
theorem theorem2 {n m : ℕ} (P : Vec n → Vec n) (Ω : Set (Vec n))
    (hPdist : ∀ z y : Vec n, y ∈ Ω → eNorm (P z - z) ≤ eNorm (y - z))
    (J : Matrix (Fin m) (Fin n) ℝ) (hJ : IsUnit (J * Jᵀ))
    (γ : ℝ) (hγ : 0 < γ) (rdot : Vec m)
    (hIntBall : ∃ ρ₀ > 0, ∀ y : Vec n, eNorm (y - rpinv J hJ *ᵥ rdot) ≤ ρ₀ → y ∈ Ω)
    (e : ℝ → Vec m)
    (hflow : ∀ t, HasFDerivAt e (ContinuousLinearMap.toSpanSingleton ℝ
      (J *ᵥ (P (vecDiv (-((Jᵀ) *ᵥ (e t))) γ + rpinv J hJ *ᵥ rdot) - rpinv J hJ *ᵥ rdot))) t) :
    Tendsto e atTop (𝓝 0) := by
  let y : Vec n := rpinv J hJ *ᵥ rdot
  rcases hIntBall with ⟨ρ₀, hρ₀, hball⟩
  have hy : y ∈ Ω := hball y (by simp)
  let Vdot : Vec m → ℝ := fun x => inner ℝ x (J *ᵥ (P (vecDiv (-((Jᵀ) *ᵥ x)) γ + y) - y))
  have hneg : ∀ x : Vec m, Vdot x ≤ 0 := by
    intro x
    have hineq : eNorm (P (vecDiv (-((Jᵀ) *ᵥ x)) γ + y) - y) ^ 2 ≤
        2 * inner ℝ (vecDiv (-((Jᵀ) *ᵥ x)) γ) (P (vecDiv (-((Jᵀ) *ᵥ x)) γ + y) - y) := by
      exact proj_sq_ineq_at P Ω hPdist y hy (vecDiv (-((Jᵀ) *ᵥ x)) γ + y)
    have hinner : inner ℝ x (J *ᵥ (P (vecDiv (-((Jᵀ) *ᵥ x)) γ + y) - y)) =
        -γ * inner ℝ (vecDiv (-((Jᵀ) *ᵥ x)) γ) (P (vecDiv (-((Jᵀ) *ᵥ x)) γ + y) - y) :=
      V2_dot_algebra P J y γ hγ x
    have hzpos : 0 ≤ inner ℝ (vecDiv (-((Jᵀ) *ᵥ x)) γ) (P (vecDiv (-((Jᵀ) *ᵥ x)) γ + y) - y) := by
      have : 0 ≤ eNorm (P (vecDiv (-((Jᵀ) *ᵥ x)) γ + y) - y) ^ 2 := sq_nonneg _
      nlinarith [hineq]
    unfold Vdot
    rw [hinner]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (le_of_lt hγ)) hzpos
  have hinv : ∀ x : Vec m, Vdot x = 0 → x = 0 := by
    intro x hx
    have hPz : P (vecDiv (-((Jᵀ) *ᵥ x)) γ + y) = y := by
      unfold Vdot at hx
      exact V2dot_zero_implies_Pzero_at P Ω hPdist y hy J γ hγ x hx
    have hJTe : (Jᵀ) *ᵥ x = 0 := proj_eq_y_implies_JTe_zero P Ω hPdist J γ hγ x y ⟨ρ₀, hρ₀, hball⟩ hPz
    exact JTe_zero_implies_e_zero J hJ x hJTe
  have hVd : ∀ t, HasDerivAt (fun s : ℝ => (1 / 2) * eNorm (e s) ^ 2) (Vdot (e t)) t := by
    intro t
    have hd := Vdot_deriv e (J *ᵥ (P (vecDiv (-((Jᵀ) *ᵥ (e t))) γ + y) - y)) t (hflow t)
    simpa [Vdot, y] using hd
  exact lasalle_global_convergence e Vdot hVd hneg hinv
