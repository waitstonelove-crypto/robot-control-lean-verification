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

/-- V = ‖e‖²/2 沿轨迹的导数：d/dt (½‖e(t)‖²) = ⟨e(t), ė(t)⟩（分量展开 + 链式法则） -/
theorem Vdot_deriv {m : ℕ} (e : ℝ → Vec m) (ed : Vec m) (t : ℝ)
    (hflow : HasFDerivAt e (ContinuousLinearMap.toSpanSingleton ℝ ed) t) :
    HasDerivAt (fun s : ℝ => (1 / 2) * eNorm (e s) ^ 2) (inner ℝ (e t) ed) t := by
  have hcomp : ∀ i : Fin m, HasDerivAt (fun s : ℝ => (e s) i) (ed i) t := by
    intro i
    let π : Vec m →L[ℝ] ℝ := ContinuousLinearMap.proj i
    have hgdiff : DifferentiableAt ℝ (fun v : Vec m => π v) (e t) := π.differentiableAt
    have hediff : DifferentiableAt ℝ e t := hflow.differentiableAt
    have hfc := fderiv_comp (g := fun v : Vec m => π v) (f := e) (x := t) hgdiff hediff
    have hπ : fderiv ℝ (fun v : Vec m => π v) (e t) = π := π.fderiv
    have hfe : fderiv ℝ e t = ContinuousLinearMap.toSpanSingleton ℝ ed := hflow.fderiv
    have hcoord : fderiv ℝ (fun s : ℝ => (e s) i) t = ContinuousLinearMap.toSpanSingleton ℝ (ed i) := by
      calc
        fderiv ℝ (fun s : ℝ => (e s) i) t = fderiv ℝ (fun s : ℝ => π (e s)) t := by rfl
        _ = (fderiv ℝ (fun v : Vec m => π v) (e t)).comp (fderiv ℝ e t) := hfc
        _ = π.comp (ContinuousLinearMap.toSpanSingleton ℝ ed) := by rw [hπ, hfe]
        _ = ContinuousLinearMap.toSpanSingleton ℝ (ed i) := by
          ext u
          simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply, π]
    have hdiff : DifferentiableAt ℝ (fun s : ℝ => (e s) i) t := by
      fun_prop
    have hder : deriv (fun s : ℝ => (e s) i) t = ed i := by
      rw [show deriv (fun s : ℝ => (e s) i) t = (fderiv ℝ (fun s : ℝ => (e s) i) t) 1 by
        rfl]
      rw [hcoord]
      simp [ContinuousLinearMap.toSpanSingleton_apply]
    simpa [hder] using hdiff.hasDerivAt
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
