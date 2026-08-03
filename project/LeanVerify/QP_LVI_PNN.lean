import LeanVerify.Core
import Mathlib.Analysis.Matrix.Normed

open Matrix Filter
open scoped Topology Matrix.Norms.Operator NNReal

namespace QPLVI

/-- 可行域 Ω = {x | Ax ≤ b ∧ Ex = d} —— 文档 (22) -/
def feasibleSet {n m p : ℕ} (A : Matrix (Fin p) (Fin n) ℝ) (b : Vec p)
    (E : Matrix (Fin m) (Fin n) ℝ) (d : Vec m) : Set (Vec n) :=
  {x | (∀ i, (A *ᵥ x) i ≤ b i) ∧ E *ᵥ x = d}

/-- 框约束可行域 Ω = {x | l ≤ x ≤ h} —— 文档 (25) -/
def feasibleSetBox {n : ℕ} (l h : Vec n) : Set (Vec n) :=
  {x | ∀ i, l i ≤ x i ∧ x i ≤ h i}

/-- 可行域是凸集 —— 文档 (22)「超平面与半空间的交为凸」 -/
theorem feasibleSet_convex {n m p : ℕ} (A : Matrix (Fin p) (Fin n) ℝ) (b : Vec p)
    (E : Matrix (Fin m) (Fin n) ℝ) (d : Vec m) :
    Convex ℝ (feasibleSet A b E d) := by
  rintro x ⟨hxA, hxE⟩ y ⟨hyA, hyE⟩ t u ht hu htu
  constructor
  · intro i
    have h1 : (A *ᵥ x) i ≤ b i := hxA i
    have h2 : (A *ᵥ y) i ≤ b i := hyA i
    calc
      (A *ᵥ (t • x + u • y)) i = (t • (A *ᵥ x) + u • (A *ᵥ y)) i := by
        rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
      _ = t * (A *ᵥ x) i + u * (A *ᵥ y) i := rfl
      _ ≤ t * b i + u * b i := by
        exact add_le_add (mul_le_mul_of_nonneg_left h1 ht) (mul_le_mul_of_nonneg_left h2 hu)
      _ = b i := by
        rw [← add_mul, htu]
        simp
  · calc
      E *ᵥ (t • x + u • y) = t • (E *ᵥ x) + u • (E *ᵥ y) := by
        rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
      _ = t • d + u • d := by rw [hxE, hyE]
      _ = d := by
        ext i
        change t * d i + u * d i = d i
        rw [← add_mul, htu]
        simp

/-- 框约束可行域是凸集 —— 文档 (22) 对 Ω = [l,h] -/
theorem feasibleSetBox_convex {n : ℕ} (l h : Vec n) : Convex ℝ (feasibleSetBox l h) := by
  rintro x hx y hy t u ht hu htu i
  constructor
  · calc
      l i = t * l i + u * l i := by rw [← add_mul, htu]; simp
      _ ≤ t * x i + u * y i := by
        exact add_le_add (mul_le_mul_of_nonneg_left (hx i).1 ht)
          (mul_le_mul_of_nonneg_left (hy i).1 hu)
  · calc
      t * x i + u * y i ≤ t * h i + u * h i := by
        exact add_le_add (mul_le_mul_of_nonneg_left (hx i).2 ht)
          (mul_le_mul_of_nonneg_left (hy i).2 hu)
      _ = h i := by rw [← add_mul, htu]; simp

/-- 变分不等式 VI(Ω, F)：x ∈ Ω ∧ ∀ y ∈ Ω, ⟨y − x, F(x)⟩ ≥ 0 —— 文档 (23)(24) -/
def VI {n : ℕ} (F : Vec n → Vec n) (Ω : Set (Vec n)) (x : Vec n) : Prop :=
  x ∈ Ω ∧ ∀ y ∈ Ω, 0 ≤ inner ℝ (y - x) (F x)

/-- KKT 条件（等式 + 不等式约束 QP） —— 文档附录 A -/
structure KKT {n m p : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (c : Vec n)
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Vec p) (E : Matrix (Fin m) (Fin n) ℝ) (d : Vec m)
    (x : Vec n) (lam : Vec m) (μ : Vec p) : Prop where
  stationary : Q *ᵥ x + c + (Aᵀ) *ᵥ μ + (Eᵀ) *ᵥ lam = 0
  primal_ineq : ∀ i, (A *ᵥ x) i ≤ b i
  primal_eq : E *ᵥ x = d
  dual : ∀ i, 0 ≤ μ i
  slack : ∀ i, μ i * (b i - (A *ᵥ x) i) = 0

/-- 凸集上二次函数最小点的一阶最优性：xstar 是 f(x) = (1 / 2)xᵀQx + cᵀx 在凸集 Ω 上的最小点
   ⟹ ⟨x − xstar, Qxstar + c⟩ ≥ 0，∀x ∈ Ω —— 文档 (23)「从凸优化到变分不等式」。
   需要 Q 对称（标准 QP 约定：正定矩阵对称）；证明用沿 (xstar → x) 线段的一维分析 +
   右极限（方向导数为非负）。 -/
theorem qp_optimal_implies_vi {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (c : Vec n) (Ω : Set (Vec n))
    (hQsym : Qᵀ = Q) (hΩ : Convex ℝ Ω) (xstar : Vec n) (hxstar : xstar ∈ Ω)
    (hopt : ∀ x ∈ Ω, (1 / 2) * inner ℝ x (Q *ᵥ x) + inner ℝ c x ≥
      (1 / 2) * inner ℝ xstar (Q *ᵥ xstar) + inner ℝ c xstar) :
    ∀ x ∈ Ω, 0 ≤ inner ℝ (x - xstar) (Q *ᵥ xstar + c) := by
  intro x hx
  let δ : Vec n := x - xstar
  let g : ℝ → ℝ := fun t => inner ℝ δ (Q *ᵥ xstar + c) + t * ((1 / 2) * inner ℝ δ (Q *ᵥ δ))
  have hg0 : g 0 = inner ℝ δ (Q *ᵥ xstar + c) := by simp [g]
  -- 对称性引理：⟨xstar, Qδ⟩ = ⟨δ, Qxstar⟩（Q 对称）
  have hsymin : inner ℝ xstar (Q *ᵥ δ) = inner ℝ δ (Q *ᵥ xstar) := by
    calc
      inner ℝ xstar (Q *ᵥ δ) = inner ℝ (Q *ᵥ δ) xstar := vec_inner_symm xstar (Q *ᵥ δ)
      _ = inner ℝ δ (Qᵀ *ᵥ xstar) := vec_mulVec_adjoint Q δ xstar
      _ = inner ℝ δ (Q *ᵥ xstar) := by rw [hQsym]
  have hQlin : ∀ t : ℝ, Q *ᵥ (xstar + t • δ) = Q *ᵥ xstar + t • (Q *ᵥ δ) := by
    intro t
    rw [Matrix.mulVec_add, Matrix.mulVec_smul]
  have hc : inner ℝ δ (Q *ᵥ xstar + c) = inner ℝ δ (Q *ᵥ xstar) + inner ℝ c δ := by
    rw [vec_inner_add_right]
    rw [vec_inner_symm δ c]
  -- 1) 沿线段展开：f(xstar + tδ) − f(xstar) = t·g(t)
  have hfg : ∀ t : ℝ, ((1 / 2) * inner ℝ (xstar + t • δ) (Q *ᵥ (xstar + t • δ)) + inner ℝ c (xstar + t • δ)) -
      ((1 / 2) * inner ℝ xstar (Q *ᵥ xstar) + inner ℝ c xstar) = t * g t := by
    intro t
    have hmain : inner ℝ (xstar + t • δ) (Q *ᵥ (xstar + t • δ)) =
        inner ℝ xstar (Q *ᵥ xstar) + 2 * t * inner ℝ δ (Q *ᵥ xstar) + t ^ 2 * inner ℝ δ (Q *ᵥ δ) := by
      calc
        inner ℝ (xstar + t • δ) (Q *ᵥ (xstar + t • δ))
            = inner ℝ (xstar + t • δ) (Q *ᵥ xstar + t • (Q *ᵥ δ)) := by rw [hQlin t]
        _ = inner ℝ xstar (Q *ᵥ xstar) + t * inner ℝ xstar (Q *ᵥ δ) + t * inner ℝ δ (Q *ᵥ xstar) + t ^ 2 * inner ℝ δ (Q *ᵥ δ) := by
          simp only [vec_inner_add_left, vec_inner_add_right, vec_inner_smul_left, vec_inner_smul_right]
          ring
        _ = inner ℝ xstar (Q *ᵥ xstar) + 2 * t * inner ℝ δ (Q *ᵥ xstar) + t ^ 2 * inner ℝ δ (Q *ᵥ δ) := by
          rw [hsymin]
          ring
    have hcpart : inner ℝ c (xstar + t • δ) = inner ℝ c xstar + t * inner ℝ c δ := by
      simp only [vec_inner_add_right, vec_inner_smul_right]
    rw [hmain, hcpart]
    unfold g
    rw [hc]
    ring
  -- 2) t ∈ (0,1] 时 g t ≥ 0（凸性给出 xstar + tδ ∈ Ω，最优性给出 f ≥ f(xstar)）
  have hge : ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) 1 → 0 ≤ g t := by
    intro t ht
    have hmem : xstar + t • δ ∈ Ω := by
      convert hΩ hxstar hx (sub_nonneg.mpr ht.right) (le_of_lt ht.1) (by ring) using 1
      ext i
      change xstar i + t * (x i - xstar i) = (1 - t) * xstar i + t * x i
      ring
    have hf : (1 / 2) * inner ℝ (xstar + t • δ) (Q *ᵥ (xstar + t • δ)) + inner ℝ c (xstar + t • δ) ≥
        (1 / 2) * inner ℝ xstar (Q *ᵥ xstar) + inner ℝ c xstar := hopt (xstar + t • δ) hmem
    have hdiff : 0 ≤ ((1 / 2) * inner ℝ (xstar + t • δ) (Q *ᵥ (xstar + t • δ)) + inner ℝ c (xstar + t • δ)) -
        ((1 / 2) * inner ℝ xstar (Q *ᵥ xstar) + inner ℝ c xstar) := by linarith
    rw [hfg t] at hdiff
    have hdiff' : 0 ≤ g t * t := by simpa [mul_comm] using hdiff
    exact nonneg_of_mul_nonneg_left hdiff' ht.1
  -- 3) 右极限：g 连续且 (0,1] 上 g ≥ 0 ⟹ g(0) ≥ 0
  have hcont : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 (g 0)) := by
    have hcontg : Continuous g := by
      unfold g
      fun_prop
    exact hcontg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hgevent : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ g t := by
    change {t : ℝ | 0 ≤ g t} ∈ 𝓝[>] (0 : ℝ)
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨Set.Ioi (-(1 / 2)) ∩ Set.Iio (1 / 2), ?hU, ?hsub⟩
    · exact inter_mem_iff.mpr ⟨
        Ioi_mem_nhds (by norm_num : (-(1 / 2) : ℝ) < 0),
        Iio_mem_nhds (by norm_num : 0 < (1 / 2 : ℝ))⟩
    · intro x hx
      exact hge x ⟨hx.2, le_of_lt (lt_trans hx.1.2 (by norm_num : (1 / 2 : ℝ) < 1))⟩
  have hg0ge : 0 ≤ g 0 := ge_of_tendsto hcont hgevent
  simpa [δ, hg0] using hg0ge

/-- 纯等式约束情形的 KKT ⟹ VI（文档 (26) 的特例，纯代数）：
   平稳性 Qx + c = −Eᵀλ 且 Ex = Ex' = d 时，⟨x'−x, Qx+c⟩ = −⟨E(x'−x), λ⟩ = 0 ≥ 0 -/
theorem kkt_eq_only_implies_vi {n m : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (c : Vec n)
    (E : Matrix (Fin m) (Fin n) ℝ) (d : Vec m) (x x' : Vec n) (lam : Vec m)
    (hstat : Q *ᵥ x + c + (Eᵀ) *ᵥ lam = 0) (hEx : E *ᵥ x = d) (hEx' : E *ᵥ x' = d) :
    0 ≤ inner ℝ (x' - x) (Q *ᵥ x + c) := by
  have hδ : E *ᵥ (x' - x) = 0 := by
    rw [Matrix.mulVec_sub]
    rw [hEx', hEx]
    simp
  have hq : Q *ᵥ x + c = -((Eᵀ) *ᵥ lam) := by
    exact eq_neg_of_add_eq_zero_left hstat
  have hinner : inner ℝ (x' - x) (Q *ᵥ x + c) = 0 := by
    calc
      inner ℝ (x' - x) (Q *ᵥ x + c) = inner ℝ (x' - x) (-((Eᵀ) *ᵥ lam)) := by rw [hq]
      _ = -inner ℝ (x' - x) ((Eᵀ) *ᵥ lam) := by
        simpa using vec_inner_neg_right (x' - x) ((Eᵀ) *ᵥ lam)
      _ = -inner ℝ (E *ᵥ (x' - x)) lam := by
        rw [← vec_mulVec_adjoint E (x' - x) lam]
      _ = 0 := by simp [hδ]
  simp [hinner]

/-- 投影特征不等式 + 不动点 ⟹ LVI 解 —— 文档 (28) 反向（干净证明）：
   不动点 ystar = P(ystar − F(ystar)) 代入特征不等式即得 ⟨z − ystar, F(ystar)⟩ ≥ 0 -/
theorem fixed_point_implies_VI {n : ℕ} (F : Vec n → Vec n) (Ω : Set (Vec n))
    (P : Vec n → Vec n) (hPmem : ∀ y, P y ∈ Ω)
    (hPchar : ∀ a z, z ∈ Ω → inner ℝ (a - P a) (z - P a) ≤ 0)
    (ystar : Vec n) (hystar : ystar ∈ Ω) (hfp : ystar = P (ystar - F ystar)) :
    VI F Ω ystar := by
  constructor
  · exact hystar
  · intro z hz
    have h := hPchar (ystar - F ystar) z hz
    rw [← hfp] at h
    have h1 : inner ℝ (-F ystar) (z - ystar) ≤ 0 := by
      have hsub : (ystar - F ystar) - ystar = -F ystar := by abel
      simpa [hsub] using h
    have h2 : - inner ℝ (F ystar) (z - ystar) ≤ 0 := by
      simpa only [vec_inner_neg_left] using h1
    have h3 : 0 ≤ inner ℝ (F ystar) (z - ystar) := by linarith
    rw [vec_inner_symm]
    exact h3

/-- LVI 解 ⟹ 不动点 —— 文档 (28) 正向：
   由 LVI（z := P a）与特征不等式（z := ystar）得 ‖ystar − P a‖² ≤ ⟨F(ystar), ystar − P a⟩ ≤ 0，
   故 ystar = P(ystar − F(ystar))（eNorm 零判据）。全程不用距离最优性（sup 范数下不成立）。 -/
theorem VI_implies_fixed_point {n : ℕ} (F : Vec n → Vec n) (Ω : Set (Vec n))
    (P : Vec n → Vec n) (hPmem : ∀ y, P y ∈ Ω)
    (hPchar : ∀ a z, z ∈ Ω → inner ℝ (a - P a) (z - P a) ≤ 0)
    (ystar : Vec n) (hystar : ystar ∈ Ω) (hVI : VI F Ω ystar) :
    ystar = P (ystar - F ystar) := by
  let a : Vec n := ystar - F ystar
  let d : Vec n := ystar - P a
  have h1 : inner ℝ (a - P a) (ystar - P a) ≤ 0 := hPchar a ystar hystar
  have h1' : inner ℝ d d ≤ inner ℝ (F ystar) d := by
    -- a − P a = (ystar − F ystar) − P a = d − F ystar；展开减法内积后移项
    have h1a : inner ℝ ((ystar - F ystar) - P a) d ≤ 0 := by
      simpa only [a] using h1
    have hrew : (ystar - F ystar) - P a = d - F ystar := by
      dsimp [d]
      abel
    rw [hrew] at h1a
    rw [vec_inner_sub_left] at h1a
    linarith
  have h2 : inner ℝ (F ystar) d ≤ 0 := by
    have h2a : 0 ≤ inner ℝ (P a - ystar) (F ystar) := hVI.2 (P a) (hPmem a)
    have h2b : 0 ≤ inner ℝ (F ystar) (P a - ystar) := by
      rw [vec_inner_symm]
      exact h2a
    have h2c : inner ℝ (F ystar) d = - inner ℝ (F ystar) (P a - ystar) := by
      rw [← vec_inner_neg_right (F ystar) (P a - ystar)]
      congr 1
      dsimp [d]
      abel
    rw [h2c]
    linarith
  have hsq : inner ℝ d d ≤ 0 := le_trans h1' h2
  have hnorm : eNorm d = 0 := by
    have hsq2 : eNorm d ^ 2 ≤ 0 := by
      rw [eNorm_sq_eq_inner]
      exact hsq
    have heq : eNorm d ^ 2 = 0 := le_antisymm hsq2 (sq_nonneg (eNorm d))
    exact sq_eq_zero_iff.mp heq
  have hzero : d = 0 := (eNorm_eq_zero_iff d).mp hnorm
  have hfp : ystar = P a := eq_of_sub_eq_zero (by simpa [d] using hzero)
  simpa [a] using hfp

/-- 框约束下：ystar 是 LVI 解 ⟺ ystar = boxProj l h (ystar − F(ystar)) —— 文档 (28) 对 Ω = [l,h] -/
theorem VI_iff_fixed_point_box {n : ℕ} {l h : Vec n} (F : Vec n → Vec n) (ystar : Vec n)
    (hlh : ∀ i, l i ≤ h i) (hystar : ∀ i, l i ≤ ystar i ∧ ystar i ≤ h i) :
    VI F (feasibleSetBox l h) ystar ↔ ystar = boxProj l h (ystar - F ystar) := by
  constructor
  · intro hVI
    exact VI_implies_fixed_point F (feasibleSetBox l h) (boxProj l h)
      (fun y => fun i => ⟨(boxProj_mem hlh y).1 i, (boxProj_mem hlh y).2 i⟩)
      (fun a z hz => @boxProj_char n l h a z (by simpa [feasibleSetBox] using hz))
      ystar hystar hVI
  · intro hfp
    exact fixed_point_implies_VI F (feasibleSetBox l h) (boxProj l h)
      (fun y => fun i => ⟨(boxProj_mem hlh y).1 i, (boxProj_mem hlh y).2 i⟩)
      (fun a z hz => @boxProj_char n l h a z (by simpa [feasibleSetBox] using hz))
      ystar hystar hfp

/-- 连续 RNN 平衡点条件（代数层）：γ ≠ 0 时 γ(P_Ω(y−Fy) − y) = 0 ⟺ P_Ω(y−Fy) = y
   —— 文档 (29)（ẏ = 0 的等价代数形式） -/
theorem pnn_equilibrium {n : ℕ} (P : Vec n → Vec n) (F : Vec n → Vec n) (γ : ℝ) (y : Vec n)
    (hγ : γ ≠ 0) :
    (γ • (P (y - F y) - y) = 0) ↔ P (y - F y) = y := by
  constructor
  · intro h
    have hsub : P (y - F y) - y = 0 := (smul_eq_zero.mp h).resolve_left hγ
    exact eq_of_sub_eq_zero hsub
  · intro h
    rw [h, sub_self, smul_zero]

/-- 框约束 RNN 平衡点 ⟹ LVI 解 —— 文档 (29)(28)(34) 组合 -/
theorem box_pnn_equilibrium_implies_VI {n : ℕ} {l h : Vec n} (F : Vec n → Vec n) (y : Vec n)
    (hlh : ∀ i, l i ≤ h i) (hfp : y = boxProj l h (y - F y)) :
    VI F (feasibleSetBox l h) y := by
  have hy : ∀ i, l i ≤ y i ∧ y i ≤ h i := by
    intro i
    rw [hfp]
    exact ⟨(boxProj_mem hlh (y - F y)).1 i, (boxProj_mem hlh (y - F y)).2 i⟩
  exact fixed_point_implies_VI F (feasibleSetBox l h) (boxProj l h)
    (fun y' => fun i => ⟨(boxProj_mem hlh y').1 i, (boxProj_mem hlh y').2 i⟩)
    (fun a z hz => @boxProj_char n l h a z (by simpa [feasibleSetBox] using hz))
    y hy hfp

/-- 离散 RNN 迭代：y_{k+1} = P_Ω(y_k − β(My_k + κ)) —— 文档 (31) -/
noncomputable def discIter {n : ℕ} (P : Vec n → Vec n) (M : Matrix (Fin n) (Fin n) ℝ) (κ : Vec n)
    (β : ℝ) (y : Vec n) : Vec n := P (y - β • (M *ᵥ y + κ))

/-- 线性部分压缩条件：‖I − βM‖ < 1 —— 文档 (31)「0 < β < 2/‖M‖」的算子范数形式。
   谱界推导（对称正定 M 下 β < 2/λ_max(M) ⟹ ‖I − βM‖ < 1）依赖谱理论，见 VERIFICATION.md -/
theorem linear_part_contraction {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (β : ℝ)
    (hLin : ‖1 - β • M‖ < 1) :
    ‖1 - β • M‖ < 1 := hLin

/-- 离散迭代收敛（Banach 不动点定理）：投影非扩张 + 线性部分压缩 ⟹ 迭代收敛到不动点
   —— 文档 (31)。不动点结合 fixed_point_implies_VI 即 LVI 解。 -/
theorem discIter_converges {n : ℕ} (P : Vec n → Vec n) (M : Matrix (Fin n) (Fin n) ℝ) (κ : Vec n)
    (β : ℝ) (hPnonex : ∀ a b, ‖P a - P b‖ ≤ ‖a - b‖)
    (hLin : ‖1 - β • M‖ < 1) (y0 : Vec n) :
    ∃ ystar, (∀ k : ℕ, Tendsto (fun i : ℕ => Nat.iterate (discIter P M κ β) i y0) atTop (𝓝 ystar)) ∧
      discIter P M κ β ystar = ystar := by
  let Φ : Vec n → Vec n := discIter P M κ β
  let q : ℝ := ‖1 - β • M‖
  have hq0 : 0 ≤ q := by exact norm_nonneg _
  -- 压缩性：‖Φ a − Φ b‖ ≤ q·‖a − b‖
  have hcontr : ∀ a b, ‖Φ a - Φ b‖ ≤ q * ‖a - b‖ := by
    intro a b
    have hd : (a - β • (M *ᵥ a + κ)) - (b - β • (M *ᵥ b + κ)) = (1 - β • M) *ᵥ (a - b) := by
      calc
        (a - β • (M *ᵥ a + κ)) - (b - β • (M *ᵥ b + κ))
            = (a - b) - β • (M *ᵥ a - M *ᵥ b) := by
              rw [smul_add, smul_add]
              rw [smul_sub]
              abel
        _ = (a - b) - β • (M *ᵥ (a - b)) := by rw [← Matrix.mulVec_sub]
        _ = (1 - β • M) *ᵥ (a - b) := by
              rw [Matrix.sub_mulVec, Matrix.one_mulVec]
              rw [Matrix.smul_mulVec]
    calc
      ‖Φ a - Φ b‖ = ‖P (a - β • (M *ᵥ a + κ)) - P (b - β • (M *ᵥ b + κ))‖ := rfl
      _ ≤ ‖(a - β • (M *ᵥ a + κ)) - (b - β • (M *ᵥ b + κ))‖ := hPnonex _ _
      _ = ‖(1 - β • M) *ᵥ (a - b)‖ := by rw [hd]
      _ ≤ ‖1 - β • M‖ * ‖a - b‖ := linfty_opNorm_mulVec (1 - β • M) (a - b)
      _ = q * ‖a - b‖ := rfl
  let qnn : ℝ≥0 := ⟨q, hq0⟩
  have hqnn : qnn < 1 := by
    exact_mod_cast hLin
  have hLip : LipschitzWith qnn Φ := (lipschitzWith_iff_dist_le_mul).mpr (by
    intro a b
    change ‖Φ a - Φ b‖ ≤ q * ‖a - b‖
    exact hcontr a b)
  have hf : ContractingWith qnn Φ := ⟨hqnn, hLip⟩
  rcases hf.exists_fixedPoint y0 (by simp : edist y0 (Φ y0) ≠ ⊤) with ⟨ystar, hfix, htend, _⟩
  refine ⟨ystar, ⟨fun k => ?_, ?_⟩⟩
  · simpa [Φ] using htend
  · simpa [Φ, Function.IsFixedPt] using hfix

end QPLVI
