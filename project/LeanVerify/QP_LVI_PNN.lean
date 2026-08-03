import LeanVerify.Core

open Matrix Filter
open scoped Topology

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

end QPLVI
