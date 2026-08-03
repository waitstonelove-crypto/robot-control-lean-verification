import Mathlib

open Matrix
open scoped BigOperators

abbrev Vec (n : ℕ) := Fin n → ℝ
abbrev Mat (m n : ℕ) := Fin m → Fin n → ℝ

/-- Vec 的欧氏内积：⟨x, y⟩ = ∑ x_i y_i —— Mathlib (v4.32.2) 对 `Fin n → ℝ` 仅提供 sup 范数，
  未提供 Inner 实例（EuclideanSpace 是 PiLp 的别名，与 `Fin n → ℝ` 不同构为定义相等），
  此处为 Vec 补上标准欧氏内积，使文档 (30b) 中的 ⟨·,·⟩ 可直接书写。
  注意：本项目 `‖·‖`（Mathlib 默认）为 sup 范数，与欧氏内积不相容（‖x‖² = ⟨x,x⟩ 不成立）；
  凡数学上需要欧氏范数的定理一律使用 `eNorm`。 -/
instance instInnerVec {n : ℕ} : Inner ℝ (Vec n) where
  inner x y := ∑ i, x i * y i

/-- 内积按定义展开为逐分量乘积和 —— 下游定理展开内积的通用引理 -/
@[simp]
theorem inner_vec_eq_sum {n : ℕ} (x y : Vec n) : inner ℝ x y = ∑ i, x i * y i := by
  rfl

/-- 框约束投影：P_Ω(y)_i = max(l_i, min(y_i, h_i)) —— 文档 (27)，论文 (30a) 的 P_V
  即逐分量截断到 [l, h]。 -/
noncomputable def boxProj {n : ℕ} (l h : Vec n) (y : Vec n) : Vec n :=
  fun i => max (l i) (min (y i) (h i))

/-- 投影结果在框内：l_i ≤ P_Ω(y)_i ≤ h_i（当 l ≤ h） -/
theorem boxProj_mem {n : ℕ} {l h : Vec n} (hlh : ∀ i, l i ≤ h i) (y : Vec n) :
    (∀ i, l i ≤ boxProj l h y i) ∧ (∀ i, boxProj l h y i ≤ h i) := by
  constructor
  · intro i
    -- l i ≤ max (l i) (min (y i) (h i))
    exact le_max_left (l i) (min (y i) (h i))
  · intro i
    -- max (l i) (min (y i) (h i)) ≤ h i ⟺ l i ≤ h i ∧ min (y i) (h i) ≤ h i
    dsimp [boxProj]
    rw [max_le_iff]
    constructor
    · exact hlh i
    · exact min_le_right (y i) (h i)

/-- 框内点是不动点：y ∈ Ω ⟹ P_Ω(y) = y -/
theorem boxProj_fixedPoint {n : ℕ} {l h y : Vec n} (hy : ∀ i, l i ≤ y i ∧ y i ≤ h i) :
    boxProj l h y = y := by
  ext i
  dsimp [boxProj]
  -- min (y i) (h i) = y i （因 y i ≤ h i）
  rw [min_eq_left (hy i).2]
  -- max (l i) (y i) = y i （因 l i ≤ y i）
  rw [max_eq_right (hy i).1]

/-- 投影特征不等式：(a - P_Ω(a))ᵀ(z - P_Ω(a)) ≤ 0, ∀ z ∈ Ω —— 非扩张性证明的关键 -/
theorem boxProj_char {n : ℕ} {l h a z : Vec n} (hz : ∀ i, l i ≤ z i ∧ z i ≤ h i) :
    inner ℝ (a - boxProj l h a) (z - boxProj l h a) ≤ 0 := by
  -- z ∈ Ω 的分量界（拆开合取，供 linarith 使用）
  have hzlo : ∀ i, l i ≤ z i := fun i => (hz i).1
  have hzhi : ∀ i, z i ≤ h i := fun i => (hz i).2
  -- 内积（实例定义）与逐点减法均按定义展开为逐分量和
  change ∑ i, (a i - boxProj l h a i) * (z i - boxProj l h a i) ≤ 0
  apply Finset.sum_nonpos
  intro i hi
  dsimp [boxProj]
  -- 逐分量：p_i = max(l_i, min(a_i, h_i))，三分支证明 (a_i − p_i)(z_i − p_i) ≤ 0
  by_cases ha : a i < l i
  · -- p_i = l_i：a_i − l_i ≤ 0，z_i − l_i ≥ 0（因 z ∈ Ω）
    have hmin : min (a i) (h i) = a i :=
      min_eq_left (le_trans (le_of_lt ha) (le_trans (hzlo i) (hzhi i)))
    have hmax : max (l i) (min (a i) (h i)) = l i := by
      rw [hmin, max_eq_left (le_of_lt ha)]
    rw [hmax]
    have h1 : a i - l i ≤ 0 := by linarith
    have h2 : 0 ≤ z i - l i := by linarith [hzlo i]
    nlinarith
  · by_cases hb : a i ≤ h i
    · -- p_i = a_i：第一因子为 0
      have hmin : min (a i) (h i) = a i := min_eq_left hb
      have hmax : max (l i) (min (a i) (h i)) = a i := by
        rw [hmin, max_eq_right (le_of_not_gt ha)]
      rw [hmax]
      nlinarith
    · -- p_i = h_i：a_i − h_i ≥ 0，z_i − h_i ≤ 0（因 z ∈ Ω）
      have hlt : h i < a i := lt_of_not_ge hb
      have hmin : min (a i) (h i) = h i := min_eq_right (le_of_lt hlt)
      have hmax : max (l i) (min (a i) (h i)) = h i := by
        rw [hmin, max_eq_right (le_trans (hzlo i) (hzhi i))]
      rw [hmax]
      have h1 : 0 ≤ a i - h i := by linarith
      have h2 : z i - h i ≤ 0 := by linarith [hzhi i]
      nlinarith

/-- 投影非扩张性：‖P_Ω(a) - P_Ω(b)‖ ≤ ‖a - b‖ —— 文档附录 C -/
theorem boxProj_nonexpansive {n : ℕ} {l h a b : Vec n} :
    ‖boxProj l h a - boxProj l h b‖ ≤ ‖a - b‖ := by
  -- 逐坐标：|p_i − q_i| ≤ |a_i − b_i|
  have hcoord : ∀ i, |boxProj l h a i - boxProj l h b i| ≤ |a i - b i| := by
    intro i
    dsimp [boxProj]
    calc
      |max (l i) (min (a i) (h i)) - max (l i) (min (b i) (h i))|
          ≤ |min (a i) (h i) - min (b i) (h i)| := by
            simpa [max_comm] using
              abs_max_sub_max_le_abs (min (a i) (h i)) (min (b i) (h i)) (l i)
      _ ≤ |a i - b i| := by
        -- |min a h - min b h| ≤ max |a − b| |h − h| = |a − b|
        exact (abs_min_sub_min_le_max (a i) (h i) (b i) (h i)).trans (by
          rw [sub_self, abs_zero, max_eq_left (abs_nonneg (a i - b i))])
  -- 逐坐标界 + sup 范数（Mathlib 对 `Fin n → ℝ` 的范数为逐坐标 sup）
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg (a - b))]
  intro i
  calc
    ‖(boxProj l h a - boxProj l h b) i‖ ≤ ‖(a - b) i‖ := by simpa using hcoord i
    _ ≤ ‖a - b‖ := (pi_norm_le_iff_of_nonneg (norm_nonneg (a - b))).1 le_rfl i

/-- 欧氏范数：‖x‖ₑ = sqrt(∑ x_i²)。Mathlib 对 `Fin n → ℝ` 的默认范数是 sup 范数
  （‖x‖ = max |x_i|），而内积是欧氏内积，‖x‖² = ⟨x,x⟩ 在 sup 范数下不成立。
  凡数学上依赖欧氏范数的定理（最小范数 (4)、配平方 (37)、VAM 展开 (24) 等）一律使用 eNorm。 -/
noncomputable def eNorm {n : ℕ} (x : Vec n) : ℝ := Real.sqrt (∑ i, x i ^ 2)

/-- eNorm 平方恒等式：‖x‖ₑ² = ⟨x, x⟩ —— 最小范数证明的根基 -/
theorem eNorm_sq_eq_inner {n : ℕ} (x : Vec n) : eNorm x ^ 2 = inner ℝ x x := by
  unfold eNorm
  rw [Real.sq_sqrt]
  · rw [inner_vec_eq_sum]
    congr 1
    ext i
    ring
  · exact Finset.sum_nonneg (fun i _ => sq_nonneg (x i))

/-- eNorm 非负性 -/
theorem eNorm_nonneg {n : ℕ} (x : Vec n) : 0 ≤ eNorm x := by
  unfold eNorm
  exact Real.sqrt_nonneg _

/-- 右伪逆 J† = Jᵀ(JJᵀ)⁻¹ —— 文档 (4) 定义（要求 JJᵀ 可逆，即 J 行满秩）。
  注意：矩阵类型在此处拼写为 `Matrix (Fin m) (Fin n) ℝ`（与 `Mat m n` 定义相等，
  两者可互换）。Mathlib v4.32.2 的类型类实例检索（DiscrTree）按类型表达式头部常量
  匹配实例：以 `Mat` 为头的类型表达式找不到 Matrix 的 `HMul`/`Inv` 实例（会退化为
  Pi 逐点乘/逐点逆或不报错地失配），因此凡涉及矩阵乘法/求逆的语句一律使用
  `Matrix` 拼写；`Mat` 仅用于逐点运算（内积、投影等）场景。
  可逆性假设采用 `IsUnit (J * Jᵀ)`（矩阵乘法幺半群意义），与文档 (4) 的
  「JJᵀ 可逆」一致；需行列式形式时经 `Matrix.isUnit_iff_isUnit_det` 转换，
  再使用 `Matrix.mul_nonsing_inv`/`Matrix.nonsing_inv_mul`。 -/
noncomputable def rpinv {m n : ℕ} (J : Matrix (Fin m) (Fin n) ℝ)
    (_h : IsUnit (J * Jᵀ)) : Matrix (Fin n) (Fin m) ℝ :=
  Jᵀ * (J * Jᵀ)⁻¹

/-- 关键恒等式：JJ† = I_m —— 文档 (5) 第一性质。
  展开定义后重组为 (JJᵀ)(JJᵀ)⁻¹，由 `Matrix.mul_nonsing_inv` 化简为 1。 -/
theorem rpinv_mul_eq_one {m n : ℕ} (J : Matrix (Fin m) (Fin n) ℝ) (h : IsUnit (J * Jᵀ)) :
    J * rpinv J h = 1 := by
  rw [rpinv, ← Matrix.mul_assoc]
  exact Matrix.mul_nonsing_inv (J * Jᵀ) ((Matrix.isUnit_iff_isUnit_det (J * Jᵀ)).1 h)

/-- MP 条件 1：JJ†J = J -/
theorem rpinv_mul_self_mul {m n : ℕ} (J : Matrix (Fin m) (Fin n) ℝ) (h : IsUnit (J * Jᵀ)) :
    J * rpinv J h * J = J := by
  rw [rpinv_mul_eq_one J h]
  simp

/-- MP 条件 2：J†JJ† = J† -/
theorem rpinv_self_mul_self {m n : ℕ} (J : Matrix (Fin m) (Fin n) ℝ) (h : IsUnit (J * Jᵀ)) :
    rpinv J h * J * rpinv J h = rpinv J h := by
  rw [Matrix.mul_assoc]
  rw [rpinv_mul_eq_one J h]
  simp

/-- MP 条件 3：(JJ†)ᵀ = JJ† —— 由关键恒等式 JJ† = I_m 直接得出 -/
theorem rpinv_mul_conjTranspose {m n : ℕ} (J : Matrix (Fin m) (Fin n) ℝ) (h : IsUnit (J * Jᵀ)) :
    (J * rpinv J h)ᵀ = J * rpinv J h := by
  rw [rpinv_mul_eq_one J h]
  simp

/-- MP 条件 4：(J†J)ᵀ = J†J —— 核心是 (JJᵀ)⁻¹ 的对称性（因 JJᵀ 自身对称，
  且 `Matrix.transpose_nonsing_inv` 给出 (A⁻¹)ᵀ = (Aᵀ)⁻¹，无条件成立） -/
theorem rpinv_self_conjTranspose {m n : ℕ} (J : Matrix (Fin m) (Fin n) ℝ) (h : IsUnit (J * Jᵀ)) :
    (rpinv J h * J)ᵀ = rpinv J h * J := by
  have hsym : ((J * Jᵀ)⁻¹)ᵀ = (J * Jᵀ)⁻¹ := by
    have hJ : (J * Jᵀ)ᵀ = J * Jᵀ := by
      rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [Matrix.transpose_nonsing_inv (J * Jᵀ), hJ]
  rw [rpinv]
  rw [Matrix.transpose_mul]
  rw [Matrix.transpose_mul]
  rw [hsym, Matrix.transpose_transpose]
  rw [← Matrix.mul_assoc]
