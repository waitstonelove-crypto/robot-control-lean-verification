import Mathlib
/-! # Core 基础引理库：框投影、右伪逆、零空间投影、欧氏范数 eNorm 与内积引理。 -/

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

/-- eNorm 零判据：‖x‖ₑ = 0 ⟺ x = 0（非负项平方和为零） -/
theorem eNorm_eq_zero_iff {n : ℕ} (x : Vec n) : eNorm x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hs : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg (x i))
    have hsqrt : Real.sqrt (∑ i, x i ^ 2) = 0 := by simpa [eNorm] using h
    have hsum : ∑ i, x i ^ 2 = 0 := by
      have : (Real.sqrt (∑ i, x i ^ 2)) ^ 2 = 0 := by rw [hsqrt]; norm_num
      simpa [Real.sq_sqrt hs] using this
    have hzero : ∀ i, x i = 0 := by
      intro i
      have hi : x i ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (x j))).mp hsum i (Finset.mem_univ i)
      exact sq_eq_zero_iff.mp hi
    ext i
    exact hzero i
  · intro h
    simp [h, eNorm]

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

section Nullspace

/-- 零空间投影矩阵 P₀ = I − J†J —— 文档 (6) -/
noncomputable def nullProj {m n : ℕ} (J : Matrix (Fin m) (Fin n) ℝ) (h : IsUnit (J * Jᵀ)) : Matrix (Fin n) (Fin n) ℝ :=
  1 - rpinv J h * J

/-- P₀ 幂等：P₀² = P₀ -/
theorem nullProj_idempotent {m n : ℕ} (J : Matrix (Fin m) (Fin n) ℝ) (h : IsUnit (J * Jᵀ)) :
    nullProj J h * nullProj J h = nullProj J h := by
  unfold nullProj
  let A : Matrix (Fin n) (Fin n) ℝ := rpinv J h * J
  have hA : A * A = A := by
    dsimp [A]
    rw [← Matrix.mul_assoc, rpinv_self_mul_self J h]
  calc
    (1 - A) * (1 - A) = (1 - A) - (A - A * A) := by
      simp [Matrix.sub_mul, Matrix.mul_sub]
    _ = (1 - A) - (A - A) := by rw [hA]
    _ = 1 - A := by abel

/-- P₀ 对称 -/
theorem nullProj_symmetric {m n : ℕ} (J : Matrix (Fin m) (Fin n) ℝ) (h : IsUnit (J * Jᵀ)) :
    (nullProj J h)ᵀ = nullProj J h := by
  unfold nullProj
  rw [Matrix.transpose_sub, Matrix.transpose_one, rpinv_self_conjTranspose J h]

/-- 关键：J·P₀ = 0 —— 文档 (6)「J(I − J†J) = 0」，误差动态解耦的根基 -/
theorem jacobian_mul_nullProj {m n : ℕ} (J : Matrix (Fin m) (Fin n) ℝ) (h : IsUnit (J * Jᵀ)) :
    J * nullProj J h = 0 := by
  unfold nullProj
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, rpinv_mul_eq_one J h, Matrix.one_mul]
  simp

/-- P₀φ ∈ N(J)：J(P₀φ) = 0 -/
theorem nullProj_in_nullspace {m n : ℕ} (J : Matrix (Fin m) (Fin n) ℝ) (h : IsUnit (J * Jᵀ)) (φ : Vec n) :
    J *ᵥ (nullProj J h *ᵥ φ) = 0 := by
  rw [Matrix.mulVec_mulVec, jacobian_mul_nullProj J h, Matrix.zero_mulVec]

/-- P₀ 在零空间上是恒等：Jx = 0 ⟹ P₀x = x -/
theorem nullProj_eq_self_of_mem_nullspace {m n : ℕ} (J : Matrix (Fin m) (Fin n) ℝ) (h : IsUnit (J * Jᵀ))
    (x : Vec n) (hx : J *ᵥ x = 0) :
    nullProj J h *ᵥ x = x := by
  unfold nullProj
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero, sub_zero]

/-- 通解结构：J(J†v + P₀φ) = v，∀φ —— 文档 (9) -/
theorem general_solution {m n : ℕ} (J : Matrix (Fin m) (Fin n) ℝ) (h : IsUnit (J * Jᵀ)) (v : Vec m) (φ : Vec n) :
    J *ᵥ (rpinv J h *ᵥ v + nullProj J h *ᵥ φ) = v := by
  rw [Matrix.mulVec_add]
  simp [Matrix.mulVec_mulVec, rpinv_mul_eq_one J h, jacobian_mul_nullProj J h,
    Matrix.one_mulVec, Matrix.zero_mulVec]

end Nullspace

/-- 内积对第一参数线性（逐分量展开） -/
lemma vec_inner_add_left {n : ℕ} (a b x : Vec n) :
    inner ℝ (a + b) x = inner ℝ a x + inner ℝ b x := by
  rw [inner_vec_eq_sum, inner_vec_eq_sum, inner_vec_eq_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  change (a i + b i) * x i = a i * x i + b i * x i
  ring

/-- 内积对第二参数线性（逐分量展开） -/
lemma vec_inner_add_right {n : ℕ} (x a b : Vec n) :
    inner ℝ x (a + b) = inner ℝ x a + inner ℝ x b := by
  rw [inner_vec_eq_sum, inner_vec_eq_sum, inner_vec_eq_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  change x i * (a i + b i) = x i * a i + x i * b i
  ring

/-- 实内积对称性（逐分量展开） -/
lemma vec_inner_symm {n : ℕ} (x y : Vec n) : inner ℝ x y = inner ℝ y x := by
  rw [inner_vec_eq_sum, inner_vec_eq_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_comm (x i) (y i)

/-- 标量提取：⟨a•x, y⟩ = a·⟨x, y⟩ -/
lemma vec_inner_smul_left {n : ℕ} (a : ℝ) (x y : Vec n) :
    inner ℝ (a • x) y = a * inner ℝ x y := by
  rw [inner_vec_eq_sum, inner_vec_eq_sum]
  calc
    ∑ i, (a • x) i * y i = ∑ i, a * (x i * y i) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp
      ring
    _ = a * ∑ i, x i * y i := by rw [Finset.mul_sum]

/-- 标量提取：⟨x, a•y⟩ = a·⟨x, y⟩ -/
lemma vec_inner_smul_right {n : ℕ} (a : ℝ) (x y : Vec n) :
    inner ℝ x (a • y) = a * inner ℝ x y := by
  rw [inner_vec_eq_sum, inner_vec_eq_sum]
  calc
    ∑ i, x i * (a • y) i = ∑ i, a * (x i * y i) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp
      ring
    _ = a * ∑ i, x i * y i := by rw [Finset.mul_sum]

/-- 负号提取：⟨−x, y⟩ = −⟨x, y⟩ -/
lemma vec_inner_neg_left {n : ℕ} (x y : Vec n) : inner ℝ (-x) y = - inner ℝ x y := by
  simpa using vec_inner_smul_left (-1) x y

/-- 负号提取（右）：⟨x, −y⟩ = −⟨x, y⟩ -/
lemma vec_inner_neg_right {n : ℕ} (x y : Vec n) : inner ℝ x (-y) = - inner ℝ x y := by
  rw [vec_inner_symm, vec_inner_neg_left, vec_inner_symm]

/-- 减法提取：⟨x−y, z⟩ = ⟨x,z⟩ − ⟨y,z⟩ -/
lemma vec_inner_sub_left {n : ℕ} (a b x : Vec n) :
    inner ℝ (a - b) x = inner ℝ a x - inner ℝ b x := by
  rw [sub_eq_add_neg, vec_inner_add_left, vec_inner_neg_left]
  ring

/-- 减法提取（右）：⟨x, a−b⟩ = ⟨x,a⟩ − ⟨x,b⟩ -/
lemma vec_inner_sub_right {n : ℕ} (x a b : Vec n) :
    inner ℝ x (a - b) = inner ℝ x a - inner ℝ x b := by
  rw [sub_eq_add_neg, vec_inner_add_right, vec_inner_neg_right]
  ring

/-- 伴随性：⟨Ax, y⟩ = ⟨x, Aᵀy⟩（逐分量展开硬算） -/
lemma vec_mulVec_adjoint {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x : Vec n) (y : Vec m) :
    inner ℝ (A *ᵥ x) y = inner ℝ x (Aᵀ *ᵥ y) := by
  rw [inner_vec_eq_sum, inner_vec_eq_sum]
  change ∑ i, (∑ j, A i j * x j) * y i = ∑ j, x j * (∑ i, A i j * y i)
  calc
    ∑ i, (∑ j, A i j * x j) * y i = ∑ i, ∑ j, A i j * x j * y i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_mul]
    _ = ∑ j, ∑ i, A i j * x j * y i := by rw [Finset.sum_comm]
    _ = ∑ j, x j * (∑ i, A i j * y i) := by
      apply Finset.sum_congr rfl
      intro j hj
      calc
        ∑ i, A i j * x j * y i = ∑ i, x j * (A i j * y i) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = x j * ∑ i, A i j * y i := by rw [Finset.mul_sum]

/-- (J†)ᵀ = (JJᵀ)⁻¹ J —— 由 (JJᵀ)⁻¹ 的对称性得出 -/
theorem rpinv_transpose {m n : ℕ} (J : Matrix (Fin m) (Fin n) ℝ) (h : IsUnit (J * Jᵀ)) :
    (rpinv J h)ᵀ = (J * Jᵀ)⁻¹ * J := by
  unfold rpinv
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hsym : ((J * Jᵀ)⁻¹)ᵀ = (J * Jᵀ)⁻¹ := by
    have hJ : (J * Jᵀ)ᵀ = J * Jᵀ := by
      rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [Matrix.transpose_nonsing_inv (J * Jᵀ), hJ]
  rw [hsym]

/-- (J†)ᵀ P₀ = 0 —— 正交性的矩阵形式 -/
theorem rpinv_transpose_mul_nullProj {m n : ℕ} (J : Matrix (Fin m) (Fin n) ℝ) (h : IsUnit (J * Jᵀ)) :
    (rpinv J h)ᵀ * nullProj J h = 0 := by
  rw [rpinv_transpose J h]
  rw [Matrix.mul_assoc]
  rw [jacobian_mul_nullProj J h, Matrix.mul_zero]

/-- 正交性：⟨J†v, P₀φ⟩ = 0 —— 最小范数证明的关键 -/
theorem rpinv_inner_nullProj {m n : ℕ} (J : Matrix (Fin m) (Fin n) ℝ) (h : IsUnit (J * Jᵀ)) (v : Vec m) (φ : Vec n) :
    inner ℝ (rpinv J h *ᵥ v) (nullProj J h *ᵥ φ) = 0 := by
  rw [vec_mulVec_adjoint (rpinv J h) v (nullProj J h *ᵥ φ)]
  rw [Matrix.mulVec_mulVec]
  rw [rpinv_transpose_mul_nullProj J h, Matrix.zero_mulVec]
  rw [inner_vec_eq_sum]
  simp

/-- P₀ 半正定：⟨x, P₀x⟩ = ‖P₀x‖² ≥ 0 —— 文档 (7) 中 (I − J†J) 半正定的依据 -/
theorem nullProj_inner_nonneg {m n : ℕ} (J : Matrix (Fin m) (Fin n) ℝ) (h : IsUnit (J * Jᵀ)) (x : Vec n) :
    0 ≤ inner ℝ x (nullProj J h *ᵥ x) := by
  have h1 : inner ℝ x (nullProj J h *ᵥ x) =
      inner ℝ (nullProj J h *ᵥ x) (nullProj J h *ᵥ x) := by
    rw [vec_mulVec_adjoint (nullProj J h) x (nullProj J h *ᵥ x)]
    congr 1
    rw [nullProj_symmetric J h]
    rw [Matrix.mulVec_mulVec, nullProj_idempotent J h]
  rw [h1]
  rw [← eNorm_sq_eq_inner (nullProj J h *ᵥ x)]
  exact sq_nonneg (eNorm (nullProj J h *ᵥ x))

/-- 最小范数性质（eNorm 版）：满足 Jθ̇ = v 的所有解中 ‖J†v‖ₑ 最小 —— 文档 (4)。
   注意：计划原文用 ‖·‖，但 Mathlib 对 Vec 的范数是 sup 范数，最小范数性质只在欧氏范数
   下成立，故用 eNorm（Core 已定义），这是已记录的记号修正。 -/
theorem rpinv_min_norm {m n : ℕ} (J : Matrix (Fin m) (Fin n) ℝ) (h : IsUnit (J * Jᵀ))
    (v : Vec m) (x : Vec n) (hx : J *ᵥ x = v) :
    eNorm (rpinv J h *ᵥ v) ≤ eNorm x := by
  let a : Vec n := rpinv J h *ᵥ v
  let b : Vec n := nullProj J h *ᵥ x
  have hxb : x = a + b := by
    dsimp [a, b]
    symm
    calc
      rpinv J h *ᵥ v + nullProj J h *ᵥ x = rpinv J h *ᵥ (J *ᵥ x) + nullProj J h *ᵥ x := by rw [← hx]
      _ = x := by
        unfold nullProj
        rw [Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
        abel
  have hab : inner ℝ a b = 0 := by
    dsimp [a, b]
    exact rpinv_inner_nullProj J h v x
  have hba : inner ℝ b a = 0 := by
    rw [vec_inner_symm b a, hab]
  have hsq : eNorm x ^ 2 = eNorm a ^ 2 + eNorm b ^ 2 := by
    rw [eNorm_sq_eq_inner x, eNorm_sq_eq_inner a, eNorm_sq_eq_inner b, hxb]
    rw [vec_inner_add_left a b (a + b), vec_inner_add_right a a b, vec_inner_add_right b a b]
    rw [hab, hba]
    simp
  have hsqle : eNorm a ^ 2 ≤ eNorm x ^ 2 := by
    rw [hsq]
    nlinarith [sq_nonneg (eNorm b)]
  have habs : |eNorm a| ≤ |eNorm x| := sq_le_sq.mp hsqle
  simpa [abs_of_nonneg (eNorm_nonneg a), abs_of_nonneg (eNorm_nonneg x)] using habs
