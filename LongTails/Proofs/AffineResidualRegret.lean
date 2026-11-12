import LongTails.Proofs.AffineResidualSaddle

namespace LongTails.Proofs.AffineResidualRegret

open LongTails.Algorithms.AffineResidualSaddle
open LongTails.Proofs.AffineResidualSaddle
open scoped RealInnerProductSpace

section Kernel

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def linearValue (c : E) (d : ι → ℝ) (u : State ι E) : ℝ :=
  ⟪c, u.point⟫ + ∑ i, d i * u.probability i

lemma pairing_linearValue (c : E) (d : ι → ℝ) (u v : State ι E) :
    pairing c d u v = linearValue c d u - linearValue c d v := by
  simp only [pairing, linearValue, inner_sub_right, mul_sub, Finset.sum_sub_distrib]
  ring

noncomputable def kernel (μ τ A : ℝ) (c : E) (d : ι → ℝ) (u : State ι E) : ℝ :=
  A * regularizer (0 : E) μ τ u - (⟪c, u.point⟫ + ∑ i, d i * u.probability i)

def kernelDomain (C : Set E) : Set (State ι E) :=
  {u | u.point ∈ C ∧ (∀ i, 0 ≤ u.probability i) ∧ ∑ i, u.probability i = 1}

lemma kernel_shift (μ τ A w : ℝ) (c g : E) (d b : ι → ℝ) (u : State ι E) :
    kernel μ τ A (c - w • g) (fun i => d i - w * b i) u =
      kernel μ τ A c d u + w * linearValue g b u := by
  simp only [kernel, linearValue, inner_sub_left, real_inner_smul_left,
    sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

lemma kernel_difference (μ τ A : ℝ) (c : E) (d : ι → ℝ) (u v : State ι E) :
    kernel μ τ A c d u - kernel μ τ A c d v = A * potential μ τ u v +
      pairing ((A * μ) • v.point - c)
        (fun i => A * τ * Real.log (v.probability i) - d i) u v := by
  have hr := regularizer_identity (0 : E) μ τ u v
  unfold kernel pairing
  simp only [pairing, sub_zero, inner_sub_left, inner_sub_right, real_inner_smul_left,
    sub_mul, mul_sub, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum] at hr ⊢
  nlinarith [congrArg (fun z : ℝ => A * z) hr]

lemma potential_kernel (μ τ a : ℝ) (u v : State ι E) :
    a * potential μ τ u v =
      kernel μ τ a ((a * μ) • v.point)
        (fun i => a * τ * Real.log (v.probability i)) u + a * μ / 2 * ‖v.point‖ ^ 2 := by
  have hr := regularizer_identity (0 : E) μ τ u v
  simp only [pairing, regularizer, sub_zero, inner_sub_right, real_inner_smul_left,
    real_inner_self_eq_norm_sq, mul_sub, Finset.sum_sub_distrib,
    mul_assoc, ← Finset.mul_sum] at hr
  simp only [kernel, regularizer, sub_zero, real_inner_smul_left,
    mul_assoc, ← Finset.mul_sum]
  have he : (∑ i, Real.log (v.probability i) * v.probability i) =
      ∑ i, v.probability i * Real.log (v.probability i) :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [he] at hr
  nlinarith [congrArg (fun z : ℝ => a * z) hr]

lemma kernel_add (μ τ A B : ℝ) (c e : E) (d f : ι → ℝ) (u : State ι E) :
    kernel μ τ A c d u + kernel μ τ B e f u =
      kernel μ τ (A + B) (c + e) (fun i => d i + f i) u := by
  simp only [kernel, inner_add_left, add_mul, Finset.sum_add_distrib]
  ring

lemma kernel_add_potential (μ τ A a : ℝ) (c : E) (d : ι → ℝ) (u v : State ι E) :
    kernel μ τ A c d u + a * potential μ τ u v =
      kernel μ τ (A + a) (c + (a * μ) • v.point)
        (fun i => d i + a * τ * Real.log (v.probability i)) u +
          a * μ / 2 * ‖v.point‖ ^ 2 := by
  rw [potential_kernel, ← add_assoc, kernel_add]

lemma linearMinimizer_primal {C : Set E}
    (hC : IsCompact C) (hne : C.Nonempty) (hconv : Convex ℝ C)
    {μ A : ℝ} (hμ : 0 < μ) (hA : 0 < A) (τ : ℝ) (c : E) (d : ι → ℝ) :
    let v := linearMinimizer C μ τ A c d
    v.point ∈ C ∧ ∀ x ∈ C, 0 ≤ ⟪(A * μ) • v.point - c, x - v.point⟫ := by
  let z := (A * μ)⁻¹ • c
  let v := linearMinimizer C μ τ A c d
  have hp := OracleTemplate.SaddlePoint.project_spec hne hC hconv z
  refine ⟨hp.1, fun x hx => ?_⟩
  have hh := mul_le_mul_of_nonneg_left (hp.2 x hx) (mul_pos hA hμ).le
  rw [← real_inner_smul_left] at hh
  have he : (A * μ) • (z - v.point) = -((A * μ) • v.point - c) := by
    dsimp only [z]
    rw [smul_sub, smul_smul, mul_inv_cancel₀ (mul_pos hA hμ).ne', one_smul]
    abel
  change ⟪(A * μ) • (z - v.point), x - v.point⟫ ≤ (A * μ) * 0 at hh
  rw [he, inner_neg_left] at hh
  linarith

lemma linearMinimizer_growth [Nonempty ι] {C : Set E}
    (hC : IsCompact C) (hne : C.Nonempty) (hconv : Convex ℝ C)
    {μ τ A : ℝ} (hμ : 0 < μ) (hτ : 0 < τ) (hA : 0 < A)
    (c : E) (d : ι → ℝ) (u : State ι E) (hu : u.point ∈ C)
    (husum : ∑ i, u.probability i = 1) :
    let v := linearMinimizer C μ τ A c d
    kernel μ τ A c d v + A * potential μ τ u v ≤ kernel μ τ A c d u := by
  let v := linearMinimizer C μ τ A c d
  have hp := (linearMinimizer_primal hC hne hconv hμ hA τ c d).2 u.point hu
  obtain ⟨r, hr⟩ := gibbs_stationarity (mul_pos hA hτ).ne' d
  have hv : ∑ i, v.probability i = 1 :=
    LongTails.Proofs.AffineSoftmaxResidual.gibbsWeight_sum _ _
  dsimp only [v, linearMinimizer] at hv
  have hd : (∑ i, (A * τ * Real.log (v.probability i) - d i) *
      (u.probability i - v.probability i)) = 0 := by
    dsimp only [v, linearMinimizer]
    simp_rw [hr]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, husum, hv, sub_self, mul_zero]
  have he := kernel_difference μ τ A c d u v
  unfold pairing at he
  rw [hd] at he
  change 0 ≤ ⟪(A * μ) • v.point - c, u.point - v.point⟫ at hp
  change kernel μ τ A c d v + A * potential μ τ u v ≤ kernel μ τ A c d u
  linarith

lemma linearMinimizer_probability_pos [Nonempty ι] (C : Set E) (μ τ A : ℝ)
    (c : E) (d : ι → ℝ) (i : ι) : 0 < (linearMinimizer C μ τ A c d).probability i := by
  dsimp only [linearMinimizer]
  exact LongTails.Proofs.AffineSoftmaxResidual.gibbsWeight_pos _ _ _

lemma linearMinimizer_probability_sum [Nonempty ι] (C : Set E) (μ τ A : ℝ)
    (c : E) (d : ι → ℝ) : ∑ i, (linearMinimizer C μ τ A c d).probability i = 1 :=
  LongTails.Proofs.AffineSoftmaxResidual.gibbsWeight_sum _ _

lemma linearMinimizer_minimizes [Nonempty ι] {C : Set E}
    (hC : IsCompact C) (hne : C.Nonempty) (hconv : Convex ℝ C)
    {μ τ A : ℝ} (hμ : 0 < μ) (hτ : 0 < τ) (hA : 0 < A)
    (c : E) (d : ι → ℝ) :
    let v := linearMinimizer C μ τ A c d
    v ∈ kernelDomain C ∧ IsMinOn (kernel μ τ A c d) (kernelDomain C) v := by
  let v := linearMinimizer C μ τ A c d
  have hv := linearMinimizer_probability_pos C μ τ A c d
  have hs := linearMinimizer_probability_sum C μ τ A c d
  refine ⟨⟨(linearMinimizer_primal hC hne hconv hμ hA τ c d).1,
    fun i => (hv i).le, hs⟩, ?_⟩
  intro u hu
  have hg := linearMinimizer_growth hC hne hconv hμ hτ hA c d u hu.1 hu.2.2
  have hn := potential_nonneg hμ.le hτ.le hu.2.1 hv hu.2.2 hs
  change kernel μ τ A c d v ≤ kernel μ τ A c d u
  change kernel μ τ A c d v + A * potential μ τ u v ≤ kernel μ τ A c d u at hg
  nlinarith

lemma linearMinimizer_stability [Nonempty ι] {C : Set E}
    (hC : IsCompact C) (hne : C.Nonempty) (hconv : Convex ℝ C)
    {μ τ A w : ℝ} (hμ : 0 < μ) (hτ : 0 < τ) (hA : 0 < A) (hw : 0 ≤ w)
    (c g : E) (d b : ι → ℝ) (hcap : ∀ i, |w * b i / (A * τ)| ≤ 1) :
    let v := linearMinimizer C μ τ A c d
    let n := linearMinimizer C μ τ A (c - w • g) (fun i => d i - w * b i)
    kernel μ τ A c d v + w * linearValue g b v -
      kernel μ τ A (c - w • g) (fun i => d i - w * b i) n ≤
        w ^ 2 * ‖g‖ ^ 2 / (2 * (A * μ)) +
          w ^ 2 / (A * τ) * ∑ i, v.probability i * (b i) ^ 2 := by
  let v := linearMinimizer C μ τ A c d
  let n := linearMinimizer C μ τ A (c - w • g) (fun i => d i - w * b i)
  have hn := (linearMinimizer_minimizes hC hne hconv hμ hτ hA
    (c - w • g) (fun i => d i - w * b i)).1
  have hg := linearMinimizer_growth hC hne hconv hμ hτ hA c d n hn.1 hn.2.2
  have hp := signed_perturbation hμ hτ hA hw hn.2.1
    (linearMinimizer_probability_pos C μ τ A c d) hn.2.2
    (linearMinimizer_probability_sum C μ τ A c d) g b hcap
  have he : pairing g b v n = ⟪g, v.point - n.point⟫ +
      ∑ i, (v.probability i - n.probability i) * b i := by
    unfold pairing
    congr 1
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [← he, pairing_linearValue] at hp
  dsimp only
  rw [kernel_shift]
  change kernel μ τ A c d v + A * potential μ τ n v ≤ kernel μ τ A c d n at hg
  change kernel μ τ A c d v + w * linearValue g b v -
    (kernel μ τ A c d n + w * linearValue g b n) ≤ _
  linarith

end Kernel

noncomputable def curvature (β : ℝ) (k : ℕ) : ℝ :=
  β ^ 2 + ∑ j ∈ Finset.range (k + 1), iterationWeight β j / 2

lemma curvature_formula (β : ℝ) (k : ℕ) :
    curvature β k = β ^ 2 + ((k : ℝ) + 1) * ((k : ℝ) + 2) / 4 +
      ((k : ℝ) + 1) * β / 2 := by
  induction k with
  | zero => norm_num [curvature, iterationWeight]; ring
  | succ k ih =>
      have hr : curvature β (k + 1) = curvature β k + iterationWeight β (k + 1) / 2 := by
        simp only [curvature, Finset.sum_range_succ]
        ring
      rw [hr, ih]
      simp only [iterationWeight, Nat.cast_add, Nat.cast_one]
      ring

lemma weight_positive {β : ℝ} (hβ : 0 < β) (k : ℕ) : 0 < iterationWeight β k := by
  unfold iterationWeight
  positivity

lemma curvature_positive {β : ℝ} (hβ : 0 < β) (k : ℕ) : 0 < curvature β k := by
  rw [curvature_formula]
  positivity

lemma weight_square_bound (β : ℝ) (k : ℕ) :
    (iterationWeight β k) ^ 2 ≤ 4 * curvature β k := by
  rw [curvature_formula]
  unfold iterationWeight
  nlinarith [sq_nonneg β, Nat.cast_nonneg (α := ℝ) k]

lemma weight_ratio_bound {β : ℝ} (hβ : 0 < β) (k : ℕ) :
    iterationWeight β k / curvature β k ≤ 4 / β := by
  apply (div_le_div_iff₀ (curvature_positive hβ k) hβ).mpr
  have hw := weight_square_bound β k
  have hp := weight_positive hβ k
  have hb : β ≤ iterationWeight β k := by
    unfold iterationWeight
    linarith [Nat.cast_nonneg (α := ℝ) k]
  nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hb)]

lemma weight_square_ratio_bound {β : ℝ} (hβ : 0 < β) (k : ℕ) :
    (iterationWeight β k) ^ 2 / curvature β k ≤ 4 :=
  (div_le_iff₀ (curvature_positive hβ k)).mpr (weight_square_bound β k)

lemma weight_sum_formula (β : ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, iterationWeight β k) =
      (N : ℝ) * ((N : ℝ) + 1) / 2 + (N : ℝ) * β := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [iterationWeight, Nat.cast_add, Nat.cast_one]
      ring

lemma weight_sum_lower {β : ℝ} (hβ : 0 ≤ β) (N : ℕ) :
    (N : ℝ) ^ 2 / 2 ≤ ∑ k ∈ Finset.range N, iterationWeight β k := by
  rw [weight_sum_formula]
  nlinarith [Nat.cast_nonneg (α := ℝ) N, mul_nonneg (Nat.cast_nonneg (α := ℝ) N) hβ]

def cumulative {X : Type*} (initial : X → ℝ) (regularization loss : ℕ → X → ℝ)
    (n : ℕ) (x : X) : ℝ :=
  initial x + ∑ k ∈ Finset.range n, (regularization k x + loss k x)

lemma cumulative_zero {X : Type*} (initial : X → ℝ) (regularization loss : ℕ → X → ℝ) (x : X) :
    cumulative initial regularization loss 0 x = initial x := by simp [cumulative]

lemma cumulative_succ {X : Type*} (initial : X → ℝ) (regularization loss : ℕ → X → ℝ)
    (n : ℕ) (x : X) :
    cumulative initial regularization loss (n + 1) x =
      cumulative initial regularization loss n x + regularization n x + loss n x := by
  simp only [cumulative, Finset.sum_range_succ]
  ring

section CumulativeKernel

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma cumulative_kernel (μ τ a : ℝ) (initial : State ι E) (weight : ℕ → ℝ)
    (center : ℕ → State ι E) (g : ℕ → E) (b : ℕ → ι → ℝ) (n : ℕ) (u : State ι E) :
    cumulative (fun x => a * potential μ τ x initial)
      (fun k x => weight k * potential μ τ x (center k))
      (fun k x => linearValue (g k) (b k) x) n u =
    kernel μ τ (a + ∑ k ∈ Finset.range n, weight k)
      ((a * μ) • initial.point + ∑ k ∈ Finset.range n,
        ((weight k * μ) • (center k).point - g k))
      (fun i => a * τ * Real.log (initial.probability i) + ∑ k ∈ Finset.range n,
        (weight k * τ * Real.log ((center k).probability i) - b k i)) u +
      (a * μ / 2 * ‖initial.point‖ ^ 2 + ∑ k ∈ Finset.range n,
        weight k * μ / 2 * ‖(center k).point‖ ^ 2) := by
  induction n with
  | zero => simp only [cumulative_zero, Finset.range_zero, Finset.sum_empty, add_zero]
            exact potential_kernel μ τ a u initial
  | succ n ih =>
      rw [cumulative_succ, ih]
      simp only [Finset.sum_range_succ]
      have hp := kernel_add_potential μ τ (a + ∑ k ∈ Finset.range n, weight k)
        (weight n)
        ((a * μ) • initial.point + ∑ k ∈ Finset.range n,
          ((weight k * μ) • (center k).point - g k))
        (fun i => a * τ * Real.log (initial.probability i) + ∑ k ∈ Finset.range n,
          (weight k * τ * Real.log ((center k).probability i) - b k i)) u (center n)
      have hs := kernel_shift μ τ ((a + ∑ k ∈ Finset.range n, weight k) + weight n) 1
        (((a * μ) • initial.point + ∑ k ∈ Finset.range n,
          ((weight k * μ) • (center k).point - g k)) + (weight n * μ) • (center n).point)
        (g n)
        (fun i => (a * τ * Real.log (initial.probability i) + ∑ k ∈ Finset.range n,
          (weight k * τ * Real.log ((center k).probability i) - b k i)) +
            weight n * τ * Real.log ((center n).probability i)) (b n) u
      simp only [one_smul, one_mul] at hs
      simp only [add_assoc, add_sub_assoc] at hp hs ⊢
      linarith

noncomputable def cumulativeCurvature (a : ℝ) (weight : ℕ → ℝ) (n : ℕ) : ℝ :=
  a + ∑ k ∈ Finset.range n, weight k

noncomputable def cumulativePrimal (μ a : ℝ) (initial : State ι E) (weight : ℕ → ℝ)
    (center : ℕ → State ι E) (g : ℕ → E) (n : ℕ) : E :=
  (a * μ) • initial.point + ∑ k ∈ Finset.range n,
    ((weight k * μ) • (center k).point - g k)

noncomputable def cumulativeDual (τ a : ℝ) (initial : State ι E) (weight : ℕ → ℝ)
    (center : ℕ → State ι E) (b : ℕ → ι → ℝ) (n : ℕ) (i : ι) : ℝ :=
  a * τ * Real.log (initial.probability i) + ∑ k ∈ Finset.range n,
    (weight k * τ * Real.log ((center k).probability i) - b k i)

noncomputable def cumulativeOffset (μ a : ℝ) (initial : State ι E) (weight : ℕ → ℝ)
    (center : ℕ → State ι E) (n : ℕ) : ℝ :=
  a * μ / 2 * ‖initial.point‖ ^ 2 + ∑ k ∈ Finset.range n,
    weight k * μ / 2 * ‖(center k).point‖ ^ 2

noncomputable def cumulativeMinimizer (C : Set E) (μ τ a : ℝ) (initial : State ι E)
    (weight : ℕ → ℝ) (center : ℕ → State ι E) (g : ℕ → E) (b : ℕ → ι → ℝ)
    (n : ℕ) : State ι E :=
  linearMinimizer C μ τ (cumulativeCurvature a weight n)
    (cumulativePrimal μ a initial weight center g n)
    (cumulativeDual τ a initial weight center b n)

noncomputable def auxiliaryPredictor (C : Set E) (μ τ a : ℝ) (initial : State ι E)
    (weight : ℕ → ℝ) (center : ℕ → State ι E) (g : ℕ → E) (b : ℕ → ι → ℝ)
    (n : ℕ) : State ι E :=
  linearMinimizer C μ τ (cumulativeCurvature a weight n + weight n)
    (cumulativePrimal μ a initial weight center g n + (weight n * μ) • (center n).point)
    (fun i => cumulativeDual τ a initial weight center b n i +
      weight n * τ * Real.log ((center n).probability i))

lemma cumulativeCurvature_pos {a : ℝ} (ha : 0 < a) {weight : ℕ → ℝ}
    (hw : ∀ k, 0 ≤ weight k) (n : ℕ) : 0 < cumulativeCurvature a weight n := by
  unfold cumulativeCurvature
  exact add_pos_of_pos_of_nonneg ha (Finset.sum_nonneg fun k _ => hw k)

lemma cumulativeMinimizer_spec [Nonempty ι] {C : Set E}
    (hC : IsCompact C) (hne : C.Nonempty) (hconv : Convex ℝ C)
    {μ τ a : ℝ} (hμ : 0 < μ) (hτ : 0 < τ) (ha : 0 < a)
    (initial : State ι E) (weight : ℕ → ℝ) (hw : ∀ k, 0 ≤ weight k)
    (center : ℕ → State ι E) (g : ℕ → E) (b : ℕ → ι → ℝ) (n : ℕ) :
    let v := cumulativeMinimizer C μ τ a initial weight center g b n
    v ∈ kernelDomain C ∧ IsMinOn
      (cumulative (fun x => a * potential μ τ x initial)
        (fun k x => weight k * potential μ τ x (center k))
        (fun k x => linearValue (g k) (b k) x) n) (kernelDomain C) v := by
  have hm := linearMinimizer_minimizes hC hne hconv hμ hτ
    (cumulativeCurvature_pos ha hw n)
    (cumulativePrimal μ a initial weight center g n)
    (cumulativeDual τ a initial weight center b n)
  refine ⟨hm.1, ?_⟩
  intro u hu
  change cumulative _ _ _ n _ ≤ cumulative _ _ _ n u
  rw [cumulative_kernel, cumulative_kernel]
  have hh := hm.2 hu
  change kernel _ _ _ _ _ _ ≤ kernel _ _ _ _ _ u at hh
  exact add_le_add hh le_rfl

lemma auxiliaryPredictor_spec [Nonempty ι] {C : Set E}
    (hC : IsCompact C) (hne : C.Nonempty) (hconv : Convex ℝ C)
    {μ τ a : ℝ} (hμ : 0 < μ) (hτ : 0 < τ) (ha : 0 < a)
    (initial : State ι E) (weight : ℕ → ℝ) (hw : ∀ k, 0 ≤ weight k)
    (center : ℕ → State ι E) (g : ℕ → E) (b : ℕ → ι → ℝ) (n : ℕ) :
    let v := auxiliaryPredictor C μ τ a initial weight center g b n
    v ∈ kernelDomain C ∧ IsMinOn
      (fun u => cumulative (fun x => a * potential μ τ x initial)
        (fun k x => weight k * potential μ τ x (center k))
        (fun k x => linearValue (g k) (b k) x) n u +
          weight n * potential μ τ u (center n)) (kernelDomain C) v := by
  have hm := linearMinimizer_minimizes hC hne hconv hμ hτ
    (add_pos_of_pos_of_nonneg (cumulativeCurvature_pos ha hw n) (hw n))
    (cumulativePrimal μ a initial weight center g n + (weight n * μ) • (center n).point)
    (fun i => cumulativeDual τ a initial weight center b n i +
      weight n * τ * Real.log ((center n).probability i))
  refine ⟨hm.1, ?_⟩
  intro u hu
  change cumulative _ _ _ n _ + _ ≤ cumulative _ _ _ n u + _
  rw [cumulative_kernel, cumulative_kernel]
  have hv := kernel_add_potential μ τ (cumulativeCurvature a weight n) (weight n)
    (cumulativePrimal μ a initial weight center g n)
    (cumulativeDual τ a initial weight center b n)
    (auxiliaryPredictor C μ τ a initial weight center g b n) (center n)
  have hu' := kernel_add_potential μ τ (cumulativeCurvature a weight n) (weight n)
    (cumulativePrimal μ a initial weight center g n)
    (cumulativeDual τ a initial weight center b n) u (center n)
  have hh := hm.2 hu
  change kernel _ _ _ _ _ _ ≤ kernel _ _ _ _ _ u at hh
  unfold cumulativeDual at hv hu' hh
  simp only [cumulativeCurvature, cumulativePrimal, cumulativeDual, auxiliaryPredictor] at hv hu' hh ⊢
  linarith

lemma cumulative_before_kernel (μ τ a : ℝ) (initial : State ι E) (weight : ℕ → ℝ)
    (center : ℕ → State ι E) (g : ℕ → E) (b : ℕ → ι → ℝ) (n : ℕ) (u : State ι E) :
    cumulative (fun x => a * potential μ τ x initial)
      (fun k x => weight k * potential μ τ x (center k))
      (fun k x => linearValue (g k) (b k) x) n u + weight n * potential μ τ u (center n) =
    kernel μ τ (cumulativeCurvature a weight n + weight n)
      (cumulativePrimal μ a initial weight center g n + (weight n * μ) • (center n).point)
      (fun i => cumulativeDual τ a initial weight center b n i +
        weight n * τ * Real.log ((center n).probability i)) u +
      (cumulativeOffset μ a initial weight center n + weight n * μ / 2 * ‖(center n).point‖ ^ 2) := by
  rw [cumulative_kernel]
  have hh := kernel_add_potential μ τ (cumulativeCurvature a weight n) (weight n)
    (cumulativePrimal μ a initial weight center g n)
    (cumulativeDual τ a initial weight center b n) u (center n)
  unfold cumulativeDual at hh
  simp only [cumulativeCurvature, cumulativePrimal, cumulativeDual, cumulativeOffset] at hh ⊢
  linarith

lemma cumulativeMinimizer_succ (C : Set E) (μ τ a : ℝ) (initial : State ι E)
    (weight : ℕ → ℝ) (center : ℕ → State ι E) (g : ℕ → E) (b : ℕ → ι → ℝ) (n : ℕ) :
    cumulativeMinimizer C μ τ a initial weight center g b (n + 1) =
      linearMinimizer C μ τ (cumulativeCurvature a weight n + weight n)
        ((cumulativePrimal μ a initial weight center g n + (weight n * μ) • (center n).point) - g n)
        (fun i => (cumulativeDual τ a initial weight center b n i +
          weight n * τ * Real.log ((center n).probability i)) - b n i) := by
  unfold cumulativeMinimizer cumulativeCurvature cumulativePrimal cumulativeDual
  simp only [Finset.sum_range_succ, add_assoc, add_sub_assoc]

lemma cumulative_stability [Nonempty ι] {C : Set E}
    (hC : IsCompact C) (hne : C.Nonempty) (hconv : Convex ℝ C)
    {μ τ a : ℝ} (hμ : 0 < μ) (hτ : 0 < τ) (ha : 0 < a)
    (initial : State ι E) (weight : ℕ → ℝ) (hw : ∀ k, 0 ≤ weight k)
    (center : ℕ → State ι E) (g : ℕ → E) (b : ℕ → ι → ℝ) (n : ℕ)
    (hcap : ∀ i, |b n i / ((cumulativeCurvature a weight n + weight n) * τ)| ≤ 1) :
    let y := auxiliaryPredictor C μ τ a initial weight center g b n
    let z := cumulativeMinimizer C μ τ a initial weight center g b (n + 1)
    cumulative (fun x => a * potential μ τ x initial)
      (fun k x => weight k * potential μ τ x (center k))
      (fun k x => linearValue (g k) (b k) x) n y + weight n * potential μ τ y (center n) +
        linearValue (g n) (b n) y -
    cumulative (fun x => a * potential μ τ x initial)
      (fun k x => weight k * potential μ τ x (center k))
      (fun k x => linearValue (g k) (b k) x) (n + 1) z ≤
      ‖g n‖ ^ 2 / (2 * ((cumulativeCurvature a weight n + weight n) * μ)) +
        1 / ((cumulativeCurvature a weight n + weight n) * τ) *
          ∑ i, y.probability i * (b n i) ^ 2 := by
  let A := cumulativeCurvature a weight n + weight n
  let c := cumulativePrimal μ a initial weight center g n + (weight n * μ) • (center n).point
  let d := fun i => cumulativeDual τ a initial weight center b n i +
    weight n * τ * Real.log ((center n).probability i)
  let y := auxiliaryPredictor C μ τ a initial weight center g b n
  let z := cumulativeMinimizer C μ τ a initial weight center g b (n + 1)
  have hs := linearMinimizer_stability hC hne hconv hμ hτ
    (add_pos_of_pos_of_nonneg (cumulativeCurvature_pos ha hw n) (hw n))
    (show (0 : ℝ) ≤ 1 by norm_num) c (g n) d (b n) (by simpa using hcap)
  simp only [one_pow, one_mul, one_smul] at hs
  have hz : z = linearMinimizer C μ τ A (c - g n) (fun i => d i - b n i) :=
    cumulativeMinimizer_succ C μ τ a initial weight center g b n
  change kernel μ τ A c d y + linearValue (g n) (b n) y -
    kernel μ τ A (c - g n) (fun i => d i - b n i)
      (linearMinimizer C μ τ A (c - g n) (fun i => d i - b n i)) ≤ _ at hs
  rw [← hz] at hs
  dsimp only
  rw [cumulative_succ, cumulative_before_kernel]
  have hb := cumulative_before_kernel μ τ a initial weight center g b n z
  have hk := kernel_shift μ τ A 1 c (g n) d (b n) z
  simp only [one_smul, one_mul] at hk
  change cumulative _ _ _ n z + weight n * potential μ τ z (center n) =
    kernel μ τ A c d z + _ at hb
  change kernel μ τ A c d y + _ + linearValue (g n) (b n) y -
    (cumulative _ _ _ n z + weight n * potential μ τ z (center n) + linearValue (g n) (b n) z) ≤ _
  rw [hb]
  dsimp only [y, auxiliaryPredictor, A, c, d] at hs hk ⊢
  linarith

end CumulativeKernel

lemma stability_of_growth {X : Type*} (before loss : X → ℝ) (distance : X → X → ℝ)
    (y z : X) (A error : ℝ)
    (hgrowth : before y + A * distance z y ≤ before z)
    (hperturb : loss y - loss z - A * distance z y ≤ error) :
    before y + loss y - (before z + loss z) ≤ error := by linarith

lemma accumulated_increment (value loss error : ℕ → ℝ) (N : ℕ)
    (hstep : ∀ k < N, loss k ≤ value (k + 1) - value k + error k) :
    (∑ k ∈ Finset.range N, loss k) ≤ value N - value 0 + ∑ k ∈ Finset.range N, error k := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hp := ih (fun k hk => hstep k (Nat.lt_succ_of_lt hk))
      have hn := hstep N (Nat.lt_succ_self N)
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      linarith

lemma regret_from_minima {X : Type*} {C : Set X}
    (initial : X → ℝ) (regularization loss : ℕ → X → ℝ)
    (minimizer predictor : ℕ → X) (error : ℕ → ℝ) (N : ℕ)
    (hmin : ∀ k ≤ N, IsMinOn (cumulative initial regularization loss k) C (minimizer k))
    (hmem : ∀ k ≤ N, minimizer k ∈ C)
    (hpred : ∀ k < N, predictor k ∈ C)
    (hinitial : ∀ x ∈ C, 0 ≤ initial x)
    (hreg : ∀ k < N, ∀ x ∈ C, 0 ≤ regularization k x)
    (hstability : ∀ k < N,
      cumulative initial regularization loss k (predictor k) + regularization k (predictor k) +
        loss k (predictor k) - cumulative initial regularization loss (k + 1) (minimizer (k + 1)) ≤ error k)
    {u : X} (hu : u ∈ C) :
    (∑ k ∈ Finset.range N, (loss k (predictor k) - loss k u)) ≤
      initial u + (∑ k ∈ Finset.range N, regularization k u) + ∑ k ∈ Finset.range N, error k := by
  let value := fun k => cumulative initial regularization loss k (minimizer k)
  have hi : 0 ≤ value 0 := by
    simpa [value, cumulative_zero] using hinitial (minimizer 0) (hmem 0 (Nat.zero_le N))
  have hs : ∀ k < N, loss k (predictor k) ≤ value (k + 1) - value k + error k := by
    intro k hk
    have hm := hmin k hk.le (hpred k hk)
    change cumulative initial regularization loss k (minimizer k) ≤
      cumulative initial regularization loss k (predictor k) at hm
    have hr := hreg k hk (predictor k) (hpred k hk)
    have he := hstability k hk
    dsimp [value]
    linarith
  have hh := accumulated_increment value (fun k => loss k (predictor k)) error N hs
  have ht : value N ≤ cumulative initial regularization loss N u := hmin N le_rfl hu
  simp only [cumulative, Finset.sum_add_distrib] at ht
  rw [Finset.sum_sub_distrib]
  linarith

lemma auxiliary_regret {ι E : Type*} [Fintype ι] [Nonempty ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {C : Set E}
    (hC : IsCompact C) (hne : C.Nonempty) (hconv : Convex ℝ C)
    {μ τ a : ℝ} (hμ : 0 < μ) (hτ : 0 < τ) (ha : 0 < a)
    (initial : State ι E) (hi : ∀ i, 0 < initial.probability i)
    (hisum : ∑ i, initial.probability i = 1)
    (weight : ℕ → ℝ) (hw : ∀ k, 0 ≤ weight k)
    (center : ℕ → State ι E) (hc : ∀ k i, 0 < (center k).probability i)
    (hcsum : ∀ k, ∑ i, (center k).probability i = 1)
    (g : ℕ → E) (b : ℕ → ι → ℝ) (N : ℕ)
    (hcap : ∀ k < N, ∀ i, |b k i / ((cumulativeCurvature a weight k + weight k) * τ)| ≤ 1)
    {u : State ι E} (hu : u ∈ kernelDomain C) :
    (∑ k ∈ Finset.range N,
      pairing (g k) (b k) (auxiliaryPredictor C μ τ a initial weight center g b k) u) ≤
      a * potential μ τ u initial +
        (∑ k ∈ Finset.range N, weight k * potential μ τ u (center k)) +
        ∑ k ∈ Finset.range N,
          (‖g k‖ ^ 2 / (2 * ((cumulativeCurvature a weight k + weight k) * μ)) +
            1 / ((cumulativeCurvature a weight k + weight k) * τ) *
              ∑ i, (auxiliaryPredictor C μ τ a initial weight center g b k).probability i * (b k i) ^ 2) := by
  simp_rw [pairing_linearValue]
  apply regret_from_minima _ _ _
    (cumulativeMinimizer C μ τ a initial weight center g b)
    (auxiliaryPredictor C μ τ a initial weight center g b) _ N
  · intro k _
    exact (cumulativeMinimizer_spec hC hne hconv hμ hτ ha initial weight hw center g b k).2
  · intro k _
    exact (cumulativeMinimizer_spec hC hne hconv hμ hτ ha initial weight hw center g b k).1
  · intro k _
    exact (auxiliaryPredictor_spec hC hne hconv hμ hτ ha initial weight hw center g b k).1
  · intro x hx
    exact mul_nonneg ha.le (potential_nonneg hμ.le hτ.le hx.2.1 hi hx.2.2 hisum)
  · intro k _ x hx
    exact mul_nonneg (hw k) (potential_nonneg hμ.le hτ.le hx.2.1 (hc k) hx.2.2 (hcsum k))
  · intro k hk
    exact cumulative_stability hC hne hconv hμ hτ ha initial weight hw center g b k (hcap k hk)
  · exact hu

end LongTails.Proofs.AffineResidualRegret
