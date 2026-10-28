import LongTails.Setups.DobocK
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped RealInnerProductSpace

namespace OracleTemplate.DobocK

open LongTails.Setups.DobocK

theorem oneDim_nonpos (ψ ψ' ψ'' : ℝ → ℝ) (h1 : ∀ t, HasDerivAt ψ (ψ' t) t)
    (h2 : ∀ t, HasDerivAt ψ' (ψ'' t) t) (h0 : ψ 0 = 0) (h0' : ψ' 0 = 0)
    (hneg : ∀ t ∈ Set.Icc (0 : ℝ) 1, ψ'' t ≤ 0) : ψ 1 ≤ 0 := by
  have hanti' : AntitoneOn ψ' (Set.Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · exact fun t _ => (h2 t).continuousAt.continuousWithinAt
    · exact fun t _ => (h2 t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(h2 t).deriv]
      exact hneg t (interior_subset ht)
  have hanti : AntitoneOn ψ (Set.Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · exact fun t _ => (h1 t).continuousAt.continuousWithinAt
    · exact fun t _ => (h1 t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(h1 t).deriv]
      have ht' := interior_subset ht
      have := hanti' (Set.left_mem_Icc.2 zero_le_one) ht' ht'.1
      linarith
  have := hanti (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one) zero_le_one
  linarith

section Taylor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem line_derivs (g : E → ℝ) (hg : ContDiff ℝ 2 g) (x d : E) :
    (∀ t : ℝ, HasDerivAt (fun s : ℝ => g (x + s • d)) ⟪gradient g (x + t • d), d⟫ t) ∧
    (∀ t : ℝ, HasDerivAt (fun s : ℝ => ⟪gradient g (x + s • d), d⟫)
      ⟪fderiv ℝ (gradient g) (x + t • d) d, d⟫ t) := by
  have hd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hgrad : ContDiff ℝ 1 (gradient g) := by
    have h1 : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (by norm_num)
    have : gradient g = fun y => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ g y) := rfl
    rw [this]
    exact (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp h1
  have hgd : Differentiable ℝ (gradient g) := hgrad.differentiable (by norm_num)
  have hline : ∀ t : ℝ, HasDerivAt (fun s : ℝ => x + s • d) d t := by
    intro t
    simpa using ((hasDerivAt_id t).smul_const d).const_add x
  constructor
  · intro t
    have := (hd (x + t • d)).hasGradientAt.hasFDerivAt.comp_hasDerivAt t (hline t)
    rw [InnerProductSpace.toDual_apply_apply] at this
    exact this
  · intro t
    have h := ((hgd (x + t • d)).hasFDerivAt.comp_hasDerivAt t (hline t))
    have := h.inner (𝕜 := ℝ) (hasDerivAt_const t d)
    simpa using this

theorem taylor_lower (g : E → ℝ) (hg : ContDiff ℝ 2 g) (c : ℝ)
    (hc : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪fderiv ℝ (gradient g) x v, v⟫) (x y : E) :
    g x + ⟪gradient g x, y - x⟫ + c / 2 * ‖y - x‖ ^ 2 ≤ g y := by
  obtain ⟨h1, h2⟩ := line_derivs g hg x (y - x)
  have key := oneDim_nonpos
    (fun t => g x + t * (inner ℝ (gradient g x) (y - x)) + c / 2 * t ^ 2 * ‖y - x‖ ^ 2 - g (x + t • (y - x)))
    (fun t => (inner ℝ (gradient g x) (y - x)) + c * t * ‖y - x‖ ^ 2 - (inner ℝ (gradient g (x + t • (y - x))) (y - x)))
    (fun t => c * ‖y - x‖ ^ 2 - (inner ℝ (fderiv ℝ (gradient g) (x + t • (y - x)) (y - x)) (y - x)))
    (by
      intro t
      have := ((((hasDerivAt_id t).mul_const (inner ℝ (gradient g x) (y - x))).const_add (g x)).add
        (((hasDerivAt_pow 2 t).const_mul (c / 2)).mul_const (‖y - x‖ ^ 2))).sub (h1 t)
      exact this.congr_deriv (by ring_nf))
    (by
      intro t
      have := (((((hasDerivAt_id t).const_mul c).mul_const (‖y - x‖ ^ 2)).const_add
        (inner ℝ (gradient g x) (y - x)))).sub (h2 t)
      exact this.congr_deriv (by ring_nf))
    (by simp) (by simp)
    (fun t _ => by linarith [hc (x + t • (y - x)) (y - x)])
  simp only [one_smul, add_sub_cancel, one_mul, one_pow] at key
  linarith

theorem taylor_upper (g : E → ℝ) (hg : ContDiff ℝ 2 g) (c : ℝ)
    (hc : ∀ x v, ⟪fderiv ℝ (gradient g) x v, v⟫ ≤ c * ‖v‖ ^ 2) (x y : E) :
    g y ≤ g x + ⟪gradient g x, y - x⟫ + c / 2 * ‖y - x‖ ^ 2 := by
  obtain ⟨h1, h2⟩ := line_derivs g hg x (y - x)
  have key := oneDim_nonpos
    (fun t => g (x + t • (y - x)) - (g x + t * (inner ℝ (gradient g x) (y - x)) + c / 2 * t ^ 2 * ‖y - x‖ ^ 2))
    (fun t => (inner ℝ (gradient g (x + t • (y - x))) (y - x)) - ((inner ℝ (gradient g x) (y - x)) + c * t * ‖y - x‖ ^ 2))
    (fun t => (inner ℝ (fderiv ℝ (gradient g) (x + t • (y - x)) (y - x)) (y - x)) - c * ‖y - x‖ ^ 2)
    (by
      intro t
      have := (h1 t).sub ((((hasDerivAt_id t).mul_const (inner ℝ (gradient g x) (y - x))).const_add (g x)).add
        (((hasDerivAt_pow 2 t).const_mul (c / 2)).mul_const (‖y - x‖ ^ 2)))
      exact this.congr_deriv (by ring_nf))
    (by
      intro t
      have := (h2 t).sub (((((hasDerivAt_id t).const_mul c).mul_const (‖y - x‖ ^ 2)).const_add
        (inner ℝ (gradient g x) (y - x))))
      exact this.congr_deriv (by ring_nf))
    (by simp) (by simp)
    (fun t _ => by linarith [hc (x + t • (y - x)) (y - x)])
  simp only [one_smul, add_sub_cancel, one_mul, one_pow] at key
  linarith

theorem taylor_cubic (g : E → ℝ) (hg : ContDiff ℝ 2 g) (L : ℝ)
    (hL : ∀ x y, ‖fderiv ℝ (gradient g) x - fderiv ℝ (gradient g) y‖ ≤ L * ‖x - y‖) (x y : E) :
    g y ≤ g x + ⟪gradient g x, y - x⟫ + 1 / 2 * ⟪fderiv ℝ (gradient g) x (y - x), y - x⟫ +
      L / 6 * ‖y - x‖ ^ 3 := by
  obtain ⟨h1, h2⟩ := line_derivs g hg x (y - x)
  set d := y - x
  set q := (inner ℝ (fderiv ℝ (gradient g) x d) (d))
  have key := oneDim_nonpos
    (fun t => g (x + t • d) - (g x + t * (inner ℝ (gradient g x) (d)) + 1 / 2 * t ^ 2 * q + L / 6 * t ^ 3 * ‖d‖ ^ 3))
    (fun t => (inner ℝ (gradient g (x + t • d)) (d)) - ((inner ℝ (gradient g x) (d)) + t * q + L / 2 * t ^ 2 * ‖d‖ ^ 3))
    (fun t => (inner ℝ (fderiv ℝ (gradient g) (x + t • d) d) (d)) - (q + L * t * ‖d‖ ^ 3))
    (by
      intro t
      have := (h1 t).sub (((((hasDerivAt_id t).mul_const (inner ℝ (gradient g x) (d))).const_add (g x)).add
        (((hasDerivAt_pow 2 t).const_mul (1 / 2)).mul_const q)).add
        (((hasDerivAt_pow 3 t).const_mul (L / 6)).mul_const (‖d‖ ^ 3)))
      exact this.congr_deriv (by ring_nf))
    (by
      intro t
      have := (h2 t).sub ((((hasDerivAt_id t).mul_const q).const_add (inner ℝ (gradient g x) (d))).add
        (((hasDerivAt_pow 2 t).const_mul (L / 2)).mul_const (‖d‖ ^ 3)))
      exact this.congr_deriv (by ring_nf))
    (by simp) (by simp)
    (by
      intro t ht
      have hdiff : (inner ℝ (fderiv ℝ (gradient g) (x + t • d) d) (d)) - q =
          (inner ℝ ((fderiv ℝ (gradient g) (x + t • d) - fderiv ℝ (gradient g) x) d) (d)) := by
        rw [sub_apply, inner_sub_left]
      have hb : (inner ℝ ((fderiv ℝ (gradient g) (x + t • d) - fderiv ℝ (gradient g) x) d) (d)) ≤
          L * t * ‖d‖ ^ 3 := by
        calc _ ≤ ‖(fderiv ℝ (gradient g) (x + t • d) - fderiv ℝ (gradient g) x) d‖ * ‖d‖ :=
              real_inner_le_norm _ _
          _ ≤ (‖fderiv ℝ (gradient g) (x + t • d) - fderiv ℝ (gradient g) x‖ * ‖d‖) * ‖d‖ := by
              gcongr; exact ContinuousLinearMap.le_opNorm _ _
          _ ≤ (L * ‖t • d‖ * ‖d‖) * ‖d‖ := by
              gcongr
              simpa using hL (x + t • d) x
          _ = L * t * ‖d‖ ^ 3 := by
              rw [norm_smul, Real.norm_of_nonneg ht.1]; ring
      linarith)
  simp only [one_smul, one_mul, one_pow] at key
  have : x + d = y := by simp [d]
  rw [this] at key
  linarith

end Taylor

theorem mix_apply_eq_sum (q : Public) (hnet : Network q) (v : Stacked q.n q.dim) (i : Fin q.n) :
    mix q v i = ∑ j, q.W i j • v j := by
  unfold mix
  change ∑ j ∈ insert i (q.G.neighborFinset i), q.W i j • v j = _
  apply Finset.sum_subset (Finset.subset_univ _)
  intro j _ hj
  have hij : i ≠ j := fun h => hj (h ▸ Finset.mem_insert_self _ _)
  have hadj : ¬ q.G.Adj i j := fun h =>
    hj (Finset.mem_insert_of_mem ((SimpleGraph.mem_neighborFinset _ _ _).2 h))
  rw [(hnet.2.2.2.2.2.1 i j hij).2 hadj, zero_smul]

theorem inner_mix_comm (q : Public) (hnet : Network q) (u v : Stacked q.n q.dim) :
    ⟪u, mix q v⟫ = ⟪mix q u, v⟫ := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [mix_apply_eq_sum q hnet, inner_sum, sum_inner, inner_smul_right, inner_smul_left,
    RCLike.conj_to_real]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hnet.2.1 j i, real_inner_comm]

theorem consensus_identity (q : Public) (hnet : Network q) (v : Stacked q.n q.dim) :
    ⟪v, v - mix q v⟫ = 1 / 2 * ∑ i, ∑ j, q.W i j * ‖v i - v j‖ ^ 2 := by
  have hrow := hnet.2.2.2.1
  have hcol := hnet.2.2.2.2.1
  have e1 : ∀ i j, q.W i j * ‖v i - v j‖ ^ 2 =
      q.W i j * ‖v i‖ ^ 2 + q.W i j * ‖v j‖ ^ 2 - 2 * (q.W i j * (inner ℝ (v i) (v j))) := by
    intro i j; rw [norm_sub_sq_real]; ring
  simp only [e1, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have s1 : ∑ i, ∑ j, q.W i j * ‖v i‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_mul, hrow i, one_mul]
  have s2 : ∑ i, ∑ j, q.W i j * ‖v j‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul, hcol j, one_mul]
  have s3 : (inner ℝ (v) (mix q v)) = ∑ i, ∑ j, q.W i j * (inner ℝ (v i) (v j)) := by
    rw [PiLp.inner_apply]
    simp only [mix_apply_eq_sum q hnet, inner_sum, inner_smul_right]
  have s4 : (inner ℝ (v) (v)) = ∑ i, ‖v i‖ ^ 2 := by
    rw [PiLp.inner_apply]; simp only [real_inner_self_eq_norm_sq]
  have s5 : ∑ i, ∑ j, 2 * (q.W i j * (inner ℝ (v i) (v j))) = 2 * ∑ i, ∑ j, q.W i j * (inner ℝ (v i) (v j)) := by
    simp only [Finset.mul_sum]
  rw [s1, s2, inner_sub_right, s3, s4, s5]
  ring

theorem wmin_le (q : Public) (i : Fin q.n) : wmin q ≤ q.W i i := by
  exact ciInf_le (Set.finite_range _).bddBelow i

theorem consensus_bounds (q : Public) (hnet : Network q) (v : Stacked q.n q.dim) :
    0 ≤ ⟪v, v - mix q v⟫ ∧ ⟪v, v - mix q v⟫ ≤ 2 * (1 - wmin q) * ‖v‖ ^ 2 := by
  rw [consensus_identity q hnet]
  have hnn := hnet.2.2.1
  constructor
  · have : 0 ≤ ∑ i, ∑ j, q.W i j * ‖v i - v j‖ ^ 2 :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_nonneg (hnn i j) (sq_nonneg _)
    linarith
  · set w' : Fin q.n → Fin q.n → ℝ := fun i j => q.W i j - if i = j then q.W i j else 0
    have hw' : ∀ i j, q.W i j * ‖v i - v j‖ ^ 2 = w' i j * ‖v i - v j‖ ^ 2 := by
      intro i j
      by_cases h : i = j
      · subst h; simp [w']
      · simp [w', h]
    have hw'nn : ∀ i j, 0 ≤ w' i j := by
      intro i j; by_cases h : i = j <;> simp [w', h, hnn i j]
    have hrow : ∀ i, ∑ j, w' i j = 1 - q.W i i := by
      intro i; simp [w', Finset.sum_sub_distrib, hnet.2.2.2.1 i]
    have hcol : ∀ j, ∑ i, w' i j = 1 - q.W j j := by
      intro j
      simp only [w', Finset.sum_sub_distrib, hnet.2.2.2.2.1 j]
      rw [Finset.sum_ite_eq']; simp
    have hsq : ∀ i j, ‖v i - v j‖ ^ 2 ≤ 2 * ‖v i‖ ^ 2 + 2 * ‖v j‖ ^ 2 := by
      intro i j
      have := norm_sub_le (v i) (v j)
      nlinarith [norm_nonneg (v i - v j), norm_nonneg (v i), norm_nonneg (v j), sq_nonneg (‖v i‖ - ‖v j‖)]
    have hb : ∑ i, ∑ j, q.W i j * ‖v i - v j‖ ^ 2 ≤
        ∑ i, ∑ j, (2 * (w' i j * ‖v i‖ ^ 2) + 2 * (w' i j * ‖v j‖ ^ 2)) := by
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
      rw [hw']
      nlinarith [mul_le_mul_of_nonneg_left (hsq i j) (hw'nn i j)]
    have e : ∑ i, ∑ j, (2 * (w' i j * ‖v i‖ ^ 2) + 2 * (w' i j * ‖v j‖ ^ 2)) =
        4 * ∑ i, (1 - q.W i i) * ‖v i‖ ^ 2 := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      have a1 : ∑ i, ∑ j, w' i j * ‖v i‖ ^ 2 = ∑ i, (1 - q.W i i) * ‖v i‖ ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_mul, hrow i]
      have a2 : ∑ i, ∑ j, w' i j * ‖v j‖ ^ 2 = ∑ i, (1 - q.W i i) * ‖v i‖ ^ 2 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.sum_mul, hcol j]
      rw [a1, a2]; ring
    have hc : ∑ i, (1 - q.W i i) * ‖v i‖ ^ 2 ≤ (1 - wmin q) * ‖v‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_right (by linarith [wmin_le q i]) (sq_nonneg _)
    linarith

theorem mix_add (q : Public) (u v : Stacked q.n q.dim) : mix q (u + v) = mix q u + mix q v := by
  ext i : 1
  simp [mix, smul_add, Finset.sum_add_distrib]

theorem mix_sub (q : Public) (u v : Stacked q.n q.dim) : mix q (u - v) = mix q u - mix q v := by
  ext i : 1
  simp [mix, smul_sub, Finset.sum_sub_distrib]

theorem mix_smul (q : Public) (c : ℝ) (u : Stacked q.n q.dim) : mix q (c • u) = c • mix q u := by
  ext i : 1
  simp [mix, Finset.smul_sum, smul_comm c]

theorem penaltyHessian_inner (p : Constants) (f : Fin p.n → EuclideanSpace ℝ (Fin p.dim) → ℝ)
    (x v : Stacked p.n p.dim) :
    ⟪penaltyHessian p.toPublic f x v, v⟫ =
      ∑ i, ⟪fderiv ℝ (gradient (f i)) (x i) (v i), v i⟫ + 1 / p.lam * ⟪v, v - mix p.toPublic v⟫ := by
  rw [real_inner_comm v, PiLp.inner_apply, PiLp.inner_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [penaltyHessian, PiLp.sub_apply]
  rw [inner_add_right, inner_smul_right, real_inner_comm (v i)]

theorem penaltyHessian_bounds (p : Constants) (f : Fin p.n → EuclideanSpace ℝ (Fin p.dim) → ℝ)
    (hnet : Network p.toPublic) (hlam : 0 < p.lam) (hA1 : Assumption1 p.toPublic p.m p.M f)
    (x v : Stacked p.n p.dim) :
    p.m * ‖v‖ ^ 2 ≤ ⟪penaltyHessian p.toPublic f x v, v⟫ ∧
      ⟪penaltyHessian p.toPublic f x v, v⟫ ≤ a p * ‖v‖ ^ 2 := by
  rw [penaltyHessian_inner]
  obtain ⟨hc0, hc1⟩ := consensus_bounds p.toPublic hnet v
  have hl : ∑ i, p.m * ‖v i‖ ^ 2 ≤ ∑ i, (inner ℝ (fderiv ℝ (gradient (f i)) (x i) (v i)) (v i)) :=
    Finset.sum_le_sum fun i _ => ((hA1 i).2 (x i) (v i)).1
  have hu : ∑ i, (inner ℝ (fderiv ℝ (gradient (f i)) (x i) (v i)) (v i)) ≤ ∑ i, p.M * ‖v i‖ ^ 2 :=
    Finset.sum_le_sum fun i _ => ((hA1 i).2 (x i) (v i)).2
  rw [← Finset.mul_sum, ← PiLp.norm_sq_eq_of_L2] at hl hu
  have hinv : 0 < 1 / p.lam := by positivity
  constructor
  · nlinarith [mul_nonneg hinv.le hc0]
  · have : 1 / p.lam * (inner ℝ (v) (v - mix p.toPublic v)) ≤ 1 / p.lam * (2 * (1 - wmin p.toPublic) * ‖v‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hc1 hinv.le
    have ha : a p * ‖v‖ ^ 2 = p.M * ‖v‖ ^ 2 + 1 / p.lam * (2 * (1 - wmin p.toPublic) * ‖v‖ ^ 2) := by
      unfold a; field_simp
    linarith

theorem penaltyGradient_inner (p : Constants) (f : Fin p.n → EuclideanSpace ℝ (Fin p.dim) → ℝ)
    (x d : Stacked p.n p.dim) :
    ⟪penaltyGradient p.toPublic f x, d⟫ =
      ∑ i, ⟪gradient (f i) (x i), d i⟫ + 1 / p.lam * ⟪x - mix p.toPublic x, d⟫ := by
  rw [PiLp.inner_apply, PiLp.inner_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [penaltyGradient, PiLp.sub_apply]
  rw [inner_add_left, inner_smul_left, RCLike.conj_to_real]

theorem penalty_decomp (p : Constants) (f : Fin p.n → EuclideanSpace ℝ (Fin p.dim) → ℝ)
    (hnet : Network p.toPublic) (x y : Stacked p.n p.dim) :
    penalty p.toPublic f y - penalty p.toPublic f x - ⟪penaltyGradient p.toPublic f x, y - x⟫ =
      ∑ i, (f i (y i) - f i (x i) - ⟪gradient (f i) (x i), y i - x i⟫) +
        1 / (2 * p.lam) * ⟪y - x, (y - x) - mix p.toPublic (y - x)⟫ := by
  obtain ⟨d, rfl⟩ : ∃ d, y = x + d := ⟨y - x, (add_sub_cancel x y).symm⟩
  have hd : x + d - x = d := add_sub_cancel_left x d
  rw [hd, penaltyGradient_inner]
  have hQ : (inner ℝ (x + d) (x + d - mix p.toPublic (x + d))) =
      (inner ℝ (x) (x - mix p.toPublic x)) + 2 * (inner ℝ (x - mix p.toPublic x) (d)) + (inner ℝ (d) (d - mix p.toPublic d)) := by
    have hc := inner_mix_comm p.toPublic hnet x d
    rw [mix_add]
    have e : x + d - (mix p.toPublic x + mix p.toPublic d) = (x - mix p.toPublic x) + (d - mix p.toPublic d) :=
      add_sub_add_comm x d (mix p.toPublic x) (mix p.toPublic d)
    rw [e, inner_add_left, inner_add_right, inner_add_right]
    rw [inner_sub_right x d, hc, ← inner_sub_left, real_inner_comm d (x - _)]
    ring
  unfold penalty
  rw [hQ]
  have hs : ∀ i, (x + d) i = x i + d i := fun i => rfl
  simp only [hs, add_sub_cancel_left]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  field_simp
  ring

theorem penalty_quadratic_bounds (p : Constants) (f : Fin p.n → EuclideanSpace ℝ (Fin p.dim) → ℝ)
    (hnet : Network p.toPublic) (hlam : 0 < p.lam) (hA1 : Assumption1 p.toPublic p.m p.M f)
    (x y : Stacked p.n p.dim) :
    penalty p.toPublic f x + ⟪penaltyGradient p.toPublic f x, y - x⟫ + p.m / 2 * ‖y - x‖ ^ 2 ≤
        penalty p.toPublic f y ∧
      penalty p.toPublic f y ≤
        penalty p.toPublic f x + ⟪penaltyGradient p.toPublic f x, y - x⟫ + a p / 2 * ‖y - x‖ ^ 2 := by
  have hdec := penalty_decomp p f hnet x y
  obtain ⟨hc0, hc1⟩ := consensus_bounds p.toPublic hnet (y - x)
  have hlo : ∑ i, p.m / 2 * ‖(y - x) i‖ ^ 2 ≤
      ∑ i, (f i (y i) - f i (x i) - (inner ℝ (gradient (f i) (x i)) (y i - x i))) :=
    Finset.sum_le_sum fun i _ => by
      have := taylor_lower (f i) (hA1 i).1 p.m (fun z v => ((hA1 i).2 z v).1) (x i) (y i)
      rw [PiLp.sub_apply]; linarith
  have hhi : ∑ i, (f i (y i) - f i (x i) - (inner ℝ (gradient (f i) (x i)) (y i - x i))) ≤
      ∑ i, p.M / 2 * ‖(y - x) i‖ ^ 2 :=
    Finset.sum_le_sum fun i _ => by
      have := taylor_upper (f i) (hA1 i).1 p.M (fun z v => ((hA1 i).2 z v).2) (x i) (y i)
      rw [PiLp.sub_apply]; linarith
  rw [← Finset.mul_sum, ← PiLp.norm_sq_eq_of_L2] at hlo hhi
  have hinv : 0 < 1 / (2 * p.lam) := by positivity
  constructor
  · nlinarith [mul_nonneg hinv.le hc0]
  · have h2 : 1 / (2 * p.lam) * (inner ℝ (y - x) ((y - x) - mix p.toPublic (y - x))) ≤
        1 / (2 * p.lam) * (2 * (1 - wmin p.toPublic) * ‖y - x‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hc1 hinv.le
    have ha : a p / 2 * ‖y - x‖ ^ 2 =
        p.M / 2 * ‖y - x‖ ^ 2 + 1 / (2 * p.lam) * (2 * (1 - wmin p.toPublic) * ‖y - x‖ ^ 2) := by
      unfold a; field_simp
    linarith

theorem sum_norm_cube_le {n dim : ℕ} (d : Stacked n dim) : ∑ i, ‖d i‖ ^ 3 ≤ ‖d‖ ^ 3 := by
  have hle : ∀ i, ‖d i‖ ≤ ‖d‖ := fun i => PiLp.norm_apply_le d i
  calc ∑ i, ‖d i‖ ^ 3 ≤ ∑ i, ‖d‖ * ‖d i‖ ^ 2 := Finset.sum_le_sum fun i _ => by
        rw [pow_succ']; exact mul_le_mul_of_nonneg_right (hle i) (sq_nonneg _)
    _ = ‖d‖ ^ 3 := by rw [← Finset.mul_sum, ← PiLp.norm_sq_eq_of_L2]; ring

theorem penalty_cubic_bound (p : Constants) (f : Fin p.n → EuclideanSpace ℝ (Fin p.dim) → ℝ)
    (hnet : Network p.toPublic) (hA1 : Assumption1 p.toPublic p.m p.M f)
    (hA2 : Assumption2 p.toPublic p.L f) (hL : 0 ≤ p.L) (x y : Stacked p.n p.dim) :
    penalty p.toPublic f y ≤ penalty p.toPublic f x + ⟪penaltyGradient p.toPublic f x, y - x⟫ +
      1 / 2 * ⟪penaltyHessian p.toPublic f x (y - x), y - x⟫ + p.L / 6 * ‖y - x‖ ^ 3 := by
  have hdec := penalty_decomp p f hnet x y
  have hH := penaltyHessian_inner p f x (y - x)
  have hcub : ∑ i, (f i (y i) - f i (x i) - (inner ℝ (gradient (f i) (x i)) (y i - x i))) ≤
      ∑ i, (1 / 2 * (inner ℝ (fderiv ℝ (gradient (f i)) (x i) ((y - x) i)) ((y - x) i)) +
        p.L / 6 * ‖(y - x) i‖ ^ 3) :=
    Finset.sum_le_sum fun i _ => by
      have := taylor_cubic (f i) (hA1 i).1 p.L (hA2 i) (x i) (y i)
      rw [PiLp.sub_apply]; linarith
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hcub
  have h3 := mul_le_mul_of_nonneg_left (sum_norm_cube_le (y - x)) (by positivity : 0 ≤ p.L / 6)
  have hcomm : 1 / (2 * p.lam) * (inner ℝ (y - x) ((y - x) - mix p.toPublic (y - x))) =
      1 / 2 * (1 / p.lam * (inner ℝ (y - x) ((y - x) - mix p.toPublic (y - x)))) := by ring
  linarith

theorem penalty_continuous (p : Constants) (f : Fin p.n → EuclideanSpace ℝ (Fin p.dim) → ℝ)
    (hA1 : Assumption1 p.toPublic p.m p.M f) : Continuous (penalty p.toPublic f) := by
  have hmix : Continuous (mix p.toPublic) := by
    unfold mix
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    apply continuous_finsetSum
    intro j _
    exact (continuous_const (y := p.W i j)).smul ((continuous_apply j).comp (PiLp.continuous_ofLp 2 (fun _ : Fin p.n => EuclideanSpace ℝ (Fin p.dim))))
  unfold penalty
  apply Continuous.add
  · apply continuous_finsetSum
    intro i _
    exact ((hA1 i).1.continuous).comp ((continuous_apply i).comp (PiLp.continuous_ofLp 2 (fun _ : Fin p.n => EuclideanSpace ℝ (Fin p.dim))))
  · exact continuous_const.mul (continuous_id.inner (continuous_id.sub hmix))

theorem penalty_exists_minimizer (p : Constants) (f : Fin p.n → EuclideanSpace ℝ (Fin p.dim) → ℝ)
    (hnet : Network p.toPublic) (hlam : 0 < p.lam) (hm : 0 < p.m)
    (hA1 : Assumption1 p.toPublic p.m p.M f) :
    ∃ xstar, IsMinOn (penalty p.toPublic f) Set.univ xstar := by
  set F := penalty p.toPublic f
  set g := penaltyGradient p.toPublic f 0
  have hlow : ∀ y, F 0 - ‖g‖ * ‖y‖ + p.m / 2 * ‖y‖ ^ 2 ≤ F y := by
    intro y
    have := (penalty_quadratic_bounds p f hnet hlam hA1 0 y).1
    simp only [sub_zero] at this
    have := neg_le_of_abs_le (abs_real_inner_le_norm g y)
    nlinarith
  have hphi : Filter.Tendsto (fun r : ℝ => F 0 + r * (p.m / 2 * r - ‖g‖)) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_add_const_left
    apply Filter.tendsto_id.atTop_mul_atTop₀
    apply Filter.tendsto_atTop_add_const_right
    exact Filter.tendsto_id.const_mul_atTop (by positivity)
  have hcoer : Filter.Tendsto F (Filter.cocompact _) Filter.atTop := by
    apply Filter.tendsto_atTop_mono _ (hphi.comp tendsto_norm_cocompact_atTop)
    intro y
    have := hlow y
    simp only [Function.comp]
    nlinarith
  obtain ⟨xstar, hx⟩ := (penalty_continuous p f hA1).exists_forall_le hcoer
  exact ⟨xstar, fun y _ => hx y⟩

theorem hessian_symm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (g : E → ℝ) (hg : ContDiff ℝ 2 g) (x u v : E) :
    ⟪fderiv ℝ (gradient g) x u, v⟫ = ⟪u, fderiv ℝ (gradient g) x v⟫ := by
  have hgr : gradient g = (InnerProductSpace.toDual ℝ E).symm ∘ fderiv ℝ g := rfl
  have hsym : IsSymmSndFDerivAt ℝ g x :=
    hg.contDiffAt.isSymmSndFDerivAt (by simp)
  have key : ∀ w z, (inner ℝ (fderiv ℝ (gradient g) x w) (z)) = fderiv ℝ (fderiv ℝ g) x w z := by
    intro w z
    rw [hgr, LinearIsometryEquiv.comp_fderiv]
    simp only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_coe'']
    exact InnerProductSpace.toDual_symm_apply
  rw [key, real_inner_comm, key, hsym u v]

theorem penaltyHessian_symm (p : Constants) (f : Fin p.n → EuclideanSpace ℝ (Fin p.dim) → ℝ)
    (hnet : Network p.toPublic) (hA1 : Assumption1 p.toPublic p.m p.M f) (x u v : Stacked p.n p.dim) :
    ⟪penaltyHessian p.toPublic f x u, v⟫ = ⟪u, penaltyHessian p.toPublic f x v⟫ := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  have hc := inner_mix_comm p.toPublic hnet u v
  rw [PiLp.inner_apply, PiLp.inner_apply] at hc
  simp only [penaltyHessian, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    inner_sub_left, inner_sub_right, RCLike.conj_to_real, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl fun i _ => hessian_symm (f i) (hA1 i).1 (x i) (u i) (v i), hc]

end OracleTemplate.DobocK
