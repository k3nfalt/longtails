import LongTails.Proofs.LinearDecaySgdStep
import LongTails.Proofs.LinearDecaySgdWeights
import Mathlib.Probability.Independence.InfinitePi

open MeasureTheory Set InnerProductSpace ProbabilityTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.SampledConvex

open LongTails.Setups.SampledSmoothConvex

section Independence

variable {Ξ : Type*} [MeasurableSpace Ξ] {Y : Type*} [MeasurableSpace Y]

lemma prefix_indep (p : Measure Ξ) [IsProbabilityMeasure p] (k : ℕ) :
    IndepFun (fun ξ : ℕ → Ξ => fun i : Fin k => ξ i) (fun ξ : ℕ → Ξ => ξ k)
      (Measure.infinitePi fun _ : ℕ => p) := by
  have hi : iIndepFun (fun j : ℕ => fun ξ : ℕ → Ξ => ξ j) (Measure.infinitePi fun _ : ℕ => p) :=
    iIndepFun_infinitePi (fun _ => measurable_id)
  have hd : Disjoint (Finset.range k) ({k} : Finset ℕ) := by simp
  have h := hi.indepFun_finset (Finset.range k) {k} hd (fun j => measurable_pi_apply j)
  have hm1 : Measurable (fun u : (Finset.range k) → Ξ => fun i : Fin k =>
      u ⟨(i : ℕ), Finset.mem_range.mpr i.isLt⟩) := by fun_prop
  have hm2 : Measurable (fun u : ({k} : Finset ℕ) → Ξ => u ⟨k, Finset.mem_singleton_self k⟩) := by
    fun_prop
  exact h.comp hm1 hm2

lemma map_prefix_pair (p : Measure Ξ) [IsProbabilityMeasure p] (k : ℕ) :
    (Measure.infinitePi fun _ : ℕ => p).map (fun ξ : ℕ → Ξ => ((fun i : Fin k => ξ i), ξ k)) =
      ((Measure.infinitePi fun _ : ℕ => p).map (fun ξ : ℕ → Ξ => fun i : Fin k => ξ i)).prod p := by
  have h1 : Measurable (fun ξ : ℕ → Ξ => fun i : Fin k => ξ i) := by fun_prop
  have h2 : Measurable (fun ξ : ℕ → Ξ => ξ k) := measurable_pi_apply k
  have h := (indepFun_iff_map_prod_eq_prod_map_map h1.aemeasurable h2.aemeasurable).mp
    (prefix_indep p k)
  rw [h, Measure.infinitePi_map_eval]

lemma integral_prefix (p : Measure Ξ) [IsProbabilityMeasure p] (k : ℕ)
    (X : (Fin k → Ξ) → Y) (hX : Measurable X) (Φ : Y → Ξ → ℝ)
    (hΦ : Measurable (Function.uncurry Φ))
    (hi : Integrable (fun ξ : ℕ → Ξ => Φ (X (fun i : Fin k => ξ i)) (ξ k))
      (Measure.infinitePi fun _ : ℕ => p)) :
    Integrable (fun ξ : ℕ → Ξ => ∫ ω, Φ (X (fun i : Fin k => ξ i)) ω ∂p)
      (Measure.infinitePi fun _ : ℕ => p) ∧
    ∫ ξ, Φ (X (fun i : Fin k => ξ i)) (ξ k) ∂(Measure.infinitePi fun _ : ℕ => p) =
      ∫ ξ, (∫ ω, Φ (X (fun i : Fin k => ξ i)) ω ∂p) ∂(Measure.infinitePi fun _ : ℕ => p) := by
  set P := Measure.infinitePi fun _ : ℕ => p
  set π : (ℕ → Ξ) → (Fin k → Ξ) := fun ξ i => ξ i
  have hπ : Measurable π := by fun_prop
  set Q := P.map π
  have hpair : Measurable (fun ξ : ℕ → Ξ => (π ξ, ξ k)) := by fun_prop
  let H : (Fin k → Ξ) × Ξ → ℝ := fun z => Φ (X z.1) z.2
  have hH : Measurable H := hΦ.comp ((hX.comp measurable_fst).prodMk measurable_snd)
  have hmap := map_prefix_pair p k
  have hHi : Integrable H (Q.prod p) := by
    rw [← hmap]
    exact (integrable_map_measure hH.aestronglyMeasurable hpair.aemeasurable).mpr hi
  have hin : Integrable (fun u => ∫ ω, H (u, ω) ∂p) Q := hHi.integral_prod_left
  refine ⟨?_, ?_⟩
  · exact (integrable_map_measure hin.aestronglyMeasurable hπ.aemeasurable).mp hin
  · calc ∫ ξ, Φ (X (π ξ)) (ξ k) ∂P = ∫ z, H z ∂(P.map (fun ξ => (π ξ, ξ k))) :=
          (integral_map hpair.aemeasurable hH.aestronglyMeasurable).symm
      _ = ∫ z, H z ∂(Q.prod p) := by rw [hmap]
      _ = ∫ u, ∫ ω, H (u, ω) ∂p ∂Q := integral_prod H hHi
      _ = ∫ ξ, ∫ ω, H (π ξ, ω) ∂p ∂P :=
          integral_map hπ.aemeasurable hin.aestronglyMeasurable

end Independence

section Trajectory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {Ξ : Type*} [MeasurableSpace Ξ]

noncomputable def anchor (G : Ξ → E → E) (L η : ℝ) (T : ℕ) (x0 xstar : E) (ξ : ℕ → Ξ) : ℕ → E
  | 0 => xstar
  | k + 1 => (weight L η T k / weight L η T (k + 1)) • anchor G L η T x0 xstar ξ k +
      (1 - weight L η T k / weight L η T (k + 1)) • path G η T x0 ξ (k + 1)

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ξ] in
lemma path_succ (G : Ξ → E → E) (η : ℝ) (T : ℕ) (x0 : E) (ξ : ℕ → Ξ) (k : ℕ) :
    path G η T x0 ξ (k + 1) = path G η T x0 ξ k - step η T k • G (ξ k) (path G η T x0 ξ k) := rfl

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ξ] in
lemma path_congr (G : Ξ → E → E) (η : ℝ) (T : ℕ) (x0 : E) {ξ ξ' : ℕ → Ξ} :
    ∀ k, (∀ i, i < k → ξ i = ξ' i) → path G η T x0 ξ k = path G η T x0 ξ' k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hξ
    rw [path_succ, path_succ, ih (fun i hi => hξ i (Nat.lt_succ_of_lt hi)), hξ k (Nat.lt_succ_self k)]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ξ] in
lemma anchor_congr (G : Ξ → E → E) (L η : ℝ) (T : ℕ) (x0 xstar : E) {ξ ξ' : ℕ → Ξ} :
    ∀ k, (∀ i, i < k → ξ i = ξ' i) →
      anchor G L η T x0 xstar ξ k = anchor G L η T x0 xstar ξ' k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hξ
    simp only [anchor]
    rw [ih (fun i hi => hξ i (Nat.lt_succ_of_lt hi)), path_congr G η T x0 (k + 1) hξ]

omit [CompleteSpace E] in
lemma measurable_path {G : Ξ → E → E} (hG : Measurable (Function.uncurry G)) (η : ℝ) (T : ℕ)
    (x0 : E) : ∀ k, Measurable (fun ξ : ℕ → Ξ => path G η T x0 ξ k) := by
  intro k
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    simp only [path_succ]
    exact ih.sub ((hG.comp ((measurable_pi_apply k).prodMk ih)).const_smul _)

omit [CompleteSpace E] in
lemma measurable_anchor {G : Ξ → E → E} (hG : Measurable (Function.uncurry G)) (L η : ℝ) (T : ℕ)
    (x0 xstar : E) : ∀ k, Measurable (fun ξ : ℕ → Ξ => anchor G L η T x0 xstar ξ k) := by
  intro k
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    simp only [anchor]
    exact (ih.const_smul _).add ((measurable_path hG η T x0 (k + 1)).const_smul _)

noncomputable def extend {k : ℕ} (ω0 : Ξ) (u : Fin k → Ξ) : ℕ → Ξ :=
  fun i => if h : i < k then u ⟨i, h⟩ else ω0

lemma measurable_extend {k : ℕ} (ω0 : Ξ) : Measurable (extend (k := k) ω0) := by
  rw [measurable_pi_iff]
  intro i
  by_cases h : i < k
  · simp only [extend, h, dite_true]; exact measurable_pi_apply _
  · simp only [extend, h, dite_false]; exact measurable_const

omit [MeasurableSpace Ξ] in
lemma extend_agree {k : ℕ} (ω0 : Ξ) (ξ : ℕ → Ξ) :
    ∀ i, i < k → extend ω0 (fun j : Fin k => ξ j) i = ξ i := by
  intro i hi
  simp [extend, hi]

end Trajectory

section Moments

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {Ξ : Type*} [MeasurableSpace Ξ]
  {p : Measure Ξ} [IsProbabilityMeasure p] {F : Ξ → E → ℝ} {G : Ξ → E → E} {L σ : ℝ} {xstar : E}

lemma Hyp.obj_convex (h : Hyp p F G L σ xstar) : ConvexOn ℝ univ (obj p F) := by
  refine ⟨convex_univ, fun a _ b _ θ φ hθ hφ hs => ?_⟩
  set w := θ • a + φ • b
  have ha := h.obj_lower w a
  have hb := h.obj_lower w b
  have hz : θ • (a - w) + φ • (b - w) = 0 := by
    simp only [w, smul_sub]
    rw [show θ • a - θ • (θ • a + φ • b) + (φ • b - φ • (θ • a + φ • b)) =
      (1 - (θ + φ)) • (θ • a + φ • b) by module, hs, sub_self, zero_smul]
  have hi : θ * ⟪mean p G w, a - w⟫ + φ * ⟪mean p G w, b - w⟫ = 0 := by
    rw [← real_inner_smul_right, ← real_inner_smul_right, ← inner_add_right, hz, inner_zero_right]
  simp only [smul_eq_mul]
  have e1 := mul_le_mul_of_nonneg_left ha hθ
  have e2 := mul_le_mul_of_nonneg_left hb hφ
  linear_combination e1 + e2 - hi - obj p F w * hs

lemma Hyp.gap_bounds (h : Hyp p F G L σ xstar) (y : E) :
    0 ≤ obj p F y - obj p F xstar ∧ obj p F y - obj p F xstar ≤ L / 2 * ‖y - xstar‖ ^ 2 := by
  refine ⟨sub_nonneg.mpr (h.min (mem_univ y)), ?_⟩
  have := h.obj_upper xstar y
  rw [h.mean_star, inner_zero_left] at this
  linarith

omit [SecondCountableTopology E] in
lemma integrable_eval_sq (h : Hyp p F G L σ xstar) (k : ℕ) :
    Integrable (fun ξ : ℕ → Ξ => ‖G (ξ k) xstar‖ ^ 2) (Measure.infinitePi fun _ : ℕ => p) := by
  have hm : Measurable (fun ξ : ℕ → Ξ => ξ k) := measurable_pi_apply k
  have hf : Measurable (fun ω : Ξ => ‖G ω xstar‖ ^ 2) := (h.grad_meas xstar).norm.pow_const 2
  have hmap : (Measure.infinitePi fun _ : ℕ => p).map (fun ξ : ℕ → Ξ => ξ k) = p :=
    Measure.infinitePi_map_eval (μ := fun _ : ℕ => p) k
  have hi : Integrable (fun ω : Ξ => ‖G ω xstar‖ ^ 2)
      ((Measure.infinitePi fun _ : ℕ => p).map (fun ξ : ℕ → Ξ => ξ k)) := by
    rw [hmap]; exact h.sq_int
  exact (integrable_map_measure hf.aestronglyMeasurable hm.aemeasurable).mp hi

lemma integrable_path_sq (h : Hyp p F G L σ xstar) (η : ℝ) (T : ℕ) (x0 : E) :
    ∀ k, Integrable (fun ξ : ℕ → Ξ => ‖path G η T x0 ξ k - xstar‖ ^ 2)
      (Measure.infinitePi fun _ : ℕ => p) := by
  intro k
  induction k with
  | zero =>
    show Integrable (fun _ : ℕ → Ξ => ‖x0 - xstar‖ ^ 2) _
    exact integrable_const _
  | succ k ih =>
    set s := step η T k
    have hb : Integrable (fun ξ : ℕ → Ξ => 2 * (1 + |s| * L) ^ 2 * ‖path G η T x0 ξ k - xstar‖ ^ 2 +
        2 * s ^ 2 * ‖G (ξ k) xstar‖ ^ 2) (Measure.infinitePi fun _ : ℕ => p) :=
      (ih.const_mul _).add ((integrable_eval_sq h k).const_mul _)
    refine Integrable.mono' hb
      (((measurable_path h.meas η T x0 (k + 1)).sub_const xstar).norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ξ => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), path_succ]
    set x := path G η T x0 ξ k
    have h1 : ‖G (ξ k) x‖ ≤ ‖G (ξ k) xstar‖ + L * ‖x - xstar‖ := by
      calc ‖G (ξ k) x‖ = ‖G (ξ k) xstar + (G (ξ k) x - G (ξ k) xstar)‖ := by congr 1; abel
        _ ≤ ‖G (ξ k) xstar‖ + ‖G (ξ k) x - G (ξ k) xstar‖ := norm_add_le _ _
        _ ≤ _ := by linarith [h.lip (ξ k) x xstar]
    have h2 : ‖x - s • G (ξ k) x - xstar‖ ≤ (1 + |s| * L) * ‖x - xstar‖ + |s| * ‖G (ξ k) xstar‖ := by
      calc ‖x - s • G (ξ k) x - xstar‖ = ‖(x - xstar) - s • G (ξ k) x‖ := by congr 1; abel
        _ ≤ ‖x - xstar‖ + ‖s • G (ξ k) x‖ := norm_sub_le _ _
        _ = ‖x - xstar‖ + |s| * ‖G (ξ k) x‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ ≤ ‖x - xstar‖ + |s| * (‖G (ξ k) xstar‖ + L * ‖x - xstar‖) := by
            gcongr
        _ = _ := by ring
    have h3 : 0 ≤ (1 + |s| * L) * ‖x - xstar‖ := mul_nonneg (by have := h.pos; positivity) (norm_nonneg _)
    have h4 : 0 ≤ |s| * ‖G (ξ k) xstar‖ := mul_nonneg (abs_nonneg _) (norm_nonneg _)
    have h5 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    have h6 : ((1 + |s| * L) * ‖x - xstar‖ + |s| * ‖G (ξ k) xstar‖) ^ 2 ≤
        2 * (1 + |s| * L) ^ 2 * ‖x - xstar‖ ^ 2 + 2 * s ^ 2 * ‖G (ξ k) xstar‖ ^ 2 := by
      have := sq_abs s
      nlinarith [sq_nonneg ((1 + |s| * L) * ‖x - xstar‖ - |s| * ‖G (ξ k) xstar‖)]
    linarith

lemma integrable_anchor_sq (h : Hyp p F G L σ xstar) (η : ℝ) (T : ℕ) (x0 : E) :
    ∀ k, Integrable (fun ξ : ℕ → Ξ => ‖anchor G L η T x0 xstar ξ k - xstar‖ ^ 2)
      (Measure.infinitePi fun _ : ℕ => p) := by
  intro k
  induction k with
  | zero => simp [anchor]
  | succ k ih =>
    set θ := weight L η T k / weight L η T (k + 1)
    have hb : Integrable (fun ξ : ℕ → Ξ => 2 * θ ^ 2 * ‖anchor G L η T x0 xstar ξ k - xstar‖ ^ 2 +
        2 * (1 - θ) ^ 2 * ‖path G η T x0 ξ (k + 1) - xstar‖ ^ 2)
        (Measure.infinitePi fun _ : ℕ => p) :=
      (ih.const_mul _).add ((integrable_path_sq h η T x0 (k + 1)).const_mul _)
    refine Integrable.mono' hb
      (((measurable_anchor h.meas L η T x0 xstar (k + 1)).sub_const xstar).norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ξ => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simp only [anchor]
    set a := anchor G L η T x0 xstar ξ k
    set b := path G η T x0 ξ (k + 1)
    have he : θ • a + (1 - θ) • b - xstar = θ • (a - xstar) + (1 - θ) • (b - xstar) := by module
    rw [he]
    have h1 := norm_add_le (θ • (a - xstar)) ((1 - θ) • (b - xstar))
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs] at h1
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 : (|θ| * ‖a - xstar‖ + |1 - θ| * ‖b - xstar‖) ^ 2 ≤
        2 * θ ^ 2 * ‖a - xstar‖ ^ 2 + 2 * (1 - θ) ^ 2 * ‖b - xstar‖ ^ 2 := by
      have := sq_abs θ
      have := sq_abs (1 - θ)
      nlinarith [sq_nonneg (|θ| * ‖a - xstar‖ - |1 - θ| * ‖b - xstar‖)]
    linarith

lemma integrable_gap (h : Hyp p F G L σ xstar) {X : (ℕ → Ξ) → E} (hX : Measurable X)
    (hsq : Integrable (fun ξ => ‖X ξ - xstar‖ ^ 2) (Measure.infinitePi fun _ : ℕ => p)) :
    Integrable (fun ξ => obj p F (X ξ) - obj p F xstar) (Measure.infinitePi fun _ : ℕ => p) := by
  refine Integrable.mono' (hsq.const_mul (L / 2))
    ((h.obj_continuous.measurable.comp hX).sub_const _).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ξ => ?_))
  obtain ⟨h0, h1⟩ := h.gap_bounds (X ξ)
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact h1

omit [InnerProductSpace ℝ E] [CompleteSpace E] [IsProbabilityMeasure p] in
lemma integrable_dist (X Y : (ℕ → Ξ) → E) (hX : Measurable X) (hY : Measurable Y)
    (hXs : Integrable (fun ξ => ‖X ξ - xstar‖ ^ 2) (Measure.infinitePi fun _ : ℕ => p))
    (hYs : Integrable (fun ξ => ‖Y ξ - xstar‖ ^ 2) (Measure.infinitePi fun _ : ℕ => p)) :
    Integrable (fun ξ => ‖X ξ - Y ξ‖ ^ 2) (Measure.infinitePi fun _ : ℕ => p) := by
  have hb : Integrable (fun ξ => 2 * ‖X ξ - xstar‖ ^ 2 + 2 * ‖Y ξ - xstar‖ ^ 2)
      (Measure.infinitePi fun _ : ℕ => p) := (hXs.const_mul 2).add (hYs.const_mul 2)
  refine Integrable.mono' hb
    ((hX.sub hY).norm.pow_const 2).aestronglyMeasurable (Filter.Eventually.of_forall (fun ξ => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h1 := norm_sub_le (X ξ - xstar) (Y ξ - xstar)
  rw [show X ξ - xstar - (Y ξ - xstar) = X ξ - Y ξ by abel] at h1
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [sq_nonneg (‖X ξ - xstar‖ - ‖Y ξ - xstar‖)]

end Moments

section Assembly

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {Ξ : Type*} [MeasurableSpace Ξ]
  {p : Measure Ξ} [IsProbabilityMeasure p] {F : Ξ → E → ℝ} {G : Ξ → E → E} {L σ : ℝ} {xstar : E}

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ξ] in
lemma prefix_eq (G : Ξ → E → E) (L η : ℝ) (T : ℕ) (x0 xstar : E) (ω0 : Ξ) (k : ℕ) (ξ : ℕ → Ξ) :
    (path G η T x0 (extend ω0 (fun i : Fin k => ξ i)) k,
      anchor G L η T x0 xstar (extend ω0 (fun i : Fin k => ξ i)) k) =
    (path G η T x0 ξ k, anchor G L η T x0 xstar ξ k) := by
  rw [path_congr G η T x0 k (extend_agree ω0 ξ), anchor_congr G L η T x0 xstar k (extend_agree ω0 ξ)]

lemma Hyp.step_bound (h : Hyp p F G L σ xstar) {η : ℝ} (hη : 0 < η) (hLη : L * η ≤ 1 / 8) {T k : ℕ} (hk : k < T)
    (x0 : E) :
    step η T k * weight L η T k *
      ((∫ ξ, obj p F (path G η T x0 ξ (k + 1)) - obj p F xstar ∂(Measure.infinitePi fun _ : ℕ => p)) -
        ∫ ξ, obj p F (anchor G L η T x0 xstar ξ k) - obj p F xstar ∂(Measure.infinitePi fun _ : ℕ => p)) ≤
    weight L η T k / 2 *
      ((∫ ξ, ‖path G η T x0 ξ k - anchor G L η T x0 xstar ξ k‖ ^ 2 ∂(Measure.infinitePi fun _ : ℕ => p)) -
        ∫ ξ, ‖path G η T x0 ξ (k + 1) - anchor G L η T x0 xstar ξ k‖ ^ 2
          ∂(Measure.infinitePi fun _ : ℕ => p)) +
    weight L η T k * charge L η T k *
      (∫ ξ, obj p F (path G η T x0 ξ k) - obj p F xstar ∂(Measure.infinitePi fun _ : ℕ => p)) +
    step η T k ^ 2 * weight L η T k * (1 + L * step η T k) * σ ^ 2 := by
  set P := Measure.infinitePi fun _ : ℕ => p
  have hL := h.pos
  obtain ⟨ω0⟩ := nonempty_of_isProbabilityMeasure p
  set s := step η T k
  have hs : 0 < s := step_pos hη hk
  have hw : 0 < weight L η T k := (weight_bounds h.pos.le hη hLη k hk).1
  set x := fun ξ : ℕ → Ξ => path G η T x0 ξ k
  set y := fun ξ : ℕ → Ξ => anchor G L η T x0 xstar ξ k
  set x' := fun ξ : ℕ → Ξ => path G η T x0 ξ (k + 1)
  have hxm : Measurable x := measurable_path h.meas η T x0 k
  have hym : Measurable y := measurable_anchor h.meas L η T x0 xstar k
  have hx'm : Measurable x' := measurable_path h.meas η T x0 (k + 1)
  have hxs := integrable_path_sq h η T x0 k
  have hys := integrable_anchor_sq h η T x0 k
  have hx's := integrable_path_sq h η T x0 (k + 1)
  have hgx := integrable_gap h hxm hxs
  have hgy := integrable_gap h hym hys
  have hgx' := integrable_gap h hx'm hx's
  have hd := integrable_dist x y hxm hym hxs hys
  have he := integrable_dist x' y hx'm hym hx's hys
  let X : (Fin k → Ξ) → E × E := fun u =>
    (path G η T x0 (extend ω0 u) k, anchor G L η T x0 xstar (extend ω0 u) k)
  have hX : Measurable X :=
    ((measurable_path h.meas η T x0 k).comp (measurable_extend ω0)).prodMk
      ((measurable_anchor h.meas L η T x0 xstar k).comp (measurable_extend ω0))
  have hXeq : ∀ ξ : ℕ → Ξ, X (fun i : Fin k => ξ i) = (x ξ, y ξ) :=
    fun ξ => prefix_eq G L η T x0 xstar ω0 k ξ
  have hcont := h.obj_continuous
  let Φ1 : E × E → Ξ → ℝ := fun q ω => obj p F (q.1 - s • G ω q.1)
  have hΦ1 : Measurable (Function.uncurry Φ1) := by
    have hg : Measurable (fun r : (E × E) × Ξ => G r.2 r.1.1) :=
      h.meas.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst))
    exact hcont.measurable.comp ((measurable_fst.comp measurable_fst).sub (hg.const_smul s))
  let Φ2 : E × E → Ξ → ℝ := fun q ω => ‖q.1 - s • G ω q.1 - q.2‖ ^ 2
  have hΦ2 : Measurable (Function.uncurry Φ2) := by
    have hg : Measurable (fun r : (E × E) × Ξ => G r.2 r.1.1) :=
      h.meas.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst))
    exact (((measurable_fst.comp measurable_fst).sub (hg.const_smul s)).sub
      (measurable_snd.comp measurable_fst)).norm.pow_const 2
  have hc1 : ∀ ξ : ℕ → Ξ, Φ1 (X (fun i : Fin k => ξ i)) (ξ k) = obj p F (x' ξ) := by
    intro ξ; rw [hXeq]; rfl
  have hc2 : ∀ ξ : ℕ → Ξ, Φ2 (X (fun i : Fin k => ξ i)) (ξ k) = ‖x' ξ - y ξ‖ ^ 2 := by
    intro ξ; rw [hXeq]; rfl
  have hobj' : Integrable (fun ξ => obj p F (x' ξ)) P :=
    (hgx'.add (integrable_const (obj p F xstar))).congr
      (Filter.Eventually.of_forall (fun ξ => by simp))
  obtain ⟨hI1, hE1⟩ := integral_prefix p k X hX Φ1 hΦ1 (by simp_rw [hc1]; exact hobj')
  obtain ⟨hI2, hE2⟩ := integral_prefix p k X hX Φ2 hΦ2 (by simp_rw [hc2]; exact he)
  simp_rw [hc1] at hE1
  simp_rw [hc2] at hE2
  simp_rw [hXeq] at hI1 hI2 hE1 hE2
  set inner1 := fun ξ => ∫ ω, obj p F (x ξ - s • G ω (x ξ)) ∂p
  set inner2 := fun ξ => ∫ ω, ‖x ξ - s • G ω (x ξ) - y ξ‖ ^ 2 ∂p
  have hpt : ∀ ξ, inner1 ξ - obj p F (y ξ) ≤
      (‖x ξ - y ξ‖ ^ 2 - inner2 ξ) / (2 * s) +
        2 * L * s * (1 + L * s) * (obj p F (x ξ) - obj p F xstar) + s * (1 + L * s) * σ ^ 2 :=
    fun ξ => (h.one_sample (x ξ) (y ξ) hs).2.2
  have hli : Integrable (fun ξ => inner1 ξ - obj p F (y ξ)) P := by
    have := hI1.sub (hgy.add (integrable_const (obj p F xstar)))
    refine this.congr (Filter.Eventually.of_forall (fun ξ => ?_))
    simp [inner1]
  have hri : Integrable (fun ξ => (‖x ξ - y ξ‖ ^ 2 - inner2 ξ) / (2 * s) +
      2 * L * s * (1 + L * s) * (obj p F (x ξ) - obj p F xstar) + s * (1 + L * s) * σ ^ 2) P :=
    (((hd.sub hI2).div_const _).add (hgx.const_mul _)).add (integrable_const _)
  have hmono := integral_mono hli hri hpt
  have hl : ∫ ξ, inner1 ξ - obj p F (y ξ) ∂P =
      (∫ ξ, obj p F (x' ξ) - obj p F xstar ∂P) - ∫ ξ, obj p F (y ξ) - obj p F xstar ∂P := by
    have hy' : Integrable (fun ξ => obj p F (y ξ)) P :=
      (hgy.add (integrable_const (obj p F xstar))).congr
        (Filter.Eventually.of_forall (fun ξ => by simp))
    rw [integral_sub hI1 hy', ← hE1, integral_sub hobj' (integrable_const _),
      integral_sub hy' (integrable_const _)]
    ring
  have hr : ∫ ξ, ((‖x ξ - y ξ‖ ^ 2 - inner2 ξ) / (2 * s) +
      2 * L * s * (1 + L * s) * (obj p F (x ξ) - obj p F xstar) + s * (1 + L * s) * σ ^ 2) ∂P =
      ((∫ ξ, ‖x ξ - y ξ‖ ^ 2 ∂P) - ∫ ξ, ‖x' ξ - y ξ‖ ^ 2 ∂P) / (2 * s) +
        2 * L * s * (1 + L * s) * (∫ ξ, obj p F (x ξ) - obj p F xstar ∂P) +
        s * (1 + L * s) * σ ^ 2 := by
    have j3 : Integrable (fun ξ => ‖x ξ - y ξ‖ ^ 2 - inner2 ξ) P := hd.sub hI2
    have j1 : Integrable (fun ξ => (‖x ξ - y ξ‖ ^ 2 - inner2 ξ) / (2 * s)) P := j3.div_const _
    have j2 : Integrable (fun ξ => 2 * L * s * (1 + L * s) * (obj p F (x ξ) - obj p F xstar)) P :=
      hgx.const_mul _
    have j12 : Integrable (fun ξ => (‖x ξ - y ξ‖ ^ 2 - inner2 ξ) / (2 * s) +
        2 * L * s * (1 + L * s) * (obj p F (x ξ) - obj p F xstar)) P := j1.add j2
    rw [integral_add j12 (integrable_const _), integral_add j1 j2, integral_div,
      integral_sub hd hI2, ← hE2, integral_const_mul, integral_const, probReal_univ, one_smul]
  rw [hl, hr] at hmono
  have hsw : 0 ≤ s * weight L η T k := (mul_pos hs hw).le
  have := mul_le_mul_of_nonneg_left hmono hsw
  have hch : charge L η T k = 2 * L * s ^ 2 * (1 + L * s) := rfl
  rw [hch]
  have hs0 : s ≠ 0 := hs.ne'
  calc _ = s * weight L η T k * ((∫ ξ, obj p F (x' ξ) - obj p F xstar ∂P) -
        ∫ ξ, obj p F (y ξ) - obj p F xstar ∂P) := rfl
    _ ≤ _ := this
    _ = _ := by field_simp; ring

lemma Hyp.jensen_bound (h : Hyp p F G L σ xstar) {η : ℝ} (hη : 0 < η) (hLη : L * η ≤ 1 / 8)
    {T k : ℕ} (hk : k + 1 < T) (x0 : E) :
    weight L η T (k + 1) *
        ∫ ξ, obj p F (anchor G L η T x0 xstar ξ (k + 1)) - obj p F xstar
          ∂(Measure.infinitePi fun _ : ℕ => p) ≤
      weight L η T k * ∫ ξ, obj p F (anchor G L η T x0 xstar ξ k) - obj p F xstar
          ∂(Measure.infinitePi fun _ : ℕ => p) +
      (weight L η T (k + 1) - weight L η T k) *
        ∫ ξ, obj p F (path G η T x0 ξ (k + 1)) - obj p F xstar ∂(Measure.infinitePi fun _ : ℕ => p) := by
  set P := Measure.infinitePi fun _ : ℕ => p
  have hw := (weight_bounds h.pos.le hη hLη k (Nat.lt_of_succ_lt hk)).1
  have hw' := (weight_bounds h.pos.le hη hLη (k + 1) hk).1
  have hmono := weight_mono h.pos.le hη hLη hk
  set a := fun ξ => anchor G L η T x0 xstar ξ k
  set a' := fun ξ => anchor G L η T x0 xstar ξ (k + 1)
  set b := fun ξ => path G η T x0 ξ (k + 1)
  have hga := integrable_gap h (measurable_anchor h.meas L η T x0 xstar k)
    (integrable_anchor_sq h η T x0 k)
  have hga' := integrable_gap h (measurable_anchor h.meas L η T x0 xstar (k + 1))
    (integrable_anchor_sq h η T x0 (k + 1))
  have hgb := integrable_gap h (measurable_path h.meas η T x0 (k + 1))
    (integrable_path_sq h η T x0 (k + 1))
  set θ := weight L η T k / weight L η T (k + 1)
  have hθ0 : 0 ≤ θ := div_nonneg hw.le hw'.le
  have hθ1 : θ ≤ 1 := (div_le_one hw').mpr hmono
  have hpt : ∀ ξ, weight L η T (k + 1) * (obj p F (a' ξ) - obj p F xstar) ≤
      weight L η T k * (obj p F (a ξ) - obj p F xstar) +
        (weight L η T (k + 1) - weight L η T k) * (obj p F (b ξ) - obj p F xstar) := by
    intro ξ
    have hc := h.obj_convex.2 (mem_univ (a ξ)) (mem_univ (b ξ)) hθ0 (sub_nonneg.mpr hθ1)
      (add_sub_cancel θ 1)
    simp only [smul_eq_mul] at hc
    have ha' : a' ξ = θ • a ξ + (1 - θ) • b ξ := rfl
    rw [← ha'] at hc
    have hm := mul_le_mul_of_nonneg_left hc hw'.le
    have e1 : weight L η T (k + 1) * θ = weight L η T k := by
      rw [mul_comm]; exact div_mul_cancel₀ _ hw'.ne'
    have e2 : weight L η T (k + 1) * (1 - θ) = weight L η T (k + 1) - weight L η T k := by
      rw [mul_sub, mul_one, e1]
    linear_combination hm + obj p F (a ξ) * e1 + obj p F (b ξ) * e2
  have hl : Integrable (fun ξ => weight L η T (k + 1) * (obj p F (a' ξ) - obj p F xstar)) P :=
    hga'.const_mul _
  have hr1 : Integrable (fun ξ => weight L η T k * (obj p F (a ξ) - obj p F xstar)) P :=
    hga.const_mul _
  have hr2 : Integrable (fun ξ => (weight L η T (k + 1) - weight L η T k) *
      (obj p F (b ξ) - obj p F xstar)) P := hgb.const_mul _
  have hr12 : Integrable (fun ξ => weight L η T k * (obj p F (a ξ) - obj p F xstar) +
      (weight L η T (k + 1) - weight L η T k) * (obj p F (b ξ) - obj p F xstar)) P := hr1.add hr2
  have hm := integral_mono hl hr12 hpt
  rw [integral_add hr1 hr2, integral_const_mul, integral_const_mul, integral_const_mul] at hm
  exact hm

lemma Hyp.anchor_dist (h : Hyp p F G L σ xstar) {η : ℝ} (hη : 0 < η) (hLη : L * η ≤ 1 / 8)
    {T k : ℕ} (hk : k + 1 < T) (x0 : E) :
    weight L η T (k + 1) * ∫ ξ, ‖path G η T x0 ξ (k + 1) - anchor G L η T x0 xstar ξ (k + 1)‖ ^ 2
        ∂(Measure.infinitePi fun _ : ℕ => p) ≤
      weight L η T k * ∫ ξ, ‖path G η T x0 ξ (k + 1) - anchor G L η T x0 xstar ξ k‖ ^ 2
        ∂(Measure.infinitePi fun _ : ℕ => p) := by
  set P := Measure.infinitePi fun _ : ℕ => p
  have hw := (weight_bounds h.pos.le hη hLη k (Nat.lt_of_succ_lt hk)).1
  have hw' := (weight_bounds h.pos.le hη hLη (k + 1) hk).1
  have hmono := weight_mono h.pos.le hη hLη hk
  set θ := weight L η T k / weight L η T (k + 1)
  have hθ0 : 0 ≤ θ := div_nonneg hw.le hw'.le
  have hθ1 : θ ≤ 1 := (div_le_one hw').mpr hmono
  have hd1 := integrable_dist (fun ξ => path G η T x0 ξ (k + 1))
    (fun ξ => anchor G L η T x0 xstar ξ (k + 1)) (measurable_path h.meas η T x0 (k + 1))
    (measurable_anchor h.meas L η T x0 xstar (k + 1)) (integrable_path_sq h η T x0 (k + 1))
    (integrable_anchor_sq h η T x0 (k + 1))
  have hd2 := integrable_dist (fun ξ => path G η T x0 ξ (k + 1))
    (fun ξ => anchor G L η T x0 xstar ξ k) (measurable_path h.meas η T x0 (k + 1))
    (measurable_anchor h.meas L η T x0 xstar k) (integrable_path_sq h η T x0 (k + 1))
    (integrable_anchor_sq h η T x0 k)
  have hpt : ∀ ξ, weight L η T (k + 1) *
      ‖path G η T x0 ξ (k + 1) - anchor G L η T x0 xstar ξ (k + 1)‖ ^ 2 ≤
      weight L η T k * ‖path G η T x0 ξ (k + 1) - anchor G L η T x0 xstar ξ k‖ ^ 2 := by
    intro ξ
    set b := path G η T x0 ξ (k + 1)
    set a := anchor G L η T x0 xstar ξ k
    have he : b - anchor G L η T x0 xstar ξ (k + 1) = θ • (b - a) := by
      simp only [anchor]
      module
    rw [he, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have e1 : weight L η T (k + 1) * θ = weight L η T k := by
      rw [mul_comm]; exact div_mul_cancel₀ _ hw'.ne'
    have hsq : 0 ≤ ‖b - a‖ ^ 2 := sq_nonneg _
    have : weight L η T (k + 1) * (θ ^ 2 * ‖b - a‖ ^ 2) = weight L η T k * θ * ‖b - a‖ ^ 2 := by
      rw [← e1]; ring
    rw [this]
    have := mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hw.le hθ1) hsq
    linarith
  have hm := integral_mono (hd1.const_mul _) (hd2.const_mul _) hpt
  rwa [integral_const_mul, integral_const_mul] at hm

theorem Hyp.expected_gap (h : Hyp p F G L σ xstar) {η : ℝ} (hη : 0 < η) (hLη : L * η ≤ 1 / 8)
    {T : ℕ} (hT : 0 < T) (x0 : E) :
    Integrable (fun ξ => obj p F (path G η T x0 ξ T) - obj p F xstar)
      (Measure.infinitePi fun _ : ℕ => p) ∧
    ∫ ξ, obj p F (path G η T x0 ξ T) - obj p F xstar ∂(Measure.infinitePi fun _ : ℕ => p) ≤
      3 * ‖x0 - xstar‖ ^ 2 / (η * T) + 6 * η * σ ^ 2 := by
  set P := Measure.infinitePi fun _ : ℕ => p
  refine ⟨integrable_gap h (measurable_path h.meas η T x0 T) (integrable_path_sq h η T x0 T), ?_⟩
  let A : ℕ → ℝ := fun k => ∫ ξ, obj p F (path G η T x0 ξ k) - obj p F xstar ∂P
  let Φ : ℕ → ℝ := fun k => ∫ ξ, obj p F (anchor G L η T x0 xstar ξ k) - obj p F xstar ∂P
  let d : ℕ → ℝ := fun k => ∫ ξ, ‖path G η T x0 ξ k - anchor G L η T x0 xstar ξ k‖ ^ 2 ∂P
  let e : ℕ → ℝ := fun k => ∫ ξ, ‖path G η T x0 ξ (k + 1) - anchor G L η T x0 xstar ξ k‖ ^ 2 ∂P
  have hH : ∀ k, k < T → step η T k * weight L η T k * (A (k + 1) - Φ k) ≤
      weight L η T k / 2 * (d k - e k) + weight L η T k * charge L η T k * A k +
        step η T k ^ 2 * weight L η T k * (1 + L * step η T k) * σ ^ 2 :=
    fun k hk => h.step_bound hη hLη hk x0
  have hJ : ∀ k, k + 1 < T → weight L η T (k + 1) * Φ (k + 1) ≤
      weight L η T k * Φ k + (weight L η T (k + 1) - weight L η T k) * A (k + 1) :=
    fun k hk => h.jensen_bound hη hLη hk x0
  have hD : ∀ k, k + 1 < T → weight L η T (k + 1) * d (k + 1) ≤ weight L η T k * e k :=
    fun k hk => h.anchor_dist hη hLη hk x0
  have he : ∀ k, k < T → 0 ≤ e k := fun k _ => integral_nonneg (fun ξ => sq_nonneg _)
  have hΦ0 : Φ 0 = 0 := by simp [Φ, anchor]
  have hd0 : d 0 ≤ ‖x0 - xstar‖ ^ 2 := by simp [d, anchor, path]
  have hA0 : A 0 ≤ L * ‖x0 - xstar‖ ^ 2 / 2 := by
    have := (h.gap_bounds x0).2
    simp only [A, path, integral_const, probReal_univ, one_smul]
    linarith
  exact potential_bound h.pos.le hη hLη hT A Φ d e hH hJ hD he hΦ0 hd0 hA0

end Assembly

end OracleTemplate.SampledConvex
