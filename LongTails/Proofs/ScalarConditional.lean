import LongTails.Proofs.ScalarConvex
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

open MeasureTheory

namespace OracleTemplate.ScalarStopLoss

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
lemma conditional_mono_on {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {s : Set Ω} (hs : MeasurableSet[m] s) {U V : Ω → ℝ}
    (hUi : Integrable U μ) (hVi : Integrable V μ)
    (hUV : ∀ᵐ ω ∂μ, ω ∈ s → U ω ≤ V ω) :
    ∀ᵐ ω ∂μ, ω ∈ s → μ[U | m] ω ≤ μ[V | m] ω := by
  have hpoint : s.indicator U ≤ᵐ[μ] s.indicator V := by
    filter_upwards [hUV] with ω hω
    by_cases h : ω ∈ s
    · simpa [Set.indicator_of_mem h] using hω h
    · simp [Set.indicator_of_notMem h]
  have hmono := condExp_mono (m := m) (hUi.indicator (hm s hs))
    (hVi.indicator (hm s hs)) hpoint
  filter_upwards [hmono, condExp_indicator hUi hs, condExp_indicator hVi hs]
    with ω hω hU hV hmem
  rw [hU, hV, Set.indicator_of_mem hmem, Set.indicator_of_mem hmem] at hω
  exact hω

omit [IsProbabilityMeasure μ] in
lemma conditional_sum_product {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (c U : ℕ → Ω → ℝ) (N : ℕ)
    (hc : ∀ j, Measurable[m] (c j)) (hU : ∀ j, Integrable (U j) μ)
    (hB : ∀ j, ∀ᵐ ω ∂μ, ‖c j ω‖ ≤ 1) :
    μ[∑ j ∈ Finset.range N, c j*U j | m] =ᵐ[μ]
      ∑ j ∈ Finset.range N, c j*μ[U j | m] := by
  have hi : ∀ j, Integrable (c j*U j) μ := fun j =>
    (hU j).bdd_mul ((hc j).stronglyMeasurable.mono hm).aestronglyMeasurable (hB j)
  have hs := condExp_finsetSum (fun j (_ : j ∈ Finset.range N) => hi j) m
  have hp := ae_all_iff.mpr (fun j =>
    condExp_mul_of_stronglyMeasurable_left (hc j).stronglyMeasurable (hi j) (hU j))
  filter_upwards [hs, hp] with ω hsω hpω
  simp only [Finset.sum_apply, Pi.mul_apply] at hsω ⊢
  rw [hsω]
  apply Finset.sum_congr rfl
  intro j _
  exact hpω j

lemma conditional_two_term_transfer {m₀ m₁ : MeasurableSpace Ω}
    (hm : m₀ ≤ m₁) (hm₁ : m₁ ≤ mΩ) {X U V p q : Ω → ℝ}
    (hUi : Integrable U μ) (hVi : Integrable V μ)
    (hp : Measurable[m₀] p) (hq : Measurable[m₀] q)
    (hpB : ∀ᵐ ω ∂μ, ‖p ω‖ ≤ 1) (hqB : ∀ᵐ ω ∂μ, ‖q ω‖ ≤ 1)
    (hstep : μ[X | m₁] ≤ᵐ[μ] p*U+q*V) :
    μ[X | m₀] ≤ᵐ[μ] p*μ[U | m₀]+q*μ[V | m₀] := by
  have hpUi : Integrable (p*U) μ := hUi.bdd_mul
    (hp.stronglyMeasurable.mono (hm.trans hm₁)).aestronglyMeasurable hpB
  have hqVi : Integrable (q*V) μ := hVi.bdd_mul
    (hq.stronglyMeasurable.mono (hm.trans hm₁)).aestronglyMeasurable hqB
  have hmono := condExp_mono (m := m₀) integrable_condExp (hpUi.add hqVi) hstep
  have htower := condExp_condExp_of_le (μ := μ) (f := X) hm hm₁
  have hadd := condExp_add hpUi hqVi m₀
  have hpull := condExp_mul_of_stronglyMeasurable_left hp.stronglyMeasurable hpUi hUi
  have hqpull := condExp_mul_of_stronglyMeasurable_left hq.stronglyMeasurable hqVi hVi
  filter_upwards [hmono, htower, hadd, hpull, hqpull] with ω h hT hA hP hQ
  change μ[X | m₀] ω ≤ p ω*μ[U | m₀] ω+q ω*μ[V | m₀] ω
  change μ[p*U+q*V | m₀] ω = μ[p*U | m₀] ω+μ[q*V | m₀] ω at hA
  change μ[p*U | m₀] ω = p ω*μ[U | m₀] ω at hP
  change μ[q*V | m₀] ω = q ω*μ[V | m₀] ω at hQ
  linarith

lemma conditional_hinge_step {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {Z V d : Ω → ℝ} (hZ : Measurable[m] Z) (hZi : Integrable Z μ)
    (hVi : Integrable V μ) (hV : ∀ᵐ ω ∂μ, |V ω| ≤ 1) (a : ℝ)
    (hmean : ∀ᵐ ω ∂μ, a-1 ≤ Z ω → μ[V | m] ω ≤ -d ω) :
    μ[fun ω => max 0 (Z ω+V ω-a) | m] ≤ᵐ[μ]
      fun ω => (1-d ω)/2*max 0 (Z ω+1-a)+(1+d ω)/2*max 0 (Z ω-1-a) := by
  let U : Ω → ℝ := fun ω => max 0 (Z ω+1-a)
  let L : Ω → ℝ := fun ω => max 0 (Z ω-1-a)
  let A : Ω → ℝ := fun ω => (U ω+L ω)/2
  let C : Ω → ℝ := fun ω => (U ω-L ω)/2
  have hUi : Integrable U μ := (integrable_const (0 : ℝ)).sup ((hZi.add (integrable_const 1)).sub (integrable_const a))
  have hLi : Integrable L μ := (integrable_const (0 : ℝ)).sup ((hZi.sub (integrable_const 1)).sub (integrable_const a))
  have hAi : Integrable A μ := (hUi.add hLi).div_const 2
  have hAm : Measurable[m] A :=
    ((measurable_const.max ((hZ.add_const 1).sub_const a)).add
      (measurable_const.max ((hZ.sub_const 1).sub_const a))).div_const 2
  have hCm : Measurable[m] C :=
    ((measurable_const.max ((hZ.add_const 1).sub_const a)).sub
      (measurable_const.max ((hZ.sub_const 1).sub_const a))).div_const 2
  have hCb : ∀ᵐ ω ∂μ, ‖C ω‖ ≤ 1 := by
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hinge_secant_bounds (Z ω) a).1]
    exact (hinge_secant_bounds (Z ω) a).2
  have hCVi : Integrable (C*V) μ := hVi.bdd_mul
    (hCm.stronglyMeasurable.mono hm).aestronglyMeasurable hCb
  have hTi : Integrable (fun ω => max 0 (Z ω+V ω-a)) μ :=
    (integrable_const (0 : ℝ)).sup ((hZi.add hVi).sub (integrable_const a))
  have hpoint : (fun ω => max 0 (Z ω+V ω-a)) ≤ᵐ[μ] A+C*V := by
    filter_upwards [hV] with ω hω
    have h := hinge_chord (x := Z ω) (a := a) hω
    change max 0 (Z ω+V ω-a) ≤ A ω+C ω*V ω
    dsimp [A, C, U, L]
    nlinarith
  have hcond := condExp_mono (m := m) hTi (hAi.add hCVi) hpoint
  have hadd := condExp_add hAi hCVi m
  have hAeq := condExp_of_stronglyMeasurable hm hAm.stronglyMeasurable hAi
  have hCeq := condExp_mul_of_stronglyMeasurable_left hCm.stronglyMeasurable hCVi hVi
  filter_upwards [hcond, hadd, hCeq, hmean] with ω hω ha hc hmω
  change μ[A+C*V | m] ω = μ[A | m] ω+μ[C*V | m] ω at ha
  rw [hAeq] at ha
  change μ[C*V | m] ω = C ω*μ[V | m] ω at hc
  have hd := hinge_drift_comparison (Z ω) a (d ω) (μ[V | m] ω) hmω
  dsimp [A, C, U, L] at ha hc
  linarith

lemma conditional_hinge_restart {m₀ m₁ : MeasurableSpace Ω}
    (hm : m₀ ≤ m₁) (hm₁ : m₁ ≤ mΩ) {Z V d : Ω → ℝ}
    (hZ : Measurable[m₁] Z) (hZi : Integrable Z μ) (hVi : Integrable V μ)
    (hV : ∀ᵐ ω ∂μ, |V ω| ≤ 1) (hd : Measurable[m₀] d)
    (hdB : ∀ᵐ ω ∂μ, 0 ≤ d ω ∧ d ω ≤ 1) (a : ℝ)
    (hmean : ∀ᵐ ω ∂μ, a-1 ≤ Z ω → μ[V | m₁] ω ≤ -d ω) :
    μ[fun ω => max 0 (Z ω+V ω-a) | m₀] ≤ᵐ[μ] fun ω =>
      (1-d ω)/2*μ[fun ξ => max 0 (Z ξ+1-a) | m₀] ω +
        (1+d ω)/2*μ[fun ξ => max 0 (Z ξ-1-a) | m₀] ω := by
  have hstep := conditional_hinge_step (mΩ := mΩ) (μ := μ) hm₁ hZ hZi hVi hV a hmean
  apply conditional_two_term_transfer (mΩ := mΩ) (μ := μ) hm hm₁
    ((integrable_const (0 : ℝ)).sup ((hZi.add (integrable_const 1)).sub (integrable_const a)))
    ((integrable_const (0 : ℝ)).sup ((hZi.sub (integrable_const 1)).sub (integrable_const a)))
    ((measurable_const.sub hd).div_const 2) ((measurable_const.add hd).div_const 2) ?_ ?_ hstep
  · filter_upwards [hdB] with ω hω
    rw [Real.norm_eq_abs]
    change |(1-d ω)/2| ≤ 1
    apply abs_le.mpr
    constructor <;> linarith [hω.1, hω.2]
  · filter_upwards [hdB] with ω hω
    rw [Real.norm_eq_abs]
    change |(1+d ω)/2| ≤ 1
    apply abs_le.mpr
    constructor <;> linarith [hω.1, hω.2]

omit [IsProbabilityMeasure μ] in
lemma conditional_hinge_zero {m : MeasurableSpace Ω} {Z : Ω → ℝ} {a : ℝ}
    (hZ : ∀ᵐ ω ∂μ, Z ω ≤ a) :
    μ[fun ω => max 0 (Z ω-a) | m] =ᵐ[μ] 0 := by
  have he : (fun ω => max 0 (Z ω-a)) =ᵐ[μ] 0 := by
    filter_upwards [hZ] with ω hω
    exact max_eq_left (sub_nonpos.mpr hω)
  simpa using condExp_congr_ae (m := m) he

lemma conditional_hinge_shift {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {Z : Ω → ℝ} (hZi : Integrable Z μ) {a b : ℝ} (hab : a ≤ b) :
    μ[fun ω => max 0 (Z ω-a) | m] ≤ᵐ[μ]
      fun ω => μ[fun ξ => max 0 (Z ξ-b) | m] ω+(b-a) := by
  have hai : Integrable (fun ω => max 0 (Z ω-a)) μ :=
    (integrable_const (0 : ℝ)).sup (hZi.sub (integrable_const a))
  have hbi : Integrable (fun ω => max 0 (Z ω-b)) μ :=
    (integrable_const (0 : ℝ)).sup (hZi.sub (integrable_const b))
  have hc : (fun ω => max 0 (Z ω-a)) ≤ᵐ[μ] fun ω => max 0 (Z ω-b)+(b-a) :=
    Filter.Eventually.of_forall (fun ω => hinge_threshold_shift (x := Z ω) hab)
  have hmono := condExp_mono (m := m) hai (hbi.add (integrable_const (b-a))) hc
  have hadd := condExp_add hbi (integrable_const (b-a)) m
  filter_upwards [hmono, hadd] with ω hω he
  change μ[(fun ξ => max 0 (Z ξ-b))+(fun _ => b-a) | m] ω =
    μ[fun ξ => max 0 (Z ξ-b) | m] ω+μ[fun _ => b-a | m] ω at he
  rw [condExp_const hm] at he
  linarith

lemma conditional_finite_envelope (m : ℕ → MeasurableSpace Ω) (hm : Monotone m)
    (hambient : ∀ n, m n ≤ mΩ) (Z d : ℕ → Ω → ℝ) (N : ℕ)
    (hZ : ∀ n, Measurable[m n] (Z n)) (hZi : ∀ n, Integrable (Z n) μ)
    (hZ0 : Z 0 =ᵐ[μ] 0)
    (hZn : ∀ n ≤ N, ∀ᵐ ω ∂μ, Z n ω ≤ n)
    (hjump : ∀ n < N, ∀ᵐ ω ∂μ, |Z (n+1) ω-Z n ω| ≤ 1)
    (hd : ∀ j, Measurable[m 0] (d j))
    (hdB : ∀ j, ∀ᵐ ω ∂μ, 0 ≤ d j ω ∧ d j ω ≤ 1)
    (hmean : ∀ n < N, ∀ k : ℕ, 2 ≤ k → ∀ᵐ ω ∂μ,
      (k : ℝ)-1 ≤ Z n ω → μ[Z (n+1)-Z n | m n] ω ≤ -d (k-2) ω) :
    ∀ k : ℕ, 2 ≤ k → μ[fun ω => max 0 (Z N ω-k) | m 0] ≤ᵐ[μ]
      fun ω => envelope (fun j => d j ω) N k := by
  let A : ℕ → ℕ → Ω → ℝ := fun n k => μ[fun ω => max 0 (Z n ω-k) | m 0]
  have hinit : ∀ k : ℕ, ∀ᵐ ω ∂μ, A 0 k ω ≤ 0 := by
    intro k
    have hz : ∀ᵐ ω ∂μ, Z 0 ω ≤ (k : ℝ) := by
      filter_upwards [hZ0] with ω hω
      rw [hω]
      exact Nat.cast_nonneg k
    exact (conditional_hinge_zero (m := m 0) hz).le
  have hupper : ∀ n k : ℕ, ∀ᵐ ω ∂μ, n ≤ N → N ≤ k → A n k ω ≤ 0 := by
    intro n k
    by_cases hn : n ≤ N
    · by_cases hk : N ≤ k
      · have hz : ∀ᵐ ω ∂μ, Z n ω ≤ (k : ℝ) := by
          filter_upwards [hZn n hn] with ω hω
          exact hω.trans (by exact_mod_cast hn.trans hk)
        filter_upwards [(conditional_hinge_zero (m := m 0) hz).le] with ω hω _ _
        exact hω
      · exact Filter.Eventually.of_forall (fun _ _ h => False.elim (hk h))
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hn h))
  have hboundary : ∀ n, ∀ᵐ ω ∂μ, A n 1 ω ≤ A n 2 ω+1 := by
    intro n
    have h := conditional_hinge_shift (hambient 0) (hZi n)
      (show (1 : ℝ) ≤ 2 by norm_num)
    norm_num at h
    filter_upwards [h] with ω hω
    simpa [A] using hω
  have hstep : ∀ n k : ℕ, ∀ᵐ ω ∂μ, n < N → 2 ≤ k →
      A (n+1) k ω ≤ (1-d (k-2) ω)/2*A n (k-1) ω +
        (1+d (k-2) ω)/2*A n (k+1) ω := by
    intro n k
    by_cases hn : n < N
    · by_cases hk : 2 ≤ k
      · have he := conditional_hinge_restart (hm (Nat.zero_le n)) (hambient n)
          (hZ n) (hZi n) ((hZi (n+1)).sub (hZi n)) (hjump n hn)
          (hd (k-2)) (hdB (k-2)) (k : ℝ) (hmean n hn k hk)
        have heT : (fun ω => max 0 (Z n ω+(Z (n+1) ω-Z n ω)-(k : ℝ))) =
            fun ω => max 0 (Z (n+1) ω-k) := by funext ω; congr 1; ring
        have heU : (fun ω => max 0 (Z n ω+1-(k : ℝ))) =
            fun ω => max 0 (Z n ω-((k-1 : ℕ) : ℝ)) := by
          funext ω
          rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
          congr 1
          ring
        have heL : (fun ω => max 0 (Z n ω-1-(k : ℝ))) =
            fun ω => max 0 (Z n ω-((k+1 : ℕ) : ℝ)) := by
          funext ω
          push_cast
          congr 1
          ring
        change (μ[fun ω => max 0 (Z n ω+(Z (n+1) ω-Z n ω)-(k : ℝ)) | m 0] ≤ᵐ[μ]
          fun ω => (1-d (k-2) ω)/2*μ[fun ξ => max 0 (Z n ξ+1-k) | m 0] ω+
            (1+d (k-2) ω)/2*μ[fun ξ => max 0 (Z n ξ-1-k) | m 0] ω) at he
        rw [heT, heU, heL] at he
        filter_upwards [he] with ω hω _ _
        exact hω
      · exact Filter.Eventually.of_forall (fun _ _ h => False.elim (hk h))
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hn h))
  have hiAll := ae_all_iff.mpr hinit
  have huAll := ae_all_iff.mpr (fun n => ae_all_iff.mpr (hupper n))
  have hbAll := ae_all_iff.mpr hboundary
  have hsAll := ae_all_iff.mpr (fun n => ae_all_iff.mpr (hstep n))
  have hdAll := ae_all_iff.mpr hdB
  intro k hk
  filter_upwards [hiAll, huAll, hbAll, hsAll, hdAll] with ω hi hu hb hs hdb
  exact finite_envelope_induction (fun j => d j ω) (fun n j => A n j ω) N
    (fun j => (hdb j).1) (fun j => (hdb j).2) hi
    (fun n hn j hj => hu n j hn hj) (fun n _ => hb n)
    (fun n hn j hj _ => hs n j hn hj) N le_rfl k hk

lemma conditional_objective_of_hinges {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (d : ℕ → Ω → ℝ) (Z b score : Ω → ℝ) (N : ℕ)
    (hd : ∀ j, Measurable[m] (d j))
    (hdB : ∀ j, ∀ᵐ ω ∂μ, 0 ≤ d j ω ∧ d j ω ≤ 1)
    (hdmono : ∀ᵐ ω ∂μ, Monotone (fun j => d j ω))
    (hb : Measurable[m] b) (hbi : Integrable b μ) (hbB : ∀ᵐ ω ∂μ, b ω ≤ 2)
    (hZi : Integrable Z μ) (hscorei : Integrable score μ)
    (hscore : score ≤ᵐ[μ] fun ω => b ω+d 2 ω*max 0 (Z ω-2)+
      ∑ j ∈ Finset.range N, (d (j+3) ω-d (j+2) ω)*max 0 (Z ω-(j+3)))
    (hH : ∀ k : ℕ, 2 ≤ k → μ[fun ω => max 0 (Z ω-k) | m] ≤ᵐ[μ]
      fun ω => envelope (fun j => d j ω) N k) :
    μ[score | m] ≤ᵐ[μ] fun _ => 6 := by
  let U : ℕ → Ω → ℝ := fun j ω => max 0 (Z ω-(j+3))
  let c : ℕ → Ω → ℝ := fun j ω => d (j+3) ω-d (j+2) ω
  let V : Ω → ℝ := fun ω => max 0 (Z ω-2)
  have hUi : ∀ j, Integrable (U j) μ := fun j =>
    (integrable_const (0 : ℝ)).sup (hZi.sub (integrable_const ((j : ℝ)+3)))
  have hVi : Integrable V μ := (integrable_const (0 : ℝ)).sup (hZi.sub (integrable_const 2))
  have hc : ∀ j, Measurable[m] (c j) := fun j => (hd (j+3)).sub (hd (j+2))
  have hcB : ∀ j, ∀ᵐ ω ∂μ, ‖c j ω‖ ≤ 1 := by
    intro j
    filter_upwards [hdB (j+3), hdB (j+2)] with ω h1 h2
    change |d (j+3) ω-d (j+2) ω| ≤ 1
    apply abs_le.mpr
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hd2B : ∀ᵐ ω ∂μ, ‖d 2 ω‖ ≤ 1 := by
    filter_upwards [hdB 2] with ω hω
    simpa [Real.norm_eq_abs, abs_of_nonneg hω.1] using hω.2
  have hpVi : Integrable (d 2*V) μ := hVi.bdd_mul
    ((hd 2).stronglyMeasurable.mono hm).aestronglyMeasurable hd2B
  have hpUi : ∀ j, Integrable (c j*U j) μ := fun j =>
    (hUi j).bdd_mul ((hc j).stronglyMeasurable.mono hm).aestronglyMeasurable (hcB j)
  have hsumi : Integrable (∑ j ∈ Finset.range N, c j*U j) μ :=
    integrable_finsetSum' _ (fun j _ => hpUi j)
  have hpoint : score ≤ᵐ[μ] b+d 2*V+(∑ j ∈ Finset.range N, c j*U j) := by
    filter_upwards [hscore] with ω hω
    simpa [V, c, U, Finset.sum_apply, Pi.mul_apply, Pi.add_apply] using hω
  have hmono := condExp_mono (m := m) hscorei ((hbi.add hpVi).add hsumi) hpoint
  have hadd1 := condExp_add (hbi.add hpVi) hsumi m
  have hadd2 := condExp_add hbi hpVi m
  have hbeq := condExp_of_stronglyMeasurable hm hb.stronglyMeasurable hbi
  have hpull := condExp_mul_of_stronglyMeasurable_left (hd 2).stronglyMeasurable hpVi hVi
  have hsum := conditional_sum_product (mΩ := mΩ) (μ := μ) hm c U N hc hUi hcB
  have hdAll := ae_all_iff.mpr hdB
  have hHAll : ∀ᵐ ω ∂μ, ∀ k : ℕ, 2 ≤ k → μ[fun ξ => max 0 (Z ξ-k) | m] ω ≤
      envelope (fun j => d j ω) N k := by
    apply ae_all_iff.mpr
    intro k
    by_cases hk : 2 ≤ k
    · filter_upwards [hH k hk] with ω hω _
      exact hω
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hk h))
  filter_upwards [hmono, hadd1, hadd2, hpull, hsum, hdAll, hdmono, hbB, hHAll]
    with ω hM hA1 hA2 hP hS hD hDM hB hHH
  have hpoly := polygon_envelope_bound (fun j => d j ω)
    (fun k => μ[fun ξ => max 0 (Z ξ-k) | m] ω) N
    (fun j => (hD j).1) (fun j => (hD j).2) hDM hHH
  rw [hbeq] at hA2
  simp only [Pi.add_apply, Pi.mul_apply, Finset.sum_apply] at hA1 hA2 hP hS
  dsimp [V, c, U] at hM hA1 hA2 hP hS
  norm_num only [Nat.cast_ofNat] at hpoly
  have he : (∑ j ∈ Finset.range N,
      (d (j+3) ω-d (j+2) ω)*μ[fun ξ => max 0 (Z ξ-(j+3)) | m] ω) =
      ∑ j ∈ Finset.range N,
      (d (j+3) ω-d (j+2) ω)*μ[fun ξ => max 0 (Z ξ-((j+3 : ℕ) : ℝ)) | m] ω := by
    simp only [Nat.cast_add, Nat.cast_ofNat]
  rw [he] at hS
  linarith

end OracleTemplate.ScalarStopLoss
