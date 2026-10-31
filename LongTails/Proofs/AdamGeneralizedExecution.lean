import LongTails.Proofs.AdamGeneralizedExpectation
import LongTails.Proofs.AdamHeavyTailedDescent
open MeasureTheory
namespace LongTails.Proofs.AdamGeneralizedExecution
open OracleTemplate.Adam LongTails.Algorithms.GeneralizedSmoothAdam
open AdamGeneralizedTrajectory AdamGeneralizedExpectation
lemma measurable_selected_point {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {g : Point d → Ω → Point d} (hg : Measurable (Function.uncurry g))
    (β ρ η τ vinit : ℝ) (x0 : Point d) (n : ℕ) :
    Measurable (fun z : Fin (n + 1) × (ℕ → Ω) => (trajectory g β ρ η τ vinit x0 z.2 z.1.val).1) :=
  measurable_from_prod_countable_right fun i => (measurable_trajectory hg β ρ η τ vinit x0 i.val).fst

lemma integrable_selected_square {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure (ℕ → Ω)) [IsFiniteMeasure P] {g : Point d → Ω → Point d}
    {h : Point d → Point d} (hg : Measurable (Function.uncurry g)) (hh : Measurable h)
    (β ρ η τ vinit : ℝ) (x0 : Point d) (n : ℕ)
    (hi : ∀ t < n + 1, Integrable (fun ξ => ‖h (trajectory g β ρ η τ vinit x0 ξ t).1‖ ^ 2) P) :
    Integrable (fun z : Fin (n + 1) × (ℕ → Ω) => ‖h (trajectory g β ρ η τ vinit x0 z.2 z.1.val).1‖ ^ 2)
      ((PMF.uniformOfFintype (Fin (n + 1))).toMeasure.prod P) := by
  apply (integrable_prod_iff ((hh.comp (measurable_selected_point hg β ρ η τ vinit x0 n)).norm.pow_const 2).aestronglyMeasurable).2
  exact ⟨Filter.Eventually.of_forall (fun i => hi i.val i.isLt), Integrable.of_finite⟩

lemma integral_selected_square {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure (ℕ → Ω)) [IsFiniteMeasure P] {g : Point d → Ω → Point d}
    {h : Point d → Point d} (hg : Measurable (Function.uncurry g)) (hh : Measurable h)
    (β ρ η τ vinit : ℝ) (x0 : Point d) (n : ℕ)
    (hi : ∀ t < n + 1, Integrable (fun ξ => ‖h (trajectory g β ρ η τ vinit x0 ξ t).1‖ ^ 2) P) :
    (∫ z : Fin (n + 1) × (ℕ → Ω), ‖h (trajectory g β ρ η τ vinit x0 z.2 z.1.val).1‖ ^ 2
      ∂((PMF.uniformOfFintype (Fin (n + 1))).toMeasure.prod P)) =
      ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ t ∈ Finset.range (n + 1), ∫ ξ, ‖h (trajectory g β ρ η τ vinit x0 ξ t).1‖ ^ 2 ∂P := by
  rw [integral_prod _ (integrable_selected_square P hg hh β ρ η τ vinit x0 n hi),
    OracleTemplate.MixedNoise.integral_uniform_finite, Fintype.card_fin,
    Fin.sum_univ_eq_sum_range (fun t => ∫ ξ, ‖h (trajectory g β ρ η τ vinit x0 ξ t).1‖ ^ 2 ∂P)]
set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
lemma tuned_trajectory_accuracy (q : LongTails.Setups.GeneralizedSmoothAdam.Params)
    (P : Measure q.Ω) [IsProbabilityMeasure P] {g : Point q.d → q.Ω → Point q.d}
    {f : Point q.d → ℝ} (hvalid : LongTails.Setups.GeneralizedSmoothAdam.spec.valid q)
    (hf : ∀ x, HasGradientAt f (gradient f x) x)
    (hs : ∀ x y, q.L1 * ‖y - x‖ ≤ 1 →
      ‖gradient f y - gradient f x‖ ≤ (q.L0 + q.L1 * ‖gradient f x‖) * ‖y - x‖)
    (hgap : ∀ x, f q.x0 - f x ≤ q.Δ)
    (hg : Measurable (Function.uncurry g)) (hi : ∀ x, Integrable (g x) P)
    (hmean : ∀ x, (∫ ω, g x ω ∂P) = gradient f x)
    (h2 : ∀ x, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ 2) P)
    (hvar : ∀ x, (∫ ω, ‖g x ω - gradient f x‖ ^ 2 ∂P) ≤ q.σ ^ 2)
    {T : ℕ} (hbudget : 2 ^ 100 * (q.d + 1) ^ 2 * (1 + q.L0 + q.L1) ^ 10 * (1 + q.σ ^ 2) *
      (1 + q.Δ) ^ 12 / ((1 - q.β) ^ 4 * q.ε ^ 4) + 2 / (1 - q.β) ≤ (T : ℝ))
    (ω0 : q.Ω) :
    Integrable (fun ξ => gradientAverage (gradient f) g q.β (1 / T) (stepScale q / Real.sqrt T)
      1 (1 + q.σ ^ 2) q.x0 ξ T) (Measure.infinitePi (fun _ : ℕ => P)) ∧
    (∫ ξ, gradientAverage (gradient f) g q.β (1 / T) (stepScale q / Real.sqrt T)
      1 (1 + q.σ ^ 2) q.x0 ξ T ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ q.ε ^ 2 := by
  rcases hvalid with ⟨hL0, hL1, hσ, hΔ, hε, hβ, hβ1⟩
  let K := 4 * (1 + q.L0 + q.L1)
  let lower := f q.x0 - q.Δ
  let a := stepScale q
  have hK4 : 4 ≤ K := by dsimp [K]; linarith
  have hK : 0 ≤ K := by linarith
  have hb : 0 < 1 - q.β := by linarith
  have hmain : 0 ≤ 2 ^ 100 * (q.d + 1) ^ 2 * (1 + q.L0 + q.L1) ^ 10 * (1 + q.σ ^ 2) *
      (1 + q.Δ) ^ 12 / ((1 - q.β) ^ 4 * q.ε ^ 4) := by positivity
  have hm : 2 / (1 - q.β) ≤ (T : ℝ) := (le_add_of_nonneg_left hmain).trans hbudget
  have ht := AdamGeneralizedParameters.horizon_memory hβ hβ1 hm
  have hTr : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have htune := AdamGeneralizedParameters.scale_envelopes (d := q.d) hβ hβ1 hK
  have ha : 0 < a := htune.1
  have hlower (x) : lower ≤ f x := by dsimp [lower]; linarith only [hgap x]
  have hgrad (x) : ‖gradient f x‖ ≤ K * (1 + f x - lower) :=
    AdamLogGeometry.gradient_gap_linear hL0 hL1 hf hs hlower x
  have hgeom := AdamGeneralizedParameters.geometry_scale hL0 hL1
  have hp := trajectory_gradient_bound P hL0 hL1 hK4 hgeom.2.1 hf hlower hs hgrad hgeom.2.2 hβ hβ1 ha
    hg hi hmean h2 hvar ht.1 ht.2 htune.2.2.1 htune.2.2.2 q.x0 ω0
  refine ⟨hp.1, hp.2.trans ?_⟩
  have hΦ : 1 + f q.x0 - lower = 1 + q.Δ := by dsimp [lower]; ring
  rw [hΦ]
  have hrate := AdamGeneralizedParameters.simplify_rate (d := q.d) (v := 1 + q.σ ^ 2)
    (Φ := 1 + q.Δ) hK4 hβ1 (Real.sqrt_pos.2 hTr)
  have he : (64 * K * Real.sqrt (1 + q.σ ^ 2) * (1 + q.Δ) ^ 2) *
      (2048 * K ^ 2 * (1 + q.Δ) ^ 4) / (a * Real.sqrt T) =
      2 ^ 17 * K ^ 3 * Real.sqrt (1 + q.σ ^ 2) * (1 + q.Δ) ^ 6 / (a * Real.sqrt T) := by ring
  change _ / (a * Real.sqrt T) ≤ _ at hrate
  rw [he] at hrate
  apply hrate.trans
  have hfrac : 2 ^ 100 * (q.d + 1) ^ 2 * (1 + q.L0 + q.L1) ^ 10 * (1 + q.σ ^ 2) *
      (1 + q.Δ) ^ 12 / ((1 - q.β) ^ 4 * q.ε ^ 4) ≤ (T : ℝ) := by
    have hz : 0 ≤ 2 / (1 - q.β) := by positivity
    exact (le_add_of_nonneg_right hz).trans hbudget
  exact AdamGeneralizedParameters.horizon_accuracy hβ1 hε hTr hfrac

set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
lemma execution_accuracy (q : LongTails.Setups.GeneralizedSmoothAdam.Params)
    (p : ProbabilityMeasure q.Ω) (P : ProbabilityMeasure (ℕ → q.Ω))
    (h_samples : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → q.Ω) => ξ k) (p : Measure q.Ω) (P : Measure (ℕ → q.Ω)))
    {g : Point q.d → q.Ω → Point q.d}
    {f : Point q.d → ℝ} (hvalid : LongTails.Setups.GeneralizedSmoothAdam.spec.valid q)
    (hf : ∀ x, HasGradientAt f (gradient f x) x)
    (hs : ∀ x y, q.L1 * ‖y - x‖ ≤ 1 →
      ‖gradient f y - gradient f x‖ ≤ (q.L0 + q.L1 * ‖gradient f x‖) * ‖y - x‖)
    (hgap : ∀ x, f q.x0 - f x ≤ q.Δ)
    (hg : Measurable (Function.uncurry g)) (hi : ∀ x, Integrable (g x) p)
    (hmean : ∀ x, (∫ ω, g x ω ∂p) = gradient f x)
    (h2 : ∀ x, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ 2) p)
    (hvar : ∀ x, (∫ ω, ‖g x ω - gradient f x‖ ^ 2 ∂p) ≤ q.σ ^ 2)
    {T : ℕ} (hbudget : 2 ^ 100 * (q.d + 1) ^ 2 * (1 + q.L0 + q.L1) ^ 10 * (1 + q.σ ^ 2) *
      (1 + q.Δ) ^ 12 / ((1 - q.β) ^ 4 * q.ε ^ 4) + 2 / (1 - q.β) ≤ (T : ℝ))
    :
    let O : OracleTemplate.Oracle (Point q.d) (Point q.d) :=
      { Seed := fun _ => q.Ω, law := P, answer := fun _ (_, x) ω => g x ω }
    let out := fun z : (algorithm q T).Seed × (ℕ → q.Ω) => output q T O z.1 z.2
    let Q := ((algorithm q T).law : Measure _).prod (P : Measure (ℕ → q.Ω))
    Measurable out ∧ Integrable (fun z => ‖gradient f (out z)‖ ^ 2) Q ∧
      (∫ z, ‖gradient f (out z)‖ ^ 2 ∂Q) ≤ q.ε ^ 2 := by
  have hβ := hvalid.2.2.2.2.2.1
  have hβ1 := hvalid.2.2.2.2.2.2
  have hb : 0 < 1 - q.β := by linarith
  have hnon : 0 ≤ 2 ^ 100 * (q.d + 1) ^ 2 * (1 + q.L0 + q.L1) ^ 10 * (1 + q.σ ^ 2) *
      (1 + q.Δ) ^ 12 / ((1 - q.β) ^ 4 * q.ε ^ 4) := by positivity
  have hm : 2 / (1 - q.β) ≤ (T : ℝ) := (le_add_of_nonneg_left hnon).trans hbudget
  have ht := AdamGeneralizedParameters.horizon_memory hβ hβ1 hm
  have hT : 0 < T := by omega
  have hn : T - 1 + 1 = T := by omega
  let η := stepScale q / Real.sqrt T
  let v := 1 + q.σ ^ 2
  let O : OracleTemplate.Oracle (Point q.d) (Point q.d) :=
    { Seed := fun _ => q.Ω, law := P, answer := fun _ (_, x) ω => g x ω }
  have hout (k : (algorithm q T).Seed) (ξ : ℕ → q.Ω) : output q T O k ξ =
      (trajectory g q.β (1 / T) η 1 v q.x0 ξ k.val).1 := by
    unfold LongTails.Algorithms.GeneralizedSmoothAdam.output algorithm
    have he : (fun _ : Fin 1 => T) = (fun _ => T - 1 + 1) := by funext i; omega
    rw [he]
    exact AdamGeneralizedTrajectory.execute_trajectory g P q.β (1 / T) η 1 v (T - 1) q.x0 k ξ
  dsimp only [O] at hout
  dsimp only
  simp_rw [hout]
  change Measurable (fun z : Fin (T - 1 + 1) × (ℕ → q.Ω) => (trajectory g q.β (1 / T) η 1 v q.x0 z.2 z.1.val).1) ∧
    Integrable (fun z : Fin (T - 1 + 1) × (ℕ → q.Ω) => ‖gradient f (trajectory g q.β (1 / T) η 1 v q.x0 z.2 z.1.val).1‖ ^ 2)
      ((PMF.uniformOfFintype (Fin (T - 1 + 1))).toMeasure.prod (P : Measure _)) ∧ _
  have hPQ := iid_sequence_law h_samples
  rw [hPQ]
  let Q := Measure.infinitePi (fun _ : ℕ => (p : Measure q.Ω))
  let ω0 : q.Ω := Classical.choice p.nonempty
  have hp := tuned_trajectory_accuracy q (p : Measure q.Ω) hvalid hf hs hgap hg hi hmean h2 hvar hbudget ω0
  have hh := (AdamLogGeometry.gradient_continuous hvalid.2.1 hs).measurable
  have hit (t : ℕ) (htt : t < T - 1 + 1) :
      Integrable (fun ξ => ‖gradient f (trajectory g q.β (1 / T) η 1 v q.x0 ξ t).1‖ ^ 2) Q :=
    integrable_individual_square Q hg hh q.β (1 / T) η 1 v q.x0 hT hp.1 (by omega)
  refine ⟨measurable_selected_point hg q.β (1 / T) η 1 v q.x0 (T - 1),
    integrable_selected_square Q hg hh q.β (1 / T) η 1 v q.x0 (T - 1) hit, ?_⟩
  change (∫ z : Fin (T - 1 + 1) × (ℕ → q.Ω),
    ‖gradient f (trajectory g q.β (1 / T) η 1 v q.x0 z.2 z.1.val).1‖ ^ 2
    ∂((PMF.uniformOfFintype (Fin (T - 1 + 1))).toMeasure.prod Q)) ≤ q.ε ^ 2
  rw [integral_selected_square Q hg hh q.β (1 / T) η 1 v q.x0 (T - 1) hit, hn]
  have he : (∫ ξ, gradientAverage (gradient f) g q.β (1 / T) η 1 v q.x0 ξ T ∂Q) =
      (∑ t ∈ Finset.range T, ∫ ξ, ‖gradient f (trajectory g q.β (1 / T) η 1 v q.x0 ξ t).1‖ ^ 2 ∂Q) / T := by
    unfold gradientAverage
    rw [integral_div, integral_finsetSum _ (fun t htt => hit t (by simpa only [hn] using Finset.mem_range.1 htt))]
  rw [he] at hp
  simpa only [div_eq_mul_inv, mul_comm] using hp.2

end LongTails.Proofs.AdamGeneralizedExecution
