import LongTails.Setups.EuclideanStrongGrowthMeanSquared
import LongTails.TemplateLowerBound
import LongTails.Proofs.Execution
import LongTails.Proofs.AdaptiveIID
import LongTails.Proofs.SmoothConvexFiniteLowerBound
import LongTails.Proofs.StrongGrowthThinning
import LongTails.Proofs.PolynomialMixingLowerBound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory ProbabilityTheory OracleTemplate
open scoped BigOperators

namespace LongTails.Proofs.StrongGrowthMeanSquaredLowerBound

open LongTails.Setups.EuclideanStrongGrowthMeanSquared
open LongTails.Proofs.SmoothConvexFiniteWall LongTails.Proofs.SmoothConvexFiniteAveraging
open LongTails.Proofs.FiniteSumNondualLowerAveraging LongTails.Proofs.FiniteSumNondualLowerBound
open LongTails.Proofs.StrongGrowthThinning
open LongTails.Proofs.PolynomialMixingLowerBound (integral_two_atoms integrable_two_atoms
  twoAtomLaw rareOracle rareOracle_mean rareOracle_measurable)

lemma average_gap_of_dimension {d k : ℕ} {S : Type*} (L R ε : ℝ) (hL : 0 ≤ L) (hR : 0 < R)
    (hd : 65536 * (k + 1) ^ 5 ≤ d)
    (hgap : 65536 * ((k : ℝ) + 1) ^ 2 * ε ≤ L * R ^ 2)
    (query output : S → EuclideanSpace ℝ (Fin d))
    (update : S → EuclideanSpace ℝ (Fin d) → S) (initial : S) :
    8 * ε * Fintype.card (CoordinateWords d k) ≤
      2 * ∑ w : CoordinateWords d k,
        objective L R (R / Real.sqrt ((k : ℝ) + 1) / (8 * ((k : ℝ) + 1)))
          (R / Real.sqrt ((k : ℝ) + 1)) (coordinateEmbedding w)
          (output ((fun s => update s (field L R
            (R / Real.sqrt ((k : ℝ) + 1) / (8 * ((k : ℝ) + 1)))
            (R / Real.sqrt ((k : ℝ) + 1)) (coordinateEmbedding w) (query s)))^[k] initial)) := by
  let K : ℝ := (k : ℝ) + 1
  let a := R / Real.sqrt K
  let δ := a / (8 * K)
  let D := 32768 * K ^ 5
  have hK : 0 < K := by dsimp [K]; positivity
  have hKone : 1 ≤ K := by dsimp [K]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have ha : 0 < a := div_pos hR (Real.sqrt_pos.mpr hK)
  have hδ : 0 < δ := div_pos ha (by positivity)
  have ha_sq : a ^ 2 = R ^ 2 / K := by
    dsimp [a]
    rw [div_pow, Real.sq_sqrt hK.le]
  have hrad : K * a ^ 2 = R ^ 2 := by rw [ha_sq, mul_div_cancel₀ _ hK.ne']
  have hscale : K * δ = a / 8 := by dsimp [δ]; field_simp
  have hD : 0 < D := by dsimp [D]; positivity
  have hpow : K ≤ K ^ 5 := by simpa using pow_le_pow_right₀ hKone (by decide : 1 ≤ 5)
  have hd' : 65536 * K ^ 5 ≤ (d : ℝ) := by dsimp [K]; exact_mod_cast hd
  have hDs : D + (k + 1 : ℕ) ≤ (d : ℝ) := by
    rw [Nat.cast_add, Nat.cast_one]
    change D + K ≤ (d : ℝ)
    dsimp [D]
    nlinarith
  have hδsq : (δ / 4) ^ 2 = R ^ 2 / (1024 * K ^ 3) := by
    dsimp [δ]
    rw [div_pow, div_pow, ha_sq]
    field_simp
    ring
  have hratio : (3 * R) ^ 2 / (δ / 4) ^ 2 = 9216 * K ^ 3 := by
    rw [hδsq]
    field_simp
    ring
  have hsize : 2 * (k + 1 : ℕ) ^ 2 * ((3 * R) ^ 2 / (δ / 4) ^ 2) ≤ D := by
    rw [hratio, Nat.cast_add, Nat.cast_one]
    change 2 * K ^ 2 * (9216 * K ^ 3) ≤ 32768 * K ^ 5
    nlinarith [pow_pos hK 5]
  have h := execution_average_gap L R δ a D hL hR hδ ha.le hrad.le hscale.le hD hDs hsize
    query output update initial
  have hg : 8 * ε ≤ L * a ^ 2 / (8192 * K) := by
    apply (le_div_iff₀ (by positivity : 0 < 8192 * K)).mpr
    rw [ha_sq]
    have hgap' : 65536 * K ^ 2 * ε ≤ L * R ^ 2 := hgap
    have he : L * (R ^ 2 / K) = L * R ^ 2 / K := by ring
    rw [he, le_div_iff₀ hK]
    nlinarith
  have hc : (0 : ℝ) ≤ Fintype.card (CoordinateWords d k) := Nat.cast_nonneg _
  calc
    8 * ε * Fintype.card (CoordinateWords d k) ≤
        (L * a ^ 2 / (8192 * K)) * Fintype.card (CoordinateWords d k) :=
      mul_le_mul_of_nonneg_right hg hc
    _ ≤ _ := h

section Atoms

variable {Ω F : Type*} [MeasurableSpace Ω] [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma rare_variance (a b : Ω) (hab : a ≠ b) (ha : MeasurableSet ({a} : Set Ω))
    (hb : MeasurableSet ({b} : Set Ω)) (p : unitInterval) (hp : 0 < (p : ℝ))
    {Q : Type*} (G : Q → F) (x : Q) :
    (∫ z, ‖rareOracle a p G x z - G x‖ ^ 2 ∂bernoulliMeasure a b p) =
      ((p : ℝ)⁻¹ - 1) * ‖G x‖ ^ 2 := by
  classical
  have hr : rareOracle a p G x a - G x = ((p : ℝ)⁻¹ - 1) • G x := by
    simp [rareOracle, sub_smul]
  have hc : rareOracle a p G x b - G x = -G x := by
    simp [rareOracle, Ne.symm hab]
  rw [integral_two_atoms a b ha hb p, hr, hc, norm_neg, norm_smul, Real.norm_eq_abs, mul_pow,
    sq_abs]
  simp only [smul_eq_mul]
  have hp' : (p : ℝ) ≠ 0 := hp.ne'
  field_simp
  ring

lemma rare_mean_square (a b : Ω) (hab : a ≠ b) (ha : MeasurableSet ({a} : Set Ω))
    (hb : MeasurableSet ({b} : Set Ω)) (p : unitInterval) (hp : 0 < (p : ℝ))
    {Q : Type*} (G : Q → F) (x y : Q) :
    (∫ z, ‖rareOracle a p G x z - rareOracle a p G y z‖ ^ 2 ∂bernoulliMeasure a b p) =
      (p : ℝ)⁻¹ * ‖G x - G y‖ ^ 2 := by
  classical
  have hr : rareOracle a p G x a - rareOracle a p G y a = (p : ℝ)⁻¹ • (G x - G y) := by
    simp [rareOracle, smul_sub]
  have hc : rareOracle a p G x b - rareOracle a p G y b = 0 := by
    simp [rareOracle, Ne.symm hab]
  rw [integral_two_atoms a b ha hb p, hr, hc, norm_zero, norm_smul, Real.norm_eq_abs, mul_pow,
    sq_abs]
  simp only [smul_eq_mul]
  have hp' : (p : ℝ) ≠ 0 := hp.ne'
  field_simp
  ring

end Atoms

section Coins

open Classical

variable {Ω : Type*}

noncomputable def coins (a : Ω) (ξ : ℕ → Ω) : ℕ → Bool := fun j => decide (ξ j = a)

noncomputable def coinCount (a : Ω) (b : ℕ) (ξ : ℕ → Ω) : ℝ :=
  ∑ j ∈ Finset.range b, ({ζ : ℕ → Ω | ζ j = a}).indicator (fun _ => (1 : ℝ)) ξ

lemma heads_coins (a : Ω) (b : ℕ) (ξ : ℕ → Ω) :
    (heads (coins a ξ) b : ℝ) = coinCount a b ξ := by
  unfold heads coinCount
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : ξ j = a <;> simp [coins, h, Set.indicator]

lemma measurableSet_coordinate [MeasurableSpace Ω] (a : Ω) (ha : MeasurableSet ({a} : Set Ω)) (j : ℕ) :
    MeasurableSet {ζ : ℕ → Ω | ζ j = a} := by
  have h : MeasurableSet ((fun ζ : ℕ → Ω => ζ j) ⁻¹' {a}) := measurable_pi_apply j ha
  exact h

lemma measurable_coinCount [MeasurableSpace Ω] (a : Ω) (ha : MeasurableSet ({a} : Set Ω)) (b : ℕ) :
    Measurable (coinCount a b) := by
  unfold coinCount
  apply Finset.measurable_sum
  intro j _
  exact measurable_const.indicator (measurableSet_coordinate a ha j)

lemma coinCount_nonneg (a : Ω) (b : ℕ) (ξ : ℕ → Ω) : 0 ≤ coinCount a b ξ := by
  unfold coinCount
  apply Finset.sum_nonneg
  intro j _
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

lemma integral_coinCount [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (a : Ω)
    (ha : MeasurableSet ({a} : Set Ω)) (b : ℕ) :
    (∫ ξ, coinCount a b ξ ∂(Measure.infinitePi fun _ : ℕ => μ)) = b * μ.real {a} := by
  unfold coinCount
  rw [integral_finsetSum]
  · have hj (j : ℕ) : (∫ ξ, ({ζ : ℕ → Ω | ζ j = a}).indicator (fun _ => (1 : ℝ)) ξ
        ∂(Measure.infinitePi fun _ : ℕ => μ)) = μ.real {a} := by
      rw [integral_indicator_const _ (measurableSet_coordinate a ha j), smul_eq_mul, mul_one]
      have hm := Measure.infinitePi_map_eval (fun _ : ℕ => μ) j
      have hx := congrArg (fun ν : Measure Ω => ν.real {a}) hm
      rw [map_measureReal_apply (measurable_pi_apply j) ha] at hx
      exact hx
    simp only [hj, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  · intro j _
    exact (integrable_const (1 : ℝ)).indicator (measurableSet_coordinate a ha j)

lemma coinCount_tail [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (a : Ω)
    (ha : MeasurableSet ({a} : Set Ω)) (b : ℕ) (t : ℝ) (ht : 0 < t) :
    (Measure.infinitePi fun _ : ℕ => μ).real {ξ | t ≤ coinCount a b ξ} ≤
      b * μ.real {a} / t := by
  have h := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun ξ => coinCount_nonneg a b ξ))
    (Integrable.of_bound (measurable_coinCount a ha b).aestronglyMeasurable (b : ℝ)
      (Filter.Eventually.of_forall fun ξ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (coinCount_nonneg a b ξ)]
        unfold coinCount
        calc
          _ ≤ ∑ _j ∈ Finset.range b, (1 : ℝ) := Finset.sum_le_sum fun j _ =>
            Set.indicator_le_self' (fun _ _ => zero_le_one) ξ
          _ = b := by simp))
    t (μ := Measure.infinitePi fun _ : ℕ => μ)
  rw [integral_coinCount μ a ha b] at h
  rw [le_div_iff₀ ht]
  linarith

end Coins


section Numerics

lemma budget_facts (Lbar Γ R ε : ℝ) (hL : 0 < Lbar) (hR : 0 < R) (hε : 0 < ε)
    (hreg : 262144 * Real.sqrt (1 + Γ ^ 2) * ε ≤ Lbar * R ^ 2) (n : ℕ)
    (hn : (n : ℝ) ≤ Real.sqrt ((1 + Γ ^ 2) * Real.sqrt (1 + Γ ^ 2) * Lbar * R ^ 2 / ε) / 8192) :
    65536 * (((2 * ⌊Real.sqrt (Lbar * R ^ 2 / (Real.sqrt (1 + Γ ^ 2) * ε)) / 1024⌋₊ : ℕ) : ℝ)
        + 1) ^ 2 * ε ≤ Lbar / Real.sqrt (1 + Γ ^ 2) * R ^ 2 ∧
      65536 * ((((2 * ⌊Real.sqrt (Lbar * R ^ 2 / (Real.sqrt (1 + Γ ^ 2) * ε)) / 1024⌋₊ : ℕ) : ℝ)
        + 1) ^ 5) ≤ (Lbar * R ^ 2 / (Real.sqrt (1 + Γ ^ 2) * ε)) ^ 3 ∧
      (n : ℝ) * (1 + Γ ^ 2)⁻¹ ≤
        ((⌊Real.sqrt (Lbar * R ^ 2 / (Real.sqrt (1 + Γ ^ 2) * ε)) / 1024⌋₊ : ℝ) + 1) / 8 := by
  set ρ := 1 + Γ ^ 2 with hρdef
  set s := Real.sqrt ρ with hsdef
  have hρ : 1 ≤ ρ := by rw [hρdef]; nlinarith [sq_nonneg Γ]
  have hρ0 : 0 < ρ := by linarith
  have hs : 0 < s := Real.sqrt_pos.mpr hρ0
  have hss : s ^ 2 = ρ := Real.sq_sqrt hρ0.le
  set T := Lbar * R ^ 2 / (s * ε) with hTdef
  have hT : 262144 ≤ T := by
    rw [hTdef, le_div_iff₀ (by positivity)]
    linarith
  set u := Real.sqrt T with hudef
  have hT0 : 0 ≤ T := by linarith
  have huu : u ^ 2 = T := Real.sq_sqrt hT0
  have hu : 512 ≤ u := by
    rw [hudef]
    rw [show (512 : ℝ) = Real.sqrt 262144 by
      rw [show (262144 : ℝ) = 512 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hT
  set M := ⌊u / 1024⌋₊ with hMdef
  have hM : (M : ℝ) ≤ u / 1024 := Nat.floor_le (by positivity)
  have hM1 : u / 1024 < (M : ℝ) + 1 := Nat.lt_floor_add_one _
  have hK : (((2 * M : ℕ) : ℝ) + 1) ≤ u / 256 := by
    push_cast
    nlinarith
  have hK0 : 0 ≤ (((2 * M : ℕ) : ℝ) + 1) := by positivity
  refine ⟨?_, ?_, ?_⟩
  · have hsq := pow_le_pow_left₀ hK0 hK 2
    have hLR : Lbar / s * R ^ 2 = T * ε := by
      rw [hTdef]; field_simp
    rw [hLR]
    have : 65536 * (((2 * M : ℕ) : ℝ) + 1) ^ 2 ≤ T := by
      calc
        _ ≤ 65536 * (u / 256) ^ 2 := by gcongr
        _ = u ^ 2 := by ring
        _ = T := huu
    nlinarith
  · have h5 := pow_le_pow_left₀ hK0 hK 5
    have hu1 : 1 ≤ u := by linarith
    calc
      65536 * (((2 * M : ℕ) : ℝ) + 1) ^ 5 ≤ 65536 * (u / 256) ^ 5 := by gcongr
      _ ≤ u ^ 6 := by
        have h6 : u ^ 5 ≤ u ^ 6 := pow_le_pow_right₀ hu1 (by norm_num)
        have : 65536 * (u / 256) ^ 5 = u ^ 5 / 16777216 := by ring
        rw [this]
        have hp5 : 0 ≤ u ^ 5 := by positivity
        linarith
      _ = T ^ 3 := by rw [← huu]; ring
  · have hroot : Real.sqrt (ρ * s * Lbar * R ^ 2 / ε) = ρ * u := by
      have he : ρ * s * Lbar * R ^ 2 / ε = (ρ * u) ^ 2 := by
        rw [mul_pow, huu, hTdef, ← hss]
        field_simp
      rw [he, Real.sqrt_sq (by positivity)]
    rw [hroot] at hn
    have hinv : (n : ℝ) * ρ⁻¹ ≤ u / 8192 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hρ0]
      nlinarith
    nlinarith

end Numerics

section Hard

abbrev Pt (d : ℕ) := EuclideanSpace ℝ (Fin d)

noncomputable def hardOracle {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (a b : Ω) (p : unitInterval)
    (G : Pt d → Pt d) : Oracle (Pt d × Pt d) (Pt d × Pt d) where
  Seed := fun _ => Ω
  law := ⟨Measure.infinitePi fun _ : ℕ => (bernoulliMeasure a b p : Measure Ω), inferInstance⟩
  answer := fun _ q ω => (rareOracle a p G q.2.1 ω, rareOracle a p G q.2.2 ω)

lemma field_continuous {d k : ℕ} (L R δ a : ℝ) (hL : 0 ≤ L) (hR : 0 < R) (hδ : 0 ≤ δ)
    (π : Fin (k + 1) ↪ Fin d) (ha : ((k : ℝ) + 1) * a ^ 2 ≤ R ^ 2) :
    Continuous (field L R δ a π) := by
  have hl : LipschitzWith ⟨L, hL⟩ (field L R δ a π) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, dist_eq_norm]
    exact field_lipschitz L R δ a hL hR hδ π ha x y
  exact hl.continuous

lemma hard_admissible (q : Params) {k : ℕ} (π : Fin (k + 1) ↪ Fin q.d) (L δ a' : ℝ)
    (hL : 0 ≤ L) (hR : 0 < q.R) (hδ : 0 ≤ δ) (ha' : ((k : ℝ) + 1) * a' ^ 2 ≤ q.R ^ 2)
    (a b : q.Ω) (hab : a ≠ b) (ha : MeasurableSet ({a} : Set q.Ω))
    (hb : MeasurableSet ({b} : Set q.Ω)) (p : unitInterval) (hp : 0 < (p : ℝ))
    (hΓ : (p : ℝ)⁻¹ - 1 ≤ q.Γ ^ 2) (hLbar : (p : ℝ)⁻¹ * L ^ 2 ≤ q.Lbar ^ 2) :
    spec.admissible q (fun x : Pt q.d => objective L q.R δ a' π (x - q.x0))
      (hardOracle a b p (fun x : Pt q.d => field L q.R δ a' π (x - q.x0))) := by
  set f : Pt q.d → ℝ := fun x => objective L q.R δ a' π (x - q.x0) with hfdef
  set G : Pt q.d → Pt q.d := fun x => field L q.R δ a' π (x - q.x0) with hGdef
  have hgrad (x : Pt q.d) : HasGradientAt f (G x) x :=
    LongTails.Proofs.SmoothConvexFiniteLowerBound.gradient_translate q.x0 _ _
      (objective_gradient L q.R δ a' hR hδ π) x
  have hgeq (x : Pt q.d) : gradient f x = G x := (hgrad x).gradient
  have hGcont : Continuous G :=
    (field_continuous L q.R δ a' hL hR hδ π ha').comp (continuous_id.sub continuous_const)
  have hGlip (x y : Pt q.d) : ‖G x - G y‖ ≤ L * ‖x - y‖ := by
    have h := field_lipschitz L q.R δ a' hL hR hδ π ha' (x - q.x0) (y - q.x0)
    simpa only [hGdef, sub_sub_sub_cancel_right] using h
  have hmin := objective_minimum L q.R δ a' hL hR hδ π ha'
  refine ⟨rareOracle a p G, twoAtomLaw a b p,
    ⟨Measure.infinitePi fun _ : ℕ => (bernoulliMeasure a b p : Measure q.Ω), inferInstance⟩,
    OracleTemplate.StochasticGeneralized.infinitePi_iid _, rfl,
    LongTails.Proofs.SmoothConvexFiniteLowerBound.convex_translate q.x0 _
      (objective_convex L q.R δ a' hL hR hδ π), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [hgeq]
    exact hgrad x
  · refine ⟨q.x0 + FiniteSumNondualLowerComponents.hiddenPoint π a', ?_, ?_⟩
    · intro x _
      change f (q.x0 + FiniteSumNondualLowerComponents.hiddenPoint π a') ≤ f x
      simp only [hfdef, add_sub_cancel_left]
      exact hmin.2 (Set.mem_univ (x - q.x0))
    · change ‖q.x0 - (q.x0 + FiniteSumNondualLowerComponents.hiddenPoint π a')‖ ≤ q.R
      rw [sub_add_cancel_left, norm_neg]
      exact hiddenPoint_radius q.R a' hR.le π ha'
  · exact rareOracle_measurable a ha p G hGcont.measurable
  · intro x
    exact integrable_two_atoms a b ha hb p _
  · intro x
    change (∫ z, rareOracle a p G x z ∂bernoulliMeasure a b p) = gradient f x
    rw [rareOracle_mean a b hab ha hb p hp G x, hgeq]
  · intro x
    exact integrable_two_atoms a b ha hb p _
  · intro x
    change (∫ z, ‖rareOracle a p G x z - gradient f x‖ ^ 2 ∂bernoulliMeasure a b p) ≤
      q.Γ ^ 2 * ‖gradient f x‖ ^ 2
    rw [hgeq, rare_variance a b hab ha hb p hp G x]
    exact mul_le_mul_of_nonneg_right hΓ (sq_nonneg _)
  · intro x y
    exact integrable_two_atoms a b ha hb p _
  · intro x y
    change (∫ z, ‖rareOracle a p G x z - rareOracle a p G y z‖ ^ 2 ∂bernoulliMeasure a b p) ≤
      q.Lbar ^ 2 * ‖x - y‖ ^ 2
    rw [rare_mean_square a b hab ha hb p hp G x y]
    have h1 := pow_le_pow_left₀ (norm_nonneg _) (hGlip x y) 2
    have hpinv : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr hp.le
    calc
      (p : ℝ)⁻¹ * ‖G x - G y‖ ^ 2 ≤ (p : ℝ)⁻¹ * (L * ‖x - y‖) ^ 2 :=
        mul_le_mul_of_nonneg_left h1 hpinv
      _ = ((p : ℝ)⁻¹ * L ^ 2) * ‖x - y‖ ^ 2 := by ring
      _ ≤ q.Lbar ^ 2 * ‖x - y‖ ^ 2 := mul_le_mul_of_nonneg_right hLbar (sq_nonneg _)

open Classical in
lemma execute_hard {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (a b : Ω) (p : unitInterval)
    (G : Pt d → Pt d) (A : Algorithm (Pt d × Pt d) (Pt d × Pt d) (Pt d)) (n : ℕ) (s : A.Seed)
    (ξ : ℕ → Ω) :
    execute (hardOracle a b p G) A (fun _ => n) s ξ =
      A.output ((realStep A.update (coins a ξ)
        (fun st => ((p : ℝ)⁻¹ • G (A.query st).2.1, (p : ℝ)⁻¹ • G (A.query st).2.2)))^[n]
          (A.initial s, 0)).1 := by
  rw [execute_indexed_of_answer (hardOracle a b p G) A n s ξ
    (fun j q => (rareOracle a p G q.2.1 (ξ j), rareOracle a p G q.2.2 (ξ j))) (fun _ _ => rfl)]
  have hf : (fun sc : A.State × ℕ =>
      (A.update sc.1 (rareOracle a p G (A.query sc.1).2.1 (ξ sc.2),
        rareOracle a p G (A.query sc.1).2.2 (ξ sc.2)), sc.2 + 1)) =
      realStep A.update (coins a ξ)
        (fun st => ((p : ℝ)⁻¹ • G (A.query st).2.1, (p : ℝ)⁻¹ • G (A.query st).2.2)) := by
    funext sc
    by_cases h : ξ sc.2 = a
    · simp [realStep, coins, rareOracle, h]
    · simp [realStep, coins, rareOracle, h]
      rfl
  rw [hf]

end Hard

section Main

open Classical

theorem exists_failure (q : Params) (hq : spec.valid q)
    (A : Algorithm (Pt q.d × Pt q.d) (Pt q.d × Pt q.d) (Pt q.d)) (n : ℕ)
    (hn : (n : ℝ) ≤
      Real.sqrt ((1 + q.Γ ^ 2) * Real.sqrt (1 + q.Γ ^ 2) * q.Lbar * q.R ^ 2 / q.ε) / 8192) :
    ∃ (I : spec.Instance (spec.publicInput q))
      (O : Oracle (spec.Query (spec.publicInput q)) (spec.Reply (spec.publicInput q))),
      spec.admissible q I O ∧
        ¬ spec.successful q I
          (fun w : A.Seed × ((k : ℕ) → O.Seed k) => execute O A (fun _ => n) w.1 w.2)
          ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  obtain ⟨hL, hΓ, hR, hε, hreg0, hdim, a, b, hab, ha, hb⟩ := hq
  have hreg : 262144 * Real.sqrt (1 + q.Γ ^ 2) * q.ε ≤ q.Lbar * q.R ^ 2 := by
    have hs0 := Real.sqrt_nonneg (1 + q.Γ ^ 2)
    nlinarith
  obtain ⟨hgap, hpow, hcount⟩ := budget_facts q.Lbar q.Γ q.R q.ε hL hR hε hreg n hn
  set ρ := 1 + q.Γ ^ 2 with hρdef
  set s := Real.sqrt ρ with hsdef
  set M := ⌊Real.sqrt (q.Lbar * q.R ^ 2 / (s * q.ε)) / 1024⌋₊ with hMdef
  set k := 2 * M with hkdef
  have hρ : 1 ≤ ρ := by rw [hρdef]; nlinarith [sq_nonneg q.Γ]
  have hρ0 : 0 < ρ := by linarith
  have hs : 0 < s := Real.sqrt_pos.mpr hρ0
  have hss : s ^ 2 = ρ := Real.sq_sqrt hρ0.le
  set L' := q.Lbar / s with hL'def
  have hL' : 0 ≤ L' := by positivity
  let p : unitInterval := ⟨ρ⁻¹, inv_nonneg.mpr hρ0.le, inv_le_one_of_one_le₀ hρ⟩
  have hpval : (p : ℝ) = ρ⁻¹ := rfl
  have hp : 0 < (p : ℝ) := by rw [hpval]; positivity
  have hpinv : (p : ℝ)⁻¹ = ρ := by rw [hpval, inv_inv]
  have hΓp : (p : ℝ)⁻¹ - 1 ≤ q.Γ ^ 2 := by rw [hpinv, hρdef]; linarith
  have hLp : (p : ℝ)⁻¹ * L' ^ 2 ≤ q.Lbar ^ 2 := by
    rw [hpinv, hL'def, div_pow, hss]
    field_simp
    exact le_rfl
  have hd : 65536 * (k + 1) ^ 5 ≤ q.d := by
    have h1 : (65536 * ((k : ℝ) + 1) ^ 5) ≤ q.d := hpow.trans hdim
    exact_mod_cast h1
  set aa := q.R / Real.sqrt ((k : ℝ) + 1) with haadef
  set δδ := aa / (8 * ((k : ℝ) + 1)) with hδδdef
  have hK : 0 < (k : ℝ) + 1 := by positivity
  have haa : 0 < aa := div_pos hR (Real.sqrt_pos.mpr hK)
  have hδδ : 0 ≤ δδ := by positivity
  have hrad : ((k : ℝ) + 1) * aa ^ 2 ≤ q.R ^ 2 := by
    rw [haadef, div_pow, Real.sq_sqrt hK.le, mul_div_cancel₀ _ hK.ne']
  let F : CoordinateWords q.d k → Pt q.d → Pt q.d := fun w x =>
    field L' q.R δδ aa (coordinateEmbedding w) (x - q.x0)
  let f : CoordinateWords q.d k → Pt q.d → ℝ := fun w x =>
    objective L' q.R δδ aa (coordinateEmbedding w) (x - q.x0)
  let O : CoordinateWords q.d k → Oracle (Pt q.d × Pt q.d) (Pt q.d × Pt q.d) := fun w =>
    hardOracle a b p (F w)
  have hadm (w : CoordinateWords q.d k) : spec.admissible q (f w) (O w) :=
    hard_admissible q (coordinateEmbedding w) L' δδ aa hL' hR hδδ hrad a b hab ha hb p hp hΓp hLp
  by_contra hcon
  push Not at hcon
  let P : Measure (ℕ → q.Ω) := Measure.infinitePi fun _ : ℕ => (bernoulliMeasure a b p : Measure q.Ω)
  let Q : Measure (A.Seed × (ℕ → q.Ω)) := (A.law : Measure A.Seed).prod P
  let loss : CoordinateWords q.d k → A.Seed × (ℕ → q.Ω) → ℝ := fun w ω =>
    f w (execute (O w) A (fun _ => n) ω.1 ω.2)
  have hzero (w : CoordinateWords q.d k) (xstar : Pt q.d) (hm : IsMinOn (f w) Set.univ xstar) :
      f w xstar = 0 := by
    have hmin := objective_minimum L' q.R δδ aa hL' hR hδδ (coordinateEmbedding w) hrad
    apply le_antisymm
    · have hh := hm (Set.mem_univ (q.x0 + FiniteSumNondualLowerComponents.hiddenPoint
        (coordinateEmbedding w) aa))
      change f w xstar ≤ f w (q.x0 + _) at hh
      simp only [f, add_sub_cancel_left] at hh
      exact hh.trans_eq hmin.1
    · exact objective_nonneg L' q.R δδ aa hL' hR (coordinateEmbedding w) _
  have hsucc (w : CoordinateWords q.d k) : Integrable (loss w) Q ∧ (∫ ω, loss w ω ∂Q) ≤ q.ε := by
    obtain ⟨_, xstar, hm, hi, he⟩ := hcon (f w) (O w) (hadm w)
    have hz := hzero w xstar hm
    have hi' : Integrable (fun ω : A.Seed × (ℕ → q.Ω) =>
        f w (execute (O w) A (fun _ => n) ω.1 ω.2) - f w xstar) Q := hi
    have he' : (∫ ω, (f w (execute (O w) A (fun _ => n) ω.1 ω.2) - f w xstar) ∂Q) ≤ q.ε := he
    simp only [hz, sub_zero] at hi' he'
    exact ⟨hi', he'⟩
  set card := (Fintype.card (CoordinateWords q.d k) : ℝ) with hcarddef
  have hcard : 0 < card := by
    have hk1 : k + 1 ≤ q.d := by
      have : k + 1 ≤ 65536 * (k + 1) ^ 5 := by
        calc k + 1 ≤ (k + 1) ^ 5 := Nat.le_self_pow (by norm_num) _
          _ ≤ 65536 * (k + 1) ^ 5 := Nat.le_mul_of_pos_left _ (by norm_num)
      omega
    have hc := coordinateWords_card_pos q.d k hk1
    rw [hcarddef]
    exact_mod_cast hc
  let Gset : Set (A.Seed × (ℕ → q.Ω)) := {ω | coinCount a n ω.2 < (M : ℝ) + 1}
  have hGmeas : MeasurableSet Gset :=
    measurableSet_lt ((measurable_coinCount a ha n).comp measurable_snd) measurable_const
  have hpoint (ω : A.Seed × (ℕ → q.Ω)) :
      Gset.indicator (fun _ => 4 * q.ε * card) ω ≤ ∑ w, loss w ω := by
    by_cases hω : ω ∈ Gset
    · rw [Set.indicator_of_mem hω]
      have hheads : heads (coins a ω.2) n ≤ M := by
        have h1 : (heads (coins a ω.2) n : ℝ) < (M : ℝ) + 1 := by
          rw [heads_coins]; exact hω
        exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast h1)
      let qx : A.State → Pt q.d := fun st => (A.query st).2.1 - q.x0
      let qy : A.State → Pt q.d := fun st => (A.query st).2.2 - q.x0
      let T : Pt q.d → Pt q.d → Pt q.d × Pt q.d := fun v1 v2 => ((p : ℝ)⁻¹ • v1, (p : ℝ)⁻¹ • v2)
      have hrw (w : CoordinateWords q.d k) : loss w ω =
          objective L' q.R δδ aa (coordinateEmbedding w)
            ((fun z : A.State × ℕ × Option (Pt q.d) => A.output z.1 - q.x0)
              ((fun z => pairUpdate A.update (coins a ω.2) n T z
                (field L' q.R δδ aa (coordinateEmbedding w) (pairQuery qx qy z)))^[k]
                (pairInit A.update (coins a ω.2) n (A.initial ω.1)))) := by
        have he := pair_eq_real A.update (coins a ω.2) n M (A.initial ω.1) qx qy
          (field L' q.R δδ aa (coordinateEmbedding w)) T hheads
        show f w (execute (O w) A (fun _ => n) ω.1 ω.2) = _
        rw [execute_hard a b p (F w) A n ω.1 ω.2]
        exact congrArg (fun st => objective L' q.R δδ aa (coordinateEmbedding w)
          (A.output st - q.x0)) he.symm
      simp only [hrw]
      have hav := average_gap_of_dimension (S := A.State × ℕ × Option (Pt q.d)) L' q.R q.ε hL' hR
        hd hgap (pairQuery qx qy) (fun z => A.output z.1 - q.x0)
        (pairUpdate A.update (coins a ω.2) n T)
        (pairInit A.update (coins a ω.2) n (A.initial ω.1))
      linarith
    · rw [Set.indicator_of_notMem hω]
      exact Finset.sum_nonneg fun w _ =>
        objective_nonneg L' q.R δδ aa hL' hR (coordinateEmbedding w) _
  have hint : Integrable (fun ω => ∑ w, loss w ω) Q :=
    integrable_finsetSum Finset.univ fun w _ => (hsucc w).1
  have hlow := integral_mono ((integrable_const _).indicator hGmeas) hint hpoint
  rw [integral_indicator_const _ hGmeas, integral_finsetSum Finset.univ fun w _ => (hsucc w).1,
    smul_eq_mul] at hlow
  have hup : (∑ w, ∫ ω, loss w ω ∂Q) ≤ card * q.ε := by
    calc
      _ ≤ ∑ _w : CoordinateWords q.d k, q.ε := Finset.sum_le_sum fun w _ => (hsucc w).2
      _ = card * q.ε := by simp [hcarddef]
  have hprod : Q.real Gset = P.real {ξ | coinCount a n ξ < (M : ℝ) + 1} := by
    have hset : Gset = Set.univ ×ˢ {ξ : ℕ → q.Ω | coinCount a n ξ < (M : ℝ) + 1} := by
      ext ω; simp [Gset]
    rw [hset, measureReal_def, measureReal_def, Measure.prod_prod]
    simp
  have hatom : (bernoulliMeasure a b p : Measure q.Ω).real {a} = (p : ℝ) := by
    rw [bernoulliMeasure_real_apply p ha]
    simp [Ne.symm hab]
  have htail := coinCount_tail (bernoulliMeasure a b p : Measure q.Ω) a ha n ((M : ℝ) + 1)
    (by positivity)
  rw [hatom] at htail
  have hcompl : P.real {ξ | coinCount a n ξ < (M : ℝ) + 1} =
      1 - P.real {ξ | (M : ℝ) + 1 ≤ coinCount a n ξ} := by
    have hm : MeasurableSet {ξ : ℕ → q.Ω | (M : ℝ) + 1 ≤ coinCount a n ξ} :=
      measurableSet_le measurable_const (measurable_coinCount a ha n)
    have hc : {ξ : ℕ → q.Ω | coinCount a n ξ < (M : ℝ) + 1} =
        {ξ | (M : ℝ) + 1 ≤ coinCount a n ξ}ᶜ := by
      ext ξ; simp
    rw [hc, probReal_compl_eq_one_sub hm]
  have hGbound : 7 / 8 ≤ Q.real Gset := by
    rw [hprod, hcompl]
    have hfrac : (n : ℝ) * (p : ℝ) / ((M : ℝ) + 1) ≤ 1 / 8 := by
      rw [div_le_iff₀ (by positivity), hpval]
      linarith
    linarith
  have hε' := hε
  nlinarith [mul_pos hcard hε']

end Main

end LongTails.Proofs.StrongGrowthMeanSquaredLowerBound
