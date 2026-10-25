import LongTails.Proofs.FairOracleTransfer

namespace OracleTemplate.FairVarianceReduction

open MeasureTheory ProbabilityTheory RadialFairLocation

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]
  {p : Measure Ω} [IsProbabilityMeasure p]
  {g : E → Ω → E} {F : E → E} {r R κ : ℝ}

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma measurable_noise (hg : Measurable (Function.uncurry g)) (x : E) :
    Measurable (fun ω => g x ω - F x) :=
  (hg.comp (measurable_const.prodMk measurable_id)).sub measurable_const

omit [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] in
lemma tail_radius (hrR : r ≤ R) (x : E)
    (hp : p.real {ω | r < ‖g x ω - F x‖} ≤ 1 / 64) :
    p.real {ω | R < ‖g x ω - F x‖} ≤ 1 / 64 := by
  apply (measureReal_mono ?_).trans hp
  intro ω hω
  exact lt_of_le_of_lt hrR hω

lemma noise_block_energy (hg : Measurable (Function.uncurry g))
    (hr : 0 ≤ r) (hR : 0 < R) (hrR : r ≤ R) {k : ℕ} (hk : 0 < k) (x y : E)
    (hpX : p.real {ω | r < ‖g x ω - F x‖} ≤ 1 / 64)
    (hpY : p.real {ω | r < ‖g y ω - F y‖} ≤ 1 / 64)
    (hrel : (∫ ω, (‖(g x ω - F x) - (g y ω - F y)‖ /
      (r + ‖g x ω - F x‖ + ‖g y ω - F y‖)) ^ 2 ∂p) ≤ κ ^ 2 * ‖x - y‖ ^ 2) :
    (∫ ξ, ‖idealNoise R (fun i => g x (ξ i) - F x) -
      idealNoise R (fun i => g y (ξ i) - F y)‖ ^ 2
      ∂(Measure.pi fun _ : Fin (4 * k) => p)) ≤
        (2 : ℝ) ^ 23 * R ^ 2 * (κ ^ 2 * ‖x - y‖ ^ 2 + (1 / 4 : ℝ) ^ k) := by
  apply integral_idealNoise_difference_product hk hR (measurable_noise hg x) (measurable_noise hg y)
    (tail_radius hrR x hpX) (tail_radius hrR y hpY) (by positivity)
  exact (integral_relative_ratio_radius hr hrR (measurable_noise hg x) (measurable_noise hg y)).trans hrel

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma noise_block_symmetry (hg : Measurable (Function.uncurry g)) (x : E)
    (hs : p.map (fun ω => g x ω - F x) = p.map (fun ω => -(g x ω - F x))) (n : ℕ) :
    IdentDistrib (fun ξ : Fin n → Ω => fun i => g x (ξ i) - F x)
      (fun ξ i => -(g x (ξ i) - F x))
      (Measure.pi fun _ => p) (Measure.pi fun _ => p) := by
  have hm := measurable_noise (F := F) hg x
  refine ⟨(Measurable.of_eval (fun i => hm.comp (measurable_pi_apply i))).aemeasurable,
    (Measurable.of_eval (fun i => (hm.comp (measurable_pi_apply i)).neg)).aemeasurable, ?_⟩
  rw [Measure.pi_map_pi (f := fun _ ω => g x ω - F x) (fun _ => hm.aemeasurable),
    Measure.pi_map_pi (f := fun _ ω => -(g x ω - F x)) (fun _ => hm.neg.aemeasurable)]
  simp only [hs]

lemma oracle_refresh_bias (hg : Measurable (Function.uncurry g)) (hR : 0 < R)
    (hrR : r ≤ R) {k : ℕ} (hk : 0 < k) (x : E) {G : ℝ} (hx : ‖F x‖ ≤ G)
    (hs : p.map (fun ω => g x ω - F x) = p.map (fun ω => -(g x ω - F x)))
    (hp : p.real {ω | r < ‖g x ω - F x‖} ≤ 1 / 64) :
    ‖(∫ ξ, refresh R G (fun i => g x (ξ i)) ∂(Measure.pi fun _ : Fin (4 * k) => p)) - F x‖ ≤
      (2 * G + 3 * R) * (1 / 4 : ℝ) ^ k := by
  have hm : Measurable (fun ξ : Fin (4 * k) → Ω => fun i => g x (ξ i) - F x) :=
    Measurable.of_eval (fun i => (measurable_noise hg x).comp (measurable_pi_apply i))
  have he := refresh_bias (by omega : 0 < 4 * k) hR hm (noise_block_symmetry hg x hs (4 * k)) (F x) hx
  simp only [sub_add_cancel] at he
  have hp' := goodBlock_failure_real (measurable_noise hg x) R (tail_radius hrR x hp) k
  have hG : 0 ≤ G := (norm_nonneg _).trans hx
  exact he.trans (mul_le_mul_of_nonneg_left hp' (by positivity))

lemma oracle_refresh_second_moment (hg : Measurable (Function.uncurry g)) (hR : 0 < R)
    (hrR : r ≤ R) {k : ℕ} (hk : 0 < k) (x : E) {G : ℝ} (hx : ‖F x‖ ≤ G)
    (hp : p.real {ω | r < ‖g x ω - F x‖} ≤ 1 / 64) :
    Integrable (fun ξ => ‖refresh R G (fun i => g x (ξ i)) - F x‖ ^ 2)
      (Measure.pi fun _ : Fin (4 * k) => p) ∧
    (∫ ξ, ‖refresh R G (fun i => g x (ξ i)) - F x‖ ^ 2 ∂(Measure.pi fun _ : Fin (4 * k) => p)) ≤
      9 * R ^ 2 + (2 * G + 3 * R) ^ 2 * (1 / 4 : ℝ) ^ k := by
  have hm : Measurable (fun ξ : Fin (4 * k) → Ω => fun i => g x (ξ i) - F x) :=
    Measurable.of_eval (fun i => (measurable_noise hg x).comp (measurable_pi_apply i))
  have he := refresh_second_moment (P := Measure.pi fun _ : Fin (4 * k) => p)
    (by omega : 0 < 4 * k) hR hm (F x) hx
  simp only [sub_add_cancel] at he
  refine ⟨he.1, he.2.trans ?_⟩
  have hp' := goodBlock_failure_real (measurable_noise hg x) R (tail_radius hrR x hp) k
  gcongr

lemma oracle_increment_bounds (hg : Measurable (Function.uncurry g))
    (hr : 0 ≤ r) (hR : 0 < R) (hrR : r ≤ R) {k : ℕ} (hk : 0 < k)
    (x y : E) {K : ℝ} (hK : 0 < K) (hxy : ‖F x - F y‖ ≤ K / 2)
    (hsX : p.map (fun ω => g x ω - F x) = p.map (fun ω => -(g x ω - F x)))
    (hsY : p.map (fun ω => g y ω - F y) = p.map (fun ω => -(g y ω - F y)))
    (hpX : p.real {ω | r < ‖g x ω - F x‖} ≤ 1 / 64)
    (hpY : p.real {ω | r < ‖g y ω - F y‖} ≤ 1 / 64)
    (hrel : (∫ ω, (‖(g x ω - F x) - (g y ω - F y)‖ /
      (r + ‖g x ω - F x‖ + ‖g y ω - F y‖)) ^ 2 ∂p) ≤ κ ^ 2 * ‖x - y‖ ^ 2) :
    Integrable (fun ξ => ‖increment R K (fun i => g x (ξ i)) (fun i => g y (ξ i)) - (F x - F y)‖ ^ 2)
      (Measure.pi fun _ : Fin (4 * k) => p) ∧
    ‖(∫ ξ, increment R K (fun i => g x (ξ i)) (fun i => g y (ξ i))
      ∂(Measure.pi fun _ : Fin (4 * k) => p)) - (F x - F y)‖ ≤
      2 / K * ((2 : ℝ) ^ 23 * R ^ 2 * (κ ^ 2 * ‖x - y‖ ^ 2 + (1 / 4 : ℝ) ^ k)) +
        4 * K * (1 / 4 : ℝ) ^ k ∧
    (∫ ξ, ‖increment R K (fun i => g x (ξ i)) (fun i => g y (ξ i)) - (F x - F y)‖ ^ 2
      ∂(Measure.pi fun _ : Fin (4 * k) => p)) ≤
      (2 : ℝ) ^ 23 * R ^ 2 * (κ ^ 2 * ‖x - y‖ ^ 2 + (1 / 4 : ℝ) ^ k) +
        8 * K ^ 2 * (1 / 4 : ℝ) ^ k := by
  have hmX : Measurable (fun ξ : Fin (4 * k) → Ω => fun i => g x (ξ i) - F x) :=
    Measurable.of_eval (fun i => (measurable_noise hg x).comp (measurable_pi_apply i))
  have hmY : Measurable (fun ξ : Fin (4 * k) → Ω => fun i => g y (ξ i) - F y) :=
    Measurable.of_eval (fun i => (measurable_noise hg y).comp (measurable_pi_apply i))
  have hmean := increment_bias (by omega : 0 < 4 * k) hR hK hmX hmY
    (noise_block_symmetry hg x hsX (4 * k)) (noise_block_symmetry hg y hsY (4 * k)) (F x) (F y) hxy
  have hmoment := increment_second_moment (P := Measure.pi fun _ : Fin (4 * k) => p)
    (by omega : 0 < 4 * k) hR hK.le hmX hmY (F x) (F y) (by linarith)
  simp only [sub_add_cancel] at hmean hmoment
  have henergy := noise_block_energy hg hr hR hrR hk x y hpX hpY hrel
  have hbad := goodBlock_pair_failure_real (measurable_noise hg x) (measurable_noise hg y) R
    (tail_radius hrR x hpX) (tail_radius hrR y hpY) k
  refine ⟨hmoment.1, ?_, ?_⟩
  · have h₁ := mul_le_mul_of_nonneg_left henergy (by positivity : 0 ≤ 2 / K)
    have h₂ := mul_le_mul_of_nonneg_left hbad (by positivity : 0 ≤ 2 * K)
    nlinarith
  · have h₂ := mul_le_mul_of_nonneg_left hbad (by positivity : 0 ≤ 4 * K ^ 2)
    nlinarith [hmoment.2]

end OracleTemplate.FairVarianceReduction
