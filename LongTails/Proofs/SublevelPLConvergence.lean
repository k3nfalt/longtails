import LongTails.Proofs.SublevelPLExecution
import LongTails.Proofs.SublevelPLTuning
import LongTails.Setups.SublevelPLBoundedVariance
import LongTails.Proofs.Execution

open MeasureTheory ProbabilityTheory

namespace OracleTemplate.SublevelRobustGradient

open RobustGradient

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

lemma sq_lt_iff_lt {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) : r ^ 2 < t ^ 2 ↔ r < t := by
  constructor
  · intro h
    by_contra hc
    rw [not_lt] at hc
    have := pow_le_pow_left₀ ht hc 2
    linarith
  · intro h
    exact pow_lt_pow_left₀ h hr.le (by norm_num)

lemma expected_gap_abstract (p : Measure Ω) [IsProbabilityMeasure p] {f : E → ℝ}
    {m L τ α ν ε' Δ ε : ℝ} {x0 : E} (H : Hyp f m L τ α x0) (hgrad : Measurable (gradient f))
    (hε' : 0 < ε') (hΔ0 : 0 ≤ Δ) (hΔ : f x0 - m ≤ Δ) (_hν0 : 0 ≤ ν)
    (hν : ν ≤ (ε' / τ) ^ (2 / α) / 8) {n K : ℕ} {G : E → (Fin n → Ω) → E}
    (hGm : Measurable (Function.uncurry G))
    (hKν : (K : ℝ) * ν / (2 * L) ≤ ε' / 4)
    (hK : 32 * α / (7 * (2 - α)) * L * τ ^ (2 / α) * ε' ^ (-(2 - α) / α) ≤ K)
    {q c : ℝ} (hq0 : 0 ≤ q) (hc0 : 0 ≤ c)
    (hq : ∀ x, (Measure.pi fun _ : Fin n => p) {ξ | ν < ‖G x ξ - gradient f x‖ ^ 2} ≤
      ENNReal.ofReal q)
    (hc : ∀ x, (∫⁻ ξ, ENNReal.ofReal (‖G x ξ - gradient f x‖ ^ 2)
      ∂(Measure.pi fun _ : Fin n => p)) ≤ ENNReal.ofReal c)
    (hnum : 9 / 4 * ε' + Δ * K * q + (K : ℝ) * c / (2 * L) ≤ ε) :
    (∫⁻ ζ, ENNReal.ofReal (f (iter L G x0 ζ K) - m)
      ∂(Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin n => p)) ≤ ENNReal.ofReal ε := by
  classical
  have hL := H.hL
  set μ := (Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin n => p) with hμ
  set Gd := {ζ : ℕ → Fin n → Ω |
    ∀ j, j < K → ‖G (iter L G x0 ζ j) (ζ j) - gradient f (iter L G x0 ζ j)‖ ^ 2 ≤ ν} with hGd
  have hGdm : MeasurableSet Gd := good_event_measurableSet hGm hgrad L ν x0 K
  have hgood : ∀ ζ ∈ Gd, f (iter L G x0 ζ K) - m ≤ 9 / 4 * ε' := fun ζ hζ =>
    good_trajectory H hε' hν K hKν hK (fun j => iter L G x0 ζ j)
      (fun j => G (iter L G x0 ζ j) (ζ j)) rfl (fun j => iter_succ L G x0 ζ j) hζ
  have hall : ∀ ζ, f (iter L G x0 ζ K) - m ≤ Δ +
      (∑ j ∈ Finset.range K, ‖G (iter L G x0 ζ j) (ζ j) - gradient f (iter L G x0 ζ j)‖ ^ 2) /
        (2 * L) := fun ζ => by
    have := failure_bound H K (fun j => iter L G x0 ζ j) (fun j => G (iter L G x0 ζ j) (ζ j)) rfl
      (fun j => iter_succ L G x0 ζ j)
    linarith
  have hmj : ∀ j, Measurable (fun ζ : ℕ → Fin n → Ω =>
      ENNReal.ofReal (‖G (iter L G x0 ζ j) (ζ j) - gradient f (iter L G x0 ζ j)‖ ^ 2)) := by
    intro j
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.pow_const
    apply Measurable.norm
    apply Measurable.sub
    · exact hGm.comp ((measurable_iter L hGm x0 j).prodMk (measurable_pi_apply j))
    · exact hgrad.comp (measurable_iter L hGm x0 j)
  set S : (ℕ → Fin n → Ω) → ENNReal := fun ζ => ∑ j ∈ Finset.range K,
    ENNReal.ofReal (‖G (iter L G x0 ζ j) (ζ j) - gradient f (iter L G x0 ζ j)‖ ^ 2) with hSdef
  have hSm : Measurable S := Finset.measurable_sum (Finset.range K) (fun j _ => hmj j)
  have hpt : ∀ ζ, ENNReal.ofReal (f (iter L G x0 ζ K) - m) ≤
      ENNReal.ofReal (9 / 4 * ε') + Gdᶜ.indicator (fun _ => ENNReal.ofReal Δ) ζ +
        ENNReal.ofReal (1 / (2 * L)) * S ζ := by
    intro ζ
    by_cases hζ : ζ ∈ Gd
    · calc ENNReal.ofReal (f (iter L G x0 ζ K) - m) ≤ ENNReal.ofReal (9 / 4 * ε') :=
            ENNReal.ofReal_le_ofReal (hgood ζ hζ)
        _ ≤ _ := le_add_right (le_add_right le_rfl)
    · have hind : Gdᶜ.indicator (fun _ => ENNReal.ofReal Δ) ζ = ENNReal.ofReal Δ :=
        Set.indicator_of_mem (Set.mem_compl hζ) _
      rw [hind]
      have hsum : ENNReal.ofReal ((∑ j ∈ Finset.range K,
          ‖G (iter L G x0 ζ j) (ζ j) - gradient f (iter L G x0 ζ j)‖ ^ 2) / (2 * L)) =
          ENNReal.ofReal (1 / (2 * L)) * S ζ := by
        have hdiv : (∑ j ∈ Finset.range K,
            ‖G (iter L G x0 ζ j) (ζ j) - gradient f (iter L G x0 ζ j)‖ ^ 2) / (2 * L) =
            (1 / (2 * L)) * ∑ j ∈ Finset.range K,
              ‖G (iter L G x0 ζ j) (ζ j) - gradient f (iter L G x0 ζ j)‖ ^ 2 := by ring
        rw [hdiv, ENNReal.ofReal_mul (by positivity), hSdef,
          ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)]
      calc ENNReal.ofReal (f (iter L G x0 ζ K) - m)
          ≤ ENNReal.ofReal (Δ + (∑ j ∈ Finset.range K,
              ‖G (iter L G x0 ζ j) (ζ j) - gradient f (iter L G x0 ζ j)‖ ^ 2) / (2 * L)) :=
            ENNReal.ofReal_le_ofReal (hall ζ)
        _ = ENNReal.ofReal Δ + ENNReal.ofReal ((∑ j ∈ Finset.range K,
              ‖G (iter L G x0 ζ j) (ζ j) - gradient f (iter L G x0 ζ j)‖ ^ 2) / (2 * L)) :=
            ENNReal.ofReal_add hΔ0 (by positivity)
        _ = ENNReal.ofReal Δ + ENNReal.ofReal (1 / (2 * L)) * S ζ := by rw [hsum]
        _ ≤ _ := by
            rw [add_assoc]
            exact le_add_left le_rfl
  have hfail : μ Gdᶜ ≤ K * ENNReal.ofReal q := failure_probability_le p hGm hgrad L ν x0 K hq
  have henergy : (∫⁻ ζ, S ζ ∂μ) ≤ K * ENNReal.ofReal c := energy_lintegral_le p hGm hgrad L x0 K hc
  have hint : (∫⁻ ζ, ENNReal.ofReal (f (iter L G x0 ζ K) - m) ∂μ) ≤
      ENNReal.ofReal (9 / 4 * ε') + ENNReal.ofReal Δ * μ Gdᶜ +
        ENNReal.ofReal (1 / (2 * L)) * ∫⁻ ζ, S ζ ∂μ := by
    calc (∫⁻ ζ, ENNReal.ofReal (f (iter L G x0 ζ K) - m) ∂μ)
        ≤ ∫⁻ ζ, (ENNReal.ofReal (9 / 4 * ε') +
            Gdᶜ.indicator (fun _ => ENNReal.ofReal Δ) ζ +
            ENNReal.ofReal (1 / (2 * L)) * S ζ) ∂μ := lintegral_mono hpt
      _ = (∫⁻ _ζ, ENNReal.ofReal (9 / 4 * ε') ∂μ) +
            (∫⁻ ζ, Gdᶜ.indicator (fun _ => ENNReal.ofReal Δ) ζ ∂μ) +
            ∫⁻ ζ, ENNReal.ofReal (1 / (2 * L)) * S ζ ∂μ := by
          rw [lintegral_add_right _ (hSm.const_mul _),
            lintegral_add_right _ (measurable_const.indicator hGdm.compl)]
      _ = ENNReal.ofReal (9 / 4 * ε') + ENNReal.ofReal Δ * μ Gdᶜ +
            ENNReal.ofReal (1 / (2 * L)) * ∫⁻ ζ, S ζ ∂μ := by
          rw [lintegral_const, lintegral_indicator_const hGdm.compl, lintegral_const_mul _ hSm]
          simp
  refine hint.trans ?_
  have hfail' : ENNReal.ofReal Δ * μ Gdᶜ ≤ ENNReal.ofReal Δ * (K * ENNReal.ofReal q) :=
    mul_le_mul' le_rfl hfail
  have henergy' : ENNReal.ofReal (1 / (2 * L)) * (∫⁻ ζ, S ζ ∂μ) ≤
      ENNReal.ofReal (1 / (2 * L)) * (K * ENNReal.ofReal c) :=
    mul_le_mul' le_rfl henergy
  calc ENNReal.ofReal (9 / 4 * ε') + ENNReal.ofReal Δ * μ Gdᶜ +
        ENNReal.ofReal (1 / (2 * L)) * ∫⁻ ζ, S ζ ∂μ
      ≤ ENNReal.ofReal (9 / 4 * ε') + ENNReal.ofReal Δ * (K * ENNReal.ofReal q) +
          ENNReal.ofReal (1 / (2 * L)) * (K * ENNReal.ofReal c) :=
        add_le_add (add_le_add le_rfl hfail') henergy'
    _ = ENNReal.ofReal (9 / 4 * ε' + Δ * K * q + (K : ℝ) * c / (2 * L)) := by
        have h1 : ENNReal.ofReal Δ * (K * ENNReal.ofReal q) = ENNReal.ofReal (Δ * K * q) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hΔ0, ENNReal.ofReal_natCast]
          ring
        have h2 : ENNReal.ofReal (1 / (2 * L)) * (K * ENNReal.ofReal c) =
            ENNReal.ofReal ((K : ℝ) * c / (2 * L)) := by
          have : (K : ℝ) * c / (2 * L) = (1 / (2 * L)) * ((K : ℝ) * c) := by ring
          rw [this, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_natCast]
        rw [h1, h2, ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hnum

lemma expected_gap (p : Measure Ω) [IsProbabilityMeasure p] {f : E → ℝ} {g : E → Ω → E}
    {L τ α σ Δ ε : ℝ} (hv : Valid L τ α σ Δ ε) {x0 : E}
    (H : Hyp f (⨅ y, f y) L τ α x0) (ho : Oracle p f g σ)
    (hΔ : f x0 - (⨅ y, f y) ≤ Δ) (hgrad : Measurable (gradient f)) :
    (∫⁻ ζ, ENNReal.ofReal (f (iter L (blockMap L τ α σ Δ ε g) x0 ζ (steps L τ α ε)) - ⨅ y, f y)
      ∂(Measure.infinitePi fun _ : ℕ =>
        Measure.pi fun _ : Fin (subbatches L τ α Δ ε * subsize L τ α σ Δ ε) => p)) ≤
      ENNReal.ofReal ε := by
  have hL := hv.hL
  have hε := hv.hε
  have hmb := subbatches_pos L τ α Δ ε
  have hbb := subsize_pos L τ α σ Δ ε
  have hBpos : 0 < radius L τ α ε := radius_pos hv
  have hB2 : (radius L τ α ε / 2) ^ 2 = L * ε / (8 * steps L τ α ε) := radius_sq hv
  have hν0 : 0 ≤ L * ε / (8 * steps L τ α ε) := by rw [← hB2]; positivity
  have hGm : Measurable (Function.uncurry (blockMap L τ α σ Δ ε g)) :=
    measurable_blockMap L τ α σ Δ ε ho.hg
  have hKrate : 32 * α / (7 * (2 - α)) * L * τ ^ (2 / α) * (ε / 4) ^ (-(2 - α) / α) ≤
      steps L τ α ε := by
    have := rate_le_steps hv
    unfold rate at this
    exact this
  have hq : ∀ x, (Measure.pi fun _ : Fin (subbatches L τ α Δ ε * subsize L τ α σ Δ ε) => p)
      {ξ | L * ε / (8 * steps L τ α ε) < ‖blockMap L τ α σ Δ ε g x ξ - gradient f x‖ ^ 2} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ subbatches L τ α Δ ε) := by
    intro x
    have hbB : 144 * σ ^ 2 ≤ subsize L τ α σ Δ ε * (radius L τ α ε / 2) ^ 2 := by
      rw [hB2]; exact variance_batch hv
    have hset : {ξ : Fin (subbatches L τ α Δ ε * subsize L τ α σ Δ ε) → Ω |
        L * ε / (8 * steps L τ α ε) < ‖blockMap L τ α σ Δ ε g x ξ - gradient f x‖ ^ 2} =
        {ξ : Fin (subbatches L τ α Δ ε * subsize L τ α σ Δ ε) → Ω |
          radius L τ α ε / 2 < ‖blockMap L τ α σ Δ ε g x ξ - gradient f x‖} := by
      ext ξ
      simp only [Set.mem_ofPred_eq]
      rw [← hB2, sq_lt_iff_lt (by positivity) (norm_nonneg _)]
    rw [hset]
    exact estimate_failure p ho x hmb hbb hBpos hbB
  have hc : ∀ x, (∫⁻ ξ, ENNReal.ofReal (‖blockMap L τ α σ Δ ε g x ξ - gradient f x‖ ^ 2)
      ∂(Measure.pi fun _ : Fin (subbatches L τ α Δ ε * subsize L τ α σ Δ ε) => p)) ≤
      ENNReal.ofReal (subbatches L τ α Δ ε * (σ ^ 2 / subsize L τ α σ Δ ε)) :=
    fun x => estimate_second_moment p ho x hmb hbb (radius L τ α ε)
  have hnum : 9 / 4 * (ε / 4) + Δ * steps L τ α ε * (1 / 2 : ℝ) ^ subbatches L τ α Δ ε +
      (steps L τ α ε : ℝ) * (subbatches L τ α Δ ε * (σ ^ 2 / subsize L τ α σ Δ ε)) / (2 * L) ≤
      ε := by
    have h1 := failure_budget hv
    have h2 := second_moment_budget hv
    linarith
  have hc0 : 0 ≤ (subbatches L τ α Δ ε : ℝ) * (σ ^ 2 / subsize L τ α σ Δ ε) := by
    have := hv.hσ
    have := subsize_pos_real (L := L) (τ := τ) (α := α) (σ := σ) (Δ := Δ) (ε := ε)
    positivity
  exact expected_gap_abstract p H hgrad (by positivity) hv.hΔ hΔ hν0 (nu_le hv) hGm
    (steps_nu hv).le hKrate (by positivity) hc0 hq hc hnum

omit [SecondCountableTopology E] in
lemma gradient_measurable {f : E → ℝ} {L : ℝ} (hL : 0 < L)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) :
    Measurable (gradient f) := by
  have hl : LipschitzWith (Real.toNNReal L) (gradient f) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hL.le]
    exact hlip x y
  exact hl.continuous.measurable

end OracleTemplate.SublevelRobustGradient
