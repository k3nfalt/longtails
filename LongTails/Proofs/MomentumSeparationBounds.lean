import LongTails.Proofs.MomentumSeparationProbability

namespace LongTails.Proofs.MomentumSeparationBounds

open MeasureTheory ProbabilityTheory OracleTemplate
open LongTails.Algorithms.MatrixPolar
open LongTails.Setups.MomentumSpectralSmooth
open LongTails.Proofs.MomentumSeparationInstance LongTails.Proofs.MomentumSeparationModel
open LongTails.Proofs.MomentumSeparationBridge LongTails.Proofs.MomentumSeparationLower
open LongTails.Proofs.MomentumSeparationProbability

lemma hard_admissible (p : Public) (hp : spec.valid p) (hr2 : 2 ≤ min p.m p.n)
    (hLΔ : 1024 * p.ε ^ 2 ≤ p.L * p.Δ) (hw : 0 < 16 * p.ε / p.L) :
    LongTails.Setups.BatchedSpectralSmooth.spec.admissible p.toBase
      (MomentumSeparationInstance.objective (p.L / 2) (8 * p.ε / ((min p.m p.n - 1 : ℕ) : ℝ))
        (SeparationInstance.valleyShape hw (p.Δ / (8 * p.ε))) p.x0)
      (hardOracle (lt_of_lt_of_le (by norm_num) hr2)
        (MomentumSeparationInstance.objective (p.L / 2) (8 * p.ε / ((min p.m p.n - 1 : ℕ) : ℝ))
          (SeparationInstance.valleyShape hw (p.Δ / (8 * p.ε))) p.x0) p.s) := by
  obtain ⟨hL, hΔ, hs, hε, _, _⟩ := hp
  have hr : 0 < min p.m p.n := lt_of_lt_of_le (by norm_num) hr2
  have hr1 : (1 : ℝ) ≤ ((min p.m p.n - 1 : ℕ) : ℝ) := by
    have : 1 ≤ min p.m p.n - 1 := by omega
    exact_mod_cast this
  obtain ⟨hrc, hc, _, _, _, hLsum⟩ := witness_params (r := min p.m p.n - 1) hL hε hr1 hLΔ
  dsimp only [LongTails.Setups.BatchedSpectralSmooth.spec, Public.toBase]
  refine ⟨?_, ?_, ⟨((min p.m p.n - 1 : ℕ) : ℝ) * ((8 * p.ε / ((min p.m p.n - 1 : ℕ) : ℝ)) *
      (16 * p.ε / p.L)), ?_, ?_⟩,
    gradientModel hr _ p.s hs, colStream p.m p.n, colStream_iid, rfl⟩
  · intro X
    rw [MomentumSeparationInstance.gradient_objective]
    exact MomentumSeparationInstance.hasGradientAt_objective _ _ _ _ _
  · intro X Y
    have h := MomentumSeparationInstance.lipschitz_objective (by positivity : 0 ≤ p.L / 2) hc.le
      (SeparationInstance.valleyShape hw (p.Δ / (8 * p.ε))) hr p.x0 X Y
    have hlip : (SeparationInstance.valleyShape hw (p.Δ / (8 * p.ε))).lip = 1 / (16 * p.ε / p.L) :=
      rfl
    rw [hlip, hLsum] at h
    exact h
  · intro X
    exact objective_lower (by positivity) hc.le hw _ hr p.x0 X
  · have h := objective_start_le (ℓ := p.L / 2) hc.le hw (p.Δ / (8 * p.ε)) hr p.x0
    have hD : |p.Δ / (8 * p.ε)| = p.Δ / (8 * p.ε) := abs_of_nonneg (by positivity)
    rw [hD] at h
    have heq : ((min p.m p.n - 1 : ℕ) : ℝ) * ((8 * p.ε / ((min p.m p.n - 1 : ℕ) : ℝ)) *
        (16 * p.ε / p.L + p.Δ / (8 * p.ε))) - ((min p.m p.n - 1 : ℕ) : ℝ) *
        ((8 * p.ε / ((min p.m p.n - 1 : ℕ) : ℝ)) * (16 * p.ε / p.L)) = p.Δ := by
      have hne : ((min p.m p.n - 1 : ℕ) : ℝ) ≠ 0 := by linarith
      field_simp
      ring
    linarith

lemma success_good_path {m n : ℕ} (hr : 0 < min m n) {ℓ c s β η ε : ℝ}
    {φ : SeparationInstance.FlatShape} {B T : ℕ} {x0 : Space m n}
    {direction : Space m n → Space m n} (hdm : Measurable direction)
    (hdirb : ∀ M, ‖direction M‖ ≤ 1 + ‖M‖) (hB : 0 < B) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hs : 0 ≤ s) (hℓ : 0 ≤ ℓ) (hc : 0 ≤ c) (hη : 0 ≤ η) (hε : 0 < ε)
    {A : Algorithm (Space m n) (Space m n) (Space m n)}
    (hA : FollowsMomentum direction β η B T x0 A)
    (hk : 4 * ((B * (T + 1) : ℕ) : ℝ) ^ 2 < ((n - min m n + 1 : ℕ) : ℝ))
    (hint : (∫ z, nuclearNorm (gradient (MomentumSeparationInstance.objective ℓ c φ x0)
      (execute (hardOracle hr (MomentumSeparationInstance.objective ℓ c φ x0) s) A
        (fun _ => B * (T + 1)) z.1 z.2)) ∂((A.law : Measure _).prod
          ((hardOracle hr (MomentumSeparationInstance.objective ℓ c φ x0) s).law : Measure _))) ≤
      ε) :
    ∃ ξ : ℕ → Col m n × Bool, Distinct B T ξ ∧
      ∑ t ∈ Finset.range (T + 1), nuclearNorm (gradient (MomentumSeparationInstance.objective ℓ c φ x0)
        (iter hr ℓ c s β η φ B x0 direction ξ t).1) ≤ 3 * (T + 1) * ε := by
  set f := MomentumSeparationInstance.objective ℓ c φ x0
  set μ := (colStream m n : Measure (ℕ → Col m n × Bool))
  set F := fun X : Space m n => nuclearNorm (gradient f X)
  have hF : Measurable F := (LongTails.Proofs.MatrixCovariance.continuous_nuclearNorm _ _).measurable.comp
    (LongTails.Proofs.MuonProcess.measurable_gradient f)
  have hg := sample_measurable hr f s
  have hXm (t : ℕ) : Measurable (fun ξ : ℕ → Col m n × Bool => (iter hr ℓ c s β η φ B x0 direction ξ t).1) :=
    ((LongTails.Proofs.MomentumMuonRate.adapted_sampledMomentum hdm β η B x0 hg t).fst).mono
      (LongTails.Proofs.MuonProcess.past_le _) le_rfl
  have hi : ∀ t, Integrable (fun ξ => F (iter hr ℓ c s β η φ B x0 direction ξ t).1) μ := by
    intro t
    obtain ⟨K, hK⟩ := iter_bounded (hr := hr) (ℓ := ℓ) (c := c) (s := s) (φ := φ) (x0 := x0)
      hdirb hB hβ0 hβ1 hs hℓ hc hη t
    apply Integrable.of_bound (hF.comp (hXm t)).aestronglyMeasurable
      (m * (ℓ * (K + ‖x0‖) + (min m n) * c))
    exact Filter.Eventually.of_forall fun ξ => by
      show ‖F (iter hr ℓ c s β η φ B x0 direction ξ t).1‖ ≤ _
      rw [Real.norm_of_nonneg (nuclearNorm_nonneg _)]
      have h1 := nuclearNorm_le_mul_norm (gradient f (iter hr ℓ c s β η φ B x0 direction ξ t).1)
      have h2 := norm_gradient_le hℓ hc φ x0 (iter hr ℓ c s β η φ B x0 direction ξ t).1
      have h3 : ℓ * (‖(iter hr ℓ c s β η φ B x0 direction ξ t).1‖ + ‖x0‖) ≤ ℓ * (K + ‖x0‖) :=
        mul_le_mul_of_nonneg_left (by linarith [(hK ξ).1]) hℓ
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
      have h4 : ‖gradient f (iter hr ℓ c s β η φ B x0 direction ξ t).1‖ ≤
          ℓ * (K + ‖x0‖) + (min m n) * c := by linarith
      exact h1.trans (mul_le_mul_of_nonneg_left h4 hm0)
  have hout := LongTails.Proofs.MomentumMuonRate.momentum_uniform_output (colStream m n)
    (sample hr f s) hg hdm hA F hF hi
  simp only at hout
  have hsum : ∑ t ∈ Finset.range (T + 1), ∫ ξ, F (iter hr ℓ c s β η φ B x0 direction ξ t).1 ∂μ ≤
      (T + 1) * ε := by
    have h := hout.2.2
    have h2 : (∑ t ∈ Finset.range (T + 1), ∫ ξ, F (iter hr ℓ c s β η φ B x0 direction ξ t).1 ∂μ) /
        (T + 1) ≤ ε := h ▸ hint
    rwa [div_le_iff₀ (by positivity), mul_comm] at h2
  rw [← integral_finsetSum _ (fun t _ => hi t)] at hsum
  by_contra hcon
  push Not at hcon
  set G := {ξ : ℕ → Col m n × Bool | Distinct B T ξ}
  have hGm : MeasurableSet G := distinct_measurable B T
  have hpoint : ∀ ξ, G.indicator (fun _ => 3 * (T + 1) * ε) ξ ≤
      ∑ t ∈ Finset.range (T + 1), F (iter hr ℓ c s β η φ B x0 direction ξ t).1 := by
    intro ξ
    by_cases hξ : ξ ∈ G
    · rw [Set.indicator_of_mem hξ]
      exact (hcon ξ hξ).le
    · rw [Set.indicator_of_notMem hξ]
      exact Finset.sum_nonneg fun t _ => nuclearNorm_nonneg _
  have hlow := integral_mono ((integrable_const _).indicator hGm)
    (integrable_finsetSum _ (fun t _ => hi t)) hpoint
  rw [integral_indicator_const _ hGm, smul_eq_mul] at hlow
  have hbad := bad_prob (m := m) (n := n) B T
  have hk0 : (0 : ℝ) < ((n - min m n + 1 : ℕ) : ℝ) := by positivity
  have hcompl : μ.real Gᶜ ≤ 1 / 4 := by
    have hset : Gᶜ = {ξ : ℕ → Col m n × Bool | ¬ Distinct B T ξ} := rfl
    rw [hset, measureReal_def]
    have hfin : ((B * T : ℕ) : ENNReal) ^ 2 * ((n - min m n + 1 : ℕ) : ENNReal)⁻¹ ≠ ⊤ := by
      apply ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))
      exact ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _))
    refine (ENNReal.toReal_mono hfin hbad).trans ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_natCast,
      ENNReal.toReal_natCast]
    rw [← div_eq_mul_inv, div_le_iff₀ hk0]
    have hBT : ((B * T : ℕ) : ℝ) ≤ ((B * (T + 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_le_mul_left B (Nat.le_succ T)
    have hBT0 : (0 : ℝ) ≤ ((B * T : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hG : 3 / 4 ≤ μ.real G := by
    have := measureReal_add_measureReal_compl (μ := μ) hGm
    simp only [probReal_univ] at this
    linarith
  have hTε : 0 < (T + 1 : ℝ) * ε := by positivity
  nlinarith

lemma measurable_frobeniusNormalize (m n : ℕ) :
    Measurable (frobeniusNormalize (m := m) (n := n)) := by
  unfold frobeniusNormalize
  fun_prop

lemma norm_frobeniusNormalize_le {m n : ℕ} (M : Space m n) :
    ‖frobeniusNormalize M‖ ≤ 1 + ‖M‖ := by
  unfold frobeniusNormalize
  rw [norm_smul, norm_inv, norm_norm]
  rcases (norm_nonneg M).eq_or_lt with h | h
  · rw [← h]; simp
  · rw [inv_mul_cancel₀ h.ne']; linarith [norm_nonneg M]

theorem momentum_lower_of {p : Public} (hp : spec.valid p)
    {direction : Space p.m p.n → Space p.m p.n} (hdm : Measurable direction)
    (hdirb : ∀ M, ‖direction M‖ ≤ 1 + ‖M‖) {κ : Space p.m p.n → ℝ}
    (hdir : ∀ M, direction M = κ M • M)
    (hcore : ∀ (hr2 : 2 ≤ min p.m p.n), 0 < p.s → 1024 * p.ε ^ 2 ≤ p.L * p.Δ →
      ∀ {η : ℝ}, 0 < η → ∀ {B T : ℕ}, 0 < B →
      ∀ {c w D : ℝ} (hw : 0 < w), 0 < c → ((min p.m p.n - 1 : ℕ) : ℝ) * c = 8 * p.ε →
      0 ≤ D - w → 2 * c ≤ 3 * (p.L / 2) * (D - w) →
      ∀ ξ : ℕ → Col p.m p.n × Bool,
      (∑ t ∈ Finset.range (T + 1), p.L / 2 * (p.s / Real.sqrt B * Real.sqrt (∑ u ∈ Finset.range T,
        ((LongTails.Proofs.MomentumSeparationCore.impulse p.β (p.L / 2)
          (gain (lt_of_lt_of_le (by norm_num) hr2) (p.L / 2) c p.s p.β η
          (SeparationInstance.valleyShape hw D) B p.x0 direction κ ξ) u t).1) ^ 2)) ≤
          3 * (T + 1) * p.ε) →
      (∑ t ∈ Finset.range (T + 1), ((min p.m p.n - 1 : ℕ) : ℝ) * c *
        |SeparationInstance.valleySlope w D (LongTails.Proofs.MomentumSeparationCore.flat p.β c w D
          (gain (lt_of_lt_of_le (by norm_num) hr2) (p.L / 2) c p.s p.β η
            (SeparationInstance.valleyShape hw D) B p.x0 direction κ ξ) t).1| ≤
          3 * (T + 1) * p.ε) →
      Distinct B T ξ →
      (D - w) * (p.L / 2) * (1 - p.β) ^ 3 * (p.s / Real.sqrt B) ^ 2 ≤
        6912 * c * p.ε ^ 2 * (T + 1)) :
    MomentumLower p direction 3 (2 ^ 21) := by
  intro hr2 hLΔ η hη B T hB A hA
  have hp' := hp
  obtain ⟨hL, hΔ, hs, hε, hβ0, hβ1⟩ := hp'
  have hr : 0 < min p.m p.n := lt_of_lt_of_le (by norm_num) hr2
  have hw : 0 < 16 * p.ε / p.L := by positivity
  have hr1 : (1 : ℝ) ≤ ((min p.m p.n - 1 : ℕ) : ℝ) := by
    have : 1 ≤ min p.m p.n - 1 := by omega
    exact_mod_cast this
  obtain ⟨_, hc, _, _, _, _⟩ := witness_params (r := min p.m p.n - 1) hL hε hr1 hLΔ
  refine ⟨_, _, hard_admissible p hp hr2 hLΔ hw, fun hsucc => ?_⟩
  by_cases hk : ((p.n - min p.m p.n + 1 : ℕ) : ℝ) ≤ 4 * (B * (T + 1) : ℝ) ^ 2
  · exact Or.inl hk
  right
  rcases hs.eq_or_lt with hs0 | hspos
  · rw [← hs0]
    have : (0 : ℝ) ≤ 2 ^ 21 * p.ε ^ 4 * (B * (T + 1)) := by positivity
    simpa using this
  have hk' : 4 * ((B * (T + 1) : ℕ) : ℝ) ^ 2 < ((p.n - min p.m p.n + 1 : ℕ) : ℝ) := by
    have h := lt_of_not_ge hk
    exact_mod_cast h
  obtain ⟨ξ, hd, hS⟩ := success_good_path hr hdm hdirb hB hβ0 hβ1 hs (by positivity) hc.le
    hη.le hε hA hk' hsucc.2.2
  exact path_bound hdir hr2 hL hε hspos hβ1 hB hLΔ
    (fun hw' hc' hrc' hDw' hDl' ξ' hst hfl hd' =>
      hcore hr2 hspos hLΔ hη hB hw' hc' hrc' hDw' hDl' ξ' hst hfl hd') hd hw hS

theorem nsgd_momentum_lower {p : Public} (hp : spec.valid p) :
    MomentumLower p frobeniusNormalize 3 (2 ^ 21) := by
  have hp' := hp
  obtain ⟨hL, _, _, hε, hβ0, hβ1⟩ := hp'
  exact momentum_lower_of hp (measurable_frobeniusNormalize _ _) norm_frobeniusNormalize_le
    (κ := fun M => ‖M‖⁻¹) (fun M => rfl)
    (fun hr2 hspos _ _ hη _ _ hB _ _ _ hw hc hrc hDw hDl ξ hst hfl hd =>
      core_app_nsgd hr2 hspos hβ0 hβ1 hε hL hη hB hw hc hrc hDw hDl ξ hst hfl hd)

theorem sgd_momentum_lower {p : Public} (hp : spec.valid p) :
    MomentumLower p id 3 (2 ^ 21) := by
  have hp' := hp
  obtain ⟨hL, _, _, hε, hβ0, hβ1⟩ := hp'
  exact momentum_lower_of hp measurable_id (fun M => by simp)
    (κ := fun _ => 1) (fun M => (one_smul ℝ M).symm)
    (fun hr2 hspos _ _ hη _ _ hB _ _ _ hw hc hrc hDw hDl ξ hst hfl hd =>
      core_app_sgd hr2 hspos hβ0 hβ1 hε hL hη hB hw hc hrc hDw hDl ξ hst hfl hd)

end LongTails.Proofs.MomentumSeparationBounds
