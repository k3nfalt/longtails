import LongTails.Proofs.KatyushaTuning
import LongTails.Proofs.ManyConstraintMulti

open MeasureTheory Set Metric
open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.ManyConstraintTuning

open LongTails.Proofs.ManyConstraintRun LongTails.Proofs.ManyConstraintInner
  LongTails.Proofs.ManyConstraintEpochEnergy

noncomputable def muT (ε R : ℝ) : ℝ := ε / (384 * R ^ 2)
noncomputable def betaT (κ σ ε L : ℝ) : ℝ := 384 * κ * (σ ^ 2 / ε + L)
noncomputable def LtT (κ σ ε L : ℝ) : ℝ := L + betaT κ σ ε L

noncomputable def kp (m : ℕ) [NeZero m] (κ σ ε L R : ℝ) :
    LongTails.Setups.CompositeFiniteSumStronglyConvex.Params :=
  { E := ℝ, n := m, L := LtT κ σ ε L, μ := muT ε R, Δ := 0, ε := 0, x0 := 0 }

open OracleTemplate.Katyusha

variable (m : ℕ) [NeZero m] (κ σ ε L R : ℝ)

noncomputable def tT : ℕ := tuning (kp m κ σ ε L R)

noncomputable def bT : ℕ :=
  max 1 ⌈(tT m κ σ ε L R : ℝ) * (768 * σ ^ 2 / ε + 2 * L) / LtT κ σ ε L⌉₊

noncomputable def knobs {E : Type*} (x0 : E) : Knobs E :=
  ⟨betaT κ σ ε L, muT ε R, R, tau (kp m κ σ ε L R), alpha (kp m κ σ ε L R), LtT κ σ ε L,
    theta (kp m κ σ ε L R), x0, bT m κ σ ε L R, 2 * m⟩

noncomputable def logX : ℝ :=
  Real.log (64 * (2 * σ * R + 2 * LtT κ σ ε L * R ^ 2 + 3 * ε) / ε)

noncomputable def ST : ℕ := ⌈(12 * (tT m κ σ ε L R : ℝ) + 1) * logX κ σ ε L R⌉₊

noncomputable def QT (δ : ℝ) : ℕ := ⌈κ * Real.log (4 * R ^ 2 / δ ^ 2)⌉₊

variable {m κ σ ε L R}

lemma tuning_facts (hκ : 1 ≤ κ) (hε : 0 < ε) (hL : 0 < L) (hR : 0 < R) :
    let p := kp m κ σ ε L R
    0 < tau p ∧ tau p ≤ 1 / 2 ∧ 0 < alpha p ∧ 3 * alpha p * (LtT κ σ ε L) * tau p ≤ 1 ∧
      1 + tau p / 6 ≤ theta p ^ (2 * m) ∧
      (1 / 2 - tau p) * theta p + 1 / 2 * theta p ^ (2 * m) ≤ 1 ∧
      tau p / (2 * alpha p) = 3 * ((2 * m : ℕ) : ℝ) * muT ε R ∧
      theta p = 1 + alpha p * muT ε R ∧ tau p = 1 / (2 * (tT m κ σ ε L R : ℝ)) := by
  intro p
  have hLt : 0 < p.L := by
    change 0 < L + 384 * κ * (σ ^ 2 / ε + L)
    have : 0 ≤ σ ^ 2 / ε := by positivity
    nlinarith
  have hμ : 0 < p.μ := by change 0 < ε / (384 * R ^ 2); positivity
  obtain ⟨h1, h2, h3, h4, _⟩ := tuning_bounds p hLt hμ
  obtain ⟨h5, _, h6⟩ := theta_epoch_bounds p hLt hμ
  exact ⟨h1, h2, h3, h4, h5, h6, distance_scale p hμ, rfl, rfl⟩

lemma tT_pos : 0 < (tT m κ σ ε L R : ℝ) := by
  have := tuning_pos (kp m κ σ ε L R); unfold tT; exact_mod_cast this

lemma LtT_pos (hκ : 1 ≤ κ) (hε : 0 < ε) (hL : 0 < L) : 0 < LtT κ σ ε L := by
  unfold LtT betaT
  have : 0 ≤ σ ^ 2 / ε := by positivity
  nlinarith

lemma bT_ge (_hκ : 1 ≤ κ) (_hε : 0 < ε) (_hL : 0 < L) :
    (tT m κ σ ε L R : ℝ) * (768 * σ ^ 2 / ε + 2 * L) / LtT κ σ ε L ≤ (bT m κ σ ε L R : ℝ) := by
  unfold bT
  rw [Nat.cast_max]
  exact (Nat.le_ceil _).trans (le_max_right _ _)

lemma bT_pos : 0 < bT m κ σ ε L R := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

section Hyp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {Ξ : Type*} [MeasurableSpace Ξ] {law : Measure Ξ} {loss : Ξ → E → ℝ}
  {grad : Ξ → E → E} {xs x0 : E} {K : Fin m → Set E} {P : Fin m → E → E}

open LongTails.Proofs.ManyConstraintGeometry LongTails.Proofs.ManyConstraintStochastic in
omit [BorelSpace E] [SecondCountableTopology E] in
lemma hyp_of (hreg : Regular law loss grad L σ xs) (hL : 0 < L) (hσ : 0 ≤ σ) (hκ : 1 ≤ κ)
    (hε : 0 < ε) (hR : 0 < R)
    (hP : ∀ j z, IsProj (K j) z (P j z)) (hK : ∀ j, Convex ℝ (K j)) (hxs : xs ∈ ⋂ j, K j)
    (hmin : IsMinOn (objective law loss) (⋂ j, K j) xs)
    (hLR : ∀ x, Metric.infDist x (⋂ j, K j) ^ 2 ≤
      κ * ((1 / (m : ℝ)) * ∑ j, Metric.infDist x (K j) ^ 2))
    (hx0 : ‖x0 - xs‖ ≤ R) :
    Hyp law loss grad L σ xs K P κ R (knobs m κ σ ε L R x0) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := tuning_facts (m := m) (σ := σ) (R := R) hκ hε hL hR
  have hLt := LtT_pos (σ := σ) hκ hε hL
  have ht := tT_pos (m := m) (κ := κ) (σ := σ) (ε := ε) (L := L) (R := R)
  have hb := bT_ge (m := m) (σ := σ) (R := R) hκ hε hL
  refine
    { reg := hreg, L_pos := hL, σ_nonneg := hσ, proj := hP, convex := hK, feasible := hxs,
      minimal := hmin, regular := hLR, κ_pos := by linarith, radius := hx0,
      ball := by rw [mem_closedBall, dist_eq_norm, norm_sub_rev]; exact hx0,
      Lt := rfl, β_pos := by
        change 0 < 384 * κ * (σ ^ 2 / ε + L)
        have : 0 ≤ σ ^ 2 / ε := by positivity
        nlinarith,
      μ_nonneg := by change 0 ≤ ε / (384 * R ^ 2); positivity, ρ_nonneg := hR.le,
      α_pos := h3, τ_pos := h1, τ_half := h2, tune := h4, b_pos := bT_pos, absorb := ?_,
      θ_eq := h8, M_pos := by change 0 < 2 * m; have := NeZero.pos m; omega, coef := h6 }
  change L ≤ tau (kp m κ σ ε L R) * ((L + betaT κ σ ε L) * (bT m κ σ ε L R : ℝ))
  rw [h9]
  change L ≤ 1 / (2 * (tT m κ σ ε L R : ℝ)) * (LtT κ σ ε L * (bT m κ σ ε L R : ℝ))
  have hb2 : (tT m κ σ ε L R : ℝ) * (2 * L) / LtT κ σ ε L ≤ (bT m κ σ ε L R : ℝ) := by
    refine le_trans ?_ hb
    apply div_le_div_of_nonneg_right _ hLt.le
    apply mul_le_mul_of_nonneg_left _ ht.le
    have : 0 ≤ 768 * σ ^ 2 / ε := by positivity
    linarith
  rw [div_le_iff₀ hLt] at hb2
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
  nlinarith

end Hyp

end LongTails.Proofs.ManyConstraintTuning
