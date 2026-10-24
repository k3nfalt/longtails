import LongTails.Proofs.CyclicPerceptronCertificate
import LongTails.Proofs.CyclicPerceptronExecution

open scoped RealInnerProductSpace

namespace LongTails.Proofs.CyclicPerceptronScanner

open LongTails.Setups.CyclicFullWidthPerceptron
open LongTails.Algorithms.CyclicFullWidthPerceptron
open CyclicPerceptronBlocks CyclicPerceptronComparisonDynamics CyclicPerceptronBootstrap
open CyclicPerceptronBounds CyclicPerceptronCounting CyclicPerceptronCone
open CyclicPerceptronCertificate CyclicPerceptronExecution CyclicPerceptronParameters

noncomputable def tolerance (p : Params) (H : ℕ) : ℝ := 256 * stepSize p ^ 2 * (H : ℝ) ^ 3

noncomputable def scaledOffset (p : Params) (D : Data p.dimension p.count)
    (i : Fin p.count) : ℝ := D.offset i / (stepSize p ^ 2 * p.μ ^ 2)

structure Controls (p : Params) (D : Data p.dimension p.count) (H : ℕ)
    (i₀ : Fin p.count) (v w : Features p.dimension) : Prop where
  count_pos : 0 < p.count
  first : i₀.val = 0
  kappa_pos : 0 < p.κ
  kappa_le : p.κ ≤ 1
  mu_pos : 0 < p.μ
  mu_le : p.μ ≤ 1
  eta_pos : 0 < stepSize p
  eta_sq : stepSize p ^ 2 ≤ 1
  horizon_pos : 1 ≤ (H : ℝ)
  horizon_count : ∀ m : ℕ, (m : ℝ) ≤ 68 / p.κ ^ 4 → m + 1 ≤ H
  small : stepSize p ^ 2 * (H : ℝ) ^ 2 ≤ 1 / 1024
  mu_horizon : p.μ * H ≤ 1 / 4096
  tolerance_small : tolerance p H ≤ 1 / 6
  bias_small : 256 * stepSize p ^ 2 * (H : ℝ) ^ 4 * p.κ ^ 4 ≤ 1
  offset_bounds : ∀ i, 0 ≤ scaledOffset p D i ∧ scaledOffset p D i ≤ 1 ∧
    D.offset i = scaledOffset p D i * stepSize p ^ 2 * p.μ ^ 2
  residual_norm : ∀ i, ‖D.residual i‖ ≤ 1
  separator_norm : ‖w‖ = 1
  separator_margin : ∀ i, p.κ ≤ ⟪w, D.residual i⟫
  projection_lower : p.κ ≤ ‖v‖
  projection_upper : ‖v‖ ≤ 1
  projection_first : ⟪v, D.residual i₀⟫ = ‖v‖ ^ 2
  projection_cloud : ∀ i, 0 ≤ ⟪v, D.residual i⟫
  cone_score : ∀ U, (∀ i, -tolerance p H ≤ ⟪U, D.residual i⟫) →
    ⟪U, D.residual i₀⟫ ≤ ⟪U, v⟫ + 2 * tolerance p H / p.κ

lemma controls_exist (p : Params) (D : Data p.dimension p.count)
    (hv : spec.valid p) (hg : Geometry p D) :
    ∃ (i₀ : Fin p.count) (v w : Features p.dimension),
      Controls p D ⌈128 / p.κ ^ 4⌉₊ i₀ v w := by
  obtain ⟨hn, hκ, hκ₁, hμ, hμs, _, hνs⟩ := hv
  obtain ⟨hoff, hu, w, hw, hmargin⟩ := hg
  let i₀ : Fin p.count := ⟨0, hn⟩
  obtain ⟨v, hvκ, hv₁, hvfirst, hvcloud, hvpolar⟩ :=
    exists_cloud_projection D.residual i₀ w p.κ hκ hu hw hmargin
  obtain ⟨hH, hH₁, hmH⟩ := horizon_bounds p.κ hκ hκ₁
  obtain ⟨hη, hη₂, hμ₁, hμH, hsmall, hδ, hbias⟩ :=
    tuning_bounds p.κ p.μ (⌈128 / p.κ ^ 4⌉₊ : ℕ) hκ hκ₁ hμ hμs hH hH₁
  refine ⟨i₀, v, w, hn, rfl, hκ, hκ₁, hμ, hμ₁, hη, hη₂, hH, hmH,
    hsmall, hμH, hδ, hbias, ?_, hu, hw, hmargin, hvκ, hv₁, hvfirst, hvcloud, ?_⟩
  · intro i
    exact mismatch_scaling p.κ p.μ (D.offset i) hκ hμ (hoff i).1
      ((hoff i).2.trans hνs)
  · intro U hU
    have hδ0 : 0 ≤ tolerance p ⌈128 / p.κ ^ 4⌉₊ := by unfold tolerance; positivity
    have hmem := approximate_cone_membership D.residual U w _ p.κ hκ hδ0 hU hmargin
    have hh := approximate_cone_score hκ hδ0 (hu i₀) hv₁ hw.le (hvpolar _ hmem)
    simpa only [real_inner_comm] using hh

abbrev Balanced (p : Params) (D : Data p.dimension p.count) (H : ℕ)
    (i₀ : Fin p.count) (v w : Features p.dimension) (m : ℕ) (σ : ℝ)
    (c : Coordinates p.dimension) (s : Comparison p.dimension) : Prop :=
  Certificate (stepSize p ^ 2) p.μ H (tolerance p H) p.κ v (D.residual i₀) w m σ c s

lemma balanced_count {p : Params} {D : Data p.dimension p.count} {H : ℕ}
    {i₀ : Fin p.count} {v w : Features p.dimension} (h : Controls p D H i₀ v w)
    {m : ℕ} {σ : ℝ} {c : Coordinates p.dimension} {s : Comparison p.dimension}
    (hc : Balanced p D H i₀ v w m σ c s) : (m : ℝ) ≤ 68 / p.κ ^ 4 :=
  certificate_count _ _ _ _ _ _ _ _ _ _ _ _ hc h.kappa_pos h.kappa_le
    (by unfold tolerance; positivity) h.tolerance_small h.projection_upper
    (h.residual_norm i₀) h.separator_norm

lemma balanced_horizon {p : Params} {D : Data p.dimension p.count} {H : ℕ}
    {i₀ : Fin p.count} {v w : Features p.dimension} (h : Controls p D H i₀ v w)
    {m : ℕ} {σ : ℝ} {c : Coordinates p.dimension} {s : Comparison p.dimension}
    (hc : Balanced p D H i₀ v w m σ c s) : (m : ℝ) ≤ H := by
  have hh := h.horizon_count m (balanced_count h hc)
  exact_mod_cast (show m ≤ H by omega)

lemma balanced_envelope {p : Params} {D : Data p.dimension p.count} {H : ℕ}
    {i₀ : Fin p.count} {v w : Features p.dimension} (h : Controls p D H i₀ v w)
    {m : ℕ} {σ : ℝ} {c : Coordinates p.dimension} {s : Comparison p.dimension}
    (hc : Balanced p D H i₀ v w m σ c s) : Envelope H c :=
  envelope_of_errors _ _ _ _ _ _ (sq_nonneg _) (by nlinarith [h.mu_pos, h.mu_le])
    h.horizon_pos (Nat.cast_nonneg _) (balanced_horizon h hc) h.small hc.errors hc.comparison_bound

lemma offset_size {p : Params} {D : Data p.dimension p.count} {H : ℕ}
    {i₀ : Fin p.count} {v w : Features p.dimension} (h : Controls p D H i₀ v w)
    (i : Fin p.count) : 1 ≤ 1 + D.offset i ∧ 1 + D.offset i ≤ 2 := by
  obtain ⟨hβ, hβ₁, he⟩ := h.offset_bounds i
  rw [he]
  have hμ₂ : p.μ ^ 2 ≤ 1 := by nlinarith [h.mu_pos, h.mu_le]
  have hb : scaledOffset p D i * stepSize p ^ 2 * p.μ ^ 2 ≤ 1 := by
    have hη₂ := h.eta_sq
    calc
      scaledOffset p D i * stepSize p ^ 2 * p.μ ^ 2 ≤ 1 * 1 * 1 := by gcongr
      _ = 1 := by ring
  constructor
  · have hh : 0 ≤ scaledOffset p D i * stepSize p ^ 2 * p.μ ^ 2 := by positivity
    linarith
  · linarith

inductive Stage (n : ℕ) where
  | balanced
  | positive
  | negative (i : Fin n)

noncomputable def pending {n : ℕ} : Stage n → ℕ
  | .balanced => 0
  | .positive => 1
  | .negative _ => 1

def Phase (p : Params) (D : Data p.dimension p.count) (H : ℕ)
    (i₀ : Fin p.count) (v : Features p.dimension)
    (c : Coordinates p.dimension) (s : Comparison p.dimension)
    (stage : Stage p.count) (state : State p.dimension p.count) : Prop :=
  match stage with
  | .balanced => state.point = realize (stepSize p) p.μ c ∧
      CheckedPrefix D (tolerance p H) s.U state.cursor
  | .positive => state.point = move (realize (stepSize p) p.μ c) (stepSize p)
      (direction (1, 0) (realize (stepSize p) p.μ c)) ∧ state.cursor = i₀.succ ∧
      ⟪s.U, D.residual i₀⟫ ≤ ⟪s.U, v⟫ + 2 * tolerance p H / p.κ ∧
      comparisonBias s * p.κ ^ 4 ≤ 1 ∧ -tolerance p H ≤ ⟪s.U, D.residual i₀⟫
  | .negative i => state.point = move (realize (stepSize p) p.μ c) (stepSize p)
      (direction (-(1 + D.offset i), -p.μ • D.residual i) (realize (stepSize p) p.μ c)) ∧
      ⟪s.U, D.residual i⟫ ≤ tolerance p H

lemma balanced_negative_guards {p : Params} {D : Data p.dimension p.count} {H : ℕ}
    {i₀ : Fin p.count} {v w : Features p.dimension} (h : Controls p D H i₀ v w)
    {m : ℕ} {σ : ℝ} {c : Coordinates p.dimension} {s : Comparison p.dimension}
    (hc : Balanced p D H i₀ v w m σ c s) (i : Fin p.count) :
    let score := margin (-(1 + D.offset i), -p.μ • D.residual i) (realize (stepSize p) p.μ c)
    (0 < score → -tolerance p H ≤ ⟪s.U, D.residual i⟫) ∧
    (score ≤ 0 → ⟪s.U, D.residual i⟫ ≤ tolerance p H) := by
  dsimp only
  rw [(h.offset_bounds i).2.2]
  exact negative_score_guards _ _ _ _ _ _ _ _ h.eta_pos h.eta_sq h.mu_pos
    (by nlinarith [h.mu_pos, h.mu_le]) (h.offset_bounds i).1 (h.offset_bounds i).2.1
    h.horizon_pos (Nat.cast_nonneg _) (balanced_horizon h hc) (h.residual_norm i)
    hc.errors (balanced_envelope h hc) hc.comparison_bound

lemma balanced_reference_guard {p : Params} {D : Data p.dimension p.count} {H : ℕ}
    {i₀ : Fin p.count} {v w : Features p.dimension} (h : Controls p D H i₀ v w)
    {m : ℕ} {σ : ℝ} {c : Coordinates p.dimension} {s : Comparison p.dimension}
    (hc : Balanced p D H i₀ v w m σ c s)
    (hscore : margin (1, 0) (realize (stepSize p) p.μ c) ≤ 0) :
    comparisonBias s * p.κ ^ 4 ≤ 1 :=
  reference_bias_guard _ _ _ _ _ _ _ h.eta_pos h.mu_pos h.horizon_pos
    (Nat.cast_nonneg _) (balanced_horizon h hc) hc.errors (balanced_envelope h hc)
    hc.comparison_bound h.bias_small hscore

lemma balanced_signs {p : Params} {D : Data p.dimension p.count} {H : ℕ}
    {i₀ : Fin p.count} {v w : Features p.dimension} (h : Controls p D H i₀ v w)
    {m : ℕ} {σ : ℝ} {c : Coordinates p.dimension} {s : Comparison p.dimension}
    (hc : Balanced p D H i₀ v w m σ c s) (i j : Fin p.count) :
    let θ := realize (stepSize p) p.μ c
    let q := (-(1 + D.offset i), -p.μ • D.residual i)
    let r := (-(1 + D.offset j), -p.μ • D.residual j)
    0 < margin (1, 0) (move θ (stepSize p) (direction (1, 0) θ)) ∧
      margin r (move θ (stepSize p) (direction (1, 0) θ)) < 0 ∧
      margin (1, 0) (move θ (stepSize p) (direction q θ)) < 0 ∧
      0 < margin r (move θ (stepSize p) (direction q θ)) :=
  balanced_pairing _ _ _ _ _ _ _ _ _ _ h.eta_pos h.eta_sq h.mu_pos h.mu_le
    h.horizon_pos (balanced_horizon h hc) h.small h.mu_horizon
    (offset_size h i).1 (offset_size h i).2 (offset_size h j).1 (offset_size h j).2
    (h.residual_norm i) (h.residual_norm j) hc.errors (balanced_envelope h hc)

lemma balanced_complete {p : Params} {D : Data p.dimension p.count} {H : ℕ}
    {i₀ : Fin p.count} {v w : Features p.dimension} (h : Controls p D H i₀ v w)
    {m : ℕ} {σ : ℝ} {c : Coordinates p.dimension} {s : Comparison p.dimension}
    (hc : Balanced p D H i₀ v w m σ c s) (b : Bool) (i : Fin p.count)
    (hPN : b = false → i = i₀ ∧
      ⟪s.U, D.residual i₀⟫ ≤ ⟪s.U, v⟫ + 2 * tolerance p H / p.κ ∧
      comparisonBias s * p.κ ^ 4 ≤ 1)
    (hNP : b = true → ⟪s.U, D.residual i⟫ ≤ tolerance p H) :
    Balanced p D H i₀ v w (m + 1) (σ + scaledOffset p D i)
      (pairedCoordinates b (stepSize p ^ 2) p.μ (scaledOffset p D i) c (D.residual i))
      (comparisonStep b (scaledOffset p D i) s (D.residual i)) := by
  apply certificate_step b _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc (sq_nonneg _) h.eta_sq
    (by nlinarith [h.mu_pos, h.mu_le]) (h.offset_bounds i).1 (h.offset_bounds i).2.1
    h.horizon_pos (balanced_horizon h hc) h.small h.kappa_pos h.kappa_le
    (by unfold tolerance; positivity) h.tolerance_small h.projection_lower h.projection_upper
    (h.residual_norm i₀) h.separator_norm h.projection_first (h.projection_cloud i)
    (h.residual_norm i) (h.separator_margin i) ?_ hNP
  intro hb
  obtain ⟨hi, hs, hC⟩ := hPN hb
  exact ⟨congrArg D.residual hi, hs, hC⟩

def CanAdvance (p : Params) (D : Data p.dimension p.count) (H : ℕ)
    (i₀ : Fin p.count) (v w : Features p.dimension) (m : ℕ)
    (stage : Stage p.count) (state : State p.dimension p.count) : Prop :=
  ∃ (m' : ℕ) (σ' : ℝ) (c' : Coordinates p.dimension) (s' : Comparison p.dimension)
    (stage' : Stage p.count), Balanced p D H i₀ v w m' σ' c' s' ∧
    Phase p D H i₀ v c' s' stage' (advance p D state) ∧
    2 * m' + pending stage' = 2 * m + pending stage +
      (if margin (sample p D state.cursor) state.point ≤ 0 then 1 else 0)

lemma balanced_advance {p : Params} {D : Data p.dimension p.count} {H : ℕ}
    {i₀ : Fin p.count} {v w : Features p.dimension} (h : Controls p D H i₀ v w)
    {m : ℕ} {σ : ℝ} {c : Coordinates p.dimension} {s : Comparison p.dimension}
    (hc : Balanced p D H i₀ v w m σ c s) (state : State p.dimension p.count)
    (hphase : Phase p D H i₀ v c s .balanced state) :
    CanAdvance p D H i₀ v w m .balanced state := by
  obtain ⟨heq, hprefix⟩ := hphase
  cases hidx : state.cursor using Fin.cases with
  | zero =>
      have hsamp : sample p D state.cursor = (1, 0) := by simp [hidx, sample]
      by_cases hbad : margin (sample p D state.cursor) state.point ≤ 0
      · refine ⟨m, σ, c, s, .positive, hc, ?_, ?_⟩
        · have hall := prefix_all D (tolerance p H) s.U (by simpa [hidx] using hprefix)
          refine ⟨?_, ?_, h.cone_score s.U hall, ?_, hall i₀⟩
          · rw [advance_mistake p D state hbad, heq, hsamp]
          · rw [advance_cursor, hidx]
            apply Fin.ext
            rw [coe_finRotate]
            simp only [Fin.ext_iff, Fin.val_zero, Fin.val_last, Fin.val_succ, h.first]
            have hn := h.count_pos
            split <;> omega
          · apply balanced_reference_guard h hc
            simpa [hsamp, heq] using hbad
        · simp [pending, hbad]
      · refine ⟨m, σ, c, s, .balanced, hc, ?_, ?_⟩
        · refine ⟨(advance_correct p D state (lt_of_not_ge hbad)).trans heq, ?_⟩
          rw [advance_cursor, hidx]
          exact prefix_after_reference D _ _ h.count_pos
        · simp [pending, hbad]
  | succ i =>
      have hsamp : sample p D state.cursor = (-(1 + D.offset i), -p.μ • D.residual i) := by
        simp [hidx, sample]
      have hg := balanced_negative_guards h hc i
      by_cases hbad : margin (sample p D state.cursor) state.point ≤ 0
      · refine ⟨m, σ, c, s, .negative i, hc, ?_, ?_⟩
        · refine ⟨?_, hg.2 ?_⟩
          · rw [advance_mistake p D state hbad, heq, hsamp]
          · simpa [hsamp, heq] using hbad
        · simp [pending, hbad]
      · refine ⟨m, σ, c, s, .balanced, hc, ?_, ?_⟩
        · refine ⟨(advance_correct p D state (lt_of_not_ge hbad)).trans heq, ?_⟩
          rw [advance_cursor, hidx]
          apply prefix_after_negative D _ _ i (by simpa [hidx] using hprefix)
          apply hg.1
          simpa [hsamp, heq] using lt_of_not_ge hbad
        · simp [pending, hbad]

lemma positive_advance {p : Params} {D : Data p.dimension p.count} {H : ℕ}
    {i₀ : Fin p.count} {v w : Features p.dimension} (h : Controls p D H i₀ v w)
    {m : ℕ} {σ : ℝ} {c : Coordinates p.dimension} {s : Comparison p.dimension}
    (hc : Balanced p D H i₀ v w m σ c s) (state : State p.dimension p.count)
    (hphase : Phase p D H i₀ v c s .positive state) :
    CanAdvance p D H i₀ v w m .positive state := by
  obtain ⟨heq, hidx, hcone, hbias, hfirst⟩ := hphase
  have hsamp : sample p D state.cursor = (-(1 + D.offset i₀), -p.μ • D.residual i₀) := by
    simp [hidx, sample]
  have hbad : margin (sample p D state.cursor) state.point ≤ 0 := by
    rw [hsamp, heq]
    exact (balanced_signs h hc i₀ i₀).2.1.le
  let β := scaledOffset p D i₀
  let c' := pairedCoordinates false (stepSize p ^ 2) p.μ β c (D.residual i₀)
  let s' := comparisonStep false β s (D.residual i₀)
  have hc' : Balanced p D H i₀ v w (m + 1) (σ + β) c' s' :=
    balanced_complete h hc false i₀ (fun _ => ⟨rfl, hcone, hbias⟩) (by simp)
  refine ⟨m + 1, σ + β, c', s', .balanced, hc', ?_, ?_⟩
  · constructor
    · rw [advance_mistake p D state hbad, hsamp, heq, (h.offset_bounds i₀).2.2]
      exact positive_negative_coordinates (stepSize p) p.μ β c (D.residual i₀)
    · rw [advance_cursor, hidx]
      apply prefix_after_negative D (tolerance p H) s'.U i₀
      · intro j hj
        simp only [Fin.val_succ, h.first] at hj
        omega
      · change -tolerance p H ≤ ⟪s.U + D.residual i₀, D.residual i₀⟫
        rw [inner_add_left, real_inner_self_eq_norm_sq]
        nlinarith [sq_nonneg ‖D.residual i₀‖]
  · simp only [pending, hbad, ↓reduceIte]
    omega

lemma negative_advance {p : Params} {D : Data p.dimension p.count} {H : ℕ}
    {i₀ : Fin p.count} {v w : Features p.dimension} (h : Controls p D H i₀ v w)
    {m : ℕ} {σ : ℝ} {c : Coordinates p.dimension} {s : Comparison p.dimension}
    (hc : Balanced p D H i₀ v w m σ c s) (state : State p.dimension p.count)
    (i : Fin p.count) (hphase : Phase p D H i₀ v c s (.negative i) state) :
    CanAdvance p D H i₀ v w m (.negative i) state := by
  obtain ⟨heq, hguard⟩ := hphase
  cases hidx : state.cursor using Fin.cases with
  | zero =>
      have hsamp : sample p D state.cursor = (1, 0) := by simp [hidx, sample]
      have hbad : margin (sample p D state.cursor) state.point ≤ 0 := by
        rw [hsamp, heq]
        exact (balanced_signs h hc i i₀).2.2.1.le
      let β := scaledOffset p D i
      let c' := pairedCoordinates true (stepSize p ^ 2) p.μ β c (D.residual i)
      let s' := comparisonStep true β s (D.residual i)
      have hc' : Balanced p D H i₀ v w (m + 1) (σ + β) c' s' :=
        balanced_complete h hc true i (by simp) (fun _ => hguard)
      refine ⟨m + 1, σ + β, c', s', .balanced, hc', ?_, ?_⟩
      · constructor
        · rw [advance_mistake p D state hbad, hsamp, heq, (h.offset_bounds i).2.2]
          exact negative_positive_coordinates (stepSize p) p.μ β c (D.residual i)
        · rw [advance_cursor, hidx]
          exact prefix_after_reference D _ _ h.count_pos
      · simp only [pending, hbad, ↓reduceIte]
        omega
  | succ j =>
      have hsamp : sample p D state.cursor = (-(1 + D.offset j), -p.μ • D.residual j) := by
        simp [hidx, sample]
      have hgood : 0 < margin (sample p D state.cursor) state.point := by
        rw [hsamp, heq]
        exact (balanced_signs h hc i j).2.2.2
      refine ⟨m, σ, c, s, .negative i, hc, ?_, ?_⟩
      · exact ⟨(advance_correct p D state hgood).trans heq, hguard⟩
      · simp [pending, not_le.mpr hgood]

lemma phase_advance {p : Params} {D : Data p.dimension p.count} {H : ℕ}
    {i₀ : Fin p.count} {v w : Features p.dimension} (h : Controls p D H i₀ v w)
    {m : ℕ} {σ : ℝ} {c : Coordinates p.dimension} {s : Comparison p.dimension}
    (hc : Balanced p D H i₀ v w m σ c s) (state : State p.dimension p.count)
    (stage : Stage p.count) (hphase : Phase p D H i₀ v c s stage state) :
    CanAdvance p D H i₀ v w m stage state := by
  cases stage with
  | balanced => exact balanced_advance h hc state hphase
  | positive => exact positive_advance h hc state hphase
  | negative i => exact negative_advance h hc state i hphase

lemma trajectory_certificate {p : Params} {D : Data p.dimension p.count} {H : ℕ}
    {i₀ : Fin p.count} {v w : Features p.dimension} (h : Controls p D H i₀ v w) (k : ℕ) :
    let start : State p.dimension p.count := ⟨initial p.dimension, 0⟩
    ∃ (m : ℕ) (σ : ℝ) (c : Coordinates p.dimension) (s : Comparison p.dimension)
      (stage : Stage p.count), Balanced p D H i₀ v w m σ c s ∧
      Phase p D H i₀ v c s stage ((advance p D)^[k] start) ∧
      mistakes p D start k = 2 * m + pending stage := by
  induction k with
  | zero =>
      refine ⟨0, 0, coordinateStart _, comparisonStart _, .balanced, ?_, ?_, ?_⟩
      · exact certificate_start _ _ _ _ _ _ _ _ h.kappa_pos
      · constructor
        · simp [initial, realize, coordinateStart]
        · intro i hi
          simp only [comparisonStart, inner_zero_left]
          have hh : 0 ≤ tolerance p H := by unfold tolerance; positivity
          linarith
      · simp [mistakes, pending]
  | succ k ih =>
      obtain ⟨m, σ, c, s, stage, hc, hphase, hcount⟩ := ih
      obtain ⟨m', σ', c', s', stage', hc', hphase', hcount'⟩ :=
        phase_advance h hc _ stage hphase
      refine ⟨m', σ', c', s', stage', hc', ?_, ?_⟩
      · simpa only [Function.iterate_succ_apply'] using hphase'
      · rw [mistakes_add, hcount]
        simpa only [mistakes, Nat.add_zero] using hcount'.symm

lemma mistakes_bound {p : Params} {D : Data p.dimension p.count} {H : ℕ}
    {i₀ : Fin p.count} {v w : Features p.dimension} (h : Controls p D H i₀ v w) (k : ℕ) :
    (mistakes p D ⟨initial p.dimension, 0⟩ k : ℝ) ≤ 137 / p.κ ^ 4 := by
  obtain ⟨m, σ, c, s, stage, hc, _, he⟩ := trajectory_certificate h k
  rw [he]
  have hm := balanced_count h hc
  have hp : pending stage ≤ 1 := by cases stage <;> simp [pending]
  have hp' : (pending stage : ℝ) ≤ 1 := by exact_mod_cast hp
  have hκ₄ : p.κ ^ 4 ≤ 1 := pow_le_one₀ h.kappa_pos.le h.kappa_le
  have hpos : 0 < p.κ ^ 4 := pow_pos h.kappa_pos 4
  have hone : (1 : ℝ) ≤ 1 / p.κ ^ 4 := (le_div_iff₀ hpos).mpr (by simpa using hκ₄)
  push_cast
  simp only [div_eq_mul_inv] at hm hone ⊢
  linarith

lemma iterate_separates (p : Params) (D : Data p.dimension p.count)
    (hv : spec.valid p) (hg : Geometry p D) :
    Separates p D (((advance p D)^[(p.count + 1) * ⌈256 / p.κ ^ 4⌉₊])
      (⟨initial p.dimension, 0⟩ : State p.dimension p.count)).point := by
  obtain ⟨i₀, v, w, h⟩ := controls_exist p D hv hg
  by_contra hn
  have hcycles := cycles_count p D ⟨initial p.dimension, 0⟩ ⌈256 / p.κ ^ 4⌉₊ hn
  have hcycles' : (⌈256 / p.κ ^ 4⌉₊ : ℝ) ≤
      (mistakes p D ⟨initial p.dimension, 0⟩ ((p.count + 1) * ⌈256 / p.κ ^ 4⌉₊) : ℝ) := by
    exact_mod_cast hcycles
  have hb := mistakes_bound h ((p.count + 1) * ⌈256 / p.κ ^ 4⌉₊)
  have hl := Nat.le_ceil (256 / p.κ ^ 4)
  have hh : 256 / p.κ ^ 4 ≤ 137 / p.κ ^ 4 := hl.trans (hcycles'.trans hb)
  have hh' := (div_le_div_iff_of_pos_right (pow_pos h.kappa_pos 4)).mp hh
  norm_num at hh'

end LongTails.Proofs.CyclicPerceptronScanner
