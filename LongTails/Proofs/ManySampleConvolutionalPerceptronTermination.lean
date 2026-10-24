import LongTails.Proofs.ManySampleConvolutionalPerceptronBootstrap
import LongTails.Proofs.ManySampleConvolutionalPerceptronParameters

open scoped RealInnerProductSpace

namespace LongTails.Proofs.ManySampleConvolutionalPerceptronTermination

open ManySampleConvolutionalPerceptronDynamics
open ManySampleConvolutionalPerceptronStability
open ManySampleConvolutionalPerceptronTrajectory
open ManySampleConvolutionalPerceptronBootstrap
open ManySampleConvolutionalPerceptronParameters

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

lemma bounded_prefix (p : Tuning) {g : Gains E n} {x : ℕ → State E} {e : ℕ → Option (Fin n)}
    (hδ : g.contrast = p.δ) (hσ : g.kick = p.δ ^ 2)
    (hp : ∀ i, ‖g.plus i‖ ≤ 1) (hr : ∀ i, ‖g.minus i‖ ≤ 1)
    (hc : ∀ j, p.ρ ≤ coefficient g j) (hc1 : ∀ j, coefficient g j ≤ 1 / 2)
    (hinit : x 0 = ⟨1, 0, 1, 0⟩) {K : ℕ}
    (hstep : ∀ j, j < K → x (j + 1) = next g (e j) (x j))
    (hpermit : ∀ j, j < K → Permitted g (e j) (x j))
    (hcount : negativeCount e K ≤ p.negatives) : Bounded p.height (x K) := by
  exact bootstrap (A := p.nuisance) p.rho_pos (p.rho_le.trans (by norm_num))
    (by simpa only [hδ] using p.delta_pos) (by rw [hσ]; positivity)
    (by simpa only [hσ] using p.kick_small) p.height_pos hp hr hc hc1 hinit
    (by simpa only [hδ, hσ] using p.global_threshold)
    (by simpa only [hδ, hσ] using p.post_threshold)
    (by simpa only [hδ] using fun j hj => p.decay_threshold (j := j) hj)
    (by simpa only [hδ] using p.noise_threshold)
    (by simpa only [hδ] using p.drift_threshold) p.early_threshold p.height_threshold
    K hstep hpermit hcount

lemma post_prefix (p : Tuning) {g : Gains E n} {x : ℕ → State E} {e : ℕ → Option (Fin n)}
    (hδ : g.contrast = p.δ) (hσ : g.kick = p.δ ^ 2)
    (hp : ∀ i, ‖g.plus i‖ ≤ 1) (hr : ∀ i, ‖g.minus i‖ ≤ 1)
    (hc : ∀ j, p.ρ ≤ coefficient g j) (hc1 : ∀ j, coefficient g j ≤ 1 / 2)
    (hinit : x 0 = ⟨1, 0, 1, 0⟩) {K : ℕ}
    (hstep : ∀ j, j < K → x (j + 1) = next g (e j) (x j))
    (hpermit : ∀ j, j < K → Permitted g (e j) (x j))
    (hcount : negativeCount e K ≤ p.negatives) :
    ∀ j, burnIn p.ρ p.δ ≤ j → j ≤ K → |(x j).a| ≤ p.nuisance ∧ |(x j).q| ≤ p.nuisance := by
  have hb : ∀ j, j ≤ K → Bounded p.height (x j) := by
    intro j hj
    exact bounded_prefix p hδ hσ hp hr hc hc1 hinit
      (fun k hk => hstep k (by omega)) (fun k hk => hpermit k (by omega))
      ((negativeCount_mono e hj).trans hcount)
  have hs := finite_stability p.rho_pos (p.rho_le.trans (by norm_num))
    (by simpa only [hδ] using p.delta_pos.le) (by rw [hσ]; positivity)
    p.height_pos.le hp hc (fun j => (hc1 j).trans (by norm_num))
    (by norm_num [hinit, coordinates])
    (fun hK => cold_first_mass hinit (hc1 none) (p.rho_pos.le.trans (hc none))
      (by rw [hσ]; positivity) (by simpa only [hσ] using p.kick_small)
      (hstep 0 (by omega)) (hpermit 0 (by omega)))
    (fun j hj => (hb j hj.le).2.2.2) hstep hpermit
  intro j hj hjK
  have hmass := hs j hjK
  rw [hδ, hσ] at hmass
  have hdec := p.decay_threshold hj
  have hpost := p.post_threshold
  have hcoord := coordinates_control (x j)
  constructor <;> nlinarith

lemma count_barrier (p : Tuning) {g : Gains E n} {x : ℕ → State E} {e : ℕ → Option (Fin n)}
    {w : E} (hδ : g.contrast = p.δ) (hσ : g.kick = p.δ ^ 2)
    (hp : ∀ i, ‖g.plus i‖ ≤ 1) (hr : ∀ i, ‖g.minus i‖ ≤ 1)
    (hw : ‖w‖ = 1) (hmargin : ∀ i, p.κ ≤ -⟪g.minus i, w⟫)
    (hc : ∀ j, p.ρ ≤ coefficient g j) (hc1 : ∀ j, coefficient g j ≤ 1 / 2)
    (hinit : x 0 = ⟨1, 0, 1, 0⟩) {K : ℕ}
    (hstep : ∀ j, j < K → x (j + 1) = next g (e j) (x j))
    (hpermit : ∀ j, j < K → Permitted g (e j) (x j))
    (hcount : negativeCount e K = p.negatives) : False := by
  have hb : ∀ j, j ≤ K → Bounded p.height (x j) := by
    intro j hj
    exact bounded_prefix p hδ hσ hp hr hc hc1 hinit
      (fun k hk => hstep k (by omega)) (fun k hk => hpermit k (by omega))
      ((negativeCount_mono e hj).trans hcount.le)
  have hBK : burnIn p.ρ p.δ ≤ K :=
    p.burnIn_lt_negatives.le.trans (hcount ▸ negativeCount_le e K)
  have hpost := post_prefix p hδ hσ hp hr hc hc1 hinit hstep hpermit hcount.le
  have hproj := projection_accumulation p.kappa_pos.le hBK hp hw hmargin (hb _ hBK).2.2.2
    (fun j hj hjK => ((hpost j hj hjK.le).1).trans p.nuisance_le_margin)
    (fun j _ hjK => (bounded_signal (hb j hjK.le)).1) hstep
  have hi := real_inner_le_norm (x K).z w
  rw [hw, mul_one] at hi
  have hheight := (hb K le_rfl).2.2.2
  have hm : (negativeCount e (burnIn p.ρ p.δ) : ℝ) ≤ burnIn p.ρ p.δ := by
    exact_mod_cast negativeCount_le e (burnIn p.ρ p.δ)
  have hsep := p.separation_threshold (Nat.cast_nonneg _) hm
  rw [hcount] at hproj
  linarith

lemma negative_count_bound (p : Tuning) {g : Gains E n} {x : ℕ → State E} {e : ℕ → Option (Fin n)}
    {w : E} (hδ : g.contrast = p.δ) (hσ : g.kick = p.δ ^ 2)
    (hp : ∀ i, ‖g.plus i‖ ≤ 1) (hr : ∀ i, ‖g.minus i‖ ≤ 1)
    (hw : ‖w‖ = 1) (hmargin : ∀ i, p.κ ≤ -⟪g.minus i, w⟫)
    (hc : ∀ j, p.ρ ≤ coefficient g j) (hc1 : ∀ j, coefficient g j ≤ 1 / 2)
    (hinit : x 0 = ⟨1, 0, 1, 0⟩) :
    ∀ K, (∀ j, j < K → x (j + 1) = next g (e j) (x j)) →
      (∀ j, j < K → Permitted g (e j) (x j)) → negativeCount e K < p.negatives := by
  intro K
  induction K with
  | zero =>
    intro _ _
    exact (Nat.zero_le _).trans_lt p.burnIn_lt_negatives
  | succ K ih =>
    intro hstep hpermit
    have hi := ih (fun j hj => hstep j (by omega)) (fun j hj => hpermit j (by omega))
    have hle : negativeCount e (K + 1) ≤ p.negatives := by
      simp only [negativeCount]
      split_ifs <;> omega
    by_contra hnot
    have heq : negativeCount e (K + 1) = p.negatives := by omega
    exact count_barrier p hδ hσ hp hr hw hmargin hc hc1 hinit hstep hpermit heq

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma reference_escape (p : Tuning) {c : ℝ} {x : ℕ → State E}
    (hc : p.ρ ≤ c) (hc1 : c ≤ 1 / 2) (ha : |(x 0).a| ≤ 2) (hq : |(x 0).q| ≤ 2)
    (hstep : ∀ j, j < p.referenceLength → x (j + 1) = positive c (p.δ ^ 2) (x j)) :
    0 < (x p.referenceLength).a * (x p.referenceLength).q := by
  let s : ℕ → ℝ := fun j => (x j).a + (x j).q
  let d : ℕ → ℝ := fun j => (x j).a - (x j).q
  have hs : ∀ j, j < p.referenceLength →
      s (j + 1) = (1 + c) * s j + escapeKick (p.δ ^ 2) (s j) := by
    intro j hj
    dsimp only [s]
    rw [hstep j hj]
    simp only [positive]
    ring
  have hd : ∀ j, j < p.referenceLength →
      d (j + 1) = (1 - c) * d j + escapeKick (p.δ ^ 2) (s j) := by
    intro j hj
    dsimp only [s, d]
    rw [hstep j hj]
    simp only [positive]
    ring
  have hsg := escape_growth p.rho_pos.le (sq_nonneg p.δ) (s := s)
    (K := p.referenceLength) (fun j hj => by
      rw [hs j hj, escape_unstable (sq_nonneg p.δ) (p.rho_pos.le.trans hc)]
      have hm := mul_le_mul_of_nonneg_right hc (abs_nonneg (s j))
      linarith)
  have hd0 : |d 0| ≤ 4 := by
    have h := abs_add_le (x 0).a (-(x 0).q)
    rw [abs_neg] at h
    change |(x 0).a - (x 0).q| ≤ 4
    rw [sub_eq_add_neg]
    linarith
  have hdb := escape_stable_bound p.rho_pos (p.rho_le.trans (by norm_num))
    (sq_nonneg p.δ) (by norm_num : (0 : ℝ) ≤ 4) hd0
    (K := p.referenceLength) (fun j hj => by
      rw [hd j hj]
      exact escape_stable (sq_nonneg p.δ) hc (hc1.trans (by norm_num)))
  have hL := p.referenceLength_pos
  have hidx : p.referenceLength - 1 + 1 = p.referenceLength := by omega
  have hsL := hsg (p.referenceLength - 1) (by omega)
  rw [hidx] at hsL
  have hgrowth := p.reference_growth
  have hdL := hdb p.referenceLength le_rfl
  have hquot : p.δ ^ 2 / p.ρ ≤ 1 := (div_le_one p.rho_pos).mpr p.kick_le_rho
  have hbad : ¬|s p.referenceLength| ≤ |d p.referenceLength| := by linarith
  apply lt_of_not_ge
  intro h
  exact hbad ((switch_criterion (x p.referenceLength).a (x p.referenceLength).q).mpr h)

end LongTails.Proofs.ManySampleConvolutionalPerceptronTermination
