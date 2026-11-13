import LongTails.Proofs.GatedEscapeGlobal
import LongTails.Proofs.GatedEscapeSaddle

namespace LongTails.Proofs.GatedEscapeLook

open MeasureTheory ProbabilityTheory LongTails.Algorithms.GatedPerturbedEscape
  LongTails.Proofs.GatedEscapeProcess LongTails.Proofs.GatedEscapeMoments
  LongTails.Proofs.GatedEscapePhases LongTails.Proofs.GatedEscapeAttempt
  LongTails.Proofs.GatedEscapeMeasurable LongTails.Proofs.GatedEscapeEscape
  LongTails.Proofs.GatedEscapeGlobal LongTails.Proofs.GatedEscapeLookahead
  LongTails.Proofs.GatedEscapeMajority LongTails.Proofs.GatedEscapeAttemptProb
  LongTails.Proofs.GatedEscapeSaddle LongTails.Proofs.StrongGrowthAgdBlocks
  LongTails.Proofs.ComparisonTrustTaylor
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {Ω : Type} [MeasurableSpace Ω] {p : Measure Ω} [IsProbabilityMeasure p] {σ : ℝ}
variable (cfg : Config) (d : ℕ) (g : E → Ω → E) (f : E → ℝ)

theorem look_test (hb : 0 < cfg.b) (hN : Noise g (gradient f) p σ) (hM : 0 < cfg.M) (hτg : 0 < cfg.τg)
    (hvar : σ ^ 2 / cfg.b / cfg.τg ^ 2 ≤ 1 / 16) (γ : ℝ) (s : State E) (hd : s.done = false)
    (hph : s.ph = .test) (hj : s.j = 0) :
    look (astep cfg d g) ((Measure.pi fun _ : Fin cfg.b => p).prod (stdGaussian E)) (rem cfg)
      (Gg cfg d g f γ) s ≤ (19 / 32) ^ cfg.M := by
  have hr : rem cfg s = cfg.M := by simp [rem, remA, hd, hph, hj]
  unfold look
  rw [hr]
  obtain ⟨m, hm⟩ : ∃ m, cfg.M = m + 1 := ⟨cfg.M - 1, by omega⟩
  have hmM : cfg.M - 1 = m := by omega
  rw [hmM]
  have hpre : ∀ tail : ℕ → (Fin cfg.b → Ω) × E, run (astep cfg d g) s tail m =
      { s with store := fill cfg g s.store s.x tail m, j := m, t := s.t + m } :=
    fun tail => run_test cfg d g s hd hph hj tail m (by omega)
  have hval : ∀ tail : ℕ → (Fin cfg.b → Ω) × E,
      Gg cfg d g f γ (run (astep cfg d g) s tail m) (tail m) =
        if 3 * cfg.τg < ‖select cfg.M cfg.τg (fill cfg g s.store s.x tail cfg.M) - gradient f s.x‖
        then 1 else 0 := by
    intro tail
    rw [hpre tail]
    simp only [Gg, hd, hph, Bool.false_eq_true, ↓reduceIte, testBad]
    rw [fill_succ, ← hm]
  simp_rw [hval]
  have hmaj := mom_phase cfg hb hN (stdGaussian E) s.x hτg hvar
  refine le_trans (integral_mono_of_nonneg (Filter.Eventually.of_forall fun β => by
    simp only [Pi.zero_apply]; split_ifs <;> norm_num) (maj_integrable cfg g f hN _ _)
    (Filter.Eventually.of_forall fun β => ?_)) hmaj
  exact ite_ind_le' (fun h1 => majority_of_not cfg.M cfg.τg _ _
    (fun c => cfg.τg < ‖bmean cfg g s.x (β c).1 - gradient f s.x‖)
    (fun c hc hnot => by unfold fill; rw [ite_eq_left hc]; push Not at hnot; exact hnot) (not_le.mpr h1))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
lemma last_state (hM : 0 < cfg.M) (hT : 0 < cfg.T) (hk : 0 < cfg.k) (s : State E)
    (hs : AttStart cfg s.x s) (ha0 : s.att = 0) (tail : ℕ → (Fin cfg.b → Ω) × E) :
    (run (astep cfg d g) s tail (cfg.k * alen cfg - 1)).done = false ∧
      (run (astep cfg d g) s tail (cfg.k * alen cfg - 1)).ph = .ray ∧
      ((run (astep cfg d g) s tail (cfg.k * alen cfg)).done = true →
        (run (astep cfg d g) s tail (cfg.k * alen cfg)).x = s.x) := by
  obtain ⟨m, hm⟩ : ∃ m, cfg.k = m + 1 := ⟨cfg.k - 1, by omega⟩
  obtain ⟨⟨hd, hph, hj, hx, _⟩, hat⟩ := reach_attempt cfg d g hM hT s.x s hs ha0 tail m (by omega)
  set s' := run (astep cfg d g) s tail (m * alen cfg) with hs'
  have hA : alen cfg = cfg.M + 1 + cfg.T + cfg.M := rfl
  have e1 : cfg.k * alen cfg - 1 = m * alen cfg + (cfg.M + 1 + cfg.T + (cfg.M - 1)) := by
    rw [hm, hA]; ring_nf; omega
  have e2 : cfg.k * alen cfg = m * alen cfg + alen cfg := by rw [hm]; ring
  obtain ⟨_, _, _, _, _, h3ph, h3j, h3d, _, _, _⟩ :=
    post_core cfg d g s' hd hph hj hM hT (shift (m * alen cfg) tail)
  set s3 := run (astep cfg d g) s' (shift (m * alen cfg) tail) (cfg.M + 1 + cfg.T)
  have hray := run_ray cfg d g s3 h3d h3ph h3j (shift (cfg.M + 1 + cfg.T) (shift (m * alen cfg) tail))
    (cfg.M - 1) (by omega)
  have hlast : run (astep cfg d g) s tail (cfg.k * alen cfg - 1) =
      run (astep cfg d g) s3 (shift (cfg.M + 1 + cfg.T) (shift (m * alen cfg) tail)) (cfg.M - 1) := by
    rw [e1, run_add, ← hs', run_add]
  refine ⟨by rw [hlast, hray]; exact h3d, by rw [hlast, hray]; exact h3ph, fun hdn => ?_⟩
  rw [e2, run_add, ← hs'] at hdn ⊢
  obtain ⟨_, hl⟩ := post_fields cfg d g s' hd hph hj hM hT (shift (m * alen cfg) tail)
  obtain ⟨hl1, hl2⟩ := hl (by rw [hat]; omega)
  by_cases hc : s'.found = true ∨ (s'.found = false ∧
      accS cfg (run (astep cfg d g) s' (shift (m * alen cfg) tail) (alen cfg)))
  · exact absurd hdn (by rw [(hl1 hc).1]; simp)
  · rw [(hl2 hc).2, hx]

theorem look_escape {L ρ γ : ℝ} (H : SHyp cfg L ρ γ σ d) (hdE : d = Module.finrank ℝ E)
    (hsm : Smooth f L ρ) (hN : Noise g (gradient f) p σ) (hσ : 0 ≤ σ) (hM : 0 < cfg.M) (hk : 0 < cfg.k)
    (hM6 : (19 / 32 : ℝ) ^ cfg.M ≤ 1 / 20) (hτq : 0 < cfg.τq) (h3τq : 3 * cfg.τq ≤ 3 * cfg.θ / 8)
    (hvar0 : σ ^ 2 / cfg.b / cfg.τ0 ^ 2 ≤ 1 / 16) (hvarq : σ ^ 2 / cfg.b / (cfg.r * cfg.τq) ^ 2 ≤ 1 / 16)
    (s : State E) (hs : AttStart cfg s.x s) (ha0 : s.att = 0) (hf0 : s.found = false) :
    look (astep cfg d g) ((Measure.pi fun _ : Fin cfg.b => p).prod (stdGaussian E)) (rem cfg)
      (Gg cfg d g f γ) s ≤ (1 / 4) ^ cfg.k + cfg.k * (2 * (19 / 32) ^ cfg.M) := by
  classical
  set ν := (Measure.pi fun _ : Fin cfg.b => p).prod (stdGaussian E)
  have hT := H.hT
  have hstep := measurable_astep cfg d g hN.meas
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hsm.hf x).continuousAt
  have hgf : Continuous (gradient f) :=
    LipschitzWith.continuous (K := ⟨|L|, abs_nonneg L⟩) (LipschitzWith.of_dist_le_mul fun y z => by
      rw [dist_eq_norm, dist_eq_norm]
      exact (hsm.lip y z).trans (mul_le_mul_of_nonneg_right (le_abs_self L) (norm_nonneg _)))
  have hr : 0 < cfg.r := by rw [H.hr]; exact div_pos H.hθ H.hρ
  have hρr : ρ * cfg.r ≤ cfg.θ := by rw [H.hr, mul_div_cancel₀ _ H.hρ.ne']
  have ⟨hd, hph, hj, _, _⟩ := hs
  have hrem : rem cfg s = cfg.k * alen cfg := by
    simp only [rem, remA, hd, hph, hj, ha0, Bool.false_eq_true, ↓reduceIte, Nat.sub_zero]
    obtain ⟨m, hm⟩ : ∃ m, cfg.k = m + 1 := ⟨cfg.k - 1, by omega⟩
    rw [hm]; simp; ring
  unfold look
  rw [hrem]
  have hval : ∀ tail : ℕ → (Fin cfg.b → Ω) × E,
      Gg cfg d g f γ (run (astep cfg d g) s tail (cfg.k * alen cfg - 1)) (tail (cfg.k * alen cfg - 1)) =
        Gesc cfg f (sadS f γ s.x) (run (astep cfg d g) s tail (cfg.k * alen cfg)) := by
    intro tail
    obtain ⟨l1, l2, l3⟩ := last_state cfg d g hM hT hk s hs ha0 tail
    have hsucc : run (astep cfg d g) s tail (cfg.k * alen cfg) =
        astep cfg d g (run (astep cfg d g) s tail (cfg.k * alen cfg - 1)) (tail (cfg.k * alen cfg - 1)) := by
      have : cfg.k * alen cfg = cfg.k * alen cfg - 1 + 1 := by
        have : 0 < cfg.k * alen cfg := Nat.mul_pos hk (by unfold alen; omega)
        omega
      conv_lhs => rw [this]
      rfl
    simp only [Gg, l1, l2, Bool.false_eq_true, ↓reduceIte, reduceCtorEq]
    rw [← hsucc]
    unfold GescG Gesc
    by_cases hdn : (run (astep cfg d g) s tail (cfg.k * alen cfg)).done = true
    · rw [ite_eq_left hdn, ite_eq_left hdn, l3 hdn]
    · rw [ite_eq_right hdn, ite_eq_right hdn]
  simp_rw [hval]
  have hb := escape_bound cfg d g f (ν := ν) hM hT hk hstep hfc s.x (sadS f γ s.x) (ε := (19 / 32) ^ cfg.M)
    (by positivity)
    (fun s' hs' hf' => by
      obtain ⟨hd', hph', hj', hx', _⟩ := hs'
      have := prob_harm cfg d g f H.hb hN hsm H.hρ.le hM hT hr H.hθ.le hρr H.hτ0 H.h3τ0 hτq h3τq hvar0 hvarq
        hgf s' hd' hph' hj'
      rw [hx'] at this; exact this)
    (fun hsad s' hs' hf' => by
      obtain ⟨hd', hph', hj', hx', _⟩ := hs'
      exact prob_miss cfg d g f H hdE hsm hN hσ hM hM6 hτq h3τq hvar0 hvarq s' hd' hph' hj'
        (by rw [hx']; exact hsad))
    s hs hf0 ha0
  refine hb.trans ?_
  have : (if sadS f γ s.x then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  have h4 : (0 : ℝ) ≤ (1 / 4) ^ cfg.k := by positivity
  nlinarith

end LongTails.Proofs.GatedEscapeLook
