import LongTails.Proofs.GatedEscapeDeviation
import LongTails.Proofs.GatedEscapePhases
import LongTails.Proofs.GatedEscapeSlice

namespace LongTails.Proofs.GatedEscapeCoupling

open MeasureTheory LongTails.Algorithms.GatedPerturbedEscape LongTails.Proofs.GatedEscapeProcess
  LongTails.Proofs.GatedEscapeDeviation LongTails.Proofs.GatedEscapePhases
  LongTails.Proofs.GatedEscapeSlice LongTails.Proofs.StrongGrowthAgdBlocks
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {Ω : Type} [MeasurableSpace Ω]
variable (cfg : Config) (g : E → Ω → E) (f : E → ℝ)

noncomputable def nmap (x g0 : E) : E → E := fun w => w - cfg.η • (gradient f (x + w) - g0)

noncomputable def preclip (x g0 v : E) (B : Fin cfg.b → Ω) : E := v - cfg.η • (bmean cfg g (x + v) B - g0)

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
open Classical in
theorem couple (x g0 v0 : E) (R δn : ℝ) (B : ℕ → (Fin cfg.b → Ω)) (h0 : ¬ bad cfg R δn v0 v0) :
    ∀ t, ((run (dstep cfg g f x g0 R δn) (v0, v0, 0, false) B t).2.2.2 = false →
        (run (dstep cfg g f x g0 R δn) (v0, v0, 0, false) B t).1 = vrun cfg g x g0 v0 B t ∧
        (run (dstep cfg g f x g0 R δn) (v0, v0, 0, false) B t).2.1 = orbit (nmap cfg f x g0) t v0 ∧
        (∀ t' ≤ t, ‖orbit (nmap cfg f x g0) t' v0‖ ≤ R) ∧
        ¬ bad cfg R δn (run (dstep cfg g f x g0 R δn) (v0, v0, 0, false) B t).1
          (run (dstep cfg g f x g0 R δn) (v0, v0, 0, false) B t).2.1) ∧
      ((run (dstep cfg g f x g0 R δn) (v0, v0, 0, false) B t).2.2.2 = true →
        ∃ tf, 1 ≤ tf ∧ tf ≤ t ∧
          bad cfg R δn (run (dstep cfg g f x g0 R δn) (v0, v0, 0, false) B t).1
            (run (dstep cfg g f x g0 R δn) (v0, v0, 0, false) B t).2.1 ∧
          (run (dstep cfg g f x g0 R δn) (v0, v0, 0, false) B t).1 =
            preclip cfg g x g0 (vrun cfg g x g0 v0 B (tf - 1)) (B (tf - 1)) ∧
          (run (dstep cfg g f x g0 R δn) (v0, v0, 0, false) B t).2.1 = orbit (nmap cfg f x g0) tf v0) := by
  intro t
  induction t with
  | zero =>
    refine ⟨fun _ => ⟨rfl, rfl, fun t' ht' => ?_, h0⟩, fun h => absurd h (by simp [run_zero])⟩
    have : t' = 0 := by omega
    subst this
    unfold bad at h0
    push Not at h0
    exact h0.2.1
  | succ t ih =>
    obtain ⟨ihu, ihf⟩ := ih
    set D := run (dstep cfg g f x g0 R δn) (v0, v0, 0, false) B t with hD
    rw [run_succ, ← hD]
    by_cases hfz : D.2.2.2 = true
    · have hs : dstep cfg g f x g0 R δn D (B t) = D := by simp only [dstep, hfz, ↓reduceIte]
      rw [hs]
      refine ⟨fun h => absurd hfz (by simp [h]), fun _ => ?_⟩
      obtain ⟨tf, h1, h2, h3, h4, h5⟩ := ihf hfz
      exact ⟨tf, h1, by omega, h3, h4, h5⟩
    · have hf : D.2.2.2 = false := by simpa using hfz
      obtain ⟨hu1, hw1, hR, _⟩ := ihu hf
      have hval : dstep cfg g f x g0 R δn D (B t) =
          (preclip cfg g x g0 (vrun cfg g x g0 v0 B t) (B t), orbit (nmap cfg f x g0) (t + 1) v0,
            D.2.2.1 + 1, decide (bad cfg R δn (preclip cfg g x g0 (vrun cfg g x g0 v0 B t) (B t))
              (orbit (nmap cfg f x g0) (t + 1) v0))) := by
        simp only [dstep, hf, Bool.false_eq_true, ↓reduceIte, hu1, hw1]
        rfl
      rw [hval]
      by_cases hb : bad cfg R δn (preclip cfg g x g0 (vrun cfg g x g0 v0 B t) (B t))
          (orbit (nmap cfg f x g0) (t + 1) v0)
      · refine ⟨fun h => absurd h (by simp [hb]), fun _ => ⟨t + 1, by omega, le_rfl, hb, by simp, rfl⟩⟩
      · refine ⟨fun _ => ⟨?_, rfl, ?_, hb⟩, fun h => absurd h (by simp [hb])⟩
        · show preclip cfg g x g0 (vrun cfg g x g0 v0 B t) (B t) = vstep cfg g x g0 (vrun cfg g x g0 v0 B t) (B t)
          have hb' := hb
          unfold bad at hb'
          push Not at hb'
          show preclip cfg g x g0 (vrun cfg g x g0 v0 B t) (B t) =
            clip cfg.r (preclip cfg g x g0 (vrun cfg g x g0 v0 B t) (B t))
          unfold clip
          rw [ite_eq_left hb'.1]
        · intro t' ht'
          rcases Nat.lt_or_ge t' (t + 1) with hlt | hge
          · exact hR t' (by omega)
          · have : t' = t + 1 := by omega
            subst this
            unfold bad at hb
            push Not at hb
            exact hb.2.1

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
theorem exit_or_dev (x g0 v0 : E) (R δn : ℝ) (B : ℕ → (Fin cfg.b → Ω)) (h0 : ¬ bad cfg R δn v0 v0)
    (hRr : cfg.r + δn ≤ R) (T' : ℕ) (hexit : ∃ t ≤ T', R < ‖orbit (nmap cfg f x g0) t v0‖) :
    ((run (dstep cfg g f x g0 R δn) (v0, v0, 0, false) B T').2.2.2 = true ∧
        δn < ‖(run (dstep cfg g f x g0 R δn) (v0, v0, 0, false) B T').1 -
          (run (dstep cfg g f x g0 R δn) (v0, v0, 0, false) B T').2.1‖) ∨
      ∃ τ < T', cfg.r < ‖preclip cfg g x g0 (vrun cfg g x g0 v0 B τ) (B τ)‖ := by
  obtain ⟨hu, hfz⟩ := couple cfg g f x g0 v0 R δn B h0 T'
  set D := run (dstep cfg g f x g0 R δn) (v0, v0, 0, false) B T'
  by_cases hf : D.2.2.2 = true
  · obtain ⟨tf, h1, h2, h3, h4, h5⟩ := hfz hf
    by_cases hdev : δn < ‖D.1 - D.2.1‖
    · exact Or.inl ⟨hf, hdev⟩
    · right
      refine ⟨tf - 1, by omega, ?_⟩
      rw [← h4]
      push Not at hdev
      unfold bad at h3
      rcases h3 with h | h | h
      · exact h
      · have := norm_sub_norm_le D.2.1 D.1
        rw [norm_sub_rev] at this
        linarith
      · linarith
  · have hf' : D.2.2.2 = false := by simpa using hf
    obtain ⟨_, _, hR, _⟩ := hu hf'
    obtain ⟨t, ht, hgt⟩ := hexit
    exact absurd (hR t ht) (not_le.mpr hgt)

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
lemma preclip_split (x g0 v : E) (B : Fin cfg.b → Ω) (H : E →L[ℝ] E) :
    preclip cfg g x g0 v B = v - cfg.η • H v - cfg.η • (gradient f (x + v) - H v - g0) -
      cfg.η • (bmean cfg g (x + v) B - gradient f (x + v)) := by
  unfold preclip; module

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
lemma vrun_succ_split (x g0 v0 : E) (B : ℕ → (Fin cfg.b → Ω)) (H : E →L[ℝ] E) (t : ℕ) :
    vrun cfg g x g0 v0 B (t + 1) = clip cfg.r (vrun cfg g x g0 v0 B t - cfg.η • H (vrun cfg g x g0 v0 B t) -
      cfg.η • (gradient f (x + vrun cfg g x g0 v0 B t) - H (vrun cfg g x g0 v0 B t) - g0) -
      cfg.η • (bmean cfg g (x + vrun cfg g x g0 v0 B t) (B t) - gradient f (x + vrun cfg g x g0 v0 B t))) := by
  show vstep cfg g x g0 _ _ = _
  unfold vstep
  rw [← preclip_split cfg g f x g0 _ (B t) H]
  rfl

end LongTails.Proofs.GatedEscapeCoupling
