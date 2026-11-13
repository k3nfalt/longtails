import LongTails.Proofs.GatedEscapeEscape
import LongTails.Proofs.GatedEscapeLookahead

namespace LongTails.Proofs.GatedEscapeGlobal

open MeasureTheory ProbabilityTheory LongTails.Algorithms.GatedPerturbedEscape
  LongTails.Proofs.GatedEscapeProcess LongTails.Proofs.GatedEscapePhases
  LongTails.Proofs.GatedEscapeAttempt LongTails.Proofs.GatedEscapeMeasurable
  LongTails.Proofs.GatedEscapeEscape LongTails.Proofs.GatedEscapeLookahead
  LongTails.Proofs.StrongGrowthAgdBlocks
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {Ω : Type} [MeasurableSpace Ω]
variable (cfg : Config) (d : ℕ) (g : E → Ω → E) (f : E → ℝ)

def Good (s : State E) : Prop :=
  s.done = true ∨
    (s.ph = .test ∧ s.j < cfg.M) ∨ (s.ph = .grad0 ∧ s.j < cfg.M ∧ s.att < cfg.k) ∨
    (s.ph = .init ∧ s.j = 0 ∧ s.att < cfg.k) ∨ (s.ph = .traj ∧ s.j < cfg.T ∧ s.att < cfg.k) ∨
    (s.ph = .ray ∧ s.j < cfg.M ∧ s.att < cfg.k)

def remA (s : State E) : ℕ :=
  match s.ph with
  | .test => cfg.M - s.j
  | .grad0 => (cfg.k - s.att - 1) * alen cfg + (alen cfg - s.j)
  | .init => (cfg.k - s.att - 1) * alen cfg + (alen cfg - cfg.M)
  | .traj => (cfg.k - s.att - 1) * alen cfg + (alen cfg - cfg.M - 1 - s.j)
  | .ray => (cfg.k - s.att - 1) * alen cfg + (alen cfg - cfg.M - 1 - cfg.T - s.j)

def rem (s : State E) : ℕ := if s.done = true then 0 else remA cfg s

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
lemma step_live (s : State E) (hd : s.done = false) (y : (Fin cfg.b → Ω) × E) :
    astep cfg d g s y = { blockUpdate cfg d s (bmean cfg g (queryPoint cfg s) y.1) y.2 with t := s.t + 1 } :=
  astep_live cfg d g s hd y

lemma pfacts (k a A : ℕ) :
    (k - a - 1 = 0 ∧ (k - a - 1) * A = 0) ∨ (1 ≤ k - a - 1 ∧ A ≤ (k - a - 1) * A) := by
  rcases Nat.eq_zero_or_pos (k - a - 1) with h | h
  · left; exact ⟨h, by rw [h, zero_mul]⟩
  · right; exact ⟨h, Nat.le_mul_of_pos_left A h⟩

lemma att_mul (k a A : ℕ) (h : a + 1 < k) : (k - (a + 1) - 1) * A + A = (k - a - 1) * A := by
  have e : k - a - 1 = (k - (a + 1) - 1) + 1 := by omega
  rw [e, add_mul, one_mul]

lemma rem_le_aux (k a A : ℕ) (h : a < k) : (k - a - 1) * A + A ≤ k * A := by
  have e : (k - a - 1) * A + A = (k - a - 1 + 1) * A := by rw [add_mul, one_mul]
  rw [e]
  exact Nat.mul_le_mul_right A (by omega)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
lemma tr_test (s : State E) (hd : s.done = false) (hph : s.ph = .test) (y : (Fin cfg.b → Ω) × E) :
    (astep cfg d g s y).done = false ∧
    (s.j + 1 < cfg.M → (astep cfg d g s y).ph = .test ∧ (astep cfg d g s y).j = s.j + 1 ∧
      (astep cfg d g s y).x = s.x) ∧
    (¬ s.j + 1 < cfg.M → (astep cfg d g s y).j = 0 ∧ ((astep cfg d g s y).ph = .test ∨
      ((astep cfg d g s y).ph = .grad0 ∧ (astep cfg d g s y).att = 0 ∧
        (astep cfg d g s y).found = false ∧ (astep cfg d g s y).x = s.x))) := by
  rw [step_live cfg d g s hd]
  simp only [blockUpdate, hph]
  split_ifs with h1 <;> simp [hd, h1]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
lemma tr_grad0 (s : State E) (hd : s.done = false) (hph : s.ph = .grad0) (y : (Fin cfg.b → Ω) × E) :
    (astep cfg d g s y).done = false ∧ (astep cfg d g s y).x = s.x ∧
    (astep cfg d g s y).att = s.att ∧
    (s.j + 1 < cfg.M → (astep cfg d g s y).ph = .grad0 ∧ (astep cfg d g s y).j = s.j + 1) ∧
    (¬ s.j + 1 < cfg.M → (astep cfg d g s y).ph = .init ∧ (astep cfg d g s y).j = 0) := by
  rw [step_live cfg d g s hd]
  simp only [blockUpdate, hph]
  split_ifs with h1 <;> simp [hd, h1]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
lemma tr_init (s : State E) (hd : s.done = false) (hph : s.ph = .init) (y : (Fin cfg.b → Ω) × E) :
    (astep cfg d g s y).done = false ∧ (astep cfg d g s y).x = s.x ∧
    (astep cfg d g s y).att = s.att ∧ (astep cfg d g s y).ph = .traj ∧
    (astep cfg d g s y).j = s.j := by
  rw [step_live cfg d g s hd]
  simp [blockUpdate, hph, hd]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
lemma tr_traj (s : State E) (hd : s.done = false) (hph : s.ph = .traj) (y : (Fin cfg.b → Ω) × E) :
    (astep cfg d g s y).done = false ∧ (astep cfg d g s y).x = s.x ∧
    (astep cfg d g s y).att = s.att ∧
    (s.j + 1 < cfg.T → (astep cfg d g s y).ph = .traj ∧ (astep cfg d g s y).j = s.j + 1) ∧
    (¬ s.j + 1 < cfg.T → (astep cfg d g s y).ph = .ray ∧ (astep cfg d g s y).j = 0) := by
  rw [step_live cfg d g s hd]
  simp only [blockUpdate, hph]
  split_ifs with h1 <;> simp [hd, h1]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
lemma tr_ray (s : State E) (hd : s.done = false) (hph : s.ph = .ray) (y : (Fin cfg.b → Ω) × E) :
    (s.j + 1 < cfg.M → (astep cfg d g s y).done = false ∧ (astep cfg d g s y).x = s.x ∧
      (astep cfg d g s y).att = s.att ∧ (astep cfg d g s y).ph = .ray ∧
      (astep cfg d g s y).j = s.j + 1) ∧
    (¬ s.j + 1 < cfg.M → s.att + 1 < cfg.k → (astep cfg d g s y).done = false ∧
      (astep cfg d g s y).x = s.x ∧ (astep cfg d g s y).att = s.att + 1 ∧
      (astep cfg d g s y).ph = .grad0 ∧ (astep cfg d g s y).j = 0) ∧
    (¬ s.j + 1 < cfg.M → ¬ s.att + 1 < cfg.k →
      ((astep cfg d g s y).done = true ∧ (astep cfg d g s y).x = s.x) ∨
      ((astep cfg d g s y).done = false ∧ (astep cfg d g s y).ph = .test ∧
        (astep cfg d g s y).j = 0 ∧ (astep cfg d g s y).x - (astep cfg d g s y).dx = s.x)) := by
  rw [step_live cfg d g s hd]
  simp only [blockUpdate, hph, endAttempt]
  split_ifs <;> simp_all

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
theorem step_good (hM : 0 < cfg.M) (hT : 0 < cfg.T) (hk : 0 < cfg.k) (s : State E) (hs : Good cfg s)
    (y : (Fin cfg.b → Ω) × E) :
    Good cfg (astep cfg d g s y) ∧
      (s.done = true → astep cfg d g s y = s) ∧
      (s.done = false → 2 ≤ rem cfg s → rem cfg (astep cfg d g s y) = rem cfg s - 1) ∧
      (s.done = false → rem cfg s = 1 →
        ((astep cfg d g s y).done = false ∧ (astep cfg d g s y).ph = .test ∧
            (astep cfg d g s y).j = 0) ∨
          ((astep cfg d g s y).done = false ∧ (astep cfg d g s y).ph = .grad0 ∧
            (astep cfg d g s y).j = 0 ∧ (astep cfg d g s y).att = 0 ∧
            (astep cfg d g s y).found = false ∧ (astep cfg d g s y).x = s.x) ∨
          (astep cfg d g s y).done = true) ∧
      (1 ≤ rem cfg s ∨ s.done = true) := by
  by_cases hd : s.done = true
  · have h := astep_done cfg d g s hd y
    refine ⟨by rw [h]; exact hs, fun _ => h, fun h' => absurd hd (by simp [h']),
      fun h' => absurd hd (by simp [h']), Or.inr hd⟩
  have hd' : s.done = false := by simpa using hd
  have : alen cfg = cfg.M + 1 + cfg.T + cfg.M := rfl
  have := pfacts cfg.k s.att (alen cfg)
  rcases hs with h0 | ⟨hph, hj⟩ | ⟨hph, hj, ha⟩ | ⟨hph, hj, ha⟩ | ⟨hph, hj, ha⟩ | ⟨hph, hj, ha⟩
  · exact absurd h0 hd
  · have hr : rem cfg s = cfg.M - s.j := by
      simp only [rem, remA, hd', hph, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨t1, t2, t3⟩ := tr_test cfg d g s hd' hph y
    by_cases hj1 : s.j + 1 < cfg.M
    · obtain ⟨u1, u2, _⟩ := t2 hj1
      have hr' : rem cfg (astep cfg d g s y) = cfg.M - (s.j + 1) := by
        simp only [rem, remA, t1, u1, u2, Bool.false_eq_true, ↓reduceIte]
      exact ⟨Or.inr (Or.inl ⟨u1, by rw [u2]; exact hj1⟩), fun h => absurd h hd, fun _ _ => by omega,
        fun _ h => absurd h (by omega), Or.inl (by omega)⟩
    · obtain ⟨u1, u2⟩ := t3 hj1
      refine ⟨?_, fun h => absurd h hd, fun _ h => absurd h (by omega), fun _ _ => ?_,
        Or.inl (by omega)⟩
      · rcases u2 with v | ⟨v1, v2, _, _⟩
        · exact Or.inr (Or.inl ⟨v, by rw [u1]; exact hM⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨v1, by rw [u1]; exact hM, by rw [v2]; exact hk⟩))
      · rcases u2 with v | ⟨v1, v2, v3, v4⟩
        · exact Or.inl ⟨t1, v, u1⟩
        · exact Or.inr (Or.inl ⟨t1, v1, u1, v2, v3, v4⟩)
  · have hr : rem cfg s = (cfg.k - s.att - 1) * alen cfg + (alen cfg - s.j) := by
      simp only [rem, remA, hd', hph, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨t1, _, t3, t4, t5⟩ := tr_grad0 cfg d g s hd' hph y
    by_cases hj1 : s.j + 1 < cfg.M
    · obtain ⟨u1, u2⟩ := t4 hj1
      have hr' : rem cfg (astep cfg d g s y) =
          (cfg.k - s.att - 1) * alen cfg + (alen cfg - (s.j + 1)) := by
        simp only [rem, remA, t1, u1, u2, t3, Bool.false_eq_true, ↓reduceIte]
      exact ⟨Or.inr (Or.inr (Or.inl ⟨u1, by rw [u2]; exact hj1, by rw [t3]; exact ha⟩)),
        fun h => absurd h hd, fun _ _ => by omega, fun _ h => absurd h (by omega), Or.inl (by omega)⟩
    · obtain ⟨u1, u2⟩ := t5 hj1
      have hr' : rem cfg (astep cfg d g s y) = (cfg.k - s.att - 1) * alen cfg + (alen cfg - cfg.M) := by
        simp only [rem, remA, t1, u1, t3, Bool.false_eq_true, ↓reduceIte]
      exact ⟨Or.inr (Or.inr (Or.inr (Or.inl ⟨u1, u2, by rw [t3]; exact ha⟩))),
        fun h => absurd h hd, fun _ _ => by omega, fun _ h => absurd h (by omega), Or.inl (by omega)⟩
  · have hr : rem cfg s = (cfg.k - s.att - 1) * alen cfg + (alen cfg - cfg.M) := by
      simp only [rem, remA, hd', hph, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨t1, _, t3, t4, t5⟩ := tr_init cfg d g s hd' hph y
    have hr' : rem cfg (astep cfg d g s y) =
        (cfg.k - s.att - 1) * alen cfg + (alen cfg - cfg.M - 1 - s.j) := by
      simp only [rem, remA, t1, t4, t5, t3, Bool.false_eq_true, ↓reduceIte]
    exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨t4, by rw [t5, hj]; exact hT,
        by rw [t3]; exact ha⟩)))),
      fun h => absurd h hd, fun _ _ => by omega, fun _ h => absurd h (by omega), Or.inl (by omega)⟩
  · have hr : rem cfg s = (cfg.k - s.att - 1) * alen cfg + (alen cfg - cfg.M - 1 - s.j) := by
      simp only [rem, remA, hd', hph, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨t1, _, t3, t4, t5⟩ := tr_traj cfg d g s hd' hph y
    by_cases hj1 : s.j + 1 < cfg.T
    · obtain ⟨u1, u2⟩ := t4 hj1
      have hr' : rem cfg (astep cfg d g s y) =
          (cfg.k - s.att - 1) * alen cfg + (alen cfg - cfg.M - 1 - (s.j + 1)) := by
        simp only [rem, remA, t1, u1, u2, t3, Bool.false_eq_true, ↓reduceIte]
      exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨u1, by rw [u2]; exact hj1,
          by rw [t3]; exact ha⟩)))),
        fun h => absurd h hd, fun _ _ => by omega, fun _ h => absurd h (by omega), Or.inl (by omega)⟩
    · obtain ⟨u1, u2⟩ := t5 hj1
      have hr' : rem cfg (astep cfg d g s y) =
          (cfg.k - s.att - 1) * alen cfg + (alen cfg - cfg.M - 1 - cfg.T - 0) := by
        simp only [rem, remA, t1, u1, u2, t3, Bool.false_eq_true, ↓reduceIte]
      exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨u1, by rw [u2]; exact hM,
          by rw [t3]; exact ha⟩)))),
        fun h => absurd h hd, fun _ _ => by omega, fun _ h => absurd h (by omega), Or.inl (by omega)⟩
  · have hr : rem cfg s = (cfg.k - s.att - 1) * alen cfg + (alen cfg - cfg.M - 1 - cfg.T - s.j) := by
      simp only [rem, remA, hd', hph, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨t1, t2, t3⟩ := tr_ray cfg d g s hd' hph y
    by_cases hj1 : s.j + 1 < cfg.M
    · obtain ⟨u1, _, u3, u4, u5⟩ := t1 hj1
      have hr' : rem cfg (astep cfg d g s y) =
          (cfg.k - s.att - 1) * alen cfg + (alen cfg - cfg.M - 1 - cfg.T - (s.j + 1)) := by
        simp only [rem, remA, u1, u4, u5, u3, Bool.false_eq_true, ↓reduceIte]
      exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨u4, by rw [u5]; exact hj1,
          by rw [u3]; exact ha⟩)))),
        fun h => absurd h hd, fun _ _ => by omega, fun _ h => absurd h (by omega), Or.inl (by omega)⟩
    · by_cases ha1 : s.att + 1 < cfg.k
      · obtain ⟨u1, _, u3, u4, u5⟩ := t2 hj1 ha1
        have hr' : rem cfg (astep cfg d g s y) =
            (cfg.k - (s.att + 1) - 1) * alen cfg + (alen cfg - 0) := by
          simp only [rem, remA, u1, u4, u5, u3, Bool.false_eq_true, ↓reduceIte]
        have := att_mul cfg.k s.att (alen cfg) ha1
        exact ⟨Or.inr (Or.inr (Or.inl ⟨u4, by rw [u5]; exact hM, by rw [u3]; exact ha1⟩)),
          fun h => absurd h hd, fun _ _ => by omega, fun _ h => absurd h (by omega),
          Or.inl (by omega)⟩
      · rcases t3 hj1 ha1 with ⟨v1, _⟩ | ⟨v1, v2, v3, _⟩
        · exact ⟨Or.inl v1, fun h => absurd h hd, fun _ h => absurd h (by omega),
            fun _ _ => Or.inr (Or.inr v1), Or.inl (by omega)⟩
        · exact ⟨Or.inr (Or.inl ⟨v2, by rw [v3]; exact hM⟩), fun h => absurd h hd,
            fun _ h => absurd h (by omega), fun _ _ => Or.inl ⟨v1, v2, v3⟩, Or.inl (by omega)⟩

noncomputable def testBad (s : State E) (y : (Fin cfg.b → Ω) × E) : ℝ :=
  if 3 * cfg.τg < ‖select cfg.M cfg.τg (Function.update s.store s.j (bmean cfg g s.x y.1)) - gradient f s.x‖
  then 1 else 0

def sadS (γ : ℝ) (x : E) : Prop := ∃ v : E, ⟪v, fderiv ℝ (gradient f) x v⟫ < -γ * ‖v‖ ^ 2

open Classical in
noncomputable def GescG (γ : ℝ) (s : State E) : ℝ :=
  if s.done = true then (if sadS f γ s.x then 1 else 0) else harm cfg f (s.x - s.dx) s.dx

noncomputable def Gg (γ : ℝ) (s : State E) (y : (Fin cfg.b → Ω) × E) : ℝ :=
  if s.done = true then 0 else if s.ph = .test then testBad cfg g f s y else GescG cfg f γ (astep cfg d g s y)

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
lemma testBad_le (s : State E) (y : (Fin cfg.b → Ω) × E) :
    0 ≤ testBad cfg g f s y ∧ testBad cfg g f s y ≤ 1 := by
  unfold testBad; split_ifs <;> norm_num

omit [MeasurableSpace E] [BorelSpace E] in
lemma GescG_le (γ : ℝ) (s : State E) : 0 ≤ GescG cfg f γ s ∧ GescG cfg f γ s ≤ 1 := by
  unfold GescG harm; split_ifs <;> norm_num

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
lemma Gg_le (γ : ℝ) (s : State E) (y : (Fin cfg.b → Ω) × E) :
    0 ≤ Gg cfg d g f γ s y ∧ Gg cfg d g f γ s y ≤ 1 := by
  unfold Gg
  split_ifs
  · norm_num
  · exact testBad_le cfg g f s y
  · exact GescG_le cfg f γ _

omit [MeasurableSpace E] [BorelSpace E] in
lemma sadS_open {ρ : ℝ} (hρc : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ ρ * ‖x - y‖)
    (γ : ℝ) : IsOpen {x : E | sadS f γ x} := by
  have hc : Continuous (fun x => fderiv ℝ (gradient f) x) :=
    LipschitzWith.continuous (K := ⟨|ρ|, abs_nonneg ρ⟩) (LipschitzWith.of_dist_le_mul fun y z => by
      rw [dist_eq_norm, dist_eq_norm]
      exact (hρc y z).trans (mul_le_mul_of_nonneg_right (le_abs_self ρ) (norm_nonneg _)))
  have : {x : E | sadS f γ x} = ⋃ v : E, {x | ⟪v, fderiv ℝ (gradient f) x v⟫ < -γ * ‖v‖ ^ 2} := by
    ext x; simp [sadS]
  rw [this]
  refine isOpen_iUnion fun v => isOpen_lt ?_ continuous_const
  exact continuous_const.inner ((ContinuousLinearMap.apply ℝ E v).continuous.comp hc)

variable {ν : Measure ((Fin cfg.b → Ω) × E)} [IsProbabilityMeasure ν]

omit [BorelSpace E] [IsProbabilityMeasure ν] in
lemma look_done (γ : ℝ) (s : State E) (hd : s.done = true) :
    look (astep cfg d g) ν (rem cfg) (Gg cfg d g f γ) s = 0 := by
  unfold look
  have hr : rem cfg s = 0 := by simp [rem, hd]
  rw [hr]
  simp only [Nat.zero_sub, run_zero]
  simp [Gg, hd]

omit [BorelSpace E] in
theorem global_count (hM : 0 < cfg.M) (hT : 0 < cfg.T) (hk : 0 < cfg.k)
    (hstep : Measurable (Function.uncurry (astep cfg d g))) (hremm : Measurable (rem cfg (E := E)))
    (γ : ℝ) (hGm : Measurable (Function.uncurry (Gg cfg d g f γ (Ω := Ω))))
    {p ε pE : ℝ} (hp : 0 ≤ p) (hεp : ε ≤ p) (hpE : pE ≤ p)
    (hlookT : ∀ s : State E, s.done = false → s.ph = .test → s.j = 0 →
      look (astep cfg d g) ν (rem cfg) (Gg cfg d g f γ) s ≤ ε)
    (hlookE : ∀ s : State E, AttStart cfg s.x s → s.att = 0 → s.found = false →
      look (astep cfg d g) ν (rem cfg) (Gg cfg d g f γ) s ≤ pE)
    (s0 : State E) (hs0 : s0.done = false) (hph0 : s0.ph = .test) (hj0 : s0.j = 0) (N : ℕ) :
    ∑ e ∈ Finset.range N, ∫ β, endBad (rem cfg) (Gg cfg d g f γ) (run (astep cfg d g) s0 β e) (shift e β)
        ∂(Measure.infinitePi fun _ : ℕ => ν) ≤
      p + N * (p / cfg.M) + ((cfg.k * alen cfg : ℕ) : ℝ) * (p / cfg.M) := by
  have hMr : (0 : ℝ) < cfg.M := by exact_mod_cast hM
  have : Nonempty ((Fin cfg.b → Ω) × E) := Measure.nonempty_of_neZero ν
  have hAM : cfg.M ≤ cfg.k * alen cfg := by
    have : cfg.M ≤ alen cfg := by unfold alen; omega
    exact this.trans (Nat.le_mul_of_pos_left _ hk)
  have hlookTp : ∀ s : State E, s.done = false → s.ph = .test → s.j = 0 →
      look (astep cfg d g) ν (rem cfg) (Gg cfg d g f γ) s ≤ (p / cfg.M) * rem cfg s := by
    intro s hd hph hj
    have hr : rem cfg s = cfg.M := by simp [rem, remA, hd, hph, hj]
    rw [hr, div_mul_cancel₀ _ hMr.ne']
    exact (hlookT s hd hph hj).trans hεp
  have hlookEp : ∀ s : State E, s.done = false → s.ph = .grad0 → s.j = 0 → s.att = 0 →
      s.found = false → look (astep cfg d g) ν (rem cfg) (Gg cfg d g f γ) s ≤ (p / cfg.M) * rem cfg s := by
    intro s hd hph hj ha hf
    have hr : rem cfg s = cfg.k * alen cfg := by
      simp only [rem, remA, hd, hph, hj, ha, Bool.false_eq_true, ↓reduceIte, Nat.sub_zero]
      obtain ⟨m, hm⟩ : ∃ m, cfg.k = m + 1 := ⟨cfg.k - 1, by omega⟩
      rw [hm]; simp; ring
    have hl := hlookE s ⟨hd, hph, hj, rfl, by omega⟩ ha hf
    rw [hr]
    have h1 : p ≤ (p / cfg.M) * (cfg.k * alen cfg : ℕ) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hMr]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hAM) hp
    linarith
  refine phase_count (astep cfg d g) ν (rem cfg) (Gg cfg d g f γ) hstep hremm hGm
    (fun s y => (Gg_le cfg d g f γ s y).1) (fun s y => (Gg_le cfg d g f γ s y).2) s0
    {s | Good cfg s} (fun s hs y => (step_good cfg d g hM hT hk s hs y).1)
    (Or.inr (Or.inl ⟨hph0, by rw [hj0]; exact hM⟩)) hp (Lmax := cfg.k * alen cfg) (fun s hs => ?_)
    (fun s hs => ?_) ?_ N
  · have : alen cfg = cfg.M + 1 + cfg.T + cfg.M := rfl
    have : alen cfg ≤ cfg.k * alen cfg := Nat.le_mul_of_pos_left _ hk
    by_cases hd : s.done = true
    · simp [rem, hd]
    · have hd' : s.done = false := by simpa using hd
      rcases hs with h0 | ⟨hph, hj⟩ | ⟨hph, hj, ha⟩ | ⟨hph, hj, ha⟩ | ⟨hph, hj, ha⟩ | ⟨hph, hj, ha⟩
      · exact absurd h0 hd
      · simp only [rem, remA, hd', hph, Bool.false_eq_true, ↓reduceIte]
        omega
      all_goals
        have := rem_le_aux cfg.k s.att (alen cfg) ha
        simp only [rem, remA, hd', hph, Bool.false_eq_true, ↓reduceIte]
        omega
  · by_cases hd : s.done = true
    · left
      exact ⟨fun y => (step_good cfg d g hM hT hk s hs y).2.1 hd, by simp [rem, hd]⟩
    · have hd' : s.done = false := by simpa using hd
      right
      have h1 : 1 ≤ rem cfg s := ((step_good cfg d g hM hT hk s hs (Classical.arbitrary _)).2.2.2.2).resolve_right hd
      rcases Nat.lt_or_ge (rem cfg s) 2 with hlt | hge
      · right
        refine ⟨by omega, fun y => ?_⟩
        rcases (step_good cfg d g hM hT hk s hs y).2.2.2.1 hd' (by omega) with ⟨q1, q2, q3⟩ | ⟨q1, q2, q3, q4, q5, _⟩ | q1
        · exact hlookTp _ q1 q2 q3
        · exact hlookEp _ q1 q2 q3 q4 q5
        · rw [look_done cfg d g f γ _ q1]
          exact mul_nonneg (div_nonneg hp hMr.le) (Nat.cast_nonneg _)
      · left
        exact ⟨hge, fun y => (step_good cfg d g hM hT hk s hs y).2.2.1 hd' hge⟩
  · exact (hlookT s0 hs0 hph0 hj0).trans hεp

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
theorem boundary_test (s : State E) (hd : s.done = false) (hph : s.ph = .test) (hr : rem cfg s = 1)
    (y : (Fin cfg.b → Ω) × E) :
    let gh := select cfg.M cfg.τg (Function.update s.store s.j (bmean cfg g s.x y.1))
    (cfg.gth < ‖gh‖ → (astep cfg d g s y).done = false ∧ (astep cfg d g s y).ph = .test ∧
        (astep cfg d g s y).j = 0 ∧ (astep cfg d g s y).x = s.x - cfg.η • gh) ∧
      (¬ cfg.gth < ‖gh‖ → (astep cfg d g s y).done = false ∧ (astep cfg d g s y).ph = .grad0 ∧
        (astep cfg d g s y).x = s.x) := by
  intro gh
  have hj : ¬ s.j + 1 < cfg.M := by
    simp only [rem, remA, hd, hph, Bool.false_eq_true, ↓reduceIte] at hr; omega
  rw [step_live cfg d g s hd]
  simp only [blockUpdate, queryPoint, hph, hj, ↓reduceIte]
  constructor
  · intro h; simp only [gh] at h; simp [h, hd, gh]
  · intro h; simp only [gh] at h; simp [h, hd]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
theorem boundary_escape (hM : 0 < cfg.M) (s : State E) (hs : Good cfg s) (hd : s.done = false)
    (hph : s.ph ≠ .test) (hr : rem cfg s = 1) (y : (Fin cfg.b → Ω) × E) :
    ((astep cfg d g s y).done = true → (astep cfg d g s y).x = s.x) ∧
      ((astep cfg d g s y).done = false → (astep cfg d g s y).ph = .test ∧
        (astep cfg d g s y).x - (astep cfg d g s y).dx = s.x) := by
  have : alen cfg = cfg.M + 1 + cfg.T + cfg.M := rfl
  have := pfacts cfg.k s.att (alen cfg)
  rcases hs with h0 | ⟨hph', _⟩ | ⟨hph', hj, ha⟩ | ⟨hph', hj, ha⟩ | ⟨hph', hj, ha⟩ | ⟨hph', hj, ha⟩
  · simp [h0] at hd
  · exact absurd hph' hph
  · simp only [rem, remA, hd, hph', Bool.false_eq_true, ↓reduceIte] at hr; omega
  · simp only [rem, remA, hd, hph', Bool.false_eq_true, ↓reduceIte] at hr; omega
  · simp only [rem, remA, hd, hph', Bool.false_eq_true, ↓reduceIte] at hr; omega
  · simp only [rem, remA, hd, hph', Bool.false_eq_true, ↓reduceIte] at hr
    have hj1 : ¬ s.j + 1 < cfg.M := by omega
    have ha1 : ¬ s.att + 1 < cfg.k := by omega
    rcases (tr_ray cfg d g s hd hph' y).2.2 hj1 ha1 with ⟨q1, q2⟩ | ⟨q1, q2, _, q4⟩
    · exact ⟨fun _ => q2, fun h => absurd q1 (by simp [h])⟩
    · exact ⟨fun h => absurd h (by simp [q1]), fun _ => ⟨q2, q4⟩⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
theorem inner_facts (s : State E) (hs : Good cfg s) (hd : s.done = false)
    (hr : 2 ≤ rem cfg s) (y : (Fin cfg.b → Ω) × E) :
    (astep cfg d g s y).done = false ∧ (astep cfg d g s y).x = s.x ∧
      ((astep cfg d g s y).ph = .test ↔ s.ph = .test) ∧
      (s.ph = .test → (astep cfg d g s y).j = s.j + 1) := by
  have : alen cfg = cfg.M + 1 + cfg.T + cfg.M := rfl
  have := pfacts cfg.k s.att (alen cfg)
  rcases hs with h0 | ⟨hph', hj⟩ | ⟨hph', hj, ha⟩ | ⟨hph', hj, ha⟩ | ⟨hph', hj, ha⟩ | ⟨hph', hj, ha⟩
  · simp [h0] at hd
  · simp only [rem, remA, hd, hph', Bool.false_eq_true, ↓reduceIte] at hr
    obtain ⟨u1, u2, u3⟩ := (tr_test cfg d g s hd hph' y).2.1 (by omega)
    exact ⟨(tr_test cfg d g s hd hph' y).1, u3, by rw [u1, hph'], fun _ => u2⟩
  · obtain ⟨t1, t2, _, t4, t5⟩ := tr_grad0 cfg d g s hd hph' y
    have hne : (astep cfg d g s y).ph ≠ .test := by
      by_cases hj1 : s.j + 1 < cfg.M
      · rw [(t4 hj1).1]; decide
      · rw [(t5 hj1).1]; decide
    refine ⟨t1, t2, ⟨fun h => absurd h hne, fun h => by rw [hph'] at h; exact absurd h (by decide)⟩,
      fun h => by rw [hph'] at h; exact absurd h (by decide)⟩
  · obtain ⟨t1, t2, _, t4, _⟩ := tr_init cfg d g s hd hph' y
    refine ⟨t1, t2, by rw [t4, hph']; simp, fun h => by rw [hph'] at h; exact absurd h (by decide)⟩
  · obtain ⟨t1, t2, _, t4, t5⟩ := tr_traj cfg d g s hd hph' y
    have hne : (astep cfg d g s y).ph ≠ .test := by
      by_cases hj1 : s.j + 1 < cfg.T
      · rw [(t4 hj1).1]; decide
      · rw [(t5 hj1).1]; decide
    refine ⟨t1, t2, ⟨fun h => absurd h hne, fun h => by rw [hph'] at h; exact absurd h (by decide)⟩,
      fun h => by rw [hph'] at h; exact absurd h (by decide)⟩
  · simp only [rem, remA, hd, hph', Bool.false_eq_true, ↓reduceIte] at hr
    obtain ⟨t1, t2, _⟩ := tr_ray cfg d g s hd hph' y
    by_cases hj1 : s.j + 1 < cfg.M
    · obtain ⟨u1, u2, _, u4, _⟩ := t1 hj1
      exact ⟨u1, u2, by rw [u4, hph'], fun h => by rw [hph'] at h; exact absurd h (by decide)⟩
    · obtain ⟨u1, u2, _, u4, _⟩ := t2 hj1 (by omega)
      exact ⟨u1, u2, by rw [u4, hph']; simp, fun h => by rw [hph'] at h; exact absurd h (by decide)⟩

section det

variable {L ρ : ℝ}

def Sosp (γ ε : ℝ) (x : E) : Prop := ‖gradient f x‖ ≤ ε ∧ ¬ sadS f γ x

noncomputable def Φ (ϱ flow : ℝ) (s : State E) : ℝ :=
  (f s.x - flow) / ϱ + ((if s.ph = .test then cfg.M - s.j + cfg.k * alen cfg else rem cfg s : ℕ) : ℝ)

def Jinv (γ ε : ℝ) (s : State E) : Prop :=
  Good cfg s ∧ (s.done = true → Sosp f γ ε s.x) ∧
    (s.done = false → s.ph ≠ .test → ‖gradient f s.x‖ ≤ ε)

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
theorem good_run (hM : 0 < cfg.M) (hT : 0 < cfg.T) (hk : 0 < cfg.k) (hL : 0 < L)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    {γ ε ϱ flow : ℝ} (hϱ : 0 < ϱ) (hη : cfg.η = 1 / L) (hgth : cfg.gth = ε / 2) (hτg : 3 * cfg.τg ≤ ε / 8)
    (hgd : (cfg.M : ℝ) ≤ ε ^ 2 / (16 * L) / ϱ)
    (hesc : ((cfg.M + cfg.k * alen cfg : ℕ) : ℝ) ≤ cfg.r ^ 2 * cfg.θ / 5 / ϱ)
    (s0 : State E) (hs0 : s0.done = false) (hph0 : s0.ph = .test) (hj0 : s0.j = 0)
    (β : ℕ → (Fin cfg.b → Ω) × E) (N : ℕ)
    (hgood : ∀ e < N, endBad (rem cfg) (Gg cfg d g f γ) (run (astep cfg d g) s0 β e) (shift e β) = 0) :
    ∀ e ≤ N, Jinv cfg f γ ε (run (astep cfg d g) s0 β e) ∧
      ((run (astep cfg d g) s0 β e).done = false →
        Φ cfg f ϱ flow (run (astep cfg d g) s0 β e) + e ≤ Φ cfg f ϱ flow s0) := by
  have hA : alen cfg = cfg.M + 1 + cfg.T + cfg.M := rfl
  intro e
  induction e with
  | zero =>
    intro _
    refine ⟨⟨Or.inr (Or.inl ⟨hph0, by rw [run_zero, hj0]; exact hM⟩), fun h => absurd h (by simp [run_zero, hs0]),
      fun _ h => absurd hph0 h⟩, fun _ => by simp [run_zero]⟩
  | succ e ih =>
    intro he
    obtain ⟨⟨hG, hdn, hgr⟩, hΦ⟩ := ih (by omega)
    set s := run (astep cfg d g) s0 β e with hsdef
    have hsucc : run (astep cfg d g) s0 β (e + 1) = astep cfg d g s (β e) := run_succ _ _ _ _
    rw [hsucc]
    have hbad := hgood e (by omega)
    simp only [endBad, shift, Nat.add_zero, ← hsdef] at hbad
    by_cases hd : s.done = true
    · rw [astep_done cfg d g s hd]
      exact ⟨⟨hG, hdn, fun h => absurd hd (by simp [h])⟩, fun h => absurd hd (by simp [h])⟩
    have hd' : s.done = false := by simpa using hd
    have hsg := step_good cfg d g hM hT hk s hG (β e)
    have hG' := hsg.1
    have hr1 : 1 ≤ rem cfg s := hsg.2.2.2.2.resolve_right hd
    have hΦs := hΦ hd'
    rcases Nat.lt_or_ge (rem cfg s) 2 with hlt | hge
    · have hr : rem cfg s = 1 := by omega
      rw [ite_eq_left hr] at hbad
      simp only [Gg, hd', Bool.false_eq_true, ↓reduceIte] at hbad
      by_cases hph : s.ph = .test
      · rw [ite_eq_left hph] at hbad
        have hacc : ‖select cfg.M cfg.τg (Function.update s.store s.j (bmean cfg g s.x (β e).1)) -
            gradient f s.x‖ ≤ ε / 8 := by
          unfold testBad at hbad
          split_ifs at hbad with hh
          · norm_num at hbad
          · push Not at hh; linarith
        obtain ⟨hgd1, hgd2⟩ := boundary_test cfg d g s hd' hph hr (β e)
        have hjM : s.j + 1 = cfg.M := by
          simp only [rem, remA, hd', hph, Bool.false_eq_true, ↓reduceIte] at hr
          have := hG.resolve_left (by simp [hd']); omega
        rcases (hsg.2.2.2.1 hd' hr) with ⟨q1, q2, q3⟩ | ⟨q1, q2, q3, q4, q5, q6⟩ | q1
        · set gh := select cfg.M cfg.τg (Function.update s.store s.j (bmean cfg g s.x (β e).1))
          have hbig : cfg.gth < ‖gh‖ := by
            by_contra hn
            have := (hgd2 hn).2.1; rw [q2] at this; exact absurd this (by decide)
          obtain ⟨_, _, _, hx'⟩ := hgd1 hbig
          have hdec := LongTails.Proofs.GatedEscapeDescent.gd_decrease hL hg hlip s.x gh hacc
            (by rw [← hgth]; exact hbig)
          rw [← hη, ← hx'] at hdec
          refine ⟨⟨hG', fun h => absurd h (by simp [q1]), fun _ h => absurd q2 h⟩, fun _ => ?_⟩
          unfold Φ
          rw [ite_eq_left q2, q3, Nat.sub_zero]
          have h1 : (f (astep cfg d g s (β e)).x - flow) / ϱ ≤ (f s.x - flow) / ϱ - cfg.M := by
            rw [div_sub' hϱ.ne', div_le_div_iff_of_pos_right hϱ]
            have := mul_le_mul_of_nonneg_right hgd hϱ.le
            rw [div_mul_cancel₀ _ hϱ.ne'] at this
            linarith
          unfold Φ at hΦs
          rw [ite_eq_left hph] at hΦs
          have hMj : cfg.M - s.j = 1 := by omega
          rw [hMj] at hΦs
          push_cast at hΦs ⊢
          nlinarith
        · have hsmall : ¬ cfg.gth < ‖select cfg.M cfg.τg (Function.update s.store s.j
              (bmean cfg g s.x (β e).1))‖ := by
            intro hb; have := (hgd1 hb).2.1; rw [q2] at this; exact absurd this (by decide)
          have hgrad : ‖gradient f s.x‖ ≤ ε :=
            LongTails.Proofs.GatedEscapeDescent.grad_norm_of_small hacc (by push Not at hsmall; linarith)
          refine ⟨⟨hG', fun h => absurd h (by simp [q1]), fun _ _ => by rw [q6]; exact hgrad⟩, fun _ => ?_⟩
          unfold Φ
          have hq2 : (astep cfg d g s (β e)).ph ≠ .test := by rw [q2]; decide
          rw [ite_eq_right hq2, q6]
          have hrem : rem cfg (astep cfg d g s (β e)) = cfg.k * alen cfg := by
            simp only [rem, remA, q1, q2, q3, q4, Bool.false_eq_true, ↓reduceIte, Nat.sub_zero]
            obtain ⟨m, hm⟩ : ∃ m, cfg.k = m + 1 := ⟨cfg.k - 1, by omega⟩
            rw [hm]; simp; ring
          rw [hrem]
          unfold Φ at hΦs
          rw [ite_eq_left hph] at hΦs
          have hMj : cfg.M - s.j = 1 := by omega
          rw [hMj] at hΦs
          push_cast at hΦs ⊢
          nlinarith
        · exact absurd q1 (by rw [(hgd2 (fun hb => by have := (hgd1 hb).1; rw [q1] at this; simp at this)).1]; simp)
      · rw [ite_eq_right hph] at hbad
        obtain ⟨hb1, hb2⟩ := boundary_escape cfg d g hM s hG hd' hph hr (β e)
        have hgs := hgr hd' hph
        by_cases hdn' : (astep cfg d g s (β e)).done = true
        · have hx := hb1 hdn'
          unfold GescG at hbad
          rw [ite_eq_left hdn'] at hbad
          have hns : ¬ sadS f γ (astep cfg d g s (β e)).x := by
            intro hh; rw [ite_eq_left hh] at hbad; norm_num at hbad
          refine ⟨⟨hG', fun _ => ⟨by rw [hx]; exact hgs, hns⟩, fun h => absurd hdn' (by simp [h])⟩,
            fun h => absurd hdn' (by simp [h])⟩
        · have hdn'' : (astep cfg d g s (β e)).done = false := by simpa using hdn'
          obtain ⟨hph'', hxd⟩ := hb2 hdn''
          unfold GescG at hbad
          rw [ite_eq_right hdn'] at hbad
          have hfdec : f (astep cfg d g s (β e)).x ≤ f s.x - cfg.r ^ 2 * cfg.θ / 5 := by
            unfold harm at hbad
            rw [hxd] at hbad
            split_ifs at hbad with hh
            · norm_num at hbad
            · push Not at hh
              have : s.x + (astep cfg d g s (β e)).dx = (astep cfg d g s (β e)).x := by rw [← hxd]; abel
              rw [this] at hh; exact hh
          rcases (hsg.2.2.2.1 hd' hr) with ⟨q1, q2, q3⟩ | ⟨q1, q2, _⟩ | q1
          · refine ⟨⟨hG', fun h => absurd h (by simp [q1]), fun _ h => absurd q2 h⟩, fun _ => ?_⟩
            unfold Φ
            rw [ite_eq_left q2, q3, Nat.sub_zero]
            unfold Φ at hΦs
            rw [ite_eq_right hph, hr] at hΦs
            have h1 : (f (astep cfg d g s (β e)).x - flow) / ϱ ≤
                (f s.x - flow) / ϱ - ((cfg.M + cfg.k * alen cfg : ℕ) : ℝ) := by
              rw [div_sub' hϱ.ne', div_le_div_iff_of_pos_right hϱ]
              have := mul_le_mul_of_nonneg_right hesc hϱ.le
              rw [div_mul_cancel₀ _ hϱ.ne'] at this
              linarith
            push_cast at hΦs h1 ⊢
            linarith
          · exact absurd hph'' (by rw [q2]; decide)
          · exact absurd q1 (by simp [hdn''])
    · have hinn := inner_facts cfg d g s hG hd' hge (β e)
      obtain ⟨i1, i2, i3, i4⟩ := hinn
      have hrem := hsg.2.2.1 hd' hge
      refine ⟨⟨hG', fun h => absurd h (by simp [i1]), fun _ h => by
        rw [i2]; exact hgr hd' (fun h' => h (i3.mpr h'))⟩, fun _ => ?_⟩
      unfold Φ at hΦs ⊢
      rw [i2]
      by_cases hph : s.ph = .test
      · rw [ite_eq_left (i3.mpr hph), i4 hph]
        rw [ite_eq_left hph] at hΦs
        have hjM : s.j + 1 < cfg.M := by
          simp only [rem, remA, hd', hph, Bool.false_eq_true, ↓reduceIte] at hge; omega
        have e1 : ((cfg.M - (s.j + 1) : ℕ) : ℝ) + 1 = ((cfg.M - s.j : ℕ) : ℝ) := by
          rw [show cfg.M - s.j = cfg.M - (s.j + 1) + 1 by omega]; push_cast; ring
        push_cast at hΦs ⊢
        linarith
      · have hph2 : ¬ (astep cfg d g s (β e)).ph = .test := fun h => hph (i3.mp h)
        rw [ite_eq_right hph2, hrem]
        rw [ite_eq_right hph] at hΦs
        have e1 : ((rem cfg s - 1 : ℕ) : ℝ) + 1 = (rem cfg s : ℝ) := by
          rw [Nat.cast_sub (by omega)]; push_cast; ring
        push_cast at hΦs ⊢
        linarith

end det

end LongTails.Proofs.GatedEscapeGlobal
