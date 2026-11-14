import LongTails.Proofs.GatedEscapeAttempt

namespace LongTails.Proofs.GatedEscapeEscape

open MeasureTheory ProbabilityTheory LongTails.Algorithms.GatedPerturbedEscape
  LongTails.Proofs.GatedEscapeProcess LongTails.Proofs.GatedEscapePhases
  LongTails.Proofs.GatedEscapeAttempt LongTails.Proofs.GatedEscapeMeasurable
  LongTails.Proofs.StrongGrowthAgdBlocks
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {Ω : Type} [MeasurableSpace Ω]
variable (cfg : Config) (d : ℕ) (g : E → Ω → E) (f : E → ℝ)
variable {ν : Measure ((Fin cfg.b → Ω) × E)} [IsProbabilityMeasure ν]

def alen : ℕ := cfg.M + 1 + cfg.T + cfg.M

def AttStart (x : E) (s : State E) : Prop :=
  s.done = false ∧ s.ph = .grad0 ∧ s.j = 0 ∧ s.x = x ∧ s.att < cfg.k

noncomputable def harm (x dx : E) : ℝ := if f x - cfg.r ^ 2 * cfg.θ / 5 < f (x + dx) then 1 else 0

noncomputable def Gesc (sad : Prop) [Decidable sad] (s : State E) : ℝ :=
  if s.done = true then (if sad then 1 else 0) else harm cfg f (s.x - s.dx) s.dx

noncomputable def Zs (sad : Prop) [Decidable sad] (ε : ℝ) (s : State E) : ℝ :=
  (if s.found = true then harm cfg f s.x s.dx else (if sad then 1 else 0) * (1 / 4) ^ (cfg.k - s.att)) +
    (cfg.k - s.att : ℕ) * (2 * ε)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
lemma post_fields (s : State E) (hd : s.done = false) (hph : s.ph = .grad0) (hj : s.j = 0)
    (hM : 0 < cfg.M) (hT : 0 < cfg.T) (β : ℕ → (Fin cfg.b → Ω) × E) :
    let post := run (astep cfg d g) s β (alen cfg)
    let acc := s.found = false ∧ accS cfg post
    (s.att + 1 < cfg.k → (post.done = false ∧ post.ph = .grad0 ∧ post.j = 0 ∧ post.x = s.x ∧
        post.att = s.att + 1 ∧ (post.found = true ↔ (s.found = true ∨ acc)) ∧
        (s.found = true → post.dx = s.dx) ∧ (acc → post.dx = dxS cfg post))) ∧
    (cfg.k ≤ s.att + 1 → ((s.found = true ∨ acc) → post.done = false ∧ post.ph = .test ∧
        post.found = false ∧ post.x - post.dx = s.x ∧ (s.found = true → post.dx = s.dx) ∧
        (acc → post.dx = dxS cfg post)) ∧
      (¬ (s.found = true ∨ acc) → post.done = true ∧ post.x = s.x)) := by
  intro post acc
  obtain ⟨_, _, h3x, h3g0, h3ph, h3j, h3d, h3f, h3att, h3dx, h3v, h3w⟩ :=
    attempt_split cfg d g s hd hph hj hM hT β
  set s3 := run (astep cfg d g) s β (cfg.M + 1 + cfg.T) with hs3
  have hpost : post = run (astep cfg d g) s3 (shift (cfg.M + 1 + cfg.T) β) cfg.M := by
    show run (astep cfg d g) s β (cfg.M + 1 + cfg.T + cfg.M) = _
    rw [run_add]
  have hre := run_ray_end cfg d g s3 h3d h3ph h3j hM (shift (cfg.M + 1 + cfg.T) β)
  rw [← hpost] at hre
  set S := fill cfg g s3.store (s3.x + cfg.r • s3.w) (shift (cfg.M + 1 + cfg.T) β) cfg.M
  have hqeq : qhat cfg g s3 (shift (cfg.M + 1 + cfg.T) β) = qhS cfg post := by
    rw [hre]; unfold qhat qhS
    split_ifs <;> simp only [endAttempt] <;> split_ifs <;> rfl
  have hveq : post.v = s3.v := by rw [hre]; split_ifs <;> simp only [endAttempt] <;> split_ifs <;> rfl
  have hweq : post.w = s3.w := by rw [hre]; split_ifs <;> simp only [endAttempt] <;> split_ifs <;> rfl
  have hgeq : post.g0 = s3.g0 := by rw [hre]; split_ifs <;> simp only [endAttempt] <;> split_ifs <;> rfl
  have hcond : (s3.found = false ∧ cfg.r / 2 ≤ ‖s3.v‖ ∧ qhat cfg g s3 (shift (cfg.M + 1 + cfg.T) β) ≤
      -2 * cfg.θ) ↔ acc := by
    simp only [acc, accS, hqeq, hveq, h3f]
  refine ⟨fun hk => ?_, fun hk => ⟨fun hfa => ?_, fun hfa => ?_⟩⟩
  · by_cases hc : s3.found = false ∧ cfg.r / 2 ≤ ‖s3.v‖ ∧
        qhat cfg g s3 (shift (cfg.M + 1 + cfg.T) β) ≤ -2 * cfg.θ
    · have ha : acc := hcond.mp hc
      rw [ite_eq_left hc] at hre
      simp only [endAttempt, h3att, ite_eq_left hk] at hre
      rw [hre]
      refine ⟨h3d, rfl, rfl, h3x, rfl, ?_, ?_, fun _ => ?_⟩
      · simp [ha]
      · intro hf; rw [h3f] at hc; simp [hf] at hc
      · rfl
    · have ha : ¬ acc := fun h => hc (hcond.mpr h)
      rw [ite_eq_right hc] at hre
      simp only [endAttempt, h3att, ite_eq_left hk] at hre
      rw [hre]
      refine ⟨h3d, rfl, rfl, h3x, rfl, ?_, fun _ => h3dx, fun h => absurd h ha⟩
      simp only [h3f, ha, or_false, iff_self]
  · by_cases hc : s3.found = false ∧ cfg.r / 2 ≤ ‖s3.v‖ ∧
        qhat cfg g s3 (shift (cfg.M + 1 + cfg.T) β) ≤ -2 * cfg.θ
    · have ha : acc := hcond.mp hc
      rw [ite_eq_left hc] at hre
      have hnk : ¬ (s3.att + 1 < cfg.k) := by rw [h3att]; omega
      simp only [endAttempt, ite_eq_right hnk, ↓reduceIte] at hre
      rw [hre]
      refine ⟨h3d, rfl, rfl, by simp [h3x], ?_, fun _ => ?_⟩
      · intro hf; rw [h3f] at hc; simp [hf] at hc
      · rfl
    · have ha : ¬ acc := fun h => hc (hcond.mpr h)
      have hsf : s.found = true := by
        rcases hfa with h | h
        · exact h
        · exact absurd h ha
      rw [ite_eq_right hc] at hre
      have hnk : ¬ (s3.att + 1 < cfg.k) := by rw [h3att]; omega
      have hf3 : s3.found = true := by rw [h3f]; exact hsf
      simp only [endAttempt, ite_eq_right hnk, hf3, ↓reduceIte] at hre
      rw [hre]
      refine ⟨h3d, rfl, rfl, by simp [h3x], fun _ => h3dx, fun h => absurd h ha⟩
  · have hsf : s.found = false := by
      by_contra h; exact hfa (Or.inl (by simpa using h))
    have ha : ¬ acc := fun h => hfa (Or.inr h)
    have hc : ¬ (s3.found = false ∧ cfg.r / 2 ≤ ‖s3.v‖ ∧
        qhat cfg g s3 (shift (cfg.M + 1 + cfg.T) β) ≤ -2 * cfg.θ) := fun h => ha (hcond.mp h)
    rw [ite_eq_right hc] at hre
    have hnk : ¬ (s3.att + 1 < cfg.k) := by rw [h3att]; omega
    have hf3 : s3.found = false := by rw [h3f]; exact hsf
    simp only [endAttempt, ite_eq_right hnk, hf3, Bool.false_eq_true, ↓reduceIte] at hre
    rw [hre]
    exact ⟨rfl, h3x⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
lemma post_core (s : State E) (hd : s.done = false) (hph : s.ph = .grad0) (hj : s.j = 0)
    (hM : 0 < cfg.M) (hT : 0 < cfg.T) (β : ℕ → (Fin cfg.b → Ω) × E) :
    let post := run (astep cfg d g) s β (alen cfg)
    let s3 := run (astep cfg d g) s β (cfg.M + 1 + cfg.T)
    post = run (astep cfg d g) s3 (shift (cfg.M + 1 + cfg.T) β) cfg.M ∧
    post.g0 = select cfg.M cfg.τ0 (fill cfg g s.store s.x β cfg.M) ∧
    post.v = vrun cfg g s.x post.g0 (clip cfg.r ((cfg.s0 / Real.sqrt d) • (β cfg.M).2))
      (fun n => (β (cfg.M + 1 + n)).1) cfg.T ∧
    post.w = (1 / ‖post.v‖) • post.v ∧
    post.store = fill cfg g s3.store (s.x + cfg.r • post.w) (shift (cfg.M + 1 + cfg.T) β) cfg.M ∧
    s3.ph = .ray ∧ s3.j = 0 ∧ s3.done = false ∧ s3.x = s.x ∧ s3.w = post.w ∧ s3.g0 = post.g0 := by
  intro post s3
  obtain ⟨h1g0, _, h3x, h3g0, h3ph, h3j, h3d, _, _, _, h3v, h3w⟩ :=
    attempt_split cfg d g s hd hph hj hM hT β
  have hpost : post = run (astep cfg d g) s3 (shift (cfg.M + 1 + cfg.T) β) cfg.M := by
    show run (astep cfg d g) s β (cfg.M + 1 + cfg.T + cfg.M) = _
    rw [run_add]
  have hre := run_ray_end cfg d g s3 h3d h3ph h3j hM (shift (cfg.M + 1 + cfg.T) β)
  rw [← hpost] at hre
  have hveq : post.v = s3.v := by rw [hre]; split_ifs <;> simp only [endAttempt] <;> split_ifs <;> rfl
  have hweq : post.w = s3.w := by rw [hre]; split_ifs <;> simp only [endAttempt] <;> split_ifs <;> rfl
  have hgeq : post.g0 = s3.g0 := by rw [hre]; split_ifs <;> simp only [endAttempt] <;> split_ifs <;> rfl
  have hseq : post.store = fill cfg g s3.store (s3.x + cfg.r • s3.w) (shift (cfg.M + 1 + cfg.T) β) cfg.M := by
    rw [hre]; split_ifs <;> simp only [endAttempt] <;> split_ifs <;> rfl
  refine ⟨hpost, by rw [hgeq, h3g0, h1g0], ?_, by rw [hweq, hveq, h3w], ?_, h3ph, h3j, h3d, h3x,
    hweq.symm, hgeq.symm⟩
  · rw [hveq, h3v, hgeq, h3g0]
  · rw [hseq, h3x, hweq]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
lemma reach_attempt (hM : 0 < cfg.M) (hT : 0 < cfg.T) (x : E) (s0 : State E) (hs0 : AttStart cfg x s0)
    (ha0 : s0.att = 0) (β : ℕ → (Fin cfg.b → Ω) × E) :
    ∀ e, e < cfg.k → AttStart cfg x (run (astep cfg d g) s0 β (e * alen cfg)) ∧
      (run (astep cfg d g) s0 β (e * alen cfg)).att = e := by
  intro e
  induction e with
  | zero => intro _; rw [Nat.zero_mul, run_zero]; exact ⟨hs0, ha0⟩
  | succ e ih =>
    intro he
    obtain ⟨⟨hd, hph, hj, hx, _⟩, hat⟩ := ih (by omega)
    have hsplit : run (astep cfg d g) s0 β ((e + 1) * alen cfg) =
        run (astep cfg d g) (run (astep cfg d g) s0 β (e * alen cfg)) (shift (e * alen cfg) β) (alen cfg) := by
      rw [add_mul, one_mul, run_add]
    rw [hsplit]
    obtain ⟨hnl, _⟩ := post_fields cfg d g _ hd hph hj hM hT (shift (e * alen cfg) β)
    obtain ⟨h1, h2, h3, h4, h5, _⟩ := hnl (by rw [hat]; omega)
    exact ⟨⟨h1, h2, h3, by rw [h4, hx], by rw [h5, hat]; omega⟩, by rw [h5, hat]⟩

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace Ω] in
lemma harm_le (x dx : E) : 0 ≤ harm cfg f x dx ∧ harm cfg f x dx ≤ 1 := by
  unfold harm; split_ifs <;> norm_num

theorem escape_bound (hM : 0 < cfg.M) (hT : 0 < cfg.T) (hk : 0 < cfg.k)
    (hstep : Measurable (Function.uncurry (astep cfg d g))) (hfc : Continuous f) (x : E)
    (sad : Prop) [Decidable sad] {ε : ℝ} (hε : 0 ≤ ε)
    (hI1 : ∀ s, AttStart cfg x s → s.found = false →
      ∫ β, (if accS cfg (run (astep cfg d g) s β (alen cfg)) ∧
          f x - cfg.r ^ 2 * cfg.θ / 5 < f (x + dxS cfg (run (astep cfg d g) s β (alen cfg)))
        then (1 : ℝ) else 0) ∂(Measure.infinitePi fun _ : ℕ => ν) ≤ 2 * ε)
    (hI2 : sad → ∀ s, AttStart cfg x s → s.found = false →
      ∫ β, (if accS cfg (run (astep cfg d g) s β (alen cfg)) then (0 : ℝ) else 1)
        ∂(Measure.infinitePi fun _ : ℕ => ν) ≤ 1 / 4)
    (s0 : State E) (hs0 : AttStart cfg x s0) (hf0 : s0.found = false) (ha0 : s0.att = 0) :
    ∫ β, Gesc cfg f sad (run (astep cfg d g) s0 β (cfg.k * alen cfg))
        ∂(Measure.infinitePi fun _ : ℕ => ν) ≤
      (if sad then 1 else 0) * (1 / 4) ^ cfg.k + cfg.k * (2 * ε) := by
  set W : State E → ℝ := fun s =>
    if s.done = true ∨ s.ph = .test then Gesc cfg f sad s else Zs cfg f sad ε s with hW
  have hsadnn : (0 : ℝ) ≤ (if sad then 1 else 0) := by split_ifs <;> norm_num
  have hsad1 : (if sad then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  have hharm_m : Measurable (fun s : State E => harm cfg f s.x s.dx) := by
    unfold harm
    refine Measurable.ite (measurableSet_lt (by fun_prop) ?_) measurable_const measurable_const
    exact hfc.measurable.comp (measurable_x.add measurable_dx)
  have hharm2_m : Measurable (fun s : State E => harm cfg f (s.x - s.dx) s.dx) := by
    unfold harm
    refine Measurable.ite (measurableSet_lt ?_ ?_) measurable_const measurable_const
    · exact (hfc.measurable.comp (measurable_x.sub measurable_dx)).sub_const _
    · exact hfc.measurable.comp ((measurable_x.sub measurable_dx).add measurable_dx)
  have hGm : Measurable (Gesc cfg f sad) := by
    unfold Gesc
    exact Measurable.ite (measurableSet_eq_fun measurable_done measurable_const) measurable_const hharm2_m
  have hZm : Measurable (Zs cfg f sad ε) := by
    unfold Zs
    refine Measurable.add ?_ ?_
    · refine Measurable.ite (measurableSet_eq_fun measurable_found measurable_const) hharm_m ?_
      exact measurable_const.mul ((measurable_from_top (f := fun n : ℕ => (1 / 4 : ℝ) ^ (cfg.k - n))).comp
        measurable_att)
    · exact ((measurable_from_top (f := fun n : ℕ => ((cfg.k - n : ℕ) : ℝ))).comp measurable_att).mul_const _
  have hWm : Measurable W := by
    refine Measurable.ite ?_ hGm hZm
    rw [Set.ofPred_or]
    exact (measurableSet_eq_fun measurable_done measurable_const).union
      (measurableSet_eq_fun measurable_ph measurable_const)
  have hWbd : ∀ s, |W s| ≤ 1 + cfg.k * (2 * ε) := by
    intro s
    have hk1 : ((cfg.k - s.att : ℕ) : ℝ) ≤ cfg.k := by exact_mod_cast Nat.sub_le _ _
    have hk0 : (0 : ℝ) ≤ ((cfg.k - s.att : ℕ) : ℝ) := Nat.cast_nonneg _
    have hp1 : (1 / 4 : ℝ) ^ (cfg.k - s.att) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hp0 : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ (cfg.k - s.att) := by positivity
    have hkε : (0 : ℝ) ≤ cfg.k * (2 * ε) := by positivity
    have hkε' : ((cfg.k - s.att : ℕ) : ℝ) * (2 * ε) ≤ cfg.k * (2 * ε) :=
      mul_le_mul_of_nonneg_right hk1 (by linarith)
    have hkε0 : (0 : ℝ) ≤ ((cfg.k - s.att : ℕ) : ℝ) * (2 * ε) := mul_nonneg hk0 (by linarith)
    obtain ⟨h0, h1⟩ := harm_le cfg f (s.x - s.dx) s.dx
    obtain ⟨h2, h3⟩ := harm_le cfg f s.x s.dx
    simp only [hW, Gesc, Zs]
    split_ifs <;> rw [abs_le] <;> constructor <;> nlinarith
  set Inv : ℕ → Set (State E) := fun t => {s | ∃ β, s = run (astep cfg d g) s0 β t} with hInv
  have hInvStep : ∀ t, ∀ s ∈ Inv t, ∀ y, (astep cfg d g) s y ∈ Inv (t + 1) := by
    intro t s ⟨β, hβ⟩ y
    refine ⟨fun n => if n = t then y else β n, ?_⟩
    rw [run_succ, run_congr (astep cfg d g) s0 t (β := fun n => if n = t then y else β n) (β' := β)
      (fun n hn => by simp [show n ≠ t by omega]), ← hβ]
    simp
  have : Nonempty ((Fin cfg.b → Ω) × E) := Measure.nonempty_of_neZero ν
  have hs0' : s0 ∈ Inv 0 := ⟨fun _ => Classical.arbitrary _, rfl⟩
  have hYint : ∀ t, Integrable (fun β => W (run (astep cfg d g) s0 β t)) (Measure.infinitePi fun _ : ℕ => ν) := by
    intro t
    refine Integrable.of_bound (C := 1 + cfg.k * (2 * ε))
      (hWm.comp (run_measurable (astep cfg d g) s0 hstep t)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun β => ?_)
    rw [Real.norm_eq_abs]; exact hWbd _
  have hInd : ∀ s, AttStart cfg x s → Integrable
      (fun β => (if accS cfg (run (astep cfg d g) s β (alen cfg)) then (0 : ℝ) else 1)) (Measure.infinitePi fun _ : ℕ => ν) ∧
      Integrable (fun β => (if accS cfg (run (astep cfg d g) s β (alen cfg)) ∧
          f x - cfg.r ^ 2 * cfg.θ / 5 < f (x + dxS cfg (run (astep cfg d g) s β (alen cfg))) then (1 : ℝ) else 0))
        (Measure.infinitePi fun _ : ℕ => ν) := by
    intro s _
    have hacc_m : MeasurableSet {s' : State E | accS cfg s'} := by
      unfold accS qhS
      rw [Set.ofPred_and]
      refine (measurableSet_le measurable_const (by fun_prop)).inter (measurableSet_le ?_ measurable_const)
      exact (measurable_select (β := ℝ) cfg.M cfg.τq).comp (measurable_pi_iff.mpr fun c =>
        ((measurable_w.inner ((measurable_pi_apply c).comp measurable_store |>.sub measurable_g0)).div_const _))
    have hdx_m : Measurable (fun s' : State E => dxS cfg s') := by
      unfold dxS
      refine (Measurable.smul ?_ measurable_w).neg
      exact (Measurable.ite (measurableSet_le measurable_const (measurable_g0.inner measurable_w))
        measurable_const measurable_const).mul_const _
    have hrun := run_measurable (astep cfg d g) s hstep (alen cfg)
    constructor
    · refine Integrable.of_bound (C := 1) ((Measurable.ite (hrun hacc_m) measurable_const
        measurable_const)).aestronglyMeasurable (Filter.Eventually.of_forall fun β => ?_)
      split_ifs <;> simp
    · refine Integrable.of_bound (C := 1) ((Measurable.ite ?_ measurable_const
        measurable_const)).aestronglyMeasurable (Filter.Eventually.of_forall fun β => ?_)
      · rw [Set.ofPred_and]
        exact (hrun hacc_m).inter (measurableSet_lt measurable_const
          (hfc.measurable.comp (measurable_const.add (hdx_m.comp hrun))))
      · split_ifs <;> simp
  have hpow : ∀ n : ℕ, (1 / 4 : ℝ) ^ n * (1 / 4) = (1 / 4) ^ (n + 1) := fun n => by rw [pow_succ]
  have key : ∀ s, AttStart cfg x s → s.att + 1 ≤ cfg.k →
      ∫ tail, W (run (astep cfg d g) s tail (alen cfg)) ∂(Measure.infinitePi fun _ : ℕ => ν) ≤ W s := by
    intro s hs hk1
    obtain ⟨hd, hph, hj, hx, hatt⟩ := hs
    have hWs : W s = Zs cfg f sad ε s := by
      simp only [hW, hd, hph, Bool.false_eq_true, false_or, reduceCtorEq, ↓reduceIte]
    rw [hWs]
    have hnl := fun β => (post_fields cfg d g s hd hph hj hM hT β).1
    have hl := fun β => (post_fields cfg d g s hd hph hj hM hT β).2
    obtain ⟨hIa, hIb⟩ := hInd s ⟨hd, hph, hj, hx, hatt⟩
    have hnatk : (cfg.k - s.att : ℕ) = (cfg.k - (s.att + 1) : ℕ) + 1 := by omega
    have hcast : ((cfg.k - s.att : ℕ) : ℝ) = ((cfg.k - (s.att + 1) : ℕ) : ℝ) + 1 := by
      rw [hnatk]; push_cast; ring
    have hWpost : ∀ β, W (run (astep cfg d g) s β (alen cfg)) ≤
        (if s.found = true then harm cfg f x s.dx else
          (if accS cfg (run (astep cfg d g) s β (alen cfg)) ∧
            f x - cfg.r ^ 2 * cfg.θ / 5 < f (x + dxS cfg (run (astep cfg d g) s β (alen cfg))) then (1 : ℝ) else 0) +
          (if sad then (1 : ℝ) else 0) * (1 / 4) ^ (cfg.k - (s.att + 1)) * (if accS cfg (run (astep cfg d g) s β (alen cfg)) then (0 : ℝ) else 1)) +
        ((cfg.k - (s.att + 1) : ℕ) : ℝ) * (2 * ε) := by
      intro β
      by_cases hlast : s.att + 1 < cfg.k
      · obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := hnl β hlast
        have hWp : W (run (astep cfg d g) s β (alen cfg)) = Zs cfg f sad ε (run (astep cfg d g) s β (alen cfg)) := by
          simp only [hW, p1, p2, Bool.false_eq_true, false_or, reduceCtorEq, ↓reduceIte]
        rw [hWp]
        unfold Zs
        rw [p5]
        by_cases hsf : s.found = true
        · have hpf : (run (astep cfg d g) s β (alen cfg)).found = true := p6.mpr (Or.inl hsf)
          simp only [hpf, hsf, ↓reduceIte, p4, p7 hsf, hx, le_refl]
        · have hsf' : s.found = false := by simpa using hsf
          simp only [hsf, Bool.false_eq_true, ↓reduceIte]
          by_cases ha : accS cfg (run (astep cfg d g) s β (alen cfg))
          · have hpf : (run (astep cfg d g) s β (alen cfg)).found = true := p6.mpr (Or.inr ⟨hsf', ha⟩)
            have hdx := p8 ⟨hsf', ha⟩
            simp only [hpf, ↓reduceIte, ha, true_and, p4, hdx, hx, mul_zero, add_zero]
            unfold harm
            split_ifs <;> norm_num
          · have hpf : (run (astep cfg d g) s β (alen cfg)).found = false := by
              have : ¬ (run (astep cfg d g) s β (alen cfg)).found = true := fun h =>
                (p6.mp h).elim hsf (fun h2 => ha h2.2)
              simpa using this
            simp only [hpf, Bool.false_eq_true, ↓reduceIte, ha, false_and, mul_one, zero_add, le_refl]
      · have hn0 : (cfg.k - (s.att + 1)) = 0 := by omega
        have hnz : (((cfg.k - (s.att + 1)) : ℕ) : ℝ) = 0 := by rw [hn0]; simp
        obtain ⟨hl1, hl2⟩ := hl β (by omega)
        by_cases hsf : s.found = true
        · obtain ⟨q1, q2, _, q4, q5, _⟩ := hl1 (Or.inl hsf)
          have hWp : W (run (astep cfg d g) s β (alen cfg)) = Gesc cfg f sad (run (astep cfg d g) s β (alen cfg)) := by
            simp only [hW, q2, or_true, ↓reduceIte]
          rw [hWp]
          unfold Gesc
          rw [q4]
          simp only [q1, Bool.false_eq_true, ↓reduceIte, q5 hsf, hsf, hnz, zero_mul, add_zero, hx,
            le_refl]
        · have hsf' : s.found = false := by simpa using hsf
          simp only [hsf, Bool.false_eq_true, ↓reduceIte, hn0, pow_zero, mul_one]
          by_cases ha : accS cfg (run (astep cfg d g) s β (alen cfg))
          · obtain ⟨q1, q2, _, q4, _, q6⟩ := hl1 (Or.inr ⟨hsf', ha⟩)
            have hWp : W (run (astep cfg d g) s β (alen cfg)) = Gesc cfg f sad (run (astep cfg d g) s β (alen cfg)) := by
              simp only [hW, q2, or_true, ↓reduceIte]
            rw [hWp]
            unfold Gesc
            simp only [q1, Bool.false_eq_true, ↓reduceIte, q4, ha, true_and, mul_zero, add_zero, hx]
            rw [q6 ⟨hsf', ha⟩]
            unfold harm
            split_ifs <;> norm_num
          · obtain ⟨q1, q2⟩ := hl2 (fun h => h.elim (fun h' => hsf h') (fun h' => ha h'.2))
            have hWp : W (run (astep cfg d g) s β (alen cfg)) = Gesc cfg f sad (run (astep cfg d g) s β (alen cfg)) := by
              simp only [hW, q1, true_or, ↓reduceIte]
            rw [hWp]
            unfold Gesc
            simp only [q1, ↓reduceIte, ha, false_and, zero_add, mul_one, Nat.cast_zero, zero_mul, add_zero,
              le_refl]
    have hRint : Integrable (fun β =>
        (if s.found = true then harm cfg f x s.dx else
          (if accS cfg (run (astep cfg d g) s β (alen cfg)) ∧
            f x - cfg.r ^ 2 * cfg.θ / 5 < f (x + dxS cfg (run (astep cfg d g) s β (alen cfg))) then (1 : ℝ) else 0) +
          (if sad then (1 : ℝ) else 0) * (1 / 4) ^ (cfg.k - (s.att + 1)) * (if accS cfg (run (astep cfg d g) s β (alen cfg)) then (0 : ℝ) else 1)) +
        ((cfg.k - (s.att + 1) : ℕ) : ℝ) * (2 * ε)) (Measure.infinitePi fun _ : ℕ => ν) := by
      refine Integrable.add ?_ (integrable_const _)
      split_ifs <;> first | exact integrable_const _ | exact hIb.add (hIa.const_mul _)
    have hWi : Integrable (fun β => W (run (astep cfg d g) s β (alen cfg))) (Measure.infinitePi fun _ : ℕ => ν) :=
      Integrable.of_bound (C := 1 + cfg.k * (2 * ε))
        (hWm.comp (run_measurable (astep cfg d g) s hstep _)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun β => by rw [Real.norm_eq_abs]; exact hWbd _)
    refine (integral_mono hWi hRint hWpost).trans ?_
    rw [integral_add (by
        split_ifs <;> first | exact integrable_const _ | exact hIb.add (hIa.const_mul _))
      (integrable_const _), integral_const]
    simp only [probReal_univ, one_smul]
    unfold Zs
    rw [hcast]
    by_cases hsf : s.found = true
    · simp only [hsf, ↓reduceIte, integral_const, probReal_univ, one_smul, hx]
      nlinarith
    · have hsf' : s.found = false := by simpa using hsf
      simp only [hsf, Bool.false_eq_true, ↓reduceIte]
      rw [integral_add hIb (hIa.const_mul _), integral_const_mul]
      have h1 := hI1 s ⟨hd, hph, hj, hx, hatt⟩ hsf'
      have hnk : cfg.k - s.att = (cfg.k - (s.att + 1)) + 1 := by omega
      rw [hnk, ← hpow (cfg.k - (s.att + 1))]
      by_cases hs : sad
      · have h2 := hI2 hs s ⟨hd, hph, hj, hx, hatt⟩ hsf'
        have hp : (0 : ℝ) ≤ (if sad then (1 : ℝ) else 0) * (1 / 4) ^ (cfg.k - (s.att + 1)) := by rw [ite_eq_left hs]; positivity
        nlinarith
      · have hsc0 : (if sad then (1 : ℝ) else 0) = 0 := ite_eq_right hs
        rw [hsc0]
        simp only [zero_mul, add_zero]
        nlinarith
  have hstate : ∀ β, ∀ e, e < cfg.k →
      AttStart cfg x (run (astep cfg d g) s0 β (e * alen cfg)) ∧ (run (astep cfg d g) s0 β (e * alen cfg)).att = e :=
    fun β => reach_attempt cfg d g hM hT x s0 hs0 ha0 β
  have hdr := drift (astep cfg d g) s0 ν hstep (alen cfg) Inv hInvStep hs0' W (fun _ => 0) (fun _ _ => 0) hWm
    measurable_const measurable_const hYint (fun _ => integrable_const _) (fun _ => integrable_const _)
    cfg.k (by
      intro e he s ⟨β, hβ⟩
      obtain ⟨hst, hat⟩ := hstate β e he
      rw [← hβ] at hst hat
      simp only [add_zero]
      exact key s hst (by omega))
  simp only [integral_zero, Finset.sum_const_zero, add_zero] at hdr
  have hfin : ∀ β, W (run (astep cfg d g) s0 β (cfg.k * alen cfg)) = Gesc cfg f sad (run (astep cfg d g) s0 β (cfg.k * alen cfg)) := by
    intro β
    obtain ⟨m, hm⟩ : ∃ m, cfg.k = m + 1 := ⟨cfg.k - 1, by omega⟩
    obtain ⟨⟨hd, hph, hj, hx, _⟩, hat⟩ := hstate β m (by omega)
    have hsplit : run (astep cfg d g) s0 β (cfg.k * alen cfg) =
        run (astep cfg d g) (run (astep cfg d g) s0 β (m * alen cfg)) (shift (m * alen cfg) β) (alen cfg) := by
      rw [hm, add_mul, one_mul, run_add]
    rw [hsplit]
    obtain ⟨_, hl⟩ := post_fields cfg d g _ hd hph hj hM hT (shift (m * alen cfg) β)
    obtain ⟨hl1, hl2⟩ := hl (by rw [hat]; omega)
    by_cases hc : (run (astep cfg d g) s0 β (m * alen cfg)).found = true ∨
        ((run (astep cfg d g) s0 β (m * alen cfg)).found = false ∧
          accS cfg (run (astep cfg d g) (run (astep cfg d g) s0 β (m * alen cfg)) (shift (m * alen cfg) β) (alen cfg)))
    · obtain ⟨_, q2, _⟩ := hl1 hc
      simp only [hW, q2, or_true, ↓reduceIte]
    · obtain ⟨q1, _⟩ := hl2 hc
      simp only [hW, q1, true_or, ↓reduceIte]
  simp_rw [hfin] at hdr
  refine hdr.trans (le_of_eq ?_)
  have hWs0 : W s0 = Zs cfg f sad ε s0 := by
    obtain ⟨hd, hph, _, _, _⟩ := hs0
    simp only [hW, hd, hph, Bool.false_eq_true, false_or, reduceCtorEq, ↓reduceIte]
  rw [hWs0]
  unfold Zs
  simp only [hf0, Bool.false_eq_true, ↓reduceIte, ha0, Nat.sub_zero]

end LongTails.Proofs.GatedEscapeEscape
