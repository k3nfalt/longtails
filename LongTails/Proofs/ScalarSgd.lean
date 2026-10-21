import LongTails.Proofs.ScalarRate

open MeasureTheory

namespace OracleTemplate.BoundedScalarConvex

open LongTails.Setups.BoundedScalarConvex

lemma conditional_mean_bound {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {Y : Ω → ℝ} (hYi : Integrable Y μ) {H : ℝ} (hY : ∀ᵐ ω ∂μ, |Y ω| ≤ H) :
    ∀ᵐ ω ∂μ, |μ[Y | m] ω| ≤ H := by
  have hlo := condExp_mono (m := m) (integrable_const (-H)) hYi
    (hY.mono (fun _ h => (abs_le.mp h).1))
  have hhi := condExp_mono (m := m) hYi (integrable_const H)
    (hY.mono (fun _ h => (abs_le.mp h).2))
  rw [condExp_const hm] at hlo hhi
  filter_upwards [hlo, hhi] with ω hl hh
  exact abs_le.mpr ⟨hl, hh⟩

lemma scalar_sgd_rate {q : Params} {f : ℝ → ℝ} {O : Oracle ℝ ℝ}
    (hq : spec.valid q) (ha : spec.admissible q f O) {η : ℝ} (hη : 0 < η)
    (T : ℕ) (hT : 0 < T) :
    ∃ xstar ∈ Set.Icc q.lower q.upper, IsMinOn f (Set.Icc q.lower q.upper) xstar ∧
      Integrable (fun ω => f (scalarIterate O q.lower q.upper η q.x0 T ω)-f xstar)
        (O.law : Measure _) ∧
      (∫ ω, f (scalarIterate O q.lower q.upper η q.x0 T ω)-f xstar ∂(O.law : Measure _)) ≤
        q.R^2/(2*η*T)+(25/2)*η*q.H^2 := by
  rcases hq with ⟨hlu, hH, hR, _, hx0⟩
  rcases ha with ⟨hf, hL, ⟨xstar, hxstar, hmin, hdist⟩, ⟨hJoint, hObounds⟩⟩
  let μ : Measure (Samples O) := O.law
  let X := scalarIterate O q.lower q.upper η q.x0
  let Hpath := fun n ω => scalarHistoryAt O q.lower q.upper η q.x0 n ω
  let Y := fun n ω => answerAt O n (Hpath n ω) (0, X n ω) (ω n)
  let F := extension f q.lower q.upper q.H
  have hFm : ConvexOn ℝ Set.univ F := extension_convex hlu hH.le hf hL
  have hFc : Continuous F := extension_continuous hlu hH.le hL
  have hFL : ∀ x y, |F x-F y| ≤ q.H*|x-y| := extension_lipschitz hlu hH.le hL
  have hRun : ∀ n, Measurable[past O n] (X n) ∧ Measurable[past O n] (Hpath n) :=
    fun n => scalarRun_adapted O _ _ _ _ hJoint n
  have hXm : ∀ n, Measurable[past O n] (X n) := fun n => (hRun n).1
  have hHm : ∀ n, Measurable[past O n] (Hpath n) := fun n => (hRun n).2
  have hXa : ∀ n, Measurable (X n) := fun n => (hXm n).mono (past_le O n) le_rfl
  have hXmem : ∀ n ω, X n ω ∈ Set.Icc q.lower q.upper :=
    fun n ω => scalarIterate_mem O hlu hx0 n ω
  have hYbd : ∀ n, ∀ᵐ ω ∂μ, |Y n ω| ≤ q.H := fun n =>
    (hObounds n (Hpath n) (X n) (hHm n) (hXm n) (hXmem n)).1
  have hYi : ∀ n, Integrable (Y n) μ := by
    intro n
    change Integrable (fun ω => answerAt O n (Hpath n ω) (0, X n ω) (ω n)) μ
    have hHglob : Measurable (Hpath n) := (hHm n).mono (past_le O n) le_rfl
    have harg : Measurable (fun ω : Samples O =>
        ((Hpath n ω, (0, X n ω)), ω n) :
          Samples O → ((HistoryAt n × (Fin 1 × ℝ)) × O.Seed n)) :=
      ((hHglob.prodMk (measurable_const.prodMk (hXa n))).prodMk (measurable_pi_apply n))
    have hbound := Integrable.of_bound ((hJoint n).comp harg).aestronglyMeasurable q.H
      (by simpa [Function.comp_apply] using hYbd n)
    convert hbound using 1
    rfl
  have hg : ∀ n, ∀ᵐ ω ∂μ, |μ[Y n | past O n] ω| ≤ q.H := fun n =>
    conditional_mean_bound (past_le O n) (hYi n) (hYbd n)
  have hsub : ∀ n, ∀ᵐ ω ∂μ, ∀ y, F (X n ω)+μ[Y n | past O n] ω*(y-X n ω) ≤ F y := by
    intro n
    filter_upwards [hg n, (hObounds n (Hpath n) (X n) (hHm n) (hXm n) (hXmem n)).2] with ω hgω hs y
    exact extension_support hlu (hXmem n ω) hgω hs y
  have hrate := integral_last_iterate_rate (μ := μ) (past O) (past_mono O) (past_le O)
    hFm hFc hlu hη hH hFL hxstar hR X Y hXm hXmem (fun _ => hdist) hYi hYbd
    (fun n => Filter.Eventually.of_forall (fun ω => by
      change scalarIterate O q.lower q.upper η q.x0 (n+1) ω =
        project q.lower q.upper (scalarIterate O q.lower q.upper η q.x0 n ω -
          η * answerAt O n (Hpath n ω) (0, X n ω) (ω n))
      rw [answerAt_scalarRun]
      rfl)) hsub T hT
  have hFi : Integrable (fun ω => F (X T ω)-F xstar) μ :=
    (integrable_objective_interval hFc hH.le hFL (hXa T) (hXmem T)).sub (integrable_const _)
  have he : (fun ω => F (X T ω)-F xstar) = fun ω => f (X T ω)-f xstar := by
    funext ω
    dsimp [F]
    rw [extension_eq (hXmem T ω), extension_eq hxstar]
  rw [he] at hrate hFi
  exact ⟨xstar, hxstar, hmin, hFi, hrate⟩

lemma scalar_tuning {H R ε : ℝ} (hH : 0 < H) (hε : 0 < ε) :
    R^2/(2*(ε/(25*H^2))*(max 1 ⌈25*H^2*R^2/ε^2⌉₊ : ℕ))+
      (25/2)*(ε/(25*H^2))*H^2 ≤ ε := by
  let K := max 1 ⌈25*H^2*R^2/ε^2⌉₊
  have hK : (0 : ℝ) < K := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _))
  have hη : 0 < ε/(25*H^2) := by positivity
  have hceil : 25*H^2*R^2/ε^2 ≤ (K : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right 1 _))
  have hmul := (div_le_iff₀ (sq_pos_of_pos hε)).mp hceil
  have hinit : R^2/(2*(ε/(25*H^2))*K) ≤ ε/2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2*(ε/(25*H^2))*(K : ℝ))).mpr
    have he : ε/2*(2*(ε/(25*H^2))*(K : ℝ)) = (K : ℝ)*ε^2/(25*H^2) := by ring
    rw [he]
    apply (le_div_iff₀ (by positivity : 0 < 25*H^2)).mpr
    nlinarith
  have hnoise : (25/2)*(ε/(25*H^2))*H^2 = ε/2 := by field_simp
  rw [hnoise]
  change R^2/(2*(ε/(25*H^2))*K)+ε/2 ≤ ε
  linarith

end OracleTemplate.BoundedScalarConvex
