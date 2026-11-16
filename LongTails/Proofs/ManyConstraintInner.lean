import LongTails.Proofs.ManyConstraintStream
import LongTails.Proofs.RecursiveGradientEnergy

open MeasureTheory Set Metric
open scoped BigOperators

namespace LongTails.Proofs.ManyConstraintInner

open LongTails.Proofs.ManyConstraintStream

variable {E : Type*} [MeasurableSpace E]
variable {Ξ : Type*} [MeasurableSpace Ξ]
variable {m b : ℕ}

noncomputable def runG (T : (E × E) → Fin m → (Fin b → Ξ) → E × E) :
    (n : ℕ) → (E × E) → (Fin n → Fin m) → (ℕ → Ξ) → E × E
  | 0, yz, _, _ => yz
  | n + 1, yz, js, ξ => runG T n (T yz (js 0) (fun i => ξ i)) (fun i => js i.succ)
      (fun t => ξ (b + 2 + t))

noncomputable def valG (T : (E × E) → Fin m → (Fin b → Ξ) → E × E) (θ : ℝ) (D : E → ℝ) :
    (n : ℕ) → (E × E) → (Fin n → Fin m) → (ℕ → Ξ) → ℝ
  | 0, _, _, _ => 0
  | n + 1, yz, js, ξ => D (T yz (js 0) (fun i => ξ i)).1 +
      θ * valG T θ D n (T yz (js 0) (fun i => ξ i)) (fun i => js i.succ) (fun t => ξ (b + 2 + t))

variable {T : (E × E) → Fin m → (Fin b → Ξ) → E × E}

lemma runG_measurable (hT : ∀ j, Measurable (fun p : (E × E) × (Fin b → Ξ) => T p.1 j p.2)) :
    ∀ (n : ℕ) (js : Fin n → Fin m),
      Measurable (fun p : (E × E) × (ℕ → Ξ) => runG T n p.1 js p.2) := by
  intro n
  induction n with
  | zero => intro js; exact measurable_fst
  | succ n ih =>
    intro js
    have hg : Measurable (fun p : (E × E) × (ℕ → Ξ) => (p.1, fun i : Fin b => p.2 i)) :=
      measurable_fst.prodMk (Measurable.of_eval fun i =>
        (measurable_pi_apply (i : ℕ)).comp measurable_snd)
    have hnext : Measurable (fun p : (E × E) × (ℕ → Ξ) => T p.1 (js 0) (fun i => p.2 i)) :=
      (hT (js 0)).comp hg
    have htail : Measurable (fun p : (E × E) × (ℕ → Ξ) => (fun t => p.2 (b + 2 + t))) :=
      Measurable.of_eval fun t => (measurable_pi_apply (b + 2 + t)).comp measurable_snd
    exact (ih (fun i => js i.succ)).comp (hnext.prodMk htail)

lemma valG_measurable (hT : ∀ j, Measurable (fun p : (E × E) × (Fin b → Ξ) => T p.1 j p.2))
    (θ : ℝ) {D : E → ℝ} (hD : Measurable D) :
    ∀ (n : ℕ) (js : Fin n → Fin m),
      Measurable (fun p : (E × E) × (ℕ → Ξ) => valG T θ D n p.1 js p.2) := by
  intro n
  induction n with
  | zero => intro js; exact measurable_const
  | succ n ih =>
    intro js
    have hg : Measurable (fun p : (E × E) × (ℕ → Ξ) => (p.1, fun i : Fin b => p.2 i)) :=
      measurable_fst.prodMk (Measurable.of_eval fun i =>
        (measurable_pi_apply (i : ℕ)).comp measurable_snd)
    have hnext : Measurable (fun p : (E × E) × (ℕ → Ξ) => T p.1 (js 0) (fun i => p.2 i)) :=
      (hT (js 0)).comp hg
    have htail : Measurable (fun p : (E × E) × (ℕ → Ξ) => (fun t => p.2 (b + 2 + t))) :=
      Measurable.of_eval fun t => (measurable_pi_apply (b + 2 + t)).comp measurable_snd
    exact (hD.comp hnext.fst).add (((ih (fun i => js i.succ)).comp (hnext.prodMk htail)).const_mul θ)

omit [MeasurableSpace E] [MeasurableSpace Ξ] in
lemma runG_mem {S : Set E} (hT : ∀ yz j ω, (T yz j ω).1 ∈ S ∧ (T yz j ω).2 ∈ S) :
    ∀ (n : ℕ) (yz : E × E) (js : Fin n → Fin m) (ξ : ℕ → Ξ),
      yz.1 ∈ S → yz.2 ∈ S → (runG T n yz js ξ).1 ∈ S ∧ (runG T n yz js ξ).2 ∈ S := by
  intro n
  induction n with
  | zero => intro yz js ξ h1 h2; exact ⟨h1, h2⟩
  | succ n ih =>
    intro yz js ξ _ _
    exact ih _ _ _ (hT _ _ _).1 (hT _ _ _).2

noncomputable def wsum (θ : ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, θ ^ i

lemma wsum_succ (θ : ℝ) (n : ℕ) : wsum θ (n + 1) = 1 + θ * wsum θ n := by
  unfold wsum
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_succ, pow_zero]
  ring_nf

lemma wsum_nonneg {θ : ℝ} (hθ : 0 ≤ θ) (n : ℕ) : 0 ≤ wsum θ n :=
  Finset.sum_nonneg fun i _ => pow_nonneg hθ i

omit [MeasurableSpace E] [MeasurableSpace Ξ] in
lemma valG_abs_le {S : Set E} (hT : ∀ yz j ω, (T yz j ω).1 ∈ S ∧ (T yz j ω).2 ∈ S)
    {θ : ℝ} (hθ : 0 ≤ θ) {D : E → ℝ} {B : ℝ} (hB : ∀ x ∈ S, |D x| ≤ B) :
    ∀ (n : ℕ) (yz : E × E) (js : Fin n → Fin m) (ξ : ℕ → Ξ),
      |valG T θ D n yz js ξ| ≤ wsum θ n * B := by
  intro n
  induction n with
  | zero => intro yz js ξ; simp [valG, wsum]
  | succ n ih =>
    intro yz js ξ
    simp only [valG]
    rw [wsum_succ]
    calc _ ≤ |D (T yz (js 0) (fun i => ξ i)).1| + |θ * valG T θ D n (T yz (js 0) (fun i => ξ i))
          (fun i => js i.succ) (fun t => ξ (b + 2 + t))| := abs_add_le _ _
      _ ≤ B + θ * (wsum θ n * B) := by
          rw [abs_mul, abs_of_nonneg hθ]
          gcongr
          · exact hB _ (hT _ _ _).1
          · exact ih _ _ _
      _ = _ := by ring

lemma expect_integral_comm {A W : Type*} [Fintype A] [MeasurableSpace W] {ν : Measure W}
    (F : A → W → ℝ) (hF : ∀ a, Integrable (F a) ν) :
    (𝔼 a, ∫ w, F a w ∂ν) = ∫ w, 𝔼 a, F a w ∂ν := by
  simp only [Finset.expect_eq_sum_div_card]
  rw [integral_div, integral_finsetSum _ fun a _ => hF a]

noncomputable def sumG [AddCommGroup E] [Module ℝ E] (T : (E × E) → Fin m → (Fin b → Ξ) → E × E)
    (θ : ℝ) : (n : ℕ) → (E × E) → (Fin n → Fin m) → (ℕ → Ξ) → E
  | 0, _, _, _ => 0
  | n + 1, yz, js, ξ => (T yz (js 0) (fun i => ξ i)).1 +
      θ • sumG T θ n (T yz (js 0) (fun i => ξ i)) (fun i => js i.succ) (fun t => ξ (b + 2 + t))

lemma wsum_pos {θ : ℝ} (hθ : 0 < θ) {n : ℕ} (hn : 0 < n) : 0 < wsum θ n := by
  unfold wsum
  exact Finset.sum_pos (fun i _ => pow_pos hθ i) (Finset.nonempty_range_iff.mpr hn.ne')

omit [MeasurableSpace E] [MeasurableSpace Ξ] in
lemma jensen_inner [AddCommGroup E] [Module ℝ E] {S : Set E} (hS : Convex ℝ S)
    (hTS : ∀ yz j ω, (T yz j ω).1 ∈ S ∧ (T yz j ω).2 ∈ S) {θ : ℝ} (hθ : 0 < θ)
    {D : E → ℝ} (hD : ConvexOn ℝ S D) :
    ∀ (n : ℕ) (yz : E × E) (js : Fin n → Fin m) (ξ : ℕ → Ξ), 0 < n →
      (wsum θ n)⁻¹ • sumG T θ n yz js ξ ∈ S ∧
      wsum θ n * D ((wsum θ n)⁻¹ • sumG T θ n yz js ξ) ≤ valG T θ D n yz js ξ := by
  intro n
  induction n with
  | zero => intro _ _ _ h; omega
  | succ n ih =>
    intro yz js ξ _
    set next := T yz (js 0) (fun i => ξ i)
    set js' := fun i : Fin n => js i.succ
    set ξ' := fun t => ξ (b + 2 + t)
    have hy := (hTS yz (js 0) (fun i => ξ i)).1
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have hw1 : wsum θ (0 + 1) = 1 := by simp [wsum]
      have hs1 : sumG T θ (0 + 1) yz js ξ = next.1 := by simp [sumG, next]
      have hv1 : valG T θ D (0 + 1) yz js ξ = D next.1 := by simp [valG, next]
      rw [hw1, hs1, hv1, inv_one, one_smul, one_mul]
      exact ⟨hy, le_refl _⟩
    · obtain ⟨hmem, hj⟩ := ih next js' ξ' hn
      have hw := wsum_pos hθ hn
      have hw1 : 0 < wsum θ (n + 1) := wsum_pos hθ (Nat.succ_pos n)
      have hsucc := wsum_succ θ n
      set a := 1 / wsum θ (n + 1)
      set c := θ * wsum θ n / wsum θ (n + 1)
      have ha : 0 ≤ a := by positivity
      have hc : 0 ≤ c := by positivity
      have hac : a + c = 1 := by
        simp only [a, c]; rw [hsucc]; field_simp
      have hpt : (wsum θ (n + 1))⁻¹ • sumG T θ (n + 1) yz js ξ =
          a • next.1 + c • ((wsum θ n)⁻¹ • sumG T θ n next js' ξ') := by
        simp only [sumG, a, c, smul_add, smul_smul]
        congr 1
        · rw [one_div]
        · congr 1; field_simp
      rw [hpt]
      refine ⟨hS hy hmem ha hc hac, ?_⟩
      have hconv := hD.2 hy hmem ha hc hac
      simp only [smul_eq_mul] at hconv
      have : wsum θ (n + 1) * (a * D next.1 + c * D ((wsum θ n)⁻¹ • sumG T θ n next js' ξ')) =
          D next.1 + θ * (wsum θ n * D ((wsum θ n)⁻¹ • sumG T θ n next js' ξ')) := by
        simp only [a, c]; field_simp
      simp only [valG]
      calc _ ≤ wsum θ (n + 1) * (a * D next.1 + c * D ((wsum θ n)⁻¹ • sumG T θ n next js' ξ')) :=
            mul_le_mul_of_nonneg_left hconv hw1.le
        _ = _ := this
        _ ≤ _ := by gcongr

section Energy

variable [NeZero m] (law : Measure Ξ) [IsProbabilityMeasure law]

lemma head_bound {S : Set E} (hTm : ∀ j, Measurable (fun p : (E × E) × (Fin b → Ξ) => T p.1 j p.2))
    (hTS : ∀ yz j ω, (T yz j ω).1 ∈ S ∧ (T yz j ω).2 ∈ S) {n : ℕ} (j : Fin m) (yz : E × E)
    (A : E × E → ℝ) (hAm : Measurable A) {CA : ℝ} (hAb : ∀ q, q.1 ∈ S → q.2 ∈ S → |A q| ≤ CA)
    (Ψ : (E × E) → (Fin n → Fin m) → (ℕ → Ξ) → ℝ)
    (hΨm : ∀ js, Measurable (fun p : (E × E) × (ℕ → Ξ) => Ψ p.1 js p.2)) {CΨ : ℝ}
    (hΨb : ∀ q js ξ, q.1 ∈ S → q.2 ∈ S → |Ψ q js ξ| ≤ CΨ) {θ : ℝ} (hθ : 0 ≤ θ)
    (R : E × E → ℝ) (hRm : Measurable R) {CR : ℝ} (hRb : ∀ q, q.1 ∈ S → q.2 ∈ S → |R q| ≤ CR)
    (ih : ∀ q, q.1 ∈ S → q.2 ∈ S →
      (𝔼 js : Fin n → Fin m, ∫ t, Ψ q js t ∂(Measure.infinitePi fun _ : ℕ => law)) ≤ R q) :
    (𝔼 js : Fin n → Fin m, ∫ ξ, (A (T yz j (fun i => ξ i)) +
        θ * Ψ (T yz j (fun i => ξ i)) js (fun t => ξ (b + 2 + t)))
        ∂(Measure.infinitePi fun _ : ℕ => law)) ≤
      ∫ ω, (A (T yz j ω) + θ * R (T yz j ω)) ∂(Measure.pi fun _ => law) := by
  set inf := Measure.infinitePi fun _ : ℕ => law
  have hn : Measurable (fun p : (Fin b → Ξ) × (ℕ → Ξ) => T yz j p.1) :=
    (hTm j).comp (measurable_const.prodMk measurable_fst)
  have hn1 : Measurable (fun ω : Fin b → Ξ => T yz j ω) :=
    (hTm j).comp (measurable_const.prodMk measurable_id)
  have hGm : ∀ js, Measurable (fun p : (Fin b → Ξ) × (ℕ → Ξ) =>
      A (T yz j p.1) + θ * Ψ (T yz j p.1) js p.2) := fun js =>
    (hAm.comp hn).add (((hΨm js).comp (hn.prodMk measurable_snd)).const_mul _)
  have hGb : ∀ (js : Fin n → Fin m) (p : (Fin b → Ξ) × (ℕ → Ξ)),
      |A (T yz j p.1) + θ * Ψ (T yz j p.1) js p.2| ≤ CA + θ * CΨ := by
    intro js p
    have h := hTS yz j p.1
    calc _ ≤ |A (T yz j p.1)| + |θ * Ψ (T yz j p.1) js p.2| := abs_add_le _ _
      _ ≤ _ := by
        rw [abs_mul, abs_of_nonneg hθ]
        gcongr
        · exact hAb _ h.1 h.2
        · exact hΨb _ _ _ h.1 h.2
  have hblock : ∀ js, ∫ ξ, (A (T yz j (fun i => ξ i)) +
      θ * Ψ (T yz j (fun i => ξ i)) js (fun t => ξ (b + 2 + t))) ∂inf =
      ∫ ω, ∫ t, (A (T yz j ω) + θ * Ψ (T yz j ω) js t) ∂inf ∂(Measure.pi fun _ => law) :=
    fun js => integral_block law b _ (hGm js) (hGb js)
  simp_rw [hblock]
  have hint : ∀ js : Fin n → Fin m, Integrable (fun ω => ∫ t,
      (A (T yz j ω) + θ * Ψ (T yz j ω) js t) ∂inf) (Measure.pi fun _ => law) := by
    intro js
    refine Integrable.of_bound ((hGm js).stronglyMeasurable.integral_prod_right'.aestronglyMeasurable)
      (CA + θ * CΨ) (Filter.Eventually.of_forall fun ω => ?_)
    refine (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun t => ?_)).trans
      (by rw [probReal_univ, mul_one])
    rw [Real.norm_eq_abs]; exact hGb js (ω, t)
  rw [expect_integral_comm _ hint]
  have hpt : ∀ ω : Fin b → Ξ, (𝔼 js : Fin n → Fin m, ∫ t,
      (A (T yz j ω) + θ * Ψ (T yz j ω) js t) ∂inf) ≤ A (T yz j ω) + θ * R (T yz j ω) := by
    intro ω
    have h := hTS yz j ω
    have hΨi : ∀ js, Integrable (fun t => Ψ (T yz j ω) js t) inf := fun js =>
      Integrable.of_bound (((hΨm js).comp (measurable_const.prodMk measurable_id)
        ).aestronglyMeasurable) CΨ (Filter.Eventually.of_forall fun t => by
          rw [Real.norm_eq_abs]; exact hΨb _ _ _ h.1 h.2)
    have heq : ∀ js, ∫ t, (A (T yz j ω) + θ * Ψ (T yz j ω) js t) ∂inf =
        A (T yz j ω) + θ * ∫ t, Ψ (T yz j ω) js t ∂inf := by
      intro js
      rw [integral_add (integrable_const _) ((hΨi js).const_mul _), integral_const,
        integral_const_mul]
      simp
    simp_rw [heq]
    rw [Finset.expect_add_distrib, Fintype.expect_const, ← Finset.mul_expect]
    have := ih _ h.1 h.2
    nlinarith [mul_le_mul_of_nonneg_left this hθ]
  have hL : Integrable (fun ω : Fin b → Ξ => 𝔼 js : Fin n → Fin m, ∫ t,
      (A (T yz j ω) + θ * Ψ (T yz j ω) js t) ∂inf) (Measure.pi fun _ => law) := by
    simp only [Finset.expect_eq_sum_div_card]
    exact (integrable_finsetSum _ fun js _ => hint js).div_const _
  have hR : Integrable (fun ω : Fin b → Ξ => A (T yz j ω) + θ * R (T yz j ω))
      (Measure.pi fun _ => law) :=
    Integrable.of_bound (((hAm.comp hn1).add ((hRm.comp hn1).const_mul _)).aestronglyMeasurable)
      (CA + θ * CR) (Filter.Eventually.of_forall fun ω => by
        have h := hTS yz j ω
        rw [Real.norm_eq_abs]
        calc _ ≤ |A (T yz j ω)| + |θ * R (T yz j ω)| := abs_add_le _ _
          _ ≤ _ := by
            rw [abs_mul, abs_of_nonneg hθ]
            gcongr
            · exact hAb _ h.1 h.2
            · exact hRb _ h.1 h.2)
  exact integral_mono hL hR hpt

lemma inner_energy [NormedAddCommGroup E] [BorelSpace E] [SecondCountableTopology E] {S : Set E}
    (hTm : ∀ j, Measurable (fun p : (E × E) × (Fin b → Ξ) => T p.1 j p.2))
    (hTS : ∀ yz j ω, (T yz j ω).1 ∈ S ∧ (T yz j ω).2 ∈ S) {θ : ℝ} (hθ : 0 < θ)
    (c d e Ds : ℝ) (u : E) {D : E → ℝ} (hDm : Measurable D) {B : ℝ}
    (hB : ∀ x ∈ S, |D x| ≤ B) {Cz : ℝ} (hzu : ∀ x ∈ S, ‖x - u‖ ^ 2 ≤ Cz)
    (hstep : ∀ yz : E × E, yz.1 ∈ S → yz.2 ∈ S →
      (𝔼 j, ∫ ω, (D (T yz j ω).1 + d * θ * ‖(T yz j ω).2 - u‖ ^ 2)
        ∂(Measure.pi fun _ => law)) ≤ c * D yz.1 + d * ‖yz.2 - u‖ ^ 2 + 1 / 2 * Ds + e) :
    ∀ (n : ℕ) (yz : E × E), yz.1 ∈ S → yz.2 ∈ S →
      (𝔼 js : Fin n → Fin m, ∫ ξ,
        ((1 - c * θ) * valG T θ D n yz js ξ + c * θ ^ n * D (runG T n yz js ξ).1 +
          d * θ ^ n * ‖(runG T n yz js ξ).2 - u‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => law)) ≤
      c * D yz.1 + d * ‖yz.2 - u‖ ^ 2 + 1 / 2 * wsum θ n * Ds + wsum θ n * e := by
  have hzm : Measurable (fun x : E => ‖x - u‖ ^ 2) := (measurable_id.sub measurable_const).norm.pow_const 2
  intro n
  induction n with
  | zero =>
    intro yz _ _
    have e0 : ∀ (js : Fin 0 → Fin m) (ξ : ℕ → Ξ),
        (1 - c * θ) * valG T θ D 0 yz js ξ + c * θ ^ 0 * D (runG T 0 yz js ξ).1 +
          d * θ ^ 0 * ‖(runG T 0 yz js ξ).2 - u‖ ^ 2 = c * D yz.1 + d * ‖yz.2 - u‖ ^ 2 := by
      intro js ξ; simp [valG, runG]
    simp only [e0, integral_const, probReal_univ, one_smul, Fintype.expect_const]
    simp [wsum]
  | succ n ih =>
    intro yz hy hz
    set Ψ : (E × E) → (Fin n → Fin m) → (ℕ → Ξ) → ℝ := fun q js ξ =>
      (1 - c * θ) * valG T θ D n q js ξ + c * θ ^ n * D (runG T n q js ξ).1 +
        d * θ ^ n * ‖(runG T n q js ξ).2 - u‖ ^ 2 with hΨ
    have hΨm : ∀ js, Measurable (fun p : (E × E) × (ℕ → Ξ) => Ψ p.1 js p.2) := by
      intro js
      have h1 := runG_measurable hTm n js
      have h2 := valG_measurable hTm θ hDm n js
      exact ((h2.const_mul _).add ((hDm.comp h1.fst).const_mul _)).add
        ((hzm.comp h1.snd).const_mul _)
    have hΨb : ∀ q js ξ, q.1 ∈ S → q.2 ∈ S →
        |Ψ q js ξ| ≤ |1 - c * θ| * (wsum θ n * B) + |c * θ ^ n| * B + |d * θ ^ n| * Cz := by
      intro q js ξ h1 h2
      have hr := runG_mem hTS n q js ξ h1 h2
      calc |Ψ q js ξ| ≤ |(1 - c * θ) * valG T θ D n q js ξ| + |c * θ ^ n * D (runG T n q js ξ).1| +
            |d * θ ^ n * ‖(runG T n q js ξ).2 - u‖ ^ 2| := abs_add_three _ _ _
        _ ≤ _ := by
          rw [abs_mul (1 - c * θ), abs_mul (c * θ ^ n), abs_mul (d * θ ^ n),
            abs_of_nonneg (sq_nonneg ‖(runG T n q js ξ).2 - u‖)]
          gcongr
          · exact valG_abs_le hTS hθ.le hB n q js ξ
          · exact hB _ hr.1
          · exact hzu _ hr.2
    have hunfold : ∀ (j : Fin m) (js : Fin n → Fin m) (ξ : ℕ → Ξ),
        (1 - c * θ) * valG T θ D (n + 1) yz (Fin.cons j js) ξ +
          c * θ ^ (n + 1) * D (runG T (n + 1) yz (Fin.cons j js) ξ).1 +
          d * θ ^ (n + 1) * ‖(runG T (n + 1) yz (Fin.cons j js) ξ).2 - u‖ ^ 2 =
        (1 - c * θ) * D (T yz j (fun i => ξ i)).1 +
          θ * Ψ (T yz j (fun i => ξ i)) js (fun t => ξ (b + 2 + t)) := by
      intro j js ξ
      simp only [valG, runG, Fin.cons_zero, Fin.cons_succ, hΨ, pow_succ]
      ring
    rw [OracleTemplate.NonconvexFiniteSum.expect_function_succ]
    simp_rw [hunfold]
    set K := 1 / 2 * wsum θ n * Ds + wsum θ n * e
    have hj : ∀ j : Fin m, (𝔼 js : Fin n → Fin m, ∫ ξ,
        ((1 - c * θ) * D (T yz j (fun i => ξ i)).1 +
          θ * Ψ (T yz j (fun i => ξ i)) js (fun t => ξ (b + 2 + t)))
          ∂(Measure.infinitePi fun _ : ℕ => law)) ≤
        (∫ ω, (D (T yz j ω).1 + d * θ * ‖(T yz j ω).2 - u‖ ^ 2) ∂(Measure.pi fun _ => law)) +
          θ * K := by
      intro j
      have hb := head_bound law hTm hTS j yz (fun q => (1 - c * θ) * D q.1)
        ((hDm.comp measurable_fst).const_mul _) (CA := |1 - c * θ| * B)
        (fun q h1 _ => by rw [abs_mul]; gcongr; exact hB _ h1) Ψ hΨm hΨb hθ.le
        (fun q => c * D q.1 + d * ‖q.2 - u‖ ^ 2 + K)
        ((((hDm.comp measurable_fst).const_mul _).add ((hzm.comp measurable_snd).const_mul _)).add
          measurable_const) (CR := |c| * B + |d| * Cz + |K|)
        (fun q h1 h2 => by
          calc |c * D q.1 + d * ‖q.2 - u‖ ^ 2 + K| ≤ |c * D q.1| + |d * ‖q.2 - u‖ ^ 2| + |K| :=
                abs_add_three _ _ _
            _ ≤ _ := by
              rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg ‖q.2 - u‖)]
              gcongr
              · exact hB _ h1
              · exact hzu _ h2)
        (fun q h1 h2 => by
          have := ih q h1 h2
          show _ ≤ c * D q.1 + d * ‖q.2 - u‖ ^ 2 + (1 / 2 * wsum θ n * Ds + wsum θ n * e)
          simp only [hΨ]
          linarith)
      have hn1 : Measurable (fun ω : Fin b → Ξ => T yz j ω) :=
        (hTm j).comp (measurable_const.prodMk measurable_id)
      have hI : Integrable (fun ω : Fin b → Ξ => D (T yz j ω).1 + d * θ * ‖(T yz j ω).2 - u‖ ^ 2)
          (Measure.pi fun _ => law) :=
        Integrable.of_bound (((hDm.comp hn1.fst).add ((hzm.comp hn1.snd).const_mul _)
          ).aestronglyMeasurable) (B + |d * θ| * Cz) (Filter.Eventually.of_forall fun ω => by
            have h := hTS yz j ω
            rw [Real.norm_eq_abs]
            calc _ ≤ |D (T yz j ω).1| + |d * θ * ‖(T yz j ω).2 - u‖ ^ 2| := abs_add_le _ _
              _ ≤ _ := by
                rw [abs_mul (d * θ), abs_of_nonneg (sq_nonneg ‖(T yz j ω).2 - u‖)]
                gcongr
                · exact hB _ h.1
                · exact hzu _ h.2)
      have heq : ∫ ω, ((1 - c * θ) * D (T yz j ω).1 +
          θ * (c * D (T yz j ω).1 + d * ‖(T yz j ω).2 - u‖ ^ 2 + K)) ∂(Measure.pi fun _ => law) =
          (∫ ω, (D (T yz j ω).1 + d * θ * ‖(T yz j ω).2 - u‖ ^ 2) ∂(Measure.pi fun _ => law)) +
            θ * K := by
        have hpt : ∀ ω : Fin b → Ξ, (1 - c * θ) * D (T yz j ω).1 +
            θ * (c * D (T yz j ω).1 + d * ‖(T yz j ω).2 - u‖ ^ 2 + K) =
            (D (T yz j ω).1 + d * θ * ‖(T yz j ω).2 - u‖ ^ 2) + θ * K := fun ω => by ring
        simp_rw [hpt]
        rw [integral_add hI (integrable_const _), integral_const]
        simp
      exact hb.trans heq.le
    have hE := Finset.expect_le_expect (s := Finset.univ) fun j _ => hj j
    rw [Finset.expect_add_distrib, Fintype.expect_const] at hE
    have hs := hstep yz hy hz
    have hKdef : θ * K = θ * (1 / 2 * wsum θ n * Ds) + θ * (wsum θ n * e) := by ring
    rw [hKdef] at hE
    rw [wsum_succ]
    linarith [hE, hs]

omit [NeZero m] in
lemma sumG_measurable [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E]
    [SecondCountableTopology E]
    (hTm : ∀ j, Measurable (fun p : (E × E) × (Fin b → Ξ) => T p.1 j p.2)) (θ : ℝ) :
    ∀ (n : ℕ) (js : Fin n → Fin m),
      Measurable (fun p : (E × E) × (ℕ → Ξ) => sumG T θ n p.1 js p.2) := by
  intro n
  induction n with
  | zero => intro js; exact measurable_const
  | succ n ih =>
    intro js
    have hg : Measurable (fun p : (E × E) × (ℕ → Ξ) => (p.1, fun i : Fin b => p.2 i)) :=
      measurable_fst.prodMk (Measurable.of_eval fun i =>
        (measurable_pi_apply (i : ℕ)).comp measurable_snd)
    have hnext : Measurable (fun p : (E × E) × (ℕ → Ξ) => T p.1 (js 0) (fun i => p.2 i)) :=
      (hTm (js 0)).comp hg
    have htail : Measurable (fun p : (E × E) × (ℕ → Ξ) => (fun t => p.2 (b + 2 + t))) :=
      Measurable.of_eval fun t => (measurable_pi_apply (b + 2 + t)).comp measurable_snd
    exact hnext.fst.add (((ih (fun i => js i.succ)).comp (hnext.prodMk htail)).const_smul θ)

lemma epoch_energy [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E]
    [SecondCountableTopology E] {S : Set E} (hS : Convex ℝ S)
    (hTm : ∀ j, Measurable (fun p : (E × E) × (Fin b → Ξ) => T p.1 j p.2))
    (hTS : ∀ yz j ω, (T yz j ω).1 ∈ S ∧ (T yz j ω).2 ∈ S) {θ : ℝ} (hθ : 0 < θ)
    (c d e Ds : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) (u : E) {D : E → ℝ} (hDm : Measurable D)
    (hDc : ConvexOn ℝ S D) (hD0 : ∀ x ∈ S, 0 ≤ D x) {B : ℝ} (hB : ∀ x ∈ S, |D x| ≤ B)
    {Cz : ℝ} (hzu : ∀ x ∈ S, ‖x - u‖ ^ 2 ≤ Cz) {M : ℕ} (hM : 0 < M)
    (hcoef : c * θ + 1 / 2 * θ ^ M ≤ 1)
    (hstep : ∀ yz : E × E, yz.1 ∈ S → yz.2 ∈ S →
      (𝔼 j, ∫ ω, (D (T yz j ω).1 + d * θ * ‖(T yz j ω).2 - u‖ ^ 2)
        ∂(Measure.pi fun _ => law)) ≤ c * D yz.1 + d * ‖yz.2 - u‖ ^ 2 + 1 / 2 * Ds + e)
    (yz : E × E) (hy : yz.1 ∈ S) (hz : yz.2 ∈ S) :
    θ ^ M * (𝔼 js : Fin M → Fin m, ∫ ξ,
      (1 / 2 * wsum θ M * D ((wsum θ M)⁻¹ • sumG T θ M yz js ξ) +
        c * D (runG T M yz js ξ).1 + d * ‖(runG T M yz js ξ).2 - u‖ ^ 2)
      ∂(Measure.infinitePi fun _ : ℕ => law)) ≤
      c * D yz.1 + d * ‖yz.2 - u‖ ^ 2 + 1 / 2 * wsum θ M * Ds + wsum θ M * e := by
  set inf := Measure.infinitePi fun _ : ℕ => law
  have hzm : Measurable (fun x : E => ‖x - u‖ ^ 2) :=
    (measurable_id.sub measurable_const).norm.pow_const 2
  have hie := inner_energy law hTm hTS hθ c d e Ds u hDm hB hzu hstep M yz hy hz
  have hw := wsum_pos hθ hM
  have hpt : ∀ js ξ, θ ^ M * (1 / 2 * wsum θ M * D ((wsum θ M)⁻¹ • sumG T θ M yz js ξ) +
        c * D (runG T M yz js ξ).1 + d * ‖(runG T M yz js ξ).2 - u‖ ^ 2) ≤
      (1 - c * θ) * valG T θ D M yz js ξ + c * θ ^ M * D (runG T M yz js ξ).1 +
        d * θ ^ M * ‖(runG T M yz js ξ).2 - u‖ ^ 2 := by
    intro js ξ
    obtain ⟨hmem, hj⟩ := jensen_inner hS hTS hθ hDc M yz js ξ hM
    have h0 : 0 ≤ wsum θ M * D ((wsum θ M)⁻¹ • sumG T θ M yz js ξ) :=
      mul_nonneg hw.le (hD0 _ hmem)
    have hcoef' : θ ^ M / 2 ≤ 1 - c * θ := by linarith
    have hv0 : 0 ≤ valG T θ D M yz js ξ := h0.trans hj
    nlinarith [mul_le_mul_of_nonneg_left hj (by positivity : (0 : ℝ) ≤ θ ^ M / 2),
      mul_le_mul_of_nonneg_right hcoef' hv0]
  have hrm := runG_measurable hTm M
  have hcm : Measurable (fun ξ : ℕ → Ξ => (yz, ξ)) := measurable_const.prodMk measurable_id
  have hsm := sumG_measurable hTm θ M
  have hvm := valG_measurable hTm θ hDm M
  have hLint : ∀ js, Integrable (fun ξ => θ ^ M * (1 / 2 * wsum θ M *
      D ((wsum θ M)⁻¹ • sumG T θ M yz js ξ) + c * D (runG T M yz js ξ).1 +
      d * ‖(runG T M yz js ξ).2 - u‖ ^ 2)) inf := by
    intro js
    have hm : Measurable (fun ξ : ℕ → Ξ => θ ^ M * (1 / 2 * wsum θ M *
        D ((wsum θ M)⁻¹ • sumG T θ M yz js ξ) + c * D (runG T M yz js ξ).1 +
        d * ‖(runG T M yz js ξ).2 - u‖ ^ 2)) := by
      have h1 := (hsm js).comp hcm
      have h2 := (hrm js).comp hcm
      exact (((hDm.comp (h1.const_smul _)).const_mul _).add ((hDm.comp h2.fst).const_mul _)).add
        ((hzm.comp h2.snd).const_mul _) |>.const_mul _
    refine Integrable.of_bound hm.aestronglyMeasurable
      (θ ^ M * (1 / 2 * wsum θ M * B + c * B + d * Cz)) (Filter.Eventually.of_forall fun ξ => ?_)
    obtain ⟨hmem, -⟩ := jensen_inner hS hTS hθ hDc M yz js ξ hM
    have hr := runG_mem hTS M yz js ξ hy hz
    have h1 := hD0 _ hmem
    have h2 := hD0 _ hr.1
    have hb1 := (abs_le.mp (hB _ hmem)).2
    have hb2 := (abs_le.mp (hB _ hr.1)).2
    have hz2 := hzu _ hr.2
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    gcongr
  have hRint : ∀ js, Integrable (fun ξ => (1 - c * θ) * valG T θ D M yz js ξ +
      c * θ ^ M * D (runG T M yz js ξ).1 + d * θ ^ M * ‖(runG T M yz js ξ).2 - u‖ ^ 2) inf := by
    intro js
    have h1 := (hvm js).comp hcm
    have h2 := (hrm js).comp hcm
    refine Integrable.of_bound ((((h1.const_mul _).add ((hDm.comp h2.fst).const_mul _)).add
      ((hzm.comp h2.snd).const_mul _)).aestronglyMeasurable)
      (|1 - c * θ| * (wsum θ M * B) + |c * θ ^ M| * B + |d * θ ^ M| * Cz)
      (Filter.Eventually.of_forall fun ξ => ?_)
    have hr := runG_mem hTS M yz js ξ hy hz
    rw [Real.norm_eq_abs]
    calc _ ≤ |(1 - c * θ) * valG T θ D M yz js ξ| + |c * θ ^ M * D (runG T M yz js ξ).1| +
          |d * θ ^ M * ‖(runG T M yz js ξ).2 - u‖ ^ 2| := abs_add_three _ _ _
      _ ≤ _ := by
        rw [abs_mul (1 - c * θ), abs_mul (c * θ ^ M), abs_mul (d * θ ^ M),
          abs_of_nonneg (sq_nonneg ‖(runG T M yz js ξ).2 - u‖)]
        gcongr
        · exact valG_abs_le hTS hθ.le hB M yz js ξ
        · exact hB _ hr.1
        · exact hzu _ hr.2
  rw [Finset.mul_expect]
  calc _ = (𝔼 js : Fin M → Fin m, ∫ ξ, θ ^ M * (1 / 2 * wsum θ M *
        D ((wsum θ M)⁻¹ • sumG T θ M yz js ξ) + c * D (runG T M yz js ξ).1 +
        d * ‖(runG T M yz js ξ).2 - u‖ ^ 2) ∂inf) := by
        congr 1; funext js; rw [integral_const_mul]
    _ ≤ _ := Finset.expect_le_expect fun js _ => integral_mono (hLint js) (hRint js) (hpt js)
    _ ≤ _ := hie

end Energy

end LongTails.Proofs.ManyConstraintInner
