import LongTails.Proofs.QuarticStageCertificate

namespace LongTails.Proofs.QuarticStageEnergy

open LongTails.Algorithms.QuarticMetricStage
open LongTails.Algorithms.GuardedMetricAcceleration
open LongTails.Proofs.QuarticStageInvariant
open LongTails.Proofs.QuarticStageTransition
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma full_trial_energy {μ L A D G n : ℝ}
    (hμ : 0 < μ) (hL : 0 < L) (hμL : μ ≤ L)
    (hn : 0 ≤ n)
    (hA₂ : μ * A ^ 2 ≤ 2 * D) (hradius : n ≤ A + G / L)
    (hdrop : G ^ 2 / (2 * L) ≤ D + G * A) : μ * n ^ 2 ≤ 28 * D := by
  have hD : 0 ≤ D := by nlinarith [sq_nonneg A]
  have hd := (div_le_iff₀ (by positivity : 0 < 2 * L)).mp hdrop
  have hy := sq_nonneg (G - 2 * L * A)
  have hg : G ^ 2 ≤ 4 * L * D + 4 * L ^ 2 * A ^ 2 := by nlinarith
  have hr := pow_le_pow_left₀ hn hradius 2
  have hcross := sq_nonneg (A - G / L)
  have hn' : n ^ 2 ≤ 2 * A ^ 2 + 2 * (G / L) ^ 2 := by nlinarith
  have hgn : (G / L) ^ 2 ≤ 4 * D / L + 4 * A ^ 2 := by
    rw [div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos hL)).mpr
    convert hg using 1
    field_simp
  have he : μ * (D / L) ≤ D := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hL).mpr
    nlinarith [mul_le_mul_of_nonneg_right hμL hD]
  have hnμ := mul_le_mul_of_nonneg_left hn' hμ.le
  have hgμ := mul_le_mul_of_nonneg_left hgn hμ.le
  rw [show 4 * D / L = 4 * (D / L) by ring] at hgμ
  nlinarith only [hnμ, hgμ, he, hA₂]

lemma truncated_trial_energy {μ L A D G n r : ℝ}
    (hμ : 0 < μ) (hL : 0 < L) (hμL : μ ≤ L) (hr : 0 < r)
    (hn : 0 ≤ n) (hAr : A ≤ r / 8)
    (hlarge : L * r / 2 ≤ G) (hradius : n ≤ A + r / 2)
    (hdrop : G * r / 4 ≤ D + G * A) : μ * n ^ 2 ≤ 16 * D := by
  have hG : 0 ≤ G := le_trans (by positivity) hlarge
  have hga := mul_le_mul_of_nonneg_left hAr hG
  have hgr := mul_le_mul_of_nonneg_right hlarge hr.le
  have hd : L * r ^ 2 ≤ 16 * D := by nlinarith
  have hnr : n ≤ r := by linarith
  have hns := pow_le_pow_left₀ hn hnr 2
  have hh := mul_le_mul_of_nonneg_left hns hμ.le
  have hm := mul_le_mul_of_nonneg_right hμL (sq_nonneg r)
  linarith

lemma trial_energy (p : Parameters E) (y next : Point E) {A : ℝ}
    (hL : 0 < p.L) (hμ : 0 < p.μ) (hμL : p.μ ≤ p.L) (hα : 0 ≤ p.α)
    (hr : 0 < p.r) (hAr : A ≤ p.r / 8) (hA₂ : p.μ * A ^ 2 = 2 * p.q)
    (hy : ‖p.S (y.x - p.center.x)‖ ≤ A) (hnext : next.x = trialPoint p y)
    (hsupport : value p y ≤ p.center.value + ‖transformedGradient p.S (gradient p y)‖ * A)
    (hdescent : value p next ≤ value p y - QuarticStageTrial.coefficient p y / 2 *
      ‖transformedGradient p.S (gradient p y)‖ ^ 2)
    (hprogress : next.value ≤ p.center.value - p.q) :
    p.μ * ‖p.S (next.x - p.center.x)‖ ^ 2 ≤ 28 * (p.center.value - next.value) := by
  let G := ‖transformedGradient p.S (gradient p y)‖
  let D := p.center.value - next.value
  have hD : p.q ≤ D := by dsimp [D]; linarith
  have hD₀ : 0 ≤ D := by nlinarith [sq_nonneg A]
  have ht₀ := QuarticStageTrial.coefficient_nonneg p y hL hr.le
  have hraw : next.value ≤ value p next := by
    unfold value regularizedValue
    exact le_add_of_nonneg_right (by positivity)
  have hdrop : QuarticStageTrial.coefficient p y / 2 * G ^ 2 ≤ D + G * A := by
    dsimp [D, G]
    linarith
  have hmove : ‖p.S (next.x - y.x)‖ = QuarticStageTrial.coefficient p y * G := by
    rw [hnext, QuarticStageTrial.trial_displacement, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht₀]
  have hn : ‖p.S (next.x - p.center.x)‖ ≤ A + QuarticStageTrial.coefficient p y * G := by
    calc
      _ = ‖p.S (y.x - p.center.x) + p.S (next.x - y.x)‖ := by rw [← map_add]; congr 2; abel
      _ ≤ ‖p.S (y.x - p.center.x)‖ + ‖p.S (next.x - y.x)‖ := norm_add_le _ _
      _ ≤ _ := by rw [hmove]; exact add_le_add_left hy _
  by_cases hz : G = 0
  · rw [hz, mul_zero, add_zero] at hn
    have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hn 2) hμ.le
    nlinarith
  have hG : 0 < G := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
  by_cases ht : p.L⁻¹ ≤ p.r / (2 * G)
  · have he : QuarticStageTrial.coefficient p y = p.L⁻¹ := min_eq_left ht
    rw [he] at hn hdrop
    apply full_trial_energy (A := A) (G := G) (D := D) hμ hL hμL (norm_nonneg _) (by linarith)
    · simpa only [div_eq_mul_inv, mul_comm] using hn
    · convert hdrop using 1
      ring
  · have ht' := lt_of_not_ge ht
    have he : QuarticStageTrial.coefficient p y = p.r / (2 * G) := min_eq_right ht'.le
    rw [he] at hn hdrop
    have he₁ : p.r / (2 * G) * G = p.r / 2 := by field_simp
    have he₂ : p.r / (2 * G) / 2 * G ^ 2 = G * p.r / 4 := by field_simp; ring
    rw [he₁] at hn
    rw [he₂] at hdrop
    have hlarge : p.L * p.r / 2 ≤ G := by
      have hh := (div_lt_iff₀ (by positivity : 0 < 2 * G)).mp ht'
      have hh' := mul_lt_mul_of_pos_left hh hL
      field_simp at hh'
      linarith
    have hh := truncated_trial_energy hμ hL hμL hr (norm_nonneg _) hAr hlarge hn hdrop
    dsimp [D] at hh ⊢
    linarith

def OutputEnergy (p : Parameters E) (x : Point E) : Prop :=
  ‖x.gradient‖ ≤ p.ε ∨ p.μ * ‖p.S (x.x - p.center.x)‖ ^ 2 ≤ 28 * (p.center.value - x.value)

def StatusEnergy (p : Parameters E) : Status E → Prop
  | .finished x => OutputEnergy p x
  | _ => True

omit [FiniteDimensional ℝ E] in
lemma radius_success_energy (p : Parameters E) (x : Point E) {A : ℝ}
    (hμ : 0 < p.μ) (hA₂ : p.μ * A ^ 2 = 2 * p.q)
    (hx : ‖p.S (x.x - p.center.x)‖ ≤ A) (hs : successful p x) : OutputEnergy p x := by
  rcases hs with hd | hg
  · right
    have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx 2) hμ.le
    have hq : 0 ≤ p.q := by nlinarith [sq_nonneg A]
    nlinarith
  · exact Or.inl hg

lemma step_energy (p : Parameters E) (f : E → ℝ) (g : Fin 2 × E → Reply E)
    (horacle : ∀ x, g (0, x) = .inl (f x, _root_.gradient f x))
    {A τ : ℝ} {k : ℕ} (status : Status E) (hi : StatusInvariant p f A τ k status)
    (he : StatusEnergy p status) (ha : 0 ≤ p.a)
    (hμ : 0 < p.μ) (hL : 0 < p.L) (hμL : p.μ ≤ p.L) (hα : 0 ≤ p.α) (hr : 0 < p.r)
    (hA₂ : p.μ * A ^ 2 = 2 * p.q) (hAr : A ≤ p.r / 8)
    (hmodel : ∀ y next : Point E, Faithful f y → Faithful f next →
      ‖p.S (y.x - p.center.x)‖ ≤ A → next.x = trialPoint p y →
      value p next ≤ value p y + ⟪gradient p y, next.x - y.x⟫ +
        p.L / 2 * ‖p.S (next.x - y.x)‖ ^ 2) :
    StatusEnergy p ((step p status).eval g) := by
  classical
  cases status with
  | finished x => exact he
  | witness w => trivial
  | running st =>
    let yx := p.S.symm (extrapolate p.a (p.S st.accepted.x) st.z)
    let y : Point E := ⟨yx, f yx, _root_.gradient f yx⟩
    let next : Point E := ⟨trialPoint p y, f (trialPoint p y), _root_.gradient f (trialPoint p y)⟩
    have hyfaith : Faithful f y := ⟨rfl, rfl⟩
    have hnfaith : Faithful f next := ⟨rfl, rfl⟩
    have hy : p.S y.x = extrapolate p.a (p.S st.accepted.x) st.z := by simp [y, yx]
    have hp := query_plane_geometry p f hi ha y hy hyfaith
    simp only [step, OracleTemplate.QueryPlan.eval, horacle, readPoint]
    split
    · rename_i hs
      exact radius_success_energy p y hμ hA₂ hp.point_radius hs
    · split
      · trivial
      · rename_i hc
        split
        · trivial
        · simp only [OracleTemplate.QueryPlan.eval, horacle]
          split
          · rename_i hs
            rcases hs with hd | hg
            · right
              have hsupport := QuarticStageModels.query_plane_center_support p y hμ.le hp.point_radius (not_not.mp hc)
              exact trial_energy p y next hL hμ hμL hα hr hAr hA₂ hp.point_radius rfl hsupport
                (QuarticStageTrial.trial_descent p y next hL hr.le rfl (hmodel y next hyfaith hnfaith hp.point_radius rfl)) hd
            · exact Or.inl hg
          · trivial

lemma loop_energy (p : Parameters E) (f : E → ℝ) (g : Fin 2 × E → Reply E)
    {A τ : ℝ}
    (hstep : ∀ k status, StatusInvariant p f A τ k status →
      StatusInvariant p f A τ (k + 1) ((step p status).eval g))
    (henergy : ∀ k status, StatusInvariant p f A τ k status → StatusEnergy p status →
      StatusEnergy p ((step p status).eval g))
    (n k : ℕ) (status : Status E) (hi : StatusInvariant p f A τ k status) (he : StatusEnergy p status) :
    StatusEnergy p ((loop p n status).eval g) := by
  induction n generalizing k status with
  | zero => exact he
  | succ n ih =>
    simp only [loop, id_eq, OracleTemplate.QueryPlan.eval_bind]
    exact ih (k + 1) _ (hstep k status hi) (henergy k status hi he)

lemma certificate_energy (p : Parameters E) (f : E → ℝ) (g : Fin 2 × E → Reply E)
    (horacle : ∀ x, g (0, x) = .inl (f x, _root_.gradient f x))
    {A τ : ℝ} {k : ℕ} (status : Status E) (hi : StatusInvariant p f A τ k status)
    (he : StatusEnergy p status) (hresult : StatusInvariant p f A τ k ((certificate p status).eval g))
    (hμ : 0 < p.μ) (hL : 0 < p.L) (hμL : p.μ ≤ p.L) (hα : 0 ≤ p.α) (hr : 0 < p.r)
    (hA : 0 ≤ A) (hA₂ : p.μ * A ^ 2 = 2 * p.q) (hAr : A ≤ p.r / 8)
    (hmodel : ∀ y next : Point E, Faithful f y → Faithful f next →
      ‖p.S (y.x - p.center.x)‖ ≤ A → next.x = trialPoint p y →
      value p next ≤ value p y + ⟪gradient p y, next.x - y.x⟫ +
        p.L / 2 * ‖p.S (next.x - y.x)‖ ^ 2) :
    StatusEnergy p ((certificate p status).eval g) := by
  classical
  cases status with
  | finished x => exact he
  | witness w => trivial
  | running st =>
    change Invariant p f A τ k st at hi
    let w : Point E := ⟨trialPoint p st.accepted, f (trialPoint p st.accepted),
      _root_.gradient f (trialPoint p st.accepted)⟩
    have hw : Faithful f w := ⟨rfl, rfl⟩
    simp only [certificate, OracleTemplate.QueryPlan.eval, horacle, readPoint] at hresult ⊢
    split at hresult <;> simp_all only [OracleTemplate.QueryPlan.eval, ↓reduceIte]
    · rename_i hs
      rcases hs with hd | hg
      · right
        have hs' : value p st.accepted ≤ p.center.value +
            ‖transformedGradient p.S (gradient p st.accepted)‖ * A :=
          hi.accepted_value.trans (le_add_of_nonneg_right (by positivity))
        exact trial_energy p st.accepted w hL hμ hμL hα hr hAr hA₂ hi.accepted_radius rfl hs'
          (QuarticStageTrial.trial_descent p st.accepted w hL hr.le rfl
            (hmodel st.accepted w hi.accepted_faithful hw hi.accepted_radius rfl)) hd
      · exact Or.inl hg
    · split
      · trivial
      · rename_i hnone
        have hh : Faithful f st.accepted ∧ successful p st.accepted := by
          simpa only [hnone, OracleTemplate.QueryPlan.eval, StatusInvariant] using hresult
        exact radius_success_energy p st.accepted hμ hA₂ hi.accepted_radius hh.2

end LongTails.Proofs.QuarticStageEnergy
