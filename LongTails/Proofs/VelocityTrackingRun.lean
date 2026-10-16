import LongTails.Proofs.VelocityTrackingStep
import LongTails.Proofs.SgdConvex
import LongTails.Proofs.SgdExecution
import LongTails.Algorithms.VelocityTrackingSgd
import LongTails.Setups.StochasticSmoothAndConvex

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace OracleTemplate.VelocityTracking

open LongTails.Setups.StochasticSmoothAndConvex

variable {E : Type*} {Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def step (g : ℕ → E → Ω → E) (γ β : ℝ) (t : ℕ) (z : E × E) (ω : Ω) : E × E :=
  (z.1 + z.2 - γ • g t (z.1 + z.2) ω, z.2 - β • g t (z.1 + z.2) ω)

def run (g : ℕ → E → Ω → E) (γ β : ℝ) : ℕ → (K : ℕ) → E × E → (Fin K → Ω) → E × E
  | _, 0, z, _ => z
  | t, K + 1, z, ξ => run g γ β (t + 1) K (step g γ β t z (ξ 0)) (fun i => ξ i.succ)

def vel (xstar : ℕ → E) (t : ℕ) : E := if t = 0 then xstar 1 - xstar 0 else xstar t - xstar (t - 1)

noncomputable def energy (xstar : ℕ → E) (s : ℝ) (t : ℕ) (z : E × E) : ℝ :=
  lyap (z.1 + z.2 - xstar t) (s⁻¹ • (z.2 - vel xstar t))

omit [InnerProductSpace ℝ E] in
lemma vel_succ (xstar : ℕ → E) (t : ℕ) : xstar (t + 1) = xstar t + vel xstar (t + 1) := by
  simp [vel]

omit [InnerProductSpace ℝ E] in
lemma vel_drift {xstar : ℕ → E} {Γ : ℝ}
    (h : ∀ k, ‖(xstar (k + 2) - xstar (k + 1)) - (xstar (k + 1) - xstar k)‖ ≤ Γ) (t : ℕ) :
    ‖vel xstar t - vel xstar (t + 1)‖ ≤ Γ := by
  rcases t with _ | t
  · simpa [vel] using (norm_nonneg _).trans (h 0)
  · rw [← norm_neg]
    simpa [vel, Nat.add_assoc] using h t

lemma lyap_drift {s : ℝ} (hs : 0 < s) (hs2 : s ≤ 1 / 2) (d : E) :
    lyap d (s⁻¹ • d) ≤ 6 * s⁻¹ ^ 2 * ‖d‖ ^ 2 := by
  have hr : 2 ≤ s⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hs]
    linarith
  simp only [lyap, inner_smul_right, real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hs), mul_pow]
  nlinarith [sq_nonneg ‖d‖]

variable [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω]

structure Hyp (f : ℕ → E → ℝ) (g : ℕ → E → Ω → E) (P : Measure Ω) [IsProbabilityMeasure P]
    (xstar : ℕ → E) (μ L σ Γ : ℝ) : Prop where
  pos : 0 < μ
  le : μ ≤ L
  oracle : ∀ k, IsStochasticGradient E Ω P (f k) (g k) σ
  grad : ∀ k x, HasGradientAt (f k) (gradient (f k) x) x
  strong : ∀ k x y, f k x + ⟪gradient (f k) x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ f k y
  lip : ∀ k x y, ‖gradient (f k) x - gradient (f k) y‖ ≤ L * ‖x - y‖
  min : ∀ k, IsMinOn (f k) univ (xstar k)
  drift : ∀ k, ‖(xstar (k + 2) - xstar (k + 1)) - (xstar (k + 1) - xstar k)‖ ≤ Γ

variable {f : ℕ → E → ℝ} {g : ℕ → E → Ω → E} {P : Measure Ω} [IsProbabilityMeasure P]
  {xstar : ℕ → E} {μ L σ Γ : ℝ}

omit [BorelSpace E] [SecondCountableTopology E] in
lemma noise_facts (h : Hyp f g P xstar μ L σ Γ) (γ : ℝ) (t : ℕ) (y : E) :
    Integrable (fun ω => γ • (g t y ω - gradient (f t) y)) P ∧
    (∫ ω, γ • (g t y ω - gradient (f t) y) ∂P) = 0 ∧
    Integrable (fun ω => ‖γ • (g t y ω - gradient (f t) y)‖ ^ 2) P ∧
    (∫ ω, ‖γ • (g t y ω - gradient (f t) y)‖ ^ 2 ∂P) ≤ γ ^ 2 * σ ^ 2 := by
  have ho := h.oracle t
  have hn : Integrable (fun ω => g t y ω - gradient (f t) y) P :=
    (ho.integrable y).sub (integrable_const _)
  have hsq : (fun ω => ‖γ • (g t y ω - gradient (f t) y)‖ ^ 2) =
      fun ω => γ ^ 2 * ‖g t y ω - gradient (f t) y‖ ^ 2 := by
    funext ω
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  refine ⟨hn.smul γ, ?_, ?_, ?_⟩
  · rw [integral_smul, integral_sub (ho.integrable y) (integrable_const (gradient (f t) y)),
      ho.unbiased, integral_const]
    simp
  · rw [hsq]
    exact (ho.variance_integrable y).const_mul _
  · rw [hsq, integral_const_mul]
    exact mul_le_mul_of_nonneg_left (ho.variance y) (sq_nonneg γ)

omit [BorelSpace E] [SecondCountableTopology E] in
lemma energy_step (h : Hyp f g P xstar μ L σ Γ) {γ : ℝ} (hγ : 0 < γ) (hγL : γ * L ≤ 1 / 2)
    (t : ℕ) (z : E × E) :
    Integrable (fun ω => energy xstar (γ * μ) (t + 1) (step g γ (γ * (γ * μ) / 4) t z ω)) P ∧
    (∫ ω, energy xstar (γ * μ) (t + 1) (step g γ (γ * (γ * μ) / 4) t z ω) ∂P) ≤
      (1 - γ * μ / 16) * energy xstar (γ * μ) t z + 102 * Γ ^ 2 * (γ * μ)⁻¹ ^ 3 +
        γ ^ 2 * σ ^ 2 := by
  set s := γ * μ with hsdef
  have hL : 0 < L := h.pos.trans_le h.le
  have hs : 0 < s := mul_pos hγ h.pos
  have hs2 : s ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left h.le hγ.le
    linarith
  set y := z.1 + z.2
  set G := γ • gradient (f t) y
  set p := y - xstar t
  set w := s⁻¹ • (z.2 - vel xstar t)
  set d := vel xstar t - vel xstar (t + 1)
  set n := fun ω => γ • (g t y ω - gradient (f t) y)
  set A1 := (p + s • w - (1 + s / 4) • G) + d
  set A2 := (w - (1 / 4 : ℝ) • G) + s⁻¹ • d
  have hw : s • w = z.2 - vel xstar t := by
    simp only [w, smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
  have hc : s⁻¹ * (γ * s / 4) = γ / 4 := by field_simp
  have hrep : ∀ ω, energy xstar s (t + 1) (step g γ (γ * s / 4) t z ω) =
      lyap (A1 + (-(1 + s / 4)) • n ω) (A2 + (-(1 / 4 : ℝ)) • n ω) := by
    intro ω
    simp only [energy, step]
    congr 1
    · rw [vel_succ xstar t]
      simp only [A1, n, G, p, d]
      rw [hw]
      module
    · simp only [A2, n, G, d, w]
      rw [show z.2 - (γ * s / 4) • g t y ω - vel xstar (t + 1) =
          (z.2 - vel xstar t) + (vel xstar t - vel xstar (t + 1)) - (γ * s / 4) • g t y ω by
          module, smul_sub, smul_add, smul_smul, hc]
      module
  obtain ⟨hn, hn0, hnn, hnn2⟩ := noise_facts h γ t y
  set c := ((2 * (-(1 + s / 4)) - 3 * (-(1 / 4 : ℝ))) • A1 +
    (12 * (-(1 / 4 : ℝ)) - 3 * (-(1 + s / 4))) • A2)
  set κ := (-(1 + s / 4)) ^ 2 - 3 * (-(1 + s / 4)) * (-(1 / 4 : ℝ)) + 6 * (-(1 / 4 : ℝ)) ^ 2
  have hexp : ∀ ω, energy xstar s (t + 1) (step g γ (γ * s / 4) t z ω) =
      lyap A1 A2 + ⟪c, n ω⟫ + κ * ‖n ω‖ ^ 2 := fun ω => by
    rw [hrep ω, lyap_add_smul]
  have hκ0 : 0 ≤ κ := by simp only [κ]; nlinarith
  have hκ1 : κ ≤ 1 := by simp only [κ]; nlinarith
  have hn' : Integrable n P := hn
  have hn0' : ∫ ω, n ω ∂P = 0 := hn0
  have hnn' : Integrable (fun ω => ‖n ω‖ ^ 2) P := hnn
  have hnn2' : ∫ ω, ‖n ω‖ ^ 2 ∂P ≤ γ ^ 2 * σ ^ 2 := hnn2
  have hi1 : Integrable (fun ω => lyap A1 A2 + ⟪c, n ω⟫) P :=
    (integrable_const _).add (hn'.const_inner c)
  have hi2 : Integrable (fun ω => κ * ‖n ω‖ ^ 2) P := hnn'.const_mul κ
  have hfun : (fun ω => energy xstar s (t + 1) (step g γ (γ * s / 4) t z ω)) =
      fun ω => (lyap A1 A2 + ⟪c, n ω⟫) + κ * ‖n ω‖ ^ 2 := funext hexp
  have hsplit : ∫ ω, (lyap A1 A2 + ⟪c, n ω⟫) + κ * ‖n ω‖ ^ 2 ∂P =
      lyap A1 A2 + κ * ∫ ω, ‖n ω‖ ^ 2 ∂P := by
    rw [integral_add hi1 hi2, integral_add (integrable_const _) (hn'.const_inner c),
      integral_inner hn' c, hn0', inner_zero_right, integral_const_mul]
    simp
  rw [hfun]
  refine ⟨hi1.add hi2, ?_⟩
  rw [hsplit]
  obtain ⟨h1, h2⟩ := sector h.pos hL hγ hγL (h.grad t) (h.strong t) (h.lip t) (h.min t) y
  have hcon := lyap_contract hs hs2 p w G (by simpa [p, G, hsdef] using h1)
    (by simpa [p, G] using h2)
  have hyoung := lyap_young (by positivity : (0 : ℝ) < s / 16)
    (p + s • w - (1 + s / 4) • G) (w - (1 / 4 : ℝ) • G) d (s⁻¹ • d)
  have hdrift := lyap_drift hs hs2 d
  have hd : ‖d‖ ≤ Γ := vel_drift h.drift t
  have hΓ : 0 ≤ Γ := (norm_nonneg _).trans hd
  have hd2 : ‖d‖ ^ 2 ≤ Γ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hd 2
  have hE : 0 ≤ lyap p w := lyap_nonneg p w
  have hr : 2 ≤ s⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hs]
    linarith
  have hinv : (s / 16)⁻¹ = 16 * s⁻¹ := by field_simp
  rw [hinv] at hyoung
  have henergy : energy xstar s t z = lyap p w := rfl
  rw [henergy]
  have hD := lyap_nonneg d (s⁻¹ • d)
  have hκn := mul_le_mul_of_nonneg_left hnn2 hκ0
  have hsq : s⁻¹ ^ 2 * Γ ^ 2 ≤ s⁻¹ ^ 3 * Γ ^ 2 := by
    have : s⁻¹ ^ 2 ≤ s⁻¹ ^ 3 := pow_le_pow_right₀ (by linarith) (by norm_num)
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  have hdr : lyap d (s⁻¹ • d) ≤ 6 * s⁻¹ ^ 2 * Γ ^ 2 :=
    hdrift.trans (mul_le_mul_of_nonneg_left hd2 (by positivity))
  have hγσ : 0 ≤ γ ^ 2 * σ ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hcon (by positivity : (0 : ℝ) ≤ 1 + s / 16),
    mul_le_mul_of_nonneg_left hdr (by positivity : (0 : ℝ) ≤ 1 + 16 * s⁻¹),
    mul_nonneg hs.le hE, mul_nonneg (mul_nonneg hs.le hs.le) hE]

omit [BorelSpace E] [SecondCountableTopology E] in
lemma exit_step (h : Hyp f g P xstar μ L σ Γ) {γ : ℝ} (hγ : 0 < γ) (hγL : γ * L ≤ 1 / 2)
    (β s : ℝ) (t : ℕ) (z : E × E) :
    Integrable (fun ω => ‖(step g γ β t z ω).1 - xstar t‖ ^ 2) P ∧
    (∫ ω, ‖(step g γ β t z ω).1 - xstar t‖ ^ 2 ∂P) ≤ 2 * energy xstar s t z + γ ^ 2 * σ ^ 2 := by
  have hL : 0 < L := h.pos.trans_le h.le
  set y := z.1 + z.2
  set a := (y - xstar t) - γ • gradient (f t) y
  set n := fun ω => γ • (g t y ω - gradient (f t) y)
  obtain ⟨hn, hn0, hnn, hnn2⟩ := noise_facts h γ t y
  have hn' : Integrable n P := hn
  have hn0' : ∫ ω, n ω ∂P = 0 := hn0
  have hnn' : Integrable (fun ω => ‖n ω‖ ^ 2) P := hnn
  have hnn2' : ∫ ω, ‖n ω‖ ^ 2 ∂P ≤ γ ^ 2 * σ ^ 2 := hnn2
  have hexp : (fun ω => ‖(step g γ β t z ω).1 - xstar t‖ ^ 2) =
      fun ω => (‖a‖ ^ 2 - 2 * ⟪a, n ω⟫) + ‖n ω‖ ^ 2 := by
    funext ω
    have : (step g γ β t z ω).1 - xstar t = a - n ω := by
      simp only [step, a, n, y]
      module
    rw [this, norm_sub_sq_real]
  have hi1 : Integrable (fun ω => ‖a‖ ^ 2 - 2 * ⟪a, n ω⟫) P :=
    (integrable_const _).sub ((hn'.const_inner a).const_mul 2)
  rw [hexp]
  refine ⟨hi1.add hnn', ?_⟩
  rw [integral_add hi1 hnn', integral_sub (integrable_const _) ((hn'.const_inner a).const_mul 2),
    integral_const_mul, integral_inner hn' a, hn0', inner_zero_right]
  simp only [integral_const, probReal_univ, one_smul, mul_zero, sub_zero]
  obtain ⟨_, h2⟩ := sector h.pos hL hγ hγL (h.grad t) (h.strong t) (h.lip t) (h.min t) y
  have ha : ‖a‖ ^ 2 ≤ ‖y - xstar t‖ ^ 2 := by
    simp only [a]
    rw [norm_sub_sq_real, real_inner_comm]
    nlinarith [sq_nonneg ‖γ • gradient (f t) y‖]
  have hp := norm_sq_le_lyap (y - xstar t) (s⁻¹ • (z.2 - vel xstar t))
  have he : energy xstar s t z = lyap (y - xstar t) (s⁻¹ • (z.2 - vel xstar t)) := rfl
  linarith

omit [CompleteSpace E] in
lemma measurable_step {g : ℕ → E → Ω → E} (hg : ∀ k, Measurable (Function.uncurry (g k)))
    (γ β : ℝ) (t : ℕ) : Measurable (fun q : (E × E) × Ω => step g γ β t q.1 q.2) := by
  have hy : Measurable (fun q : (E × E) × Ω => q.1.1 + q.1.2) := by fun_prop
  have hq : Measurable (fun q : (E × E) × Ω => g t (q.1.1 + q.1.2) q.2) :=
    (hg t).comp (hy.prodMk measurable_snd)
  exact ((hy.sub (hq.const_smul γ)).prodMk ((measurable_fst.snd).sub (hq.const_smul β)))

omit [CompleteSpace E] in
lemma measurable_run {g : ℕ → E → Ω → E} (hg : ∀ k, Measurable (Function.uncurry (g k)))
    (γ β : ℝ) (K : ℕ) :
    ∀ t, Measurable (fun q : (E × E) × (Fin K → Ω) => run g γ β t K q.1 q.2) := by
  induction K with
  | zero => intro t; exact measurable_fst
  | succ K ih =>
    intro t
    have hs : Measurable (fun q : (E × E) × (Fin (K + 1) → Ω) =>
        (step g γ β t q.1 (q.2 0), fun i : Fin K => q.2 i.succ)) :=
      ((measurable_step hg γ β t).comp (measurable_fst.prodMk
        ((measurable_pi_apply 0).comp measurable_snd))).prodMk (by fun_prop)
    exact (ih (t + 1)).comp hs

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma cons_bound {K : ℕ} {F : (Fin (K + 1) → Ω) → ℝ} (hF : Measurable F)
    (hnn : ∀ ξ, 0 ≤ F ξ) {B : Ω → ℝ} (hB : Integrable B P)
    (hsec : ∀ ω, Integrable (fun ξ : Fin K → Ω => F (Fin.cons ω ξ)) (Measure.pi fun _ => P) ∧
      (∫ ξ, F (Fin.cons ω ξ) ∂Measure.pi fun _ => P) ≤ B ω) :
    Integrable F (Measure.pi fun _ => P) ∧ (∫ ξ, F ξ ∂Measure.pi fun _ => P) ≤ ∫ ω, B ω ∂P := by
  let q := Measure.pi (fun _ : Fin K => P)
  let H := fun z : Ω × (Fin K → Ω) => F (Fin.cons z.1 z.2)
  have hcons := StochasticGradient.cons_measurePreserving P K
  have hH : Measurable H := hF.comp hcons.measurable
  have hint : Integrable (fun ω => ∫ ξ, ‖H (ω, ξ)‖ ∂q) P := by
    apply hB.mono_nonneg hH.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun ω => integral_nonneg (fun ξ => norm_nonneg _))
    · apply Filter.Eventually.of_forall
      intro ω
      simpa only [H, Real.norm_eq_abs, abs_of_nonneg (hnn _)] using (hsec ω).2
  have hHi : Integrable H (P.prod q) := (integrable_prod_iff hH.aestronglyMeasurable).mpr
    ⟨Filter.Eventually.of_forall (fun ω => (hsec ω).1), hint⟩
  have hFi : Integrable F (Measure.pi fun _ : Fin (K + 1) => P) :=
    (hcons.integrable_comp hF.aestronglyMeasurable).mp (by simpa only [Function.comp_def] using hHi)
  refine ⟨hFi, ?_⟩
  calc
    _ = ∫ z, H z ∂P.prod q := by
      rw [← hcons.map_eq, integral_map hcons.measurable.aemeasurable hF.aestronglyMeasurable]
    _ = ∫ ω, ∫ ξ, H (ω, ξ) ∂q ∂P := integral_prod H hHi
    _ ≤ ∫ ω, B ω ∂P := integral_mono hHi.integral_prod_left hB (fun ω => (hsec ω).2)

lemma error_bound (h : Hyp f g P xstar μ L σ Γ) {γ : ℝ} (hγ : 0 < γ) (hγL : γ * L ≤ 1 / 2)
    (K : ℕ) : ∀ t z,
    Integrable (fun ξ : Fin (K + 1) → Ω =>
      ‖(run g γ (γ * (γ * μ) / 4) t (K + 1) z ξ).1 - xstar (t + K)‖ ^ 2) (Measure.pi fun _ => P) ∧
    (∫ ξ, ‖(run g γ (γ * (γ * μ) / 4) t (K + 1) z ξ).1 - xstar (t + K)‖ ^ 2
      ∂Measure.pi fun _ => P) ≤
      2 * ((1 - γ * μ / 16) ^ K * energy xstar (γ * μ) t z +
        16 * (γ * μ)⁻¹ * (102 * Γ ^ 2 * (γ * μ)⁻¹ ^ 3 + γ ^ 2 * σ ^ 2) *
          (1 - (1 - γ * μ / 16) ^ K)) +
        γ ^ 2 * σ ^ 2 := by
  set s := γ * μ with hsdef
  set β := γ * s / 4
  set C := 102 * Γ ^ 2 * s⁻¹ ^ 3 + γ ^ 2 * σ ^ 2
  have hs : 0 < s := mul_pos hγ h.pos
  have hmeas : ∀ (K t : ℕ) (z : E × E), Measurable (fun ξ : Fin K → Ω =>
      ‖(run g γ β t K z ξ).1 - xstar (t + K - 1)‖ ^ 2) := fun K t z =>
    ((((measurable_run (fun k => (h.oracle k).measurable) γ β K t).comp
      (measurable_const.prodMk measurable_id)).fst.sub_const _).norm.pow_const 2)
  induction K with
  | zero =>
    intro t z
    have hF := hmeas 1 t z
    simp only [Nat.add_sub_cancel] at hF
    have hex := exit_step h hγ hγL β s t z
    have hc := cons_bound (P := P) (K := 0) hF (fun _ => sq_nonneg _) hex.1 (fun ω =>
      ⟨by simp only [run, Fin.cons_zero]; exact integrable_const _, by simp [run]⟩)
    simp only [pow_zero, one_mul, sub_self, mul_zero, add_zero]
    exact ⟨by simpa using hc.1, by simpa using hc.2.trans hex.2⟩
  | succ K ih =>
    intro t z
    have hF := hmeas (K + 2) t z
    simp only [show t + (K + 2) - 1 = t + (K + 1) by omega] at hF
    have hes : Integrable (fun ω => energy xstar s (t + 1) (step g γ β t z ω)) P ∧
        (∫ ω, energy xstar s (t + 1) (step g γ β t z ω) ∂P) ≤
          (1 - s / 16) * energy xstar s t z + C := by
      have he := energy_step h hγ hγL t z
      exact ⟨he.1, by simp only [C]; linarith [he.2]⟩
    set ρK := (1 - s / 16) ^ K
    set D := 16 * s⁻¹ * C * (1 - ρK)
    have hB : Integrable (fun ω => 2 * (ρK * energy xstar s (t + 1)
        (step g γ β t z ω) + D) + γ ^ 2 * σ ^ 2) P :=
      (((hes.1.const_mul _).add (integrable_const _)).const_mul 2).add (integrable_const _)
    have hc := cons_bound (P := P) (K := K + 1) hF (fun _ => sq_nonneg _) hB (fun ω => by
      have hi := ih (t + 1) (step g γ β t z ω)
      simp only [show t + 1 + K = t + (K + 1) by omega] at hi
      exact ⟨by simpa [run] using hi.1, by simpa [run] using hi.2⟩)
    refine ⟨hc.1, hc.2.trans ?_⟩
    have hfun : (fun ω => 2 * (ρK * energy xstar s (t + 1) (step g γ β t z ω) + D) +
        γ ^ 2 * σ ^ 2) = fun ω => (2 * ρK) * energy xstar s (t + 1) (step g γ β t z ω) +
          (2 * D + γ ^ 2 * σ ^ 2) := by
      funext ω
      ring
    rw [hfun, integral_add (hes.1.const_mul _) (integrable_const _), integral_const_mul]
    simp only [integral_const, probReal_univ, one_smul]
    have hs2 : s ≤ 1 / 2 := by
      have := mul_le_mul_of_nonneg_left h.le hγ.le
      nlinarith [(h.pos.trans_le h.le)]
    have hρ : 0 ≤ ρK := pow_nonneg (by linarith) K
    have hkey := mul_le_mul_of_nonneg_left hes.2 (by positivity : (0 : ℝ) ≤ 2 * ρK)
    have hid : 16 * s⁻¹ * C * (s / 16) = C := by field_simp
    have hpow : (1 - s / 16) ^ (K + 1) = ρK * (1 - s / 16) := pow_succ _ _
    rw [hpow]
    simp only [D]
    nlinarith [hid]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] in
lemma advance_vt (g : ℕ → E → Ω → E) (γ β : ℝ) (x0 : E) (ξ : ℕ → Ω) (K call count : ℕ)
    (z : E × E) :
    StochasticGradient.advance (fun k state => (velocityTrackingSgd γ β x0).update state
      (g k ((velocityTrackingSgd γ β x0).query state).2 (ξ k))) K call (count, z.1, z.2) =
      (count + K, (run g γ β call K z (fun i => ξ (call + i))).1,
        (run g γ β call K z (fun i => ξ (call + i))).2) := by
  induction K generalizing call count z with
  | zero => rfl
  | succ K ih =>
    simp only [StochasticGradient.advance]
    have h := ih (call + 1) (count + 1) (step g γ β call z (ξ call))
    simp only [velocityTrackingSgd, step] at h ⊢
    rw [h]
    simp only [run, step, Fin.val_zero, Nat.add_zero, Fin.val_succ]
    refine Prod.ext (by omega) (Prod.ext ?_ ?_) <;>
      simp only [show ∀ i : ℕ, call + 1 + i = call + (i + 1) from fun i => by omega]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma execute_vt (Q : ProbabilityMeasure Ω) (g : ℕ → E → Ω → E) (γ β : ℝ) (x0 : E) (N : ℕ)
    (ξ : ℕ → Ω) :
    execute { Seed := fun _ => Ω
              law := ⟨Measure.infinitePi (fun _ : ℕ => (Q : Measure Ω)), inferInstance⟩
              answer := fun k (_, x) seed => g k x seed } (velocityTrackingSgd γ β x0)
      (fun _ => N) () ξ = ((run g γ β 0 N (x0, 0) (fun i => ξ i)).1, N) := by
  erw [StochasticGradient.execute_advance]
  change (velocityTrackingSgd γ β x0).output (StochasticGradient.advance _ N 0 (0, (x0, 0).1,
    (x0, 0).2)) = _
  erw [advance_vt g γ β x0 ξ N 0 0 (x0, 0)]
  simp [velocityTrackingSgd]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma initial_energy {s R V : ℝ} (x0 : E) (hR : ‖x0 - xstar 0‖ ≤ R)
    (hV : ‖xstar 1 - xstar 0‖ ≤ V) (hs : 0 < s) :
    energy xstar s 0 (x0, 0) ≤ 5 / 2 * R ^ 2 + 15 / 2 * (s⁻¹ ^ 2 * V ^ 2) := by
  have h := lyap_le (x0 + 0 - xstar 0) (s⁻¹ • ((0 : E) - vel xstar 0))
  have hv : ‖s⁻¹ • ((0 : E) - vel xstar 0)‖ ^ 2 = s⁻¹ ^ 2 * ‖xstar 1 - xstar 0‖ ^ 2 := by
    rw [norm_smul, zero_sub, norm_neg, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs), mul_pow]
    simp [vel]
  have hR2 : ‖x0 - xstar 0‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hR 2
  have hV2 : ‖xstar 1 - xstar 0‖ ^ 2 ≤ V ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hV 2
  simp only [energy, add_zero] at h ⊢
  rw [hv] at h
  nlinarith [mul_le_mul_of_nonneg_left hV2 (sq_nonneg s⁻¹)]

lemma expected_error (h : Hyp f g P xstar μ L σ Γ) {γ R V : ℝ} (hγ : 0 < γ)
    (hγL : γ * L ≤ 1 / 2) (x0 : E) (hR : ‖x0 - xstar 0‖ ≤ R) (hV : ‖xstar 1 - xstar 0‖ ≤ V)
    (K : ℕ) :
    Integrable (fun ξ : ℕ → Ω =>
      ‖(run g γ (γ * (γ * μ) / 4) 0 (K + 1) (x0, 0) (fun i => ξ i)).1 - xstar K‖ ^ 2)
        (Measure.infinitePi fun _ => P) ∧
    (∫ ξ : ℕ → Ω, ‖(run g γ (γ * (γ * μ) / 4) 0 (K + 1) (x0, 0)
        (fun i : Fin (K + 1) => ξ i)).1 - xstar K‖ ^ 2 ∂Measure.infinitePi fun _ => P) ≤
      2 * ((1 - γ * μ / 16) ^ K * (5 / 2 * R ^ 2 + 15 / 2 * ((γ * μ)⁻¹ ^ 2 * V ^ 2)) +
        16 * (γ * μ)⁻¹ * (102 * Γ ^ 2 * (γ * μ)⁻¹ ^ 3 + γ ^ 2 * σ ^ 2)) + γ ^ 2 * σ ^ 2 := by
  have hs : 0 < γ * μ := mul_pos hγ h.pos
  have hs2 : γ * μ ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left h.le hγ.le
    linarith
  have hb := error_bound h hγ hγL K 0 (x0, 0)
  simp only [Nat.zero_add] at hb
  have hpre := StochasticGradient.prefix_measurePreserving P (K + 1)
  have hm : Measurable (fun ξ : Fin (K + 1) → Ω =>
      ‖(run g γ (γ * (γ * μ) / 4) 0 (K + 1) (x0, 0) ξ).1 - xstar K‖ ^ 2) :=
    ((((measurable_run (fun k => (h.oracle k).measurable) γ _ (K + 1) 0).comp
      (measurable_const.prodMk measurable_id)).fst.sub_const _).norm.pow_const 2)
  refine ⟨hpre.integrable_comp_of_integrable hb.1, ?_⟩
  rw [← integral_map hpre.measurable.aemeasurable hm.aestronglyMeasurable, hpre.map_eq]
  refine hb.2.trans ?_
  have hρ0 : 0 ≤ (1 - γ * μ / 16) ^ K := pow_nonneg (by linarith) K
  have hρ1 : (1 - γ * μ / 16) ^ K ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hE := initial_energy (xstar := xstar) x0 hR hV hs
  have hC : 0 ≤ 16 * (γ * μ)⁻¹ * (102 * Γ ^ 2 * (γ * μ)⁻¹ ^ 3 + γ ^ 2 * σ ^ 2) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hE hρ0, mul_nonneg hC hρ0]

end OracleTemplate.VelocityTracking
