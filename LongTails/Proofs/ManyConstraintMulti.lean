import LongTails.Proofs.ManyConstraintEpochEnergy

open MeasureTheory Set Metric
open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.ManyConstraintMulti

open LongTails.Proofs.ManyConstraintGeometry LongTails.Proofs.ManyConstraintFinite
  LongTails.Proofs.ManyConstraintRun LongTails.Proofs.ManyConstraintStream
  LongTails.Proofs.ManyConstraintInner LongTails.Proofs.ManyConstraintStochastic
  LongTails.Proofs.ManyConstraintEpochs LongTails.Proofs.ManyConstraintEpochEnergy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {Ξ : Type*} [MeasurableSpace Ξ]
variable {m : ℕ} [NeZero m]
variable {law : Measure Ξ} {loss : Ξ → E → ℝ} {grad : Ξ → E → E} {L σ : ℝ} {xs : E}
  {K : Fin m → Set E} {P : Fin m → E → E} {κ R : ℝ} {k : Knobs E}

noncomputable def ext (n : ℕ) (ξ0 : ℕ → Ξ) (w : Fin n → Ξ) : ℕ → Ξ :=
  fun i => if h : i < n then w ⟨i, h⟩ else ξ0 i

omit [MeasurableSpace Ξ] in
lemma ext_prefix (n : ℕ) (ξ0 ξ : ℕ → Ξ) (i : ℕ) (hi : i < n) :
    ext n ξ0 (fun j : Fin n => ξ j) i = ξ i := by
  simp [ext, hi]

lemma ext_measurable (n : ℕ) (ξ0 : ℕ → Ξ) : Measurable (ext n ξ0) := by
  refine Measurable.of_eval fun i => ?_
  unfold ext
  by_cases hi : i < n
  · simp only [hi, dite_true]; exact measurable_pi_apply _
  · simp only [hi, dite_false]; exact measurable_const

def tri (st : St E) : E × (E × E) := (st.s, (st.y, st.z))
def untri (p : E × (E × E)) : St E := ⟨p.1, p.2.1, p.2.2⟩

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] in
lemma untri_tri (st : St E) : untri (tri st) = st := rfl

omit [NeZero m] in
lemma run_measurable_joint (H : Hyp law loss grad L σ xs K P κ R k) :
    ∀ (S : ℕ) (jss : Fin S → Fin k.M → Fin m),
      Measurable (fun p : (E × (E × E)) × (ℕ → Ξ) => tri (run grad P k S (untri p.1) jss p.2)) := by
  intro S
  induction S with
  | zero => intro jss; exact measurable_fst
  | succ S ih =>
    intro jss
    have he := epoch_measurable_joint H.reg.measurable H.proj k (jss 0)
    have hshift : Measurable (fun p : (E × (E × E)) × (ℕ → Ξ) =>
        (fun t => p.2 (epochLen m k + t))) :=
      Measurable.of_eval fun t => (measurable_pi_apply (epochLen m k + t)).comp measurable_snd
    have := (ih (fun i => jss i.succ)).comp (he.prodMk hshift)
    exact this

omit [BorelSpace E] [SecondCountableTopology E] [NeZero m] in
lemma run_mem (H : Hyp law loss grad L σ xs K P κ R k) :
    ∀ (S : ℕ) (st : St E) (jss : Fin S → Fin k.M → Fin m) (ξ : ℕ → Ξ),
      st.s ∈ closedBall k.x0 k.ρ → st.y ∈ closedBall k.x0 k.ρ → st.z ∈ closedBall k.x0 k.ρ →
      (run grad P k S st jss ξ).s ∈ closedBall k.x0 k.ρ ∧
      (run grad P k S st jss ξ).y ∈ closedBall k.x0 k.ρ ∧
      (run grad P k S st jss ξ).z ∈ closedBall k.x0 k.ρ := by
  have hθ : 0 < k.θ := by rw [H.θ_eq]; have := mul_nonneg H.α_pos.le H.μ_nonneg; linarith
  intro S
  induction S with
  | zero => intro st jss ξ h1 h2 h3; exact ⟨h1, h2, h3⟩
  | succ S ih =>
    intro st jss ξ _ _ _
    obtain ⟨a, b, c⟩ := epoch_mem grad P k H.ρ_nonneg hθ H.M_pos st (jss 0) ξ
    exact ih _ _ _ a b c

omit [NeZero m] in
lemma Pot_measurable (H : Hyp law loss grad L σ xs K P κ R k) :
    Measurable (fun p : E × (E × E) => Pot law loss P σ κ R k xs (untri p)) := by
  have hD := Dgap_measurable H
  have hzm : Measurable (fun x : E => ‖x - xs‖ ^ 2) :=
    (measurable_id.sub measurable_const).norm.pow_const 2
  unfold Pot untri
  exact (((hD.comp measurable_fst).const_mul _).add
    ((hD.comp (measurable_fst.comp measurable_snd)).const_mul _)).add
    ((hzm.comp (measurable_snd.comp measurable_snd)).const_mul _)

noncomputable def Pbound (law : Measure Ξ) (loss : Ξ → E → ℝ) (grad : Ξ → E → E)
    (P : Fin m → E → E) (L σ κ R : ℝ) (k : Knobs E) (xs : E) : ℝ :=
  1 / 2 * wsum k.θ k.M * Dbound law loss grad P L σ κ R k xs +
    (1 / 2 - k.τ) * Dbound law loss grad P L σ κ R k xs + k.τ / (2 * k.α) * (2 * k.ρ) ^ 2

lemma Pot_bounds (H : Hyp law loss grad L σ xs K P κ R k) {st : St E}
    (hs : st.s ∈ closedBall k.x0 k.ρ) (hy : st.y ∈ closedBall k.x0 k.ρ)
    (hz : st.z ∈ closedBall k.x0 k.ρ) :
    0 ≤ Pot law loss P σ κ R k xs st ∧ Pot law loss P σ κ R k xs st ≤
      Pbound law loss grad P L σ κ R k xs := by
  have hθ : 0 < k.θ := by rw [H.θ_eq]; have := mul_nonneg H.α_pos.le H.μ_nonneg; linarith
  have hw := wsum_nonneg hθ.le k.M
  have hc : 0 ≤ 1 / 2 - k.τ := by linarith [H.τ_half]
  have hd : 0 ≤ k.τ / (2 * k.α) := div_nonneg H.τ_pos.le (by linarith [H.α_pos])
  have e1 := Dgap_nonneg H st.s
  have e2 := Dgap_nonneg H st.y
  have b1 := (abs_le.mp (Dgap_abs_le H hs)).2
  have b2 := (abs_le.mp (Dgap_abs_le H hy)).2
  have b3 := zbound H hz
  unfold Pot Pbound
  constructor
  · positivity
  · gcongr

variable [IsProbabilityMeasure law]

lemma multi_epoch (H : Hyp law loss grad L σ xs K P κ R k) :
    ∀ (S : ℕ) (st : St E), st.s ∈ closedBall k.x0 k.ρ → st.y ∈ closedBall k.x0 k.ρ →
      st.z ∈ closedBall k.x0 k.ρ →
      (k.θ ^ k.M) ^ S * (𝔼 jss : Fin S → Fin k.M → Fin m, ∫ ξ,
        Pot law loss P σ κ R k xs (run grad P k S st jss ξ)
          ∂(Measure.infinitePi fun _ : ℕ => law)) ≤
        Pot law loss P σ κ R k xs st +
          (∑ i ∈ Finset.range S, (k.θ ^ k.M) ^ i) * (wsum k.θ k.M * err L σ κ R k) := by
  have hθ : 0 < k.θ := by rw [H.θ_eq]; have := mul_nonneg H.α_pos.le H.μ_nonneg; linarith
  have hq : 0 < k.θ ^ k.M := pow_pos hθ _
  have := nonempty_of_isProbabilityMeasure law
  obtain ⟨ξ0⟩ : Nonempty (ℕ → Ξ) := inferInstance
  set inf := Measure.infinitePi fun _ : ℕ => law
  set n := epochLen m k
  set B := Pbound law loss grad P L σ κ R k xs
  intro S
  induction S with
  | zero =>
    intro st _ _ _
    simp [run, integral_const]
  | succ S ih =>
    intro st hs hy hz
    set Pot' := Pot law loss P σ κ R k xs
    set Cst := (∑ i ∈ Finset.range S, (k.θ ^ k.M) ^ i) * (wsum k.θ k.M * err L σ κ R k)
    set eP : (Fin k.M → Fin m) → (Fin n → Ξ) → St E := fun js w =>
      epoch grad P k st js (ext n ξ0 w)
    have heP : ∀ js ξ, epoch grad P k st js ξ = eP js (fun i : Fin n => ξ i) := by
      intro js ξ
      exact epoch_congr k st js ξ _ fun i hi => (ext_prefix n ξ0 ξ i hi).symm
    have hePm : ∀ js, Measurable (fun w => tri (eP js w)) := by
      intro js
      have he := epoch_measurable_joint H.reg.measurable H.proj k js
      have : Measurable (fun w : Fin n → Ξ => ((st.s, (st.y, st.z)), ext n ξ0 w)) :=
        measurable_const.prodMk (ext_measurable n ξ0)
      exact he.comp this
    have hePmem : ∀ js w, (eP js w).s ∈ closedBall k.x0 k.ρ ∧ (eP js w).y ∈ closedBall k.x0 k.ρ ∧
        (eP js w).z ∈ closedBall k.x0 k.ρ := fun js w =>
      epoch_mem grad P k H.ρ_nonneg hθ H.M_pos st js _
    set G : (Fin k.M → Fin m) → (Fin S → Fin k.M → Fin m) → (Fin n → Ξ) × (ℕ → Ξ) → ℝ :=
      fun js jss p => Pot' (run grad P k S (eP js p.1) jss p.2) with hG
    have hGm : ∀ js jss, Measurable (G js jss) := by
      intro js jss
      have hr := run_measurable_joint H S jss
      have hp := Pot_measurable H
      have : Measurable (fun p : (Fin n → Ξ) × (ℕ → Ξ) => (tri (eP js p.1), p.2)) :=
        ((hePm js).comp measurable_fst).prodMk measurable_snd
      have h3 := hp.comp (hr.comp this)
      simpa only [hG, Pot', Function.comp_def, untri_tri] using h3
    have hGb : ∀ js jss p, |G js jss p| ≤ B := by
      intro js jss p
      obtain ⟨a, b, c⟩ := hePmem js p.1
      obtain ⟨a', b', c'⟩ := run_mem H S _ jss p.2 a b c
      obtain ⟨h0, h1⟩ := Pot_bounds H a' b' c'
      rw [abs_of_nonneg h0]; exact h1
    have hrun : ∀ js jss ξ, Pot' (run grad P k (S + 1) st (Fin.cons js jss) ξ) =
        G js jss ((fun i : Fin n => ξ i), (fun t => ξ (n + t))) := by
      intro js jss ξ
      simp only [run, Fin.cons_zero, Fin.cons_succ, hG, heP]
      rfl
    rw [OracleTemplate.NonconvexFiniteSum.expect_function_succ]
    simp_rw [hrun]
    have hsplit : ∀ js jss, ∫ ξ, G js jss ((fun i : Fin n => ξ i), (fun t => ξ (n + t))) ∂inf =
        ∫ w, ∫ t, G js jss (w, t) ∂inf ∂(Measure.pi fun _ : Fin n => law) := fun js jss =>
      integral_prefix law n (G js jss) (hGm js jss) (hGb js jss)
    simp_rw [hsplit]
    have hinner : ∀ js jss, Integrable (fun w => ∫ t, G js jss (w, t) ∂inf)
        (Measure.pi fun _ : Fin n => law) := by
      intro js jss
      refine Integrable.of_bound ((hGm js jss).stronglyMeasurable.integral_prod_right'
        |>.aestronglyMeasurable) B (Filter.Eventually.of_forall fun w => ?_)
      refine (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun t => ?_)).trans
        (by rw [probReal_univ, mul_one])
      rw [Real.norm_eq_abs]; exact hGb js jss (w, t)
    have hj : ∀ js, (k.θ ^ k.M) ^ S * (𝔼 jss : Fin S → Fin k.M → Fin m,
        ∫ w, ∫ t, G js jss (w, t) ∂inf ∂(Measure.pi fun _ : Fin n => law)) ≤
        (∫ ξ, Pot' (epoch grad P k st js ξ) ∂inf) + Cst := by
      intro js
      rw [expect_integral_comm _ (hinner js), ← integral_const_mul]
      have hpt : ∀ w, (k.θ ^ k.M) ^ S * (𝔼 jss : Fin S → Fin k.M → Fin m,
          ∫ t, G js jss (w, t) ∂inf) ≤ Pot' (eP js w) + Cst := by
        intro w
        obtain ⟨a, b, c⟩ := hePmem js w
        exact ih (eP js w) a b c
      have hL : Integrable (fun w => (k.θ ^ k.M) ^ S * (𝔼 jss : Fin S → Fin k.M → Fin m,
          ∫ t, G js jss (w, t) ∂inf)) (Measure.pi fun _ : Fin n => law) := by
        refine Integrable.const_mul ?_ _
        simp only [Finset.expect_eq_sum_div_card]
        exact (integrable_finsetSum _ fun jss _ => hinner js jss).div_const _
      have hPm : Measurable (fun w => Pot' (eP js w)) := by
        have := (Pot_measurable H).comp (hePm js)
        simpa only [Pot', Function.comp_def, untri_tri] using this
      have hP1 : Integrable (fun w => Pot' (eP js w)) (Measure.pi fun _ : Fin n => law) :=
        Integrable.of_bound hPm.aestronglyMeasurable B (Filter.Eventually.of_forall fun w => by
          obtain ⟨a, b, c⟩ := hePmem js w
          obtain ⟨h0, h1⟩ := Pot_bounds H a b c
          rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1)
      have hR : Integrable (fun w => Pot' (eP js w) + Cst) (Measure.pi fun _ : Fin n => law) :=
        hP1.add (integrable_const _)
      have hm := integral_mono hL hR hpt
      rw [integral_add hP1 (integrable_const _), integral_const] at hm
      have hprefix : ∫ w, Pot' (eP js w) ∂(Measure.pi fun _ : Fin n => law) =
          ∫ ξ, Pot' (epoch grad P k st js ξ) ∂inf := by
        rw [integral_prefix_only law n _ hPm]
        congr 1; funext ξ; rw [heP]
      simp only [probReal_univ, one_smul] at hm
      rw [hprefix] at hm
      exact hm
    have hE := Finset.expect_le_expect (s := Finset.univ) fun js _ => hj js
    rw [Finset.expect_add_distrib, Fintype.expect_const] at hE
    have hep := epoch_energy_concrete H st hs hy hz
    have h1 : (k.θ ^ k.M) ^ S * (𝔼 js : Fin k.M → Fin m, 𝔼 jss : Fin S → Fin k.M → Fin m,
        ∫ w, ∫ t, G js jss (w, t) ∂inf ∂(Measure.pi fun _ : Fin n => law)) ≤
        (𝔼 js : Fin k.M → Fin m, ∫ ξ, Pot' (epoch grad P k st js ξ) ∂inf) + Cst := by
      rw [Finset.mul_expect]; exact hE
    have hsum : (∑ i ∈ Finset.range (S + 1), (k.θ ^ k.M) ^ i) =
        k.θ ^ k.M * (∑ i ∈ Finset.range S, (k.θ ^ k.M) ^ i) + 1 := by
      rw [Finset.sum_range_succ', Finset.mul_sum]; simp [pow_succ, mul_comm]
    rw [hsum, pow_succ]
    have hW : Cst = (∑ i ∈ Finset.range S, (k.θ ^ k.M) ^ i) * (wsum k.θ k.M * err L σ κ R k) := rfl
    calc (k.θ ^ k.M) ^ S * k.θ ^ k.M * (𝔼 js : Fin k.M → Fin m, 𝔼 jss : Fin S → Fin k.M → Fin m,
          ∫ w, ∫ t, G js jss (w, t) ∂inf ∂(Measure.pi fun _ : Fin n => law)) =
        k.θ ^ k.M * ((k.θ ^ k.M) ^ S * (𝔼 js : Fin k.M → Fin m, 𝔼 jss : Fin S → Fin k.M → Fin m,
          ∫ w, ∫ t, G js jss (w, t) ∂inf ∂(Measure.pi fun _ : Fin n => law))) := by ring
      _ ≤ k.θ ^ k.M * ((𝔼 js : Fin k.M → Fin m, ∫ ξ, Pot' (epoch grad P k st js ξ) ∂inf) + Cst) :=
          mul_le_mul_of_nonneg_left h1 hq.le
      _ = k.θ ^ k.M * (𝔼 js : Fin k.M → Fin m, ∫ ξ, Pot' (epoch grad P k st js ξ) ∂inf) +
          k.θ ^ k.M * Cst := by ring
      _ ≤ Pot' st + wsum k.θ k.M * err L σ κ R k + k.θ ^ k.M * Cst := by linarith [hep]
      _ = _ := by rw [hW]; ring

end LongTails.Proofs.ManyConstraintMulti
