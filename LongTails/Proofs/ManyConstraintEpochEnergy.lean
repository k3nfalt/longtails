import LongTails.Proofs.ManyConstraintEpochs

open MeasureTheory Set Metric
open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.ManyConstraintEpochEnergy

open LongTails.Proofs.ManyConstraintGeometry LongTails.Proofs.ManyConstraintPenalty
  LongTails.Proofs.ManyConstraintFinite LongTails.Proofs.ManyConstraintNoise
  LongTails.Proofs.ManyConstraintBall LongTails.Proofs.ManyConstraintCoupling
  LongTails.Proofs.ManyConstraintRun LongTails.Proofs.ManyConstraintStream
  LongTails.Proofs.ManyConstraintRegularity LongTails.Proofs.ManyConstraintInner
  LongTails.Proofs.ManyConstraintStochastic LongTails.Proofs.ManyConstraintStep
  LongTails.Proofs.ManyConstraintExpected LongTails.Proofs.ManyConstraintLower
  LongTails.Proofs.ManyConstraintEpochs LongTails.Proofs.ManyConstraintEnergy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {Ξ : Type*} [MeasurableSpace Ξ]
variable {m : ℕ} [NeZero m]
variable {law : Measure Ξ} {loss : Ξ → E → ℝ} {grad : Ξ → E → E} {L σ : ℝ} {xs : E}
  {K : Fin m → Set E} {P : Fin m → E → E}

structure Hyp (law : Measure Ξ) (loss : Ξ → E → ℝ) (grad : Ξ → E → E) (L σ : ℝ) (xs : E)
    (K : Fin m → Set E) (P : Fin m → E → E) (κ R : ℝ) (k : Knobs E) : Prop where
  reg : Regular law loss grad L σ xs
  L_pos : 0 < L
  σ_nonneg : 0 ≤ σ
  proj : ∀ j z, IsProj (K j) z (P j z)
  convex : ∀ j, Convex ℝ (K j)
  feasible : xs ∈ ⋂ j, K j
  minimal : IsMinOn (objective law loss) (⋂ j, K j) xs
  regular : ∀ x, Metric.infDist x (⋂ j, K j) ^ 2 ≤
    κ * ((1 / (m : ℝ)) * ∑ j, Metric.infDist x (K j) ^ 2)
  κ_pos : 0 < κ
  radius : ‖k.x0 - xs‖ ≤ R
  ball : xs ∈ closedBall k.x0 k.ρ
  Lt : k.Lt = L + k.β
  β_pos : 0 < k.β
  μ_nonneg : 0 ≤ k.μ
  ρ_nonneg : 0 ≤ k.ρ
  α_pos : 0 < k.α
  τ_pos : 0 < k.τ
  τ_half : k.τ ≤ 1 / 2
  tune : 3 * k.α * (L + k.β) * k.τ ≤ 1
  b_pos : 0 < k.b
  absorb : L ≤ k.τ * ((L + k.β) * k.b)
  θ_eq : k.θ = 1 + k.α * k.μ
  M_pos : 0 < k.M
  coef : (1 / 2 - k.τ) * k.θ + 1 / 2 * k.θ ^ k.M ≤ 1

noncomputable def c0 (σ κ R : ℝ) (k : Knobs E) : ℝ := κ * σ ^ 2 / (2 * k.β) + k.μ / 2 * R ^ 2

noncomputable def Dgap (law : Measure Ξ) (loss : Ξ → E → ℝ) (P : Fin m → E → E) (σ κ R : ℝ)
    (k : Knobs E) (xs x : E) : ℝ :=
  Phi law loss k.β P k.μ k.x0 x - Phi law loss k.β P k.μ k.x0 xs + c0 σ κ R k

noncomputable def Pot (law : Measure Ξ) (loss : Ξ → E → ℝ) (P : Fin m → E → E) (σ κ R : ℝ)
    (k : Knobs E) (xs : E) (st : St E) : ℝ :=
  1 / 2 * wsum k.θ k.M * Dgap law loss P σ κ R k xs st.s +
    (1 / 2 - k.τ) * Dgap law loss P σ κ R k xs st.y + k.τ / (2 * k.α) * ‖st.z - xs‖ ^ 2

noncomputable def err (L σ κ R : ℝ) (k : Knobs E) : ℝ :=
  σ ^ 2 / (2 * (L + k.β) * k.b) + k.τ * c0 σ κ R k

variable {κ R : ℝ} {k : Knobs E}

omit [NeZero m] in
lemma Dgap_nonneg (H : Hyp law loss grad L σ xs K P κ R k) (x : E) :
    0 ≤ Dgap law loss P σ κ R k xs x := by
  have := Phi_lower H.reg H.L_pos H.σ_nonneg H.proj H.convex H.feasible H.minimal H.κ_pos
    H.β_pos H.μ_nonneg H.radius x (H.regular x)
  unfold Dgap c0; linarith

noncomputable def Dbound (law : Measure Ξ) (loss : Ξ → E → ℝ) (grad : Ξ → E → E)
    (P : Fin m → E → E) (L σ κ R : ℝ) (k : Knobs E) (xs : E) : ℝ :=
  2 * (|objective law loss xs| + ‖meanGrad law grad xs‖ * (2 * k.ρ) + L / 2 * (2 * k.ρ) ^ 2 +
    (hpen k.β P xs + ‖hgrad k.β P xs‖ * (2 * k.ρ) + k.β / 2 * (2 * k.ρ) ^ 2) +
    k.μ / 2 * k.ρ ^ 2) + c0 σ κ R k

lemma Dgap_abs_le (H : Hyp law loss grad L σ xs K P κ R k) {x : E}
    (hx : x ∈ closedBall k.x0 k.ρ) :
    |Dgap law loss P σ κ R k xs x| ≤ Dbound law loss grad P L σ κ R k xs := by
  have h1 := Phi_abs_le H.reg H.L_pos H.proj H.β_pos.le H.μ_nonneg H.ball hx
  have h2 := Phi_abs_le H.reg H.L_pos H.proj H.β_pos.le H.μ_nonneg H.ball H.ball
  have h0 := Dgap_nonneg H x
  rw [abs_of_nonneg h0]
  unfold Dgap Dbound
  have := (abs_le.mp h1).2
  have := (abs_le.mp h2).1
  linarith

lemma concrete_step (H : Hyp law loss grad L σ xs K P κ R k) (s : E)
    (hs : s ∈ closedBall k.x0 k.ρ) (yz : E × E) (hy : yz.1 ∈ closedBall k.x0 k.ρ) :
    (𝔼 j, ∫ ω, (Dgap law loss P σ κ R k xs (step grad P k s (hgrad k.β P s) yz j ω).1 +
      k.τ / (2 * k.α) * k.θ * ‖(step grad P k s (hgrad k.β P s) yz j ω).2 - xs‖ ^ 2)
      ∂(Measure.pi fun _ => law)) ≤
      (1 / 2 - k.τ) * Dgap law loss P σ κ R k xs yz.1 + k.τ / (2 * k.α) * ‖yz.2 - xs‖ ^ 2 +
        1 / 2 * Dgap law loss P σ κ R k xs s + err L σ κ R k := by
  have := H.reg.prob
  obtain ⟨hint, hle⟩ := expected_step (z := yz.2) H.reg H.proj H.L_pos H.β_pos H.μ_nonneg
    H.ρ_nonneg H.α_pos H.τ_pos H.τ_half H.tune H.b_pos H.absorb hs hy H.ball
  have hY : ∀ j ω, (step grad P k s (hgrad k.β P s) yz j ω).1 =
      stepY grad k.β P L k.μ k.ρ k.τ k.x0 s yz.1 yz.2 (b := k.b) j ω := by
    intro j ω; simp only [step, stepY, hest, H.Lt]
  have hZ : ∀ j ω, (step grad P k s (hgrad k.β P s) yz j ω).2 =
      stepZ grad k.β P k.μ k.ρ k.τ k.α k.x0 s yz.1 yz.2 (b := k.b) j ω := by
    intro j ω; simp only [step, stepZ, hest]
  simp_rw [hY, hZ]
  set Φ := Phi law loss k.β P k.μ k.x0
  have hpt : ∀ j ω, Dgap law loss P σ κ R k xs (stepY grad k.β P L k.μ k.ρ k.τ k.x0 s yz.1 yz.2
      (b := k.b) j ω) + k.τ / (2 * k.α) * k.θ *
      ‖stepZ grad k.β P k.μ k.ρ k.τ k.α k.x0 s yz.1 yz.2 (b := k.b) j ω - xs‖ ^ 2 =
      (Φ (stepY grad k.β P L k.μ k.ρ k.τ k.x0 s yz.1 yz.2 (b := k.b) j ω) +
        k.τ / (2 * k.α) * (1 + k.α * k.μ) *
          ‖stepZ grad k.β P k.μ k.ρ k.τ k.α k.x0 s yz.1 yz.2 (b := k.b) j ω - xs‖ ^ 2) +
      (c0 σ κ R k - Φ xs) := by
    intro j ω; simp only [Dgap, H.θ_eq, Φ]; ring
  simp_rw [hpt]
  have hj : ∀ j, ∫ ω, ((Φ (stepY grad k.β P L k.μ k.ρ k.τ k.x0 s yz.1 yz.2 (b := k.b) j ω) +
        k.τ / (2 * k.α) * (1 + k.α * k.μ) *
          ‖stepZ grad k.β P k.μ k.ρ k.τ k.α k.x0 s yz.1 yz.2 (b := k.b) j ω - xs‖ ^ 2) +
      (c0 σ κ R k - Φ xs)) ∂(Measure.pi fun _ => law) =
      (∫ ω, (Φ (stepY grad k.β P L k.μ k.ρ k.τ k.x0 s yz.1 yz.2 (b := k.b) j ω) +
        k.τ / (2 * k.α) * (1 + k.α * k.μ) *
          ‖stepZ grad k.β P k.μ k.ρ k.τ k.α k.x0 s yz.1 yz.2 (b := k.b) j ω - xs‖ ^ 2)
        ∂(Measure.pi fun _ => law)) + (c0 σ κ R k - Φ xs) := by
    intro j
    rw [integral_add (hint j) (integrable_const _), integral_const]
    simp
  simp_rw [hj]
  rw [Finset.expect_add_distrib, Fintype.expect_const]
  simp only [Dgap, err, Φ] at hle ⊢
  nlinarith [hle]

omit [BorelSpace E] [SecondCountableTopology E] [NeZero m] in
lemma zbound (H : Hyp law loss grad L σ xs K P κ R k) {x : E} (hx : x ∈ closedBall k.x0 k.ρ) :
    ‖x - xs‖ ^ 2 ≤ (2 * k.ρ) ^ 2 := by
  have hb := H.ball
  rw [mem_closedBall, dist_eq_norm] at hx hb
  have : ‖x - xs‖ ≤ 2 * k.ρ := by
    calc ‖x - xs‖ = ‖(x - k.x0) - (xs - k.x0)‖ := by congr 1; abel
      _ ≤ ‖x - k.x0‖ + ‖xs - k.x0‖ := norm_sub_le _ _
      _ ≤ 2 * k.ρ := by linarith
  exact pow_le_pow_left₀ (norm_nonneg _) this 2

omit [NeZero m] in
lemma Dgap_measurable (H : Hyp law loss grad L σ xs K P κ R k) :
    Measurable (Dgap law loss P σ κ R k xs) := by
  unfold Dgap
  exact ((Phi_measurable H.reg H.L_pos H.proj k.β k.μ k.x0).sub measurable_const).add
    measurable_const

omit [NeZero m] in
lemma Dgap_convex (H : Hyp law loss grad L σ xs K P κ R k) :
    ConvexOn ℝ (closedBall k.x0 k.ρ) (Dgap law loss P σ κ R k xs) := by
  have hc := (Phi_convex H.reg H.L_pos H.proj H.β_pos.le k.μ H.μ_nonneg k.x0).subset
    (subset_univ _) (convex_closedBall k.x0 k.ρ)
  have he : Dgap law loss P σ κ R k xs = fun x => Phi law loss k.β P k.μ k.x0 x +
      (c0 σ κ R k - Phi law loss k.β P k.μ k.x0 xs) := by
    funext x; unfold Dgap; ring
  rw [he]
  exact hc.add (convexOn_const _ (convex_closedBall _ _))

variable [IsProbabilityMeasure law]

lemma epoch_energy_concrete (H : Hyp law loss grad L σ xs K P κ R k) (st : St E)
    (hs : st.s ∈ closedBall k.x0 k.ρ) (hy : st.y ∈ closedBall k.x0 k.ρ)
    (hz : st.z ∈ closedBall k.x0 k.ρ) :
    k.θ ^ k.M * (𝔼 js : Fin k.M → Fin m, ∫ ξ,
      Pot law loss P σ κ R k xs (epoch grad P k st js ξ) ∂(Measure.infinitePi fun _ : ℕ => law)) ≤
      Pot law loss P σ κ R k xs st + wsum k.θ k.M * err L σ κ R k := by
  set T := step grad P k st.s (hgrad k.β P st.s)
  set D := Dgap law loss P σ κ R k xs
  have hθ : 0 < k.θ := by rw [H.θ_eq]; have := mul_nonneg H.α_pos.le H.μ_nonneg; linarith
  have hTm : ∀ j, Measurable (fun p : (E × E) × (Fin k.b → Ξ) => T p.1 j p.2) := fun j =>
    ManyConstraintEnergy.step_measurable H.reg.measurable H.proj k st.s _ j
  have hTS : ∀ yz j ω, (T yz j ω).1 ∈ closedBall k.x0 k.ρ ∧ (T yz j ω).2 ∈ closedBall k.x0 k.ρ :=
    fun yz j ω => step_mem grad P k H.ρ_nonneg _ _ yz j ω
  have hzm : Measurable (fun x : E => ‖x - xs‖ ^ 2) :=
    (measurable_id.sub measurable_const).norm.pow_const 2
  set Q : (Fin k.M → Fin m) → (ℕ → Ξ) → ℝ := fun js ξ =>
    1 / 2 * wsum k.θ k.M * D ((wsum k.θ k.M)⁻¹ • sumG T k.θ k.M (st.y, st.z) js ξ) +
      (1 / 2 - k.τ) * D (runG T k.M (st.y, st.z) js ξ).1 +
      k.τ / (2 * k.α) * ‖(runG T k.M (st.y, st.z) js ξ).2 - xs‖ ^ 2 with hQ
  have hrw : ∀ js ξ, Pot law loss P σ κ R k xs (epoch grad P k st js ξ) =
      Q js (fun t => ξ (m + t)) := by
    intro js ξ
    simp only [Pot, epoch, innerRun_eq, hQ, D, T]
    rfl
  simp_rw [hrw]
  have hQm : ∀ js, Measurable (Q js) := by
    intro js
    have hcm : Measurable (fun ξ : ℕ → Ξ => ((st.y, st.z), ξ)) :=
      measurable_const.prodMk measurable_id
    have h1 := (sumG_measurable hTm k.θ k.M js).comp hcm
    have h2 := (runG_measurable hTm k.M js).comp hcm
    have hDm := Dgap_measurable H
    exact (((hDm.comp (h1.const_smul _)).const_mul _).add ((hDm.comp h2.fst).const_mul _)).add
      ((hzm.comp h2.snd).const_mul _)
  have hQb : ∀ js ξ, |Q js ξ| ≤ 1 / 2 * wsum k.θ k.M * Dbound law loss grad P L σ κ R k xs +
      (1 / 2 - k.τ) * Dbound law loss grad P L σ κ R k xs + k.τ / (2 * k.α) * (2 * k.ρ) ^ 2 := by
    intro js ξ
    obtain ⟨hmem, -⟩ := jensen_inner (convex_closedBall k.x0 k.ρ) hTS hθ (Dgap_convex H)
      k.M (st.y, st.z) js ξ H.M_pos
    have hr := runG_mem hTS k.M (st.y, st.z) js ξ hy hz
    have hw := wsum_nonneg hθ.le k.M
    have hc : 0 ≤ 1 / 2 - k.τ := by linarith [H.τ_half]
    have hd : 0 ≤ k.τ / (2 * k.α) := div_nonneg H.τ_pos.le (by linarith [H.α_pos])
    have e1 := Dgap_nonneg H ((wsum k.θ k.M)⁻¹ • sumG T k.θ k.M (st.y, st.z) js ξ)
    have e2 := Dgap_nonneg H (runG T k.M (st.y, st.z) js ξ).1
    have b1 := (abs_le.mp (Dgap_abs_le H hmem)).2
    have b2 := (abs_le.mp (Dgap_abs_le H hr.1)).2
    have b3 := zbound H hr.2
    rw [abs_of_nonneg (by simp only [hQ, D]; positivity)]
    simp only [hQ, D]
    gcongr
  have hskip : ∀ js, ∫ ξ, Q js (fun t => ξ (m + t)) ∂(Measure.infinitePi fun _ : ℕ => law) =
      ∫ ξ, Q js ξ ∂(Measure.infinitePi fun _ : ℕ => law) := fun js =>
    integral_skip law m (Q js) (hQm js) (hQb js)
  simp_rw [hskip]
  have hc : 0 ≤ 1 / 2 - k.τ := by linarith [H.τ_half]
  have hd : 0 ≤ k.τ / (2 * k.α) := div_nonneg H.τ_pos.le (by linarith [H.α_pos])
  have he := epoch_energy law (convex_closedBall k.x0 k.ρ) hTm hTS hθ (1 / 2 - k.τ)
    (k.τ / (2 * k.α)) (err L σ κ R k) (D st.s) hc hd xs (Dgap_measurable H) (Dgap_convex H)
    (fun x _ => Dgap_nonneg H x) (fun x hx => Dgap_abs_le H hx) (fun x hx => zbound H hx)
    H.M_pos H.coef (fun yz h1 _ => concrete_step H st.s hs yz h1) (st.y, st.z) hy hz
  simp only [Pot]
  change k.θ ^ k.M * (𝔼 js : Fin k.M → Fin m, ∫ ξ, Q js ξ ∂(Measure.infinitePi fun _ : ℕ => law)) ≤ _
  simp only [hQ]
  linarith [he]

end LongTails.Proofs.ManyConstraintEpochEnergy
