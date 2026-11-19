import LongTails.Proofs.SignSgdRate
import LongTails.Proofs.BatchedExecution
import LongTails.Proofs.MixedNoiseSelectors
import LongTails.Setups.SeparableNoiseLinfSmooth

open MeasureTheory OracleTemplate Finset
open scoped BigOperators

namespace LongTails.Proofs.SignSgdConvergence

open LongTails.Proofs.SignSgdRate LongTails.Proofs.AbcSgdUpper LongTails.Algorithms.AbcSgd
open LongTails.Algorithms.MinibatchSignSgd
open OracleTemplate.StochasticGradient OracleTemplate.HeavyTailedMarkovGradient

section Execution

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]

noncomputable def signOracle (g : Sp d → Ω → Sp d) (B : ℕ) : Sp d → (Fin B → Ω) → Sp d :=
  fun x z => signVec (batchMean (fun b => g x (z b)))

def blocks (B : ℕ) (ξ : ℕ → Ω) : ℕ → Fin B → Ω := fun t i => ξ (t * B + i)

lemma execute_minibatch (g : Sp d → Ω → Sp d) (η : ℝ) (K B : ℕ) (hB : 0 < B) (x0 : Sp d)
    (law : ProbabilityMeasure (ℕ → Ω)) (τ : Fin (K + 1)) (ξ : ℕ → Ω) :
    execute { Seed := fun _ => Ω, law := law, answer := fun _ (_, x) ω => g x ω }
      (minibatchSignSgd η K B hB x0) (fun _ => (K + 1) * B) τ ξ =
      sgdIter (signOracle g B) η x0 (blocks B ξ) τ.val := by
  unfold minibatchSignSgd
  rw [execute_batched hB (sampledSgd η K x0) (fun s _ => s.2.2.1) (fun _ r => signVec (batchMean r))
    0 law g ξ (K + 1) τ]
  set step := fun (call : ℕ) (state : (sampledSgd η K x0).State) =>
    (sampledSgd η K x0).update state (signVec (batchMean (fun i => g state.2.2.1 (ξ (call * B + i)))))
  have hstate : ∀ t, advance step t 0 ((sampledSgd η K x0).initial τ) =
      (τ, t, sgdIter (signOracle g B) η x0 (blocks B ξ) t,
        if τ.val < t then sgdIter (signOracle g B) η x0 (blocks B ξ) τ.val else x0) := by
    intro t
    induction t with
    | zero => simp [advance, sampledSgd, sgdIter]
    | succ t ih =>
      rw [advance_add step t 1 0, ih]
      simp only [advance, zero_add, step, sampledSgd, Prod.mk.injEq, true_and]
      refine ⟨rfl, ?_⟩
      by_cases h1 : t = τ.val
      · subst h1; simp
      · by_cases h2 : τ.val < t
        · have h3 : τ.val < t + 1 := by omega
          simp [h1, h2, h3]
        · have h3 : ¬ τ.val < t + 1 := by omega
          simp [h1, h2, h3]
  change (sampledSgd η K x0).output (advance step (K + 1) 0 ((sampledSgd η K x0).initial τ)) = _
  rw [hstate]
  simp [sampledSgd, τ.isLt]

end Execution

section Rate

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
lemma phiLoss_eq_sum (φ : Sp d → ℝ) (G : Sp d → Ω → Sp d) (η : ℝ) (K : ℕ) (x0 : Sp d)
    (ζ : ℕ → Ω) :
    phiLoss φ G η K x0 (fun i : Fin K => ζ i) =
      ∑ t ∈ Finset.range K, φ (sgdIter G η x0 ζ t) := by
  induction K generalizing x0 ζ with
  | zero => rfl
  | succ K ih =>
    rw [Finset.sum_range_succ', phiLoss]
    have h := ih (x0 - η • G x0 (ζ 0)) (fun i => ζ (i + 1))
    have he : (fun i : Fin K => (fun i : Fin (K + 1) => ζ i) i.succ) =
        fun i : Fin K => (fun i => ζ (i + 1)) (i : ℕ) := by
      funext i; simp [Fin.val_succ]
    simp only [Fin.val_zero] at h ⊢
    rw [he, h]
    simp only [sgdIter_succ_shift]
    rw [show sgdIter G η x0 ζ 0 = x0 from rfl]
    ring

lemma grad_coord_continuous {f : Sp d → ℝ} {L : ℝ}
    (hsm : ∀ x y r, (∀ i, |x i - y i| ≤ r) → ∑ i, |gradient f x i - gradient f y i| ≤ L * r)
    (i : Fin d) : Continuous (fun x => gradient f x i) := by
  apply LipschitzWith.continuous (K := ⟨max L 0, le_max_right _ _⟩)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, dist_eq_norm]
  have hc : ∀ j, |x j - y j| ≤ ‖x - y‖ := by
    intro j
    have := PiLp.norm_apply_le (x - y) j
    simpa [Real.norm_eq_abs] using this
  calc |gradient f x i - gradient f y i| ≤ ∑ j, |gradient f x j - gradient f y j| :=
        Finset.single_le_sum (f := fun j => |gradient f x j - gradient f y j|)
          (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    _ ≤ L * ‖x - y‖ := hsm x y _ hc
    _ ≤ max L 0 * ‖x - y‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)

end Rate

section Main

open LongTails.Setups.SeparableNoiseLinfSmooth

noncomputable def steps (q : Params) : ℕ := ⌈8 * q.L * q.Δ / q.ε ^ 2⌉₊

noncomputable def batch (q : Params) : ℕ := ⌈16 * q.S ^ 2 / q.ε ^ 2⌉₊ + 1

noncomputable def stepSize (q : Params) : ℝ := q.ε / (2 * q.L)

lemma batch_pos (q : Params) : 0 < batch q := Nat.succ_pos _

noncomputable def algorithm (q : Params) : Algorithm (Sp q.d) (Sp q.d) (Sp q.d) :=
  minibatchSignSgd (stepSize q) (steps q) (batch q) (batch_pos q) q.x0

lemma tuning (q : Params) (hv : spec.valid q) :
    q.Δ / (stepSize q * ((steps q : ℝ) + 1)) + 2 * q.S / Real.sqrt (batch q) +
      q.L * stepSize q / 2 ≤ q.ε := by
  obtain ⟨hL, hS, hΔ, hε⟩ := hv
  have hK : 8 * q.L * q.Δ / q.ε ^ 2 ≤ (steps q : ℝ) := Nat.le_ceil _
  have hB : 16 * q.S ^ 2 / q.ε ^ 2 ≤ (batch q : ℝ) := by
    unfold batch; push_cast; linarith [Nat.le_ceil (16 * q.S ^ 2 / q.ε ^ 2)]
  have hBpos : (0 : ℝ) < batch q := by exact_mod_cast batch_pos q
  have h1 : q.Δ / (stepSize q * ((steps q : ℝ) + 1)) ≤ q.ε / 4 := by
    unfold stepSize
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hK
    field_simp
    nlinarith
  have h2 : 2 * q.S / Real.sqrt (batch q) ≤ q.ε / 2 := by
    have hspos : 0 < Real.sqrt (batch q) := Real.sqrt_pos.mpr hBpos
    rw [div_le_iff₀ (by positivity)] at hB
    have h4 : 4 * q.S ≤ q.ε * Real.sqrt (batch q) := by
      rw [show q.ε * Real.sqrt (batch q) = Real.sqrt (batch q * q.ε ^ 2) by
        rw [Real.sqrt_mul hBpos.le, Real.sqrt_sq hε.le]; ring]
      rw [show 4 * q.S = Real.sqrt ((4 * q.S) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
      exact Real.sqrt_le_sqrt (by nlinarith)
    rw [div_le_iff₀ hspos]
    linarith
  have h3 : q.L * stepSize q / 2 = q.ε / 4 := by unfold stepSize; field_simp; ring
  linarith

theorem sign_convergence :
    Convergence spec (fun q _ => (⌈8 * q.L * q.Δ / q.ε ^ 2⌉₊ + 1) * (⌈16 * q.S ^ 2 / q.ε ^ 2⌉₊ + 1)) := by
  refine ⟨fun q => algorithm q, ?_, fun _ _ => trivial⟩
  intro q hv f O hadm
  obtain ⟨g, p, P, fstar, hiid, rfl, hgrad, hsm, hlow, _, hΔ, hmeas, hint, hmean, hvarint,
    hvar⟩ := hadm
  have hM : SignModel f g (p : Measure q.Ω) q.L q.S fstar :=
    ⟨hgrad, hsm, hlow, hmeas, hint, hmean, hvarint, hvar⟩
  have hv' := hv
  obtain ⟨hL, hS, hΔ0, hε⟩ := hv
  set η := stepSize q with hηdef
  set K := steps q
  set B := batch q
  have hη : 0 < η := by unfold η stepSize; positivity
  have hout : ∀ z : (algorithm q).Seed × ((k : ℕ) → q.Ω),
      execute { Seed := fun _ => q.Ω, law := P, answer := fun _ (_, x) ω => g x ω }
        (algorithm q) (fun _ => (K + 1) * B) z.1 z.2 =
          sgdIter (signOracle g B) η q.x0 (blocks B z.2) (Fin.val z.1) := by
    intro z
    exact execute_minibatch g η K B (batch_pos q) q.x0 P z.1 z.2
  let φ : Sp q.d → ℝ := fun x => ∑ i, |gradient f x i|
  have hφc : Continuous φ :=
    continuous_finsetSum _ fun i _ => (grad_coord_continuous hsm i).abs
  have hφ0 : ∀ x, 0 ≤ φ x := fun x => Finset.sum_nonneg fun i _ => abs_nonneg _
  have hG : Measurable (Function.uncurry (signOracle g B)) :=
    measurable_signVec.comp (measurable_batchMean_comp hmeas B)
  have hstep : ∀ x, Integrable (fun z => f (x - η • signOracle g B x z) - fstar)
      (Measure.pi fun _ : Fin B => (p : Measure q.Ω)) ∧
      ∫ z, f (x - η • signOracle g B x z) - fstar ∂(Measure.pi fun _ : Fin B => (p : Measure q.Ω)) ≤
        (f x - fstar) - η * φ x + η * (2 * q.S / Real.sqrt B + q.L * η / 2) :=
    fun x => sign_step_expect hM hη.le B (batch_pos q) x
  have hbound := phiLoss_bound hη hφc.measurable hφ0 hlow hG hstep (K + 1) q.x0
  have hblk := block_law hiid (K + 1) B
  let unifM : Measure (Fin (K + 1)) := (PMF.uniformOfFintype (Fin (K + 1))).toMeasure
  let Q : Measure (Fin (K + 1) × (ℕ → q.Ω)) := unifM.prod (P : Measure (ℕ → q.Ω))
  have hblkm : ∀ t, Measurable (fun ξ : ℕ → q.Ω => blocks B ξ t) := by
    intro t; unfold blocks; fun_prop
  have hiter : ∀ t, Measurable (fun ξ : ℕ → q.Ω => sgdIter (signOracle g B) η q.x0 (blocks B ξ) t) := by
    intro t
    induction t with
    | zero => exact measurable_const
    | succ t ih =>
      exact ih.sub ((hG.comp (ih.prodMk (hblkm t))).const_smul η)
  let Y : Fin (K + 1) × (ℕ → q.Ω) → ℝ :=
    fun z => φ (sgdIter (signOracle g B) η q.x0 (blocks B z.2) z.1.val)
  have hYm : Measurable Y := by
    apply measurable_from_prod_countable_right
    intro τ
    exact hφc.measurable.comp (hiter τ.val)
  let Gs : (ℕ → q.Ω) → ℝ := fun ξ =>
    phiLoss φ (signOracle g B) η (K + 1) q.x0 (fun t : Fin (K + 1) => blocks B ξ t)
  have hGm : Measurable (phiLoss φ (signOracle g B) η (K + 1) q.x0) :=
    (measurable_phiLoss hφc.measurable hG η (K + 1)).of_uncurry_left
  have hGs : Integrable Gs (P : Measure _) :=
    (hblk.integrable_comp hGm.aestronglyMeasurable).mpr hbound.1
  have hGsint : ∫ ξ, Gs ξ ∂(P : Measure _) =
      ∫ z, phiLoss φ (signOracle g B) η (K + 1) q.x0 z
        ∂Measure.pi (fun _ : Fin (K + 1) => Measure.pi fun _ : Fin B => (p : Measure q.Ω)) := by
    rw [← hblk.map_eq, integral_map hblk.measurable.aemeasurable hGm.aestronglyMeasurable]
    rfl
  have hYle : ∀ z, Y z ≤ Gs z.2 := by
    intro z
    dsimp only [Y, Gs]
    rw [phiLoss_eq_sum]
    exact Finset.single_le_sum (f := fun t => φ (sgdIter (signOracle g B) η q.x0 (blocks B z.2) t))
      (fun t _ => hφ0 _) (Finset.mem_range.mpr z.1.isLt)
  have hsnd : MeasurePreserving Prod.snd Q (P : Measure _) := by
    refine ⟨measurable_snd, ?_⟩
    dsimp only [Q]
    rw [Measure.map_snd_prod]
    simp [unifM]
  have hGsQ : Integrable (fun z : Fin (K + 1) × (ℕ → q.Ω) => Gs z.2) Q :=
    (hsnd.integrable_comp hGs.aestronglyMeasurable).mpr hGs
  have hYi : Integrable Y Q :=
    hGsQ.mono_nonneg hYm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => hφ0 _)) (Filter.Eventually.of_forall hYle)
  have hsec : ∀ τ : Fin (K + 1), Integrable (fun ξ => Y (τ, ξ)) (P : Measure _) := by
    intro τ
    exact hGs.mono_nonneg (hφc.measurable.comp (hiter τ.val)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun _ => hφ0 _))
      (Filter.Eventually.of_forall (fun ξ => hYle (τ, ξ)))
  have hEY : ∫ z, Y z ∂Q = ((K : ℝ) + 1)⁻¹ * ∫ ξ, Gs ξ ∂(P : Measure _) := by
    rw [integral_prod _ hYi, OracleTemplate.MixedNoise.integral_uniform_finite, Fintype.card_fin]
    push_cast
    congr 1
    rw [← integral_finsetSum _ (fun τ _ => hsec τ)]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro ξ
    dsimp only [Y, Gs]
    rw [phiLoss_eq_sum,
      Fin.sum_univ_eq_sum_range (fun t => φ (sgdIter (signOracle g B) η q.x0 (blocks B ξ) t))]
  have hfx : f q.x0 - fstar ≤ q.Δ := hΔ
  have hEbound : ∫ z, Y z ∂Q ≤ q.ε := by
    rw [hEY, hGsint]
    have hb := hbound.2
    have hMpos : (0 : ℝ) < (K : ℝ) + 1 := by positivity
    have hc0 : 0 ≤ 2 * q.S / Real.sqrt B + q.L * η / 2 := by positivity
    have e : (f q.x0 - fstar) / η + ((K + 1 : ℕ) : ℝ) * (η * (2 * q.S / Real.sqrt B + q.L * η / 2)) / η =
        (f q.x0 - fstar) / η + ((K : ℝ) + 1) * (2 * q.S / Real.sqrt B + q.L * η / 2) := by
      push_cast; field_simp
    rw [e] at hb
    have ht := tuning q hv'
    calc ((K : ℝ) + 1)⁻¹ * ∫ z, phiLoss φ (signOracle g B) η (K + 1) q.x0 z
          ∂Measure.pi (fun _ : Fin (K + 1) => Measure.pi fun _ : Fin B => (p : Measure q.Ω))
        ≤ ((K : ℝ) + 1)⁻¹ * ((f q.x0 - fstar) / η +
            ((K : ℝ) + 1) * (2 * q.S / Real.sqrt B + q.L * η / 2)) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = (f q.x0 - fstar) / (η * ((K : ℝ) + 1)) + (2 * q.S / Real.sqrt B + q.L * η / 2) := by
          field_simp
      _ ≤ q.Δ / (η * ((K : ℝ) + 1)) + (2 * q.S / Real.sqrt B + q.L * η / 2) := by
          gcongr
      _ ≤ q.ε := by linarith
  have hmeasout : Measurable (fun z : Fin (K + 1) × (ℕ → q.Ω) =>
      sgdIter (signOracle g B) η q.x0 (blocks B z.2) z.1.val) := by
    apply measurable_from_prod_countable_right
    intro τ
    exact hiter τ.val
  have hbud : (fun _ : Fin 1 => (⌈8 * q.L * q.Δ / q.ε ^ 2⌉₊ + 1) * (⌈16 * q.S ^ 2 / q.ε ^ 2⌉₊ + 1)) =
      fun _ => (K + 1) * B := rfl
  change spec.successful q f
      (fun seed : (algorithm q).Seed × ((k : ℕ) → q.Ω) =>
        execute { Seed := fun _ => q.Ω, law := P, answer := fun _ (_, x) ω => g x ω }
          (algorithm q) (fun _ => (K + 1) * B) seed.1 seed.2)
      ⟨((algorithm q).law : Measure _).prod (P : Measure (ℕ → q.Ω)), inferInstance⟩
  simp only [hout]
  exact ⟨hmeasout, hYi, hEbound⟩

end Main

end LongTails.Proofs.SignSgdConvergence
