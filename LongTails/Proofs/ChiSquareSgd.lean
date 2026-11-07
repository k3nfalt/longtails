import LongTails.Proofs.ChiSquareStep
import LongTails.Proofs.LinearDecaySgdExpectation

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace OracleTemplate.ChiSquareDro

open OracleTemplate.SampledConvex (extend measurable_extend extend_agree integral_prefix)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ξ : Type*}

noncomputable def run (k : Cfg) (proj : E → E) (loss : E → Ξ → ℝ) (sub : E → Ξ → E)
    (z0 : E × ℝ × ℝ) (ξ : ℕ → Ξ) : ℕ → E × ℝ × ℝ
  | 0 => z0
  | t + 1 => stepState k proj loss sub (run k proj loss sub z0 ξ t) (ξ t)

structure Hyp (k : Cfg) (D : Set E) (proj : E → E) (loss : E → Ξ → ℝ) (sub : E → Ξ → E)
    (B G : ℝ) : Prop where
  c_pos : 0 < k.c
  gx_pos : 0 < k.gx
  ge_pos : 0 < k.ge
  gs_pos : 0 < k.gs
  slo_pos : 0 < k.slo
  s_le : k.slo ≤ k.shi
  e_le : k.elo ≤ k.ehi
  elo_le : k.elo ≤ B
  proj_mem : ∀ y, proj y ∈ D
  proj_vi : ∀ y, ∀ u ∈ D, ⟪y - proj y, u - proj y⟫ ≤ 0
  subgrad : ∀ ω, ∀ x ∈ D, ∀ y ∈ D, loss x ω + ⟪sub x ω, y - x⟫ ≤ loss y ω
  loss_nonneg : ∀ ω, ∀ x ∈ D, 0 ≤ loss x ω
  loss_le : ∀ ω, ∀ x ∈ D, loss x ω ≤ B
  sub_le : ∀ ω, ∀ x ∈ D, ‖sub x ω‖ ≤ G

section Basic

variable {k : Cfg} {D : Set E} {proj : E → E} {loss : E → Ξ → ℝ} {sub : E → Ξ → E} {B G : ℝ}

lemma run_succ (z0 : E × ℝ × ℝ) (ξ : ℕ → Ξ) (t : ℕ) :
    run k proj loss sub z0 ξ (t + 1) = stepState k proj loss sub (run k proj loss sub z0 ξ t) (ξ t) :=
  rfl

lemma run_congr (z0 : E × ℝ × ℝ) {ξ ξ' : ℕ → Ξ} :
    ∀ t, (∀ i, i < t → ξ i = ξ' i) → run k proj loss sub z0 ξ t = run k proj loss sub z0 ξ' t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro hξ
    rw [run_succ, run_succ, ih (fun i hi => hξ i (Nat.lt_succ_of_lt hi)), hξ t (Nat.lt_succ_self t)]

lemma run_mem (h : Hyp k D proj loss sub B G) {z0 : E × ℝ × ℝ} (he0 : z0.2.1 ∈ Icc k.elo k.ehi)
    (hs0 : z0.2.2 ∈ Icc k.slo k.shi) (ξ : ℕ → Ξ) :
    ∀ t, (run k proj loss sub z0 ξ t).2.1 ∈ Icc k.elo k.ehi ∧
      (run k proj loss sub z0 ξ t).2.2 ∈ Icc k.slo k.shi := by
  intro t
  cases t with
  | zero => exact ⟨he0, hs0⟩
  | succ t => exact ⟨clampTo_mem h.e_le _, clampTo_mem h.s_le _⟩

lemma tailAt_le (h : Hyp k D proj loss sub B G) {x : E} (hx : x ∈ D) {η : ℝ} (hη : k.elo ≤ η)
    (ω : Ξ) : tailAt loss x η ω ≤ B - k.elo := by
  unfold tailAt tail
  have := h.loss_le ω x hx
  have hB : 0 ≤ B - k.elo := by linarith [h.elo_le]
  exact max_le (by linarith) hB

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma tailAt_nonneg (x : E) (η : ℝ) (ω : Ξ) : 0 ≤ tailAt loss x η ω := tail_nonneg _ _ _

lemma gradX_norm_le (h : Hyp k D proj loss sub B G) {x : E} (hx : x ∈ D) {η s : ℝ}
    (hη : k.elo ≤ η) (hs : k.slo ≤ s) (ω : Ξ) :
    ‖gradX k loss sub x η s ω‖ ≤ k.c * (B - k.elo) * G / k.slo := by
  unfold gradX
  have hs0 : 0 < s := lt_of_lt_of_le h.slo_pos hs
  have ht := tailAt_le h hx hη ω
  have ht0 := tailAt_nonneg (loss := loss) x η ω
  have hg := h.sub_le ω x hx
  have hG : 0 ≤ G := le_trans (norm_nonneg _) hg
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (mul_nonneg h.c_pos.le ht0) hs0.le)]
  calc k.c * tailAt loss x η ω / s * ‖sub x ω‖ ≤ k.c * (B - k.elo) / k.slo * G := by
        apply mul_le_mul _ hg (norm_nonneg _) (by
          have : 0 ≤ B - k.elo := le_trans ht0 ht
          exact div_nonneg (mul_nonneg h.c_pos.le this) h.slo_pos.le)
        exact div_le_div₀ (mul_nonneg h.c_pos.le (le_trans ht0 ht))
          (mul_le_mul_of_nonneg_left ht h.c_pos.le) h.slo_pos hs
    _ = _ := by ring

lemma run_dist (h : Hyp k D proj loss sub B G) {z0 : E × ℝ × ℝ} (he0 : z0.2.1 ∈ Icc k.elo k.ehi)
    (hs0 : z0.2.2 ∈ Icc k.slo k.shi) (ξ : ℕ → Ξ) {xs : E} (hxs : xs ∈ D) :
    ∀ t, ‖proj (run k proj loss sub z0 ξ t).1 - xs‖ ≤
      ‖proj z0.1 - xs‖ + t * (k.gx * (k.c * (B - k.elo) * G / k.slo)) := by
  intro t
  induction t with
  | zero => simp [run]
  | succ t ih =>
    obtain ⟨he, hs⟩ := run_mem h he0 hs0 ξ t
    set z := run k proj loss sub z0 ξ t
    rw [run_succ]
    change ‖proj (proj z.1 - k.gx • gradX k loss sub (proj z.1) z.2.1 z.2.2 (ξ t)) - xs‖ ≤ _
    have h1 : ‖proj (proj z.1 - k.gx • gradX k loss sub (proj z.1) z.2.1 z.2.2 (ξ t)) - xs‖ ≤
        ‖proj z.1 - k.gx • gradX k loss sub (proj z.1) z.2.1 z.2.2 (ξ t) - xs‖ := by
      have := proj_dist h.proj_vi
        (proj z.1 - k.gx • gradX k loss sub (proj z.1) z.2.1 z.2.2 (ξ t)) hxs
      exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) this
    have h2 : ‖proj z.1 - k.gx • gradX k loss sub (proj z.1) z.2.1 z.2.2 (ξ t) - xs‖ ≤
        ‖proj z.1 - xs‖ + k.gx * ‖gradX k loss sub (proj z.1) z.2.1 z.2.2 (ξ t)‖ := by
      have e : proj z.1 - k.gx • gradX k loss sub (proj z.1) z.2.1 z.2.2 (ξ t) - xs =
          (proj z.1 - xs) - k.gx • gradX k loss sub (proj z.1) z.2.1 z.2.2 (ξ t) := by abel
      rw [e]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos h.gx_pos]
    have h3 := gradX_norm_le h (h.proj_mem z.1) he.1 hs.1 (ξ t)
    have h4 : k.gx * ‖gradX k loss sub (proj z.1) z.2.1 z.2.2 (ξ t)‖ ≤
        k.gx * (k.c * (B - k.elo) * G / k.slo) := mul_le_mul_of_nonneg_left h3 h.gx_pos.le
    push_cast
    linarith

end Basic

section Moments

variable [MeasurableSpace Ξ] (p : Measure Ξ) [IsProbabilityMeasure p]
variable {k : Cfg} {D : Set E} {proj : E → E} {loss : E → Ξ → ℝ} {sub : E → Ξ → E} {B G : ℝ}

noncomputable def PhiX (k : Cfg) (loss : E → Ξ → ℝ) (x : E) (η s : ℝ) : ℝ :=
  ∫ ω, phiAt k loss x η s ω ∂p

noncomputable def NoiseX (k : Cfg) (loss : E → Ξ → ℝ) (sub : E → Ξ → E) (x : E) (η s : ℝ) : ℝ :=
  ∫ ω, noiseAt k loss sub x η s ω ∂p

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma measurable_section [MeasurableSpace E] (hl : Measurable (Function.uncurry loss)) (x : E) :
    Measurable (loss x) :=
  hl.comp (measurable_const.prodMk measurable_id)

omit [MeasurableSpace Ξ] in
lemma loss_le_of (h : Hyp k D proj loss sub B G) {x : E} (hx : x ∈ D) : ∀ ω, loss x ω ≤ B :=
  fun ω => h.loss_le ω x hx

lemma PhiX_eq [MeasurableSpace E] (h : Hyp k D proj loss sub B G)
    (hl : Measurable (Function.uncurry loss)) {x : E} (hx : x ∈ D) (η s : ℝ) :
    PhiX p k loss x η s = η + k.c * sq p (loss x) η / (2 * s) + k.c * s / 2 := by
  have hm := measurable_section hl x
  have hi2 := integrable_tail_sq p hm (loss_le_of h hx) η
  unfold PhiX phiAt phi tailAt
  have e : (fun ω => η + k.c * tail (loss x) η ω ^ 2 / (2 * s) + k.c * s / 2) =
      fun ω => k.c / (2 * s) * tail (loss x) η ω ^ 2 + (η + k.c * s / 2) := by
    funext ω; ring
  rw [e, integral_add_const' p (hi2.const_mul _), integral_const_mul]
  unfold sq
  ring

lemma NoiseX_le [MeasurableSpace E] (h : Hyp k D proj loss sub B G)
    (hl : Measurable (Function.uncurry loss)) (hs' : Measurable (Function.uncurry sub))
    [BorelSpace E] {x : E} (hx : x ∈ D) {η s : ℝ} (hη : k.elo ≤ η) (hs : k.slo ≤ s) :
    NoiseX p k loss sub x η s ≤
      k.gx * (k.c ^ 2 * G ^ 2 * sq p (loss x) η / s ^ 2) +
      k.ge * (2 + 2 * k.c ^ 2 * sq p (loss x) η / s ^ 2) +
      k.gs * (k.c ^ 2 / 2 + k.c ^ 2 * (B - k.elo) ^ 2 * sq p (loss x) η / (2 * s ^ 4)) := by
  have hs0 : 0 < s := lt_of_lt_of_le h.slo_pos hs
  have hm := measurable_section hl x
  have hsm : Measurable (sub x) := hs'.comp (measurable_const.prodMk measurable_id)
  have hi2 := integrable_tail_sq p hm (loss_le_of h hx) η
  have htm : Measurable (fun ω => tailAt loss x η ω) := measurable_tail hm η
  have hpt : ∀ ω, noiseAt k loss sub x η s ω ≤
      k.gx * (k.c ^ 2 * G ^ 2 * tailAt loss x η ω ^ 2 / s ^ 2) +
      k.ge * (2 + 2 * k.c ^ 2 * tailAt loss x η ω ^ 2 / s ^ 2) +
      k.gs * (k.c ^ 2 / 2 + k.c ^ 2 * (B - k.elo) ^ 2 * tailAt loss x η ω ^ 2 / (2 * s ^ 4)) := by
    intro ω
    unfold noiseAt gradX gradE gradS
    have h1 := noise_x (c := k.c) (G := G) (u := tailAt loss x η ω) (s := s) (h.sub_le ω x hx)
    have h2 := noise_eta (c := k.c) (u := tailAt loss x η ω) (s := s)
    have h3 := noise_s (c := k.c) (u := tailAt loss x η ω) hs0 (tailAt_nonneg x η ω)
      (tailAt_le h hx hη ω)
    have := add_le_add (add_le_add (mul_le_mul_of_nonneg_left h1 h.gx_pos.le)
      (mul_le_mul_of_nonneg_left h2 h.ge_pos.le)) (mul_le_mul_of_nonneg_left h3 h.gs_pos.le)
    exact this
  set α := k.gx * k.c ^ 2 * G ^ 2 / s ^ 2 + k.ge * (2 * k.c ^ 2) / s ^ 2 +
    k.gs * (k.c ^ 2 * (B - k.elo) ^ 2) / (2 * s ^ 4)
  set β := k.ge * 2 + k.gs * (k.c ^ 2 / 2)
  have hrw : (fun ω =>
      k.gx * (k.c ^ 2 * G ^ 2 * tailAt loss x η ω ^ 2 / s ^ 2) +
      k.ge * (2 + 2 * k.c ^ 2 * tailAt loss x η ω ^ 2 / s ^ 2) +
      k.gs * (k.c ^ 2 / 2 + k.c ^ 2 * (B - k.elo) ^ 2 * tailAt loss x η ω ^ 2 / (2 * s ^ 4))) =
      fun ω => α * tail (loss x) η ω ^ 2 + β := by
    funext ω
    simp only [α, β, tailAt]
    field_simp
    ring
  have hri : Integrable (fun ω => α * tail (loss x) η ω ^ 2 + β) p :=
    (hi2.const_mul α).add (integrable_const β)
  have hnm : Measurable (fun ω => noiseAt k loss sub x η s ω) := by
    have e : (fun ω => noiseAt k loss sub x η s ω) = fun ω =>
        k.gx * (|k.c * tailAt loss x η ω / s| * ‖sub x ω‖) ^ 2 +
          k.ge * (1 - k.c * tailAt loss x η ω / s) ^ 2 +
          k.gs * (k.c / 2 - k.c * tailAt loss x η ω ^ 2 / (2 * s ^ 2)) ^ 2 := by
      funext ω; unfold noiseAt gradX gradE gradS; rw [norm_smul, Real.norm_eq_abs]
    rw [e]
    have ha : Measurable (fun ω => k.c * tailAt loss x η ω / s) := (measurable_const.mul htm).div_const s
    exact ((measurable_const.mul (((continuous_abs.measurable.comp ha).mul hsm.norm).pow_const 2)).add
      (measurable_const.mul ((measurable_const.sub ha).pow_const 2))).add
      (measurable_const.mul ((measurable_const.sub
        ((measurable_const.mul (htm.pow_const 2)).div_const _)).pow_const 2))
  have hn0 : ∀ ω, 0 ≤ noiseAt k loss sub x η s ω := by
    intro ω
    unfold noiseAt
    have := h.gx_pos; have := h.ge_pos; have := h.gs_pos
    positivity
  have hni : Integrable (fun ω => noiseAt k loss sub x η s ω) p := by
    refine hri.mono' hnm.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hn0 ω)]
    exact (hpt ω).trans_eq (congrFun hrw ω)
  have hmono := integral_mono hni hri (fun ω => (hpt ω).trans_eq (congrFun hrw ω))
  refine hmono.trans (le_of_eq ?_)
  rw [integral_add_const' p (hi2.const_mul α), integral_const_mul]
  unfold sq
  simp only [α, β]
  field_simp
  ring

end Moments

section Measurability

variable [MeasurableSpace Ξ] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {k : Cfg} {proj : E → E} {loss : E → Ξ → ℝ} {sub : E → Ξ → E}

lemma measurable_stepState (hp : Measurable proj) (hl : Measurable (Function.uncurry loss))
    (hs : Measurable (Function.uncurry sub)) :
    Measurable (fun q : (E × ℝ × ℝ) × Ξ => stepState k proj loss sub q.1 q.2) := by
  have hx : Measurable (fun q : (E × ℝ × ℝ) × Ξ => proj q.1.1) :=
    hp.comp (measurable_fst.comp measurable_fst)
  have hη : Measurable (fun q : (E × ℝ × ℝ) × Ξ => q.1.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_fst)
  have hsv : Measurable (fun q : (E × ℝ × ℝ) × Ξ => q.1.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_fst)
  have hL : Measurable (fun q : (E × ℝ × ℝ) × Ξ => loss (proj q.1.1) q.2) :=
    hl.comp (hx.prodMk measurable_snd)
  have hG : Measurable (fun q : (E × ℝ × ℝ) × Ξ => sub (proj q.1.1) q.2) :=
    hs.comp (hx.prodMk measurable_snd)
  have hT : Measurable (fun q : (E × ℝ × ℝ) × Ξ => max (loss (proj q.1.1) q.2 - q.1.2.1) 0) :=
    (hL.sub hη).max measurable_const
  unfold stepState gradX gradE gradS clampTo tailAt tail
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
  · exact hx.sub ((((measurable_const.mul hT).div hsv).smul hG).const_smul k.gx)
  · exact measurable_const.max (measurable_const.min
      (hη.sub (measurable_const.mul (measurable_const.sub ((measurable_const.mul hT).div hsv)))))
  · exact measurable_const.max (measurable_const.min (hsv.sub (measurable_const.mul
      (measurable_const.sub ((measurable_const.mul (hT.pow_const 2)).div
        (measurable_const.mul (hsv.pow_const 2)))))))

lemma measurable_run (hp : Measurable proj) (hl : Measurable (Function.uncurry loss))
    (hs : Measurable (Function.uncurry sub)) (z0 : E × ℝ × ℝ) :
    ∀ t, Measurable (fun ξ : ℕ → Ξ => run k proj loss sub z0 ξ t) := by
  intro t
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    simp only [run_succ]
    exact (measurable_stepState hp hl hs).comp (ih.prodMk (measurable_pi_apply t))

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [BorelSpace E] [SecondCountableTopology E] in
lemma measurable_phiAt (hp : Measurable proj) (hl : Measurable (Function.uncurry loss)) :
    Measurable (fun q : (E × ℝ × ℝ) × Ξ => phiAt k loss (proj q.1.1) q.1.2.1 q.1.2.2 q.2) := by
  have hx : Measurable (fun q : (E × ℝ × ℝ) × Ξ => proj q.1.1) :=
    hp.comp (measurable_fst.comp measurable_fst)
  have hη : Measurable (fun q : (E × ℝ × ℝ) × Ξ => q.1.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_fst)
  have hsv : Measurable (fun q : (E × ℝ × ℝ) × Ξ => q.1.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_fst)
  have hL : Measurable (fun q : (E × ℝ × ℝ) × Ξ => loss (proj q.1.1) q.2) :=
    hl.comp (hx.prodMk measurable_snd)
  have hT : Measurable (fun q : (E × ℝ × ℝ) × Ξ => max (loss (proj q.1.1) q.2 - q.1.2.1) 0) :=
    (hL.sub hη).max measurable_const
  unfold phiAt phi tailAt tail
  exact (hη.add ((measurable_const.mul (hT.pow_const 2)).div (measurable_const.mul hsv))).add
    ((measurable_const.mul hsv).div_const 2)

lemma measurable_noiseAt (hp : Measurable proj) (hl : Measurable (Function.uncurry loss))
    (hs : Measurable (Function.uncurry sub)) :
    Measurable (fun q : (E × ℝ × ℝ) × Ξ =>
      noiseAt k loss sub (proj q.1.1) q.1.2.1 q.1.2.2 q.2) := by
  have hx : Measurable (fun q : (E × ℝ × ℝ) × Ξ => proj q.1.1) :=
    hp.comp (measurable_fst.comp measurable_fst)
  have hη : Measurable (fun q : (E × ℝ × ℝ) × Ξ => q.1.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_fst)
  have hsv : Measurable (fun q : (E × ℝ × ℝ) × Ξ => q.1.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_fst)
  have hL : Measurable (fun q : (E × ℝ × ℝ) × Ξ => loss (proj q.1.1) q.2) :=
    hl.comp (hx.prodMk measurable_snd)
  have hG : Measurable (fun q : (E × ℝ × ℝ) × Ξ => sub (proj q.1.1) q.2) :=
    hs.comp (hx.prodMk measurable_snd)
  have hT : Measurable (fun q : (E × ℝ × ℝ) × Ξ => max (loss (proj q.1.1) q.2 - q.1.2.1) 0) :=
    (hL.sub hη).max measurable_const
  have hA : Measurable (fun q : (E × ℝ × ℝ) × Ξ =>
      k.c * max (loss (proj q.1.1) q.2 - q.1.2.1) 0 / q.1.2.2) := (measurable_const.mul hT).div hsv
  have hV : Measurable (fun q : (E × ℝ × ℝ) × Ξ =>
      ‖(k.c * max (loss (proj q.1.1) q.2 - q.1.2.1) 0 / q.1.2.2) • sub (proj q.1.1) q.2‖ ^ 2) :=
    (hA.smul hG).norm.pow_const 2
  have hW : Measurable (fun q : (E × ℝ × ℝ) × Ξ =>
      (1 - k.c * max (loss (proj q.1.1) q.2 - q.1.2.1) 0 / q.1.2.2) ^ 2) :=
    (measurable_const.sub hA).pow_const 2
  have hY : Measurable (fun q : (E × ℝ × ℝ) × Ξ =>
      (k.c / 2 - k.c * max (loss (proj q.1.1) q.2 - q.1.2.1) 0 ^ 2 / (2 * q.1.2.2 ^ 2)) ^ 2) :=
    (measurable_const.sub ((measurable_const.mul (hT.pow_const 2)).div
      (measurable_const.mul (hsv.pow_const 2)))).pow_const 2
  unfold noiseAt gradX gradE gradS tailAt tail
  exact ((measurable_const.mul hV).add (measurable_const.mul hW)).add (measurable_const.mul hY)

end Measurability

section SelfBound

variable [MeasurableSpace Ξ] (p : Measure Ξ) [IsProbabilityMeasure p]
variable {k : Cfg} {D : Set E} {proj : E → E} {loss : E → Ξ → ℝ} {sub : E → Ξ → E} {B G : ℝ}

noncomputable def noiseConst (k : Cfg) (B G : ℝ) : ℝ :=
  2 * k.gx * k.c ^ 2 * G ^ 2 + k.ge * (2 + 4 * k.c ^ 2) +
    k.gs * (k.c ^ 2 / 2 + k.c ^ 2 * (B - k.elo) ^ 2 / k.slo ^ 2)

noncomputable def noiseSlope (k : Cfg) (B G : ℝ) : ℝ :=
  4 * k.gx * k.c * G ^ 2 / k.slo + 8 * k.ge * k.c / k.slo +
    2 * k.gs * k.c * (B - k.elo) ^ 2 / k.slo ^ 3

lemma noise_self_bound [MeasurableSpace E] [BorelSpace E] (h : Hyp k D proj loss sub B G)
    (hl : Measurable (Function.uncurry loss)) (hs' : Measurable (Function.uncurry sub))
    {x : E} (hx : x ∈ D) {η s L : ℝ} (hη : k.elo ≤ η) (hs : k.slo ≤ s)
    (hF : L ≤ η + k.c * nrm p (loss x) η) :
    NoiseX p k loss sub x η s ≤ noiseConst k B G + noiseSlope k B G * (PhiX p k loss x η s - L) := by
  have hs0 : 0 < s := lt_of_lt_of_le h.slo_pos hs
  have hc := h.c_pos
  have hslo := h.slo_pos
  set Q := sq p (loss x) η
  have hQ : 0 ≤ Q := sq_nonneg' p (loss x) η
  have hPhi := PhiX_eq p h hl hx η s
  set X := PhiX p k loss x η s - L
  have hsb : Q ≤ 2 * s ^ 2 + 4 * s / k.c * X := by
    have := self_bound (c := k.c) (Q := Q) (s := s) (η := η) (L := L) hc hs0 hQ hF
    simp only [X, hPhi]
    exact this
  have hX : 0 ≤ X := by
    have h1 : k.c * Real.sqrt Q ≤ k.c * Q / (2 * s) + k.c * s / 2 := by
      have hr := Real.sq_sqrt hQ
      have : Real.sqrt Q ≤ Q / (2 * s) + s / 2 := by
        rw [div_add_div _ _ (by positivity) two_ne_zero, le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg (Real.sqrt Q - s), Real.sqrt_nonneg Q]
      have := mul_le_mul_of_nonneg_left this hc.le
      linarith [show k.c * (Q / (2 * s) + s / 2) = k.c * Q / (2 * s) + k.c * s / 2 by ring]
    have : L ≤ PhiX p k loss x η s := by
      rw [hPhi]; unfold nrm at hF; linarith
    simp only [X]; linarith
  have hq2 : Q / s ^ 2 ≤ 2 + 4 * X / (k.c * k.slo) := by
    rw [div_le_iff₀ (by positivity)]
    have : 4 * s / k.c * X ≤ 4 * X / (k.c * k.slo) * s ^ 2 := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff₀ hc (by positivity)]
      have h5 : s * k.slo ≤ s ^ 2 := by nlinarith
      have h6 := mul_le_mul_of_nonneg_left h5 (show 0 ≤ 4 * X * k.c by positivity)
      linarith
    nlinarith
  have hq4 : Q / s ^ 4 ≤ 2 / k.slo ^ 2 + 4 * X / (k.c * k.slo ^ 3) := by
    have hsq : k.slo ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hslo.le hs 2
    have hcube : k.slo ^ 3 ≤ s ^ 3 := pow_le_pow_left₀ hslo.le hs 3
    have e : Q / s ^ 4 ≤ 2 / s ^ 2 + 4 * X / (k.c * s ^ 3) := by
      rw [div_le_iff₀ (by positivity)]
      have : 4 * s / k.c * X = 4 * X / (k.c * s ^ 3) * s ^ 4 := by field_simp
      have : 2 * s ^ 2 = 2 / s ^ 2 * s ^ 4 := by field_simp
      nlinarith
    have e2 : 2 / s ^ 2 ≤ 2 / k.slo ^ 2 := div_le_div_of_nonneg_left (by norm_num) (by positivity) hsq
    have e3 : 4 * X / (k.c * s ^ 3) ≤ 4 * X / (k.c * k.slo ^ 3) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (mul_le_mul_of_nonneg_left hcube hc.le)
    linarith
  have hN := NoiseX_le p h hl hs' hx hη hs
  have hgx := h.gx_pos; have hge := h.ge_pos; have hgs := h.gs_pos
  have t1 : k.gx * (k.c ^ 2 * G ^ 2 * Q / s ^ 2) ≤
      2 * k.gx * k.c ^ 2 * G ^ 2 + 4 * k.gx * k.c * G ^ 2 / k.slo * X := by
    have : k.c ^ 2 * G ^ 2 * Q / s ^ 2 = k.c ^ 2 * G ^ 2 * (Q / s ^ 2) := by ring
    rw [this]
    have := mul_le_mul_of_nonneg_left hq2 (show 0 ≤ k.gx * (k.c ^ 2 * G ^ 2) by positivity)
    have e : k.gx * (k.c ^ 2 * G ^ 2) * (2 + 4 * X / (k.c * k.slo)) =
        2 * k.gx * k.c ^ 2 * G ^ 2 + 4 * k.gx * k.c * G ^ 2 / k.slo * X := by
      field_simp
    linarith
  have t2 : k.ge * (2 + 2 * k.c ^ 2 * Q / s ^ 2) ≤
      k.ge * (2 + 4 * k.c ^ 2) + 8 * k.ge * k.c / k.slo * X := by
    have : 2 * k.c ^ 2 * Q / s ^ 2 = 2 * k.c ^ 2 * (Q / s ^ 2) := by ring
    rw [this]
    have := mul_le_mul_of_nonneg_left hq2 (show 0 ≤ k.ge * (2 * k.c ^ 2) by positivity)
    have e : k.ge * (2 * k.c ^ 2) * (2 + 4 * X / (k.c * k.slo)) =
        k.ge * (4 * k.c ^ 2) + 8 * k.ge * k.c / k.slo * X := by
      field_simp; ring
    linarith
  have t3 : k.gs * (k.c ^ 2 / 2 + k.c ^ 2 * (B - k.elo) ^ 2 * Q / (2 * s ^ 4)) ≤
      k.gs * (k.c ^ 2 / 2 + k.c ^ 2 * (B - k.elo) ^ 2 / k.slo ^ 2) +
        2 * k.gs * k.c * (B - k.elo) ^ 2 / k.slo ^ 3 * X := by
    have : k.c ^ 2 * (B - k.elo) ^ 2 * Q / (2 * s ^ 4) =
        k.c ^ 2 * (B - k.elo) ^ 2 / 2 * (Q / s ^ 4) := by ring
    rw [this]
    have := mul_le_mul_of_nonneg_left hq4
      (show 0 ≤ k.gs * (k.c ^ 2 * (B - k.elo) ^ 2 / 2) by positivity)
    have e : k.gs * (k.c ^ 2 * (B - k.elo) ^ 2 / 2) * (2 / k.slo ^ 2 + 4 * X / (k.c * k.slo ^ 3)) =
        k.gs * (k.c ^ 2 * (B - k.elo) ^ 2 / k.slo ^ 2) +
          2 * k.gs * k.c * (B - k.elo) ^ 2 / k.slo ^ 3 * X := by
      field_simp; ring
    linarith
  unfold noiseConst noiseSlope
  linarith [hN, t1, t2, t3]

end SelfBound

section Expectation

variable [MeasurableSpace Ξ] (p : Measure Ξ) [IsProbabilityMeasure p]
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {k : Cfg} {D : Set E} {proj : E → E} {loss : E → Ξ → ℝ} {sub : E → Ξ → E} {B G : ℝ}

noncomputable def phiBound (k : Cfg) (B : ℝ) : ℝ :=
  (|k.elo| + |k.ehi|) + k.c * (B - k.elo) ^ 2 / (2 * k.slo) + k.c * k.shi / 2

noncomputable def noiseBound (k : Cfg) (B G : ℝ) : ℝ :=
  k.gx * (k.c * (B - k.elo) * G / k.slo) ^ 2 + k.ge * (1 + k.c * (B - k.elo) / k.slo) ^ 2 +
    k.gs * (k.c / 2 + k.c * (B - k.elo) ^ 2 / (2 * k.slo ^ 2)) ^ 2

omit [MeasurableSpace Ξ] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma phiAt_abs_le (h : Hyp k D proj loss sub B G) {x : E} (hx : x ∈ D) {η s : ℝ}
    (hη : η ∈ Icc k.elo k.ehi) (hs : s ∈ Icc k.slo k.shi) (ω : Ξ) :
    |phiAt k loss x η s ω| ≤ phiBound k B := by
  have hslo := h.slo_pos
  have hs0 : 0 < s := lt_of_lt_of_le h.slo_pos hs.1
  have ht := tailAt_le h hx hη.1 ω
  have ht0 := tailAt_nonneg (loss := loss) x η ω
  have hc := h.c_pos
  unfold phiAt phi phiBound
  have h1 : |η| ≤ |k.elo| + |k.ehi| := by
    rcases le_total 0 η with h0 | h0
    · rw [abs_of_nonneg h0]; linarith [le_abs_self k.ehi, abs_nonneg k.elo, hη.2]
    · rw [abs_of_nonpos h0]; linarith [neg_abs_le k.elo, abs_nonneg k.ehi, hη.1]
  have h2 : 0 ≤ k.c * tailAt loss x η ω ^ 2 / (2 * s) := by positivity
  have h3 : k.c * tailAt loss x η ω ^ 2 / (2 * s) ≤ k.c * (B - k.elo) ^ 2 / (2 * k.slo) := by
    apply div_le_div₀ (by positivity) _ (by positivity) (by linarith [hs.1])
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht0 ht 2) hc.le
  have h4 : 0 ≤ k.c * s / 2 := by positivity
  have h5 : k.c * s / 2 ≤ k.c * k.shi / 2 := by
    have := mul_le_mul_of_nonneg_left hs.2 hc.le; linarith
  rw [abs_le]
  constructor <;> nlinarith [abs_nonneg η, le_abs_self η, neg_abs_le η]

omit [MeasurableSpace Ξ] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma noiseAt_le (h : Hyp k D proj loss sub B G) {x : E} (hx : x ∈ D) {η s : ℝ}
    (hη : k.elo ≤ η) (hs : k.slo ≤ s) (ω : Ξ) :
    0 ≤ noiseAt k loss sub x η s ω ∧ noiseAt k loss sub x η s ω ≤ noiseBound k B G := by
  have hslo := h.slo_pos
  have hs0 : 0 < s := lt_of_lt_of_le h.slo_pos hs
  have ht := tailAt_le h hx hη ω
  have ht0 := tailAt_nonneg (loss := loss) x η ω
  have hc := h.c_pos
  have hgx := h.gx_pos; have hge := h.ge_pos; have hgs := h.gs_pos
  have hB0 : 0 ≤ B - k.elo := le_trans ht0 ht
  constructor
  · unfold noiseAt; positivity
  unfold noiseAt noiseBound
  have g1 := gradX_norm_le h hx hη hs ω
  have g2 : |gradE k loss x η s ω| ≤ 1 + k.c * (B - k.elo) / k.slo := by
    unfold gradE
    have a1 : 0 ≤ k.c * tailAt loss x η ω / s := by positivity
    have a2 : k.c * tailAt loss x η ω / s ≤ k.c * (B - k.elo) / k.slo :=
      div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left ht hc.le) h.slo_pos hs
    rw [abs_le]; constructor <;> linarith
  have g3 : |gradS k loss x η s ω| ≤ k.c / 2 + k.c * (B - k.elo) ^ 2 / (2 * k.slo ^ 2) := by
    unfold gradS
    have a1 : 0 ≤ k.c * tailAt loss x η ω ^ 2 / (2 * s ^ 2) := by positivity
    have a2 : k.c * tailAt loss x η ω ^ 2 / (2 * s ^ 2) ≤ k.c * (B - k.elo) ^ 2 / (2 * k.slo ^ 2) := by
      apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht0 ht 2) hc.le)
        (by positivity)
      have := pow_le_pow_left₀ h.slo_pos.le hs 2
      linarith
    rw [abs_le]; constructor <;> linarith [show 0 ≤ k.c / 2 by positivity]
  have q1 : ‖gradX k loss sub x η s ω‖ ^ 2 ≤ (k.c * (B - k.elo) * G / k.slo) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) g1 2
  have q2 : gradE k loss x η s ω ^ 2 ≤ (1 + k.c * (B - k.elo) / k.slo) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) g2 2
  have q3 : gradS k loss x η s ω ^ 2 ≤ (k.c / 2 + k.c * (B - k.elo) ^ 2 / (2 * k.slo ^ 2)) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) g3 2
  have := add_le_add (add_le_add (mul_le_mul_of_nonneg_left q1 hgx.le)
    (mul_le_mul_of_nonneg_left q2 hge.le)) (mul_le_mul_of_nonneg_left q3 hgs.le)
  exact this

omit [MeasurableSpace Ξ] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma potential_run_le (h : Hyp k D proj loss sub B G) {z0 : E × ℝ × ℝ}
    (he0 : z0.2.1 ∈ Icc k.elo k.ehi) (hs0 : z0.2.2 ∈ Icc k.slo k.shi) {xs : E} (hxs : xs ∈ D)
    {es ss : ℝ} (ξ : ℕ → Ξ) (t : ℕ) :
    0 ≤ potential k proj xs es ss (run k proj loss sub z0 ξ t) ∧
    potential k proj xs es ss (run k proj loss sub z0 ξ t) ≤
      (‖proj z0.1 - xs‖ + t * (k.gx * (k.c * (B - k.elo) * G / k.slo))) ^ 2 / k.gx +
      (|k.elo| + |k.ehi| + |es|) ^ 2 / k.ge + (|k.slo| + |k.shi| + |ss|) ^ 2 / k.gs := by
  obtain ⟨he, hs⟩ := run_mem h he0 hs0 ξ t
  have hd := run_dist h he0 hs0 ξ hxs t
  have hgx := h.gx_pos; have hge := h.ge_pos; have hgs := h.gs_pos
  unfold potential
  constructor
  · positivity
  have a1 : ‖proj (run k proj loss sub z0 ξ t).1 - xs‖ ^ 2 ≤
      (‖proj z0.1 - xs‖ + t * (k.gx * (k.c * (B - k.elo) * G / k.slo))) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hd 2
  have a2 : ((run k proj loss sub z0 ξ t).2.1 - es) ^ 2 ≤ (|k.elo| + |k.ehi| + |es|) ^ 2 := by
    rw [← sq_abs]
    apply pow_le_pow_left₀ (abs_nonneg _)
    refine (abs_sub _ _).trans ?_
    have : |(run k proj loss sub z0 ξ t).2.1| ≤ |k.elo| + |k.ehi| := by
      rw [abs_le]; constructor <;> linarith [he.1, he.2, neg_abs_le k.elo, le_abs_self k.ehi,
        abs_nonneg k.elo, abs_nonneg k.ehi]
    linarith
  have a3 : ((run k proj loss sub z0 ξ t).2.2 - ss) ^ 2 ≤ (|k.slo| + |k.shi| + |ss|) ^ 2 := by
    rw [← sq_abs]
    apply pow_le_pow_left₀ (abs_nonneg _)
    refine (abs_sub _ _).trans ?_
    have : |(run k proj loss sub z0 ξ t).2.2| ≤ |k.slo| + |k.shi| := by
      rw [abs_le]; constructor <;> linarith [hs.1, hs.2, neg_abs_le k.slo, le_abs_self k.shi,
        abs_nonneg k.slo, abs_nonneg k.shi]
    linarith
  have := add_le_add (add_le_add (div_le_div_of_nonneg_right a1 hgx.le)
    (div_le_div_of_nonneg_right a2 hge.le)) (div_le_div_of_nonneg_right a3 hgs.le)
  exact this

theorem exp_step (h : Hyp k D proj loss sub B G) (hp : Measurable proj)
    (hl : Measurable (Function.uncurry loss)) (hsm : Measurable (Function.uncurry sub))
    {z0 : E × ℝ × ℝ} (he0 : z0.2.1 ∈ Icc k.elo k.ehi) (hs0 : z0.2.2 ∈ Icc k.slo k.shi)
    {xs : E} (hxs : xs ∈ D) {es ss : ℝ} (hes : es ∈ Icc k.elo k.ehi)
    (hss : ss ∈ Icc k.slo k.shi) (t : ℕ) :
    let P := Measure.infinitePi fun _ : ℕ => p
    let z := fun ξ : ℕ → Ξ => run k proj loss sub z0 ξ t
    (∫ ξ, potential k proj xs es ss (run k proj loss sub z0 ξ (t + 1)) ∂P) ≤
      (∫ ξ, potential k proj xs es ss (z ξ) ∂P) -
        2 * ((∫ ξ, PhiX p k loss (proj (z ξ).1) (z ξ).2.1 (z ξ).2.2 ∂P) - PhiX p k loss xs es ss) +
        ∫ ξ, NoiseX p k loss sub (proj (z ξ).1) (z ξ).2.1 (z ξ).2.2 ∂P := by
  intro P z
  obtain ⟨ω0⟩ := nonempty_of_isProbabilityMeasure p
  have hzm : Measurable z := measurable_run hp hl hsm z0 t
  have hz'm : Measurable (fun ξ : ℕ → Ξ => run k proj loss sub z0 ξ (t + 1)) :=
    measurable_run hp hl hsm z0 (t + 1)
  have hpotm : Measurable (fun w : E × ℝ × ℝ => potential k proj xs es ss w) := by
    unfold potential
    exact ((((hp.comp measurable_fst).sub_const xs).norm.pow_const 2).div_const _).add
      (((measurable_fst.comp measurable_snd).sub_const es).pow_const 2 |>.div_const _) |>.add
      (((measurable_snd.comp measurable_snd).sub_const ss).pow_const 2 |>.div_const _)
  set C := (‖proj z0.1 - xs‖ + t * (k.gx * (k.c * (B - k.elo) * G / k.slo))) ^ 2 / k.gx +
      (|k.elo| + |k.ehi| + |es|) ^ 2 / k.ge + (|k.slo| + |k.shi| + |ss|) ^ 2 / k.gs
  set C' := (‖proj z0.1 - xs‖ + (t + 1 : ℕ) * (k.gx * (k.c * (B - k.elo) * G / k.slo))) ^ 2 / k.gx +
      (|k.elo| + |k.ehi| + |es|) ^ 2 / k.ge + (|k.slo| + |k.shi| + |ss|) ^ 2 / k.gs
  have hpi : Integrable (fun ξ => potential k proj xs es ss (z ξ)) P :=
    Integrable.of_bound (hpotm.comp hzm).aestronglyMeasurable C (Filter.Eventually.of_forall
      fun ξ => by
        obtain ⟨a, b⟩ := potential_run_le h he0 hs0 hxs (es := es) (ss := ss) ξ t
        rw [Real.norm_eq_abs, abs_of_nonneg a]; exact b)
  have hpi' : Integrable (fun ξ => potential k proj xs es ss (run k proj loss sub z0 ξ (t + 1))) P :=
    Integrable.of_bound (hpotm.comp hz'm).aestronglyMeasurable C' (Filter.Eventually.of_forall
      fun ξ => by
        obtain ⟨a, b⟩ := potential_run_le h he0 hs0 hxs (es := es) (ss := ss) ξ (t + 1)
        rw [Real.norm_eq_abs, abs_of_nonneg a]; exact b)
  let Φ1 : E × ℝ × ℝ → Ξ → ℝ := fun w ω => phiAt k loss (proj w.1) w.2.1 w.2.2 ω
  let Φ2 : E × ℝ × ℝ → Ξ → ℝ := fun w ω => noiseAt k loss sub (proj w.1) w.2.1 w.2.2 ω
  have hΦ1 : Measurable (Function.uncurry Φ1) := measurable_phiAt hp hl
  have hΦ2 : Measurable (Function.uncurry Φ2) := measurable_noiseAt hp hl hsm
  let X : (Fin t → Ξ) → E × ℝ × ℝ := fun u => run k proj loss sub z0 (extend ω0 u) t
  have hX : Measurable X := (measurable_run hp hl hsm z0 t).comp (measurable_extend ω0)
  have hXeq : ∀ ξ : ℕ → Ξ, X (fun i : Fin t => ξ i) = z ξ := fun ξ =>
    run_congr z0 t (extend_agree ω0 ξ)
  have hmem : ∀ ξ, proj (z ξ).1 ∈ D ∧ (z ξ).2.1 ∈ Icc k.elo k.ehi ∧ (z ξ).2.2 ∈ Icc k.slo k.shi :=
    fun ξ => ⟨h.proj_mem _, run_mem h he0 hs0 ξ t⟩
  have hφi : Integrable (fun ξ : ℕ → Ξ => Φ1 (X (fun i : Fin t => ξ i)) (ξ t)) P := by
    simp_rw [hXeq]
    refine Integrable.of_bound ((hΦ1.comp (hzm.prodMk (measurable_pi_apply t))).aestronglyMeasurable)
      (phiBound k B) (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs]
    exact phiAt_abs_le h (hmem ξ).1 (hmem ξ).2.1 (hmem ξ).2.2 (ξ t)
  have hni : Integrable (fun ξ : ℕ → Ξ => Φ2 (X (fun i : Fin t => ξ i)) (ξ t)) P := by
    simp_rw [hXeq]
    refine Integrable.of_bound ((hΦ2.comp (hzm.prodMk (measurable_pi_apply t))).aestronglyMeasurable)
      (noiseBound k B G) (Filter.Eventually.of_forall fun ξ => ?_)
    obtain ⟨a, b⟩ := noiseAt_le h (hmem ξ).1 (hmem ξ).2.1.1 (hmem ξ).2.2.1 (ξ t)
    rw [Real.norm_eq_abs, abs_of_nonneg a]; exact b
  obtain ⟨-, hE1⟩ := integral_prefix p t X hX Φ1 hΦ1 hφi
  obtain ⟨-, hE2⟩ := integral_prefix p t X hX Φ2 hΦ2 hni
  simp_rw [hXeq] at hE1 hE2 hφi hni
  have hsm' : MeasurePreserving (fun ξ : ℕ → Ξ => ξ t) P p :=
    measurePreserving_eval_infinitePi (fun _ : ℕ => p) t
  have hcmp : Measurable (fun ω : Ξ => phiAt k loss xs es ss ω) := by
    exact (measurable_phiAt (k := k) (proj := id) measurable_id hl).comp
      ((measurable_const (a := ((xs, es, ss) : E × ℝ × ℝ))).prodMk measurable_id)
  have hcmpi : Integrable (fun ξ : ℕ → Ξ => phiAt k loss xs es ss (ξ t)) P := by
    refine Integrable.of_bound (hcmp.comp (measurable_pi_apply t)).aestronglyMeasurable
      (phiBound k B) (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs]
    exact phiAt_abs_le h hxs hes hss (ξ t)
  have hcmpE : (∫ ξ, phiAt k loss xs es ss (ξ t) ∂P) = PhiX p k loss xs es ss := by
    unfold PhiX
    rw [← hsm'.map_eq, integral_map hsm'.measurable.aemeasurable hcmp.aestronglyMeasurable]
  have hpt : ∀ ξ, potential k proj xs es ss (run k proj loss sub z0 ξ (t + 1)) ≤
      potential k proj xs es ss (z ξ) -
        2 * (Φ1 (z ξ) (ξ t) - phiAt k loss xs es ss (ξ t)) + Φ2 (z ξ) (ξ t) := by
    intro ξ
    exact one_step h.c_pos.le h.gx_pos h.ge_pos h.gs_pos h.slo_pos h.proj_mem h.proj_vi h.subgrad
      hxs hes hss (hmem ξ).2.2 (ξ t)
  have hI1 : Integrable (fun ξ => Φ1 (z ξ) (ξ t) - phiAt k loss xs es ss (ξ t)) P := hφi.sub hcmpi
  have hI2 : Integrable (fun ξ => 2 * (Φ1 (z ξ) (ξ t) - phiAt k loss xs es ss (ξ t))) P :=
    hI1.const_mul 2
  have hI3 : Integrable (fun ξ => potential k proj xs es ss (z ξ) -
      2 * (Φ1 (z ξ) (ξ t) - phiAt k loss xs es ss (ξ t))) P := hpi.sub hI2
  have hri : Integrable (fun ξ => potential k proj xs es ss (z ξ) -
      2 * (Φ1 (z ξ) (ξ t) - phiAt k loss xs es ss (ξ t)) + Φ2 (z ξ) (ξ t)) P := hI3.add hni
  have hmono := integral_mono hpi' hri hpt
  refine hmono.trans (le_of_eq ?_)
  rw [integral_add hI3 hni, integral_sub hpi hI2, integral_const_mul, integral_sub hφi hcmpi,
    hE1, hE2, hcmpE]
  all_goals rfl

end Expectation

section Jensen

variable [MeasurableSpace Ξ] (p : Measure Ξ) [IsProbabilityMeasure p]
variable [MeasurableSpace E] [BorelSpace E]
variable {k : Cfg} {D : Set E} {proj : E → E} {loss : E → Ξ → ℝ} {sub : E → Ξ → E} {B G : ℝ}

omit [MeasurableSpace Ξ] [MeasurableSpace E] [BorelSpace E] in
lemma phi_average_le (h : Hyp k D proj loss sub B G) {T : ℕ} (hT : 0 < T)
    (x : ℕ → E) (η s : ℕ → ℝ) (hx : ∀ t, x t ∈ D) (hs : ∀ t, s t ∈ Icc k.slo k.shi)
    (hD : Convex ℝ D) (ω : Ξ) :
    let xb := (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, x t
    let eb := (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, η t
    let sb := (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, s t
    phiAt k loss xb eb sb ω ≤ (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, phiAt k loss (x t) (η t) (s t) ω := by
  intro xb eb sb
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hxb : xb ∈ D := by
    have := hD.sum_mem (t := Finset.range T) (w := fun _ => (T : ℝ)⁻¹) (z := x)
      (fun _ _ => by positivity) (by simp [Finset.card_range]; field_simp) (fun t _ => hx t)
    simpa [xb, Finset.smul_sum] using this
  have hsb : 0 < sb := by
    have : ∀ t ∈ Finset.range T, k.slo ≤ s t := fun t _ => (hs t).1
    have hsum : (T : ℝ) * k.slo ≤ ∑ t ∈ Finset.range T, s t := by
      have := Finset.sum_le_sum this
      simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using this
    have : k.slo ≤ sb := by
      simp only [sb]; rw [le_inv_mul_iff₀ hT']; linarith
    linarith [h.slo_pos]
  set u := tailAt loss xb eb ω
  have hineq : ∀ t ∈ Finset.range T,
      phiAt k loss xb eb sb ω + k.c * u / sb * ⟪sub xb ω, x t - xb⟫ +
        (1 - k.c * u / sb) * (η t - eb) + (k.c / 2 - k.c * u ^ 2 / (2 * sb ^ 2)) * (s t - sb) ≤
      phiAt k loss (x t) (η t) (s t) ω := by
    intro t _
    have hst : 0 < s t := lt_of_lt_of_le h.slo_pos (hs t).1
    exact sample_ineq h.c_pos.le hsb hst (h.subgrad ω xb hxb (x t) (hx t))
  have hsum := Finset.sum_le_sum hineq
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  have z1 : ∑ t ∈ Finset.range T, k.c * u / sb * ⟪sub xb ω, x t - xb⟫ = 0 := by
    rw [← Finset.mul_sum, ← inner_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
    have : ∑ t ∈ Finset.range T, x t = (T : ℝ) • xb := by
      simp only [xb, smul_smul, mul_inv_cancel₀ hT'.ne', one_smul]
    rw [this, ← Nat.cast_smul_eq_nsmul ℝ, sub_self, inner_zero_right, mul_zero]
  have z2 : ∑ t ∈ Finset.range T, (1 - k.c * u / sb) * (η t - eb) = 0 := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    simp only [eb]; field_simp; ring
  have z3 : ∑ t ∈ Finset.range T, (k.c / 2 - k.c * u ^ 2 / (2 * sb ^ 2)) * (s t - sb) = 0 := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    simp only [sb]; field_simp; ring
  rw [z1, z2, z3, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  rw [le_inv_mul_iff₀ hT']
  linarith

end Jensen

section Bracket

variable [MeasurableSpace Ξ] (p : Measure Ξ) [IsProbabilityMeasure p]
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {k : Cfg} {D : Set E} {proj : E → E} {loss : E → Ξ → ℝ} {sub : E → Ξ → E} {B G : ℝ}

noncomputable def avgX (k : Cfg) (proj : E → E) (loss : E → Ξ → ℝ) (sub : E → Ξ → E)
    (z0 : E × ℝ × ℝ) (T : ℕ) (ξ : ℕ → Ξ) : E :=
  (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, proj (run k proj loss sub z0 ξ t).1

noncomputable def avgE (k : Cfg) (proj : E → E) (loss : E → Ξ → ℝ) (sub : E → Ξ → E)
    (z0 : E × ℝ × ℝ) (T : ℕ) (ξ : ℕ → Ξ) : ℝ :=
  (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, (run k proj loss sub z0 ξ t).2.1

noncomputable def avgS (k : Cfg) (proj : E → E) (loss : E → Ξ → ℝ) (sub : E → Ξ → E)
    (z0 : E × ℝ × ℝ) (T : ℕ) (ξ : ℕ → Ξ) : ℝ :=
  (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, (run k proj loss sub z0 ξ t).2.2

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [BorelSpace E] [SecondCountableTopology E] in
lemma measurable_PhiX (hp : Measurable proj) (hl : Measurable (Function.uncurry loss)) :
    Measurable (fun w : E × ℝ × ℝ => PhiX p k loss (proj w.1) w.2.1 w.2.2) := by
  have := (measurable_phiAt (k := k) hp hl).stronglyMeasurable.integral_prod_right'
    (ν := p)
  exact this.measurable

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [BorelSpace E] [SecondCountableTopology E] in
lemma measurable_PhiX' (hl : Measurable (Function.uncurry loss)) :
    Measurable (fun w : E × ℝ × ℝ => PhiX p k loss w.1 w.2.1 w.2.2) := by
  have := measurable_PhiX p (k := k) (proj := id) measurable_id hl
  simpa using this

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma PhiX_abs_le (h : Hyp k D proj loss sub B G) {x : E} (hx : x ∈ D) {η s : ℝ}
    (hη : η ∈ Icc k.elo k.ehi) (hs : s ∈ Icc k.slo k.shi) : |PhiX p k loss x η s| ≤ phiBound k B := by
  unfold PhiX
  refine (abs_integral_le_integral_abs).trans ?_
  have := integral_mono_of_nonneg (μ := p) (f := fun ω => |phiAt k loss x η s ω|)
    (g := fun _ => phiBound k B) (Filter.Eventually.of_forall fun _ => abs_nonneg _)
    (integrable_const _) (Filter.Eventually.of_forall fun ω => phiAt_abs_le h hx hη hs ω)
  simpa using this

omit [BorelSpace E] [SecondCountableTopology E] in
lemma PhiX_ge (h : Hyp k D proj loss sub B G) (hl : Measurable (Function.uncurry loss))
    {x : E} (hx : x ∈ D) {η s L : ℝ} (hs : 0 < s) (hF : L ≤ η + k.c * nrm p (loss x) η) :
    L ≤ PhiX p k loss x η s := by
  rw [PhiX_eq p h hl hx η s]
  have hQ := sq_nonneg' p (loss x) η
  have hr := Real.sq_sqrt hQ
  have : Real.sqrt (sq p (loss x) η) ≤ sq p (loss x) η / (2 * s) + s / 2 := by
    rw [div_add_div _ _ (by positivity) two_ne_zero, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (Real.sqrt (sq p (loss x) η) - s), Real.sqrt_nonneg (sq p (loss x) η)]
  have := mul_le_mul_of_nonneg_left this h.c_pos.le
  unfold nrm at hF
  have e : k.c * (sq p (loss x) η / (2 * s) + s / 2) =
      k.c * sq p (loss x) η / (2 * s) + k.c * s / 2 := by ring
  linarith

lemma avg_mem_Icc {a b : ℝ} {T : ℕ} (hT : 0 < T) (f : ℕ → ℝ) (hf : ∀ t, f t ∈ Icc a b) :
    (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, f t ∈ Icc a b := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have h1 : (T : ℝ) * a ≤ ∑ t ∈ Finset.range T, f t := by
    have := Finset.sum_le_sum (s := Finset.range T) (fun t _ => (hf t).1)
    simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using this
  have h2 : ∑ t ∈ Finset.range T, f t ≤ (T : ℝ) * b := by
    have := Finset.sum_le_sum (s := Finset.range T) (fun t _ => (hf t).2)
    simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using this
  constructor
  · rw [le_inv_mul_iff₀ hT']; linarith
  · rw [inv_mul_le_iff₀ hT']; linarith

omit [MeasurableSpace Ξ] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma avgX_mem (h : Hyp k D proj loss sub B G) (hD : Convex ℝ D) {T : ℕ} (hT : 0 < T)
    (z0 : E × ℝ × ℝ) (ξ : ℕ → Ξ) : avgX k proj loss sub z0 T ξ ∈ D := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have := hD.sum_mem (t := Finset.range T) (w := fun _ => (T : ℝ)⁻¹)
    (z := fun t => proj (run k proj loss sub z0 ξ t).1)
    (fun _ _ => by positivity) (by simp [Finset.card_range]; field_simp) (fun t _ => h.proj_mem _)
  simpa [avgX, Finset.smul_sum] using this

theorem bracket_bound (h : Hyp k D proj loss sub B G) (hD : Convex ℝ D) (hp : Measurable proj)
    (hl : Measurable (Function.uncurry loss)) (hsm : Measurable (Function.uncurry sub))
    {z0 : E × ℝ × ℝ} (he0 : z0.2.1 ∈ Icc k.elo k.ehi)
    (hs0 : z0.2.2 ∈ Icc k.slo k.shi)
    {xs : E} (hxs : xs ∈ D) {es ss : ℝ} (hes : es ∈ Icc k.elo k.ehi) (hss : ss ∈ Icc k.slo k.shi)
    {L : ℝ} (hF : ∀ x ∈ D, ∀ η, L ≤ η + k.c * nrm p (loss x) η)
    (hK : noiseSlope k B G ≤ 1) {T : ℕ} (hT : 0 < T) :
    (∫ ξ, PhiX p k loss (avgX k proj loss sub z0 T ξ) (avgE k proj loss sub z0 T ξ)
        (avgS k proj loss sub z0 T ξ) ∂(Measure.infinitePi fun _ : ℕ => p)) - L ≤
      potential k proj xs es ss z0 / T + 2 * (PhiX p k loss xs es ss - L) + noiseConst k B G := by
  set P := Measure.infinitePi fun _ : ℕ => p
  set z := fun (t : ℕ) (ξ : ℕ → Ξ) => run k proj loss sub z0 ξ t
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hzm : ∀ t, Measurable (z t) := measurable_run hp hl hsm z0
  have hmem : ∀ t ξ, proj (z t ξ).1 ∈ D ∧ (z t ξ).2.1 ∈ Icc k.elo k.ehi ∧
      (z t ξ).2.2 ∈ Icc k.slo k.shi := fun t ξ => ⟨h.proj_mem _, run_mem h he0 hs0 ξ t⟩
  have hPm : Measurable (fun w : E × ℝ × ℝ => PhiX p k loss (proj w.1) w.2.1 w.2.2) :=
    measurable_PhiX p hp hl
  have hPi : ∀ t, Integrable (fun ξ => PhiX p k loss (proj (z t ξ).1) (z t ξ).2.1 (z t ξ).2.2) P :=
    fun t => Integrable.of_bound (hPm.comp (hzm t)).aestronglyMeasurable (phiBound k B)
      (Filter.Eventually.of_forall fun ξ => by
        rw [Real.norm_eq_abs]
        exact PhiX_abs_le p h (hmem t ξ).1 (hmem t ξ).2.1 (hmem t ξ).2.2)
  have hNm : Measurable (fun w : E × ℝ × ℝ => NoiseX p k loss sub (proj w.1) w.2.1 w.2.2) :=
    ((measurable_noiseAt (k := k) hp hl hsm).stronglyMeasurable.integral_prod_right' (ν := p)).measurable
  have hNb : ∀ t ξ, 0 ≤ NoiseX p k loss sub (proj (z t ξ).1) (z t ξ).2.1 (z t ξ).2.2 ∧
      NoiseX p k loss sub (proj (z t ξ).1) (z t ξ).2.1 (z t ξ).2.2 ≤ noiseBound k B G := by
    intro t ξ
    obtain ⟨hx, he, hs⟩ := hmem t ξ
    constructor
    · exact integral_nonneg fun ω => (noiseAt_le h hx he.1 hs.1 ω).1
    · unfold NoiseX
      have := integral_mono_of_nonneg (μ := p) (Filter.Eventually.of_forall fun ω =>
        (noiseAt_le h hx he.1 hs.1 ω).1) (integrable_const (noiseBound k B G))
        (Filter.Eventually.of_forall fun ω => (noiseAt_le h hx he.1 hs.1 ω).2)
      simpa using this
  have hNi : ∀ t, Integrable (fun ξ => NoiseX p k loss sub (proj (z t ξ).1) (z t ξ).2.1 (z t ξ).2.2) P :=
    fun t => Integrable.of_bound (hNm.comp (hzm t)).aestronglyMeasurable (noiseBound k B G)
      (Filter.Eventually.of_forall fun ξ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hNb t ξ).1]; exact (hNb t ξ).2)
  set Φt := fun t => ∫ ξ, PhiX p k loss (proj (z t ξ).1) (z t ξ).2.1 (z t ξ).2.2 ∂P
  set Nt := fun t => ∫ ξ, NoiseX p k loss sub (proj (z t ξ).1) (z t ξ).2.1 (z t ξ).2.2 ∂P
  set a := fun t => ∫ ξ, potential k proj xs es ss (z t ξ) ∂P
  set Φs := PhiX p k loss xs es ss
  have hΦL : ∀ t, L ≤ Φt t := by
    intro t
    have := integral_mono (integrable_const L) (hPi t) fun ξ =>
      PhiX_ge p h hl (hmem t ξ).1 (lt_of_lt_of_le h.slo_pos (hmem t ξ).2.2.1)
        (hF _ (hmem t ξ).1 _)
    simpa using this
  have hN : ∀ t, Nt t ≤ noiseConst k B G + noiseSlope k B G * (Φt t - L) := by
    intro t
    have hpt : ∀ ξ, NoiseX p k loss sub (proj (z t ξ).1) (z t ξ).2.1 (z t ξ).2.2 ≤
        noiseConst k B G + noiseSlope k B G *
          (PhiX p k loss (proj (z t ξ).1) (z t ξ).2.1 (z t ξ).2.2 - L) := fun ξ =>
      noise_self_bound p h hl hsm (hmem t ξ).1 (hmem t ξ).2.1.1 (hmem t ξ).2.2.1
        (hF _ (hmem t ξ).1 _)
    have hri : Integrable (fun ξ => noiseConst k B G + noiseSlope k B G *
        (PhiX p k loss (proj (z t ξ).1) (z t ξ).2.1 (z t ξ).2.2 - L)) P :=
      (integrable_const _).add (((hPi t).sub (integrable_const L)).const_mul _)
    have := integral_mono (hNi t) hri hpt
    refine this.trans (le_of_eq ?_)
    rw [integral_add (f := fun _ => noiseConst k B G)
      (g := fun ξ => noiseSlope k B G * (PhiX p k loss (proj (z t ξ).1) (z t ξ).2.1 (z t ξ).2.2 - L))
      (integrable_const _) (((hPi t).sub (integrable_const L)).const_mul _),
      integral_const, probReal_univ, one_smul, integral_const_mul,
      integral_sub (f := fun ξ => PhiX p k loss (proj (z t ξ).1) (z t ξ).2.1 (z t ξ).2.2)
        (g := fun _ => L) (hPi t) (integrable_const L),
      integral_const, probReal_univ, one_smul]
  have hK0 : 0 ≤ noiseSlope k B G := by
    unfold noiseSlope
    have := h.gx_pos; have := h.ge_pos; have := h.gs_pos; have := h.c_pos; have := h.slo_pos
    positivity
  have hstep : ∀ t, a (t + 1) ≤ a t - (Φt t - L) + 2 * (Φs - L) + noiseConst k B G := by
    intro t
    have h1 := exp_step p h hp hl hsm he0 hs0 hxs hes hss t
    have h2 := hN t
    have h3 := hΦL t
    have h4 : noiseSlope k B G * (Φt t - L) ≤ 1 * (Φt t - L) :=
      mul_le_mul_of_nonneg_right hK (by linarith)
    change a (t + 1) ≤ a t - 2 * (Φt t - Φs) + Nt t at h1
    linarith
  have hsum : ∀ n, a n + ∑ t ∈ Finset.range n, (Φt t - L) ≤
      a 0 + n * (2 * (Φs - L) + noiseConst k B G) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have := hstep n
      push_cast
      linarith
  have ha0 : a 0 = potential k proj xs es ss z0 := by
    simp [a, z, run]
  have haT : 0 ≤ a T := integral_nonneg fun ξ =>
    (potential_run_le h he0 hs0 hxs (es := es) (ss := ss) ξ T).1
  have hJ : ∀ ξ, PhiX p k loss (avgX k proj loss sub z0 T ξ) (avgE k proj loss sub z0 T ξ)
      (avgS k proj loss sub z0 T ξ) ≤
      (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, PhiX p k loss (proj (z t ξ).1) (z t ξ).2.1 (z t ξ).2.2 := by
    intro ξ
    have hpt := fun ω => phi_average_le h hT (fun t => proj (z t ξ).1) (fun t => (z t ξ).2.1)
      (fun t => (z t ξ).2.2) (fun t => (hmem t ξ).1) (fun t => (hmem t ξ).2.2) hD ω
    have hint : ∀ t, Integrable (fun ω => phiAt k loss (proj (z t ξ).1) (z t ξ).2.1 (z t ξ).2.2 ω) p :=
      fun t => Integrable.of_bound ((measurable_phiAt (k := k) hp hl).comp
        ((measurable_const (a := z t ξ)).prodMk measurable_id)).aestronglyMeasurable (phiBound k B)
        (Filter.Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs]
          exact phiAt_abs_le h (hmem t ξ).1 (hmem t ξ).2.1 (hmem t ξ).2.2 ω)
    have hxa := avgX_mem h hD hT z0 ξ
    have hea := avg_mem_Icc hT (fun t => (z t ξ).2.1) (fun t => (hmem t ξ).2.1)
    have hsa := avg_mem_Icc hT (fun t => (z t ξ).2.2) (fun t => (hmem t ξ).2.2)
    have hlint : Integrable (fun ω => phiAt k loss (avgX k proj loss sub z0 T ξ)
        (avgE k proj loss sub z0 T ξ) (avgS k proj loss sub z0 T ξ) ω) p := by
      have hpm := (measurable_phiAt (k := k) (proj := id) measurable_id hl).comp
        ((measurable_const (a := ((avgX k proj loss sub z0 T ξ, avgE k proj loss sub z0 T ξ,
          avgS k proj loss sub z0 T ξ) : E × ℝ × ℝ))).prodMk measurable_id)
      exact Integrable.of_bound hpm.aestronglyMeasurable (phiBound k B)
        (Filter.Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs]; exact phiAt_abs_le h hxa hea hsa ω)
    unfold PhiX
    rw [← integral_finsetSum _ (fun t _ => hint t), ← integral_const_mul]
    exact integral_mono hlint ((integrable_finsetSum _ (fun t _ => hint t)).const_mul _) hpt
  have hAm : Measurable (fun ξ => PhiX p k loss (avgX k proj loss sub z0 T ξ)
      (avgE k proj loss sub z0 T ξ) (avgS k proj loss sub z0 T ξ)) := by
    have hX : Measurable (fun ξ => avgX k proj loss sub z0 T ξ) :=
      (Finset.measurable_sum _ fun t _ => hp.comp (measurable_fst.comp (hzm t))).const_smul _
    have hE : Measurable (fun ξ => avgE k proj loss sub z0 T ξ) :=
      measurable_const.mul (Finset.measurable_sum _ fun t _ =>
        measurable_fst.comp (measurable_snd.comp (hzm t)))
    have hS : Measurable (fun ξ => avgS k proj loss sub z0 T ξ) :=
      measurable_const.mul (Finset.measurable_sum _ fun t _ =>
        measurable_snd.comp (measurable_snd.comp (hzm t)))
    exact (measurable_PhiX' p (k := k) hl).comp (hX.prodMk (hE.prodMk hS))
  have hAi : Integrable (fun ξ => PhiX p k loss (avgX k proj loss sub z0 T ξ)
      (avgE k proj loss sub z0 T ξ) (avgS k proj loss sub z0 T ξ)) P :=
    Integrable.of_bound hAm.aestronglyMeasurable (phiBound k B)
      (Filter.Eventually.of_forall fun ξ => by
        rw [Real.norm_eq_abs]
        exact PhiX_abs_le p h (avgX_mem h hD hT z0 ξ)
          (avg_mem_Icc hT (fun t => (z t ξ).2.1) (fun t => (hmem t ξ).2.1))
          (avg_mem_Icc hT (fun t => (z t ξ).2.2) (fun t => (hmem t ξ).2.2)))
  have hJi := integral_mono hAi ((integrable_finsetSum _ (fun t _ => hPi t)).const_mul _) hJ
  rw [integral_const_mul, integral_finsetSum _ (fun t _ => hPi t)] at hJi
  have hfin := hsum T
  rw [ha0] at hfin
  have hsumL : ∑ t ∈ Finset.range T, (Φt t - L) = (∑ t ∈ Finset.range T, Φt t) - T * L := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hsumL] at hfin
  have hkey : (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, Φt t - L ≤
      potential k proj xs es ss z0 / T + 2 * (Φs - L) + noiseConst k B G := by
    have : ∑ t ∈ Finset.range T, Φt t ≤ potential k proj xs es ss z0 + T * L +
        T * (2 * (Φs - L) + noiseConst k B G) := by linarith
    have h2 : (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, Φt t ≤
        (T : ℝ)⁻¹ * (potential k proj xs es ss z0 + T * L + T * (2 * (Φs - L) + noiseConst k B G)) :=
      mul_le_mul_of_nonneg_left this (by positivity)
    have e : (T : ℝ)⁻¹ * (potential k proj xs es ss z0 + T * L + T * (2 * (Φs - L) +
        noiseConst k B G)) = potential k proj xs es ss z0 / T + L + (2 * (Φs - L) +
        noiseConst k B G) := by
      field_simp
    linarith
  calc _ ≤ (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, Φt t - L := by
        have : (∫ ξ, PhiX p k loss (avgX k proj loss sub z0 T ξ) (avgE k proj loss sub z0 T ξ)
            (avgS k proj loss sub z0 T ξ) ∂P) ≤ (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, Φt t := hJi
        linarith
    _ ≤ _ := hkey

end Bracket

end OracleTemplate.ChiSquareDro
