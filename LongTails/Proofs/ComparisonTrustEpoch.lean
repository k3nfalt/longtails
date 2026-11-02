import LongTails.Proofs.ComparisonTrustGuess
import LongTails.Proofs.ComparisonTrustLine

namespace LongTails.Proofs.ComparisonTrustEpoch

open OracleTemplate LongTails.Algorithms.ComparisonTrustRegion
  LongTails.Algorithms.GuardedMetricAcceleration
  LongTails.Proofs.ComparisonTrustPlans LongTails.Proofs.ComparisonTrustDirection
  LongTails.Proofs.ComparisonTrustTaylor LongTails.Proofs.ComparisonTrustHvp
  LongTails.Proofs.ComparisonTrustAgd LongTails.Proofs.ComparisonTrustQuadratic
  LongTails.Proofs.ComparisonTrustGuess LongTails.Proofs.ComparisonTrustLine
open scoped RealInnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Select

variable (f : E → ℝ)

def selectPure (cands : List E) (k : ℕ) (x : E) : E :=
  loopPure (fun i best => if decide (f (cands.getD i best) ≤ f best) then cands.getD i best
    else best) k 0 x

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma select_spec (cands : List E) (k : ℕ) (x : E) :
    f (selectPure f cands k x) ≤ f x ∧
      ∀ i < k, ∀ y, cands[i]? = some y → f (selectPure f cands k x) ≤ f y := by
  have key := loopPure_induction
    (fun i best => if decide (f (cands.getD i best) ≤ f best) then cands.getD i best else best)
    (fun k best => f best ≤ f x ∧ ∀ i < k, ∀ y, cands[i]? = some y → f best ≤ f y)
    x ⟨le_rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
    (fun k best ⟨h1, h2⟩ => by
      by_cases hc : f (cands.getD k best) ≤ f best
      · simp only [hc, decide_true, ↓reduceIte]
        refine ⟨by linarith, fun i hi y hy => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
        · linarith [h2 i hi y hy]
        · subst hi
          rw [List.getD_eq_getElem?_getD, hy, Option.getD_some]
      · simp only [hc, decide_false, Bool.false_eq_true, ↓reduceIte]
        refine ⟨h1, fun i hi y hy => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
        · exact h2 i hi y hy
        · subst hi
          rw [List.getD_eq_getElem?_getD, hy, Option.getD_some] at hc
          push Not at hc
          exact hc.le) k
  exact key

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma select_le_mem {cands : List E} {k : ℕ} (hk : cands.length ≤ k) (x : E) {y : E}
    (hy : y ∈ cands) : f (selectPure f cands k x) ≤ f y := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
  exact (select_spec f cands k x).2 i (by omega) _ (List.getElem?_eq_getElem hi)

end Select

def epochCands (f : E → ℝ) (t : Tuning) (x : E) : List E :=
  let u := dirAt f t x
  let lh := ternaryPure f x u t.mt t.r
  let du := dirAt f t (x + probeStep t u • u)
  let F : Frame E := { x := x, u := u, Tu := tangential t x u u du, κ := lh.2⁻¹ }
  (x - (t.r / 8) • u) :: ((List.ofFn (fun j : Fin t.J =>
    QueryPlan.eval (cmpOf f) (guessPlan t F (guessScale t j)))).map (guessCands t x)).flatten

lemma eval_epochPlan (f : E → ℝ) (t : Tuning) (x : E) :
    QueryPlan.eval (cmpOf f) (epochPlan t x) =
      (selectPure f (epochCands f t x) (4 * t.J + 1) x, epochCands f t x) := by
  have ht : ∀ u, QueryPlan.eval (cmpOf f) (ternaryPlan t x u) = ternaryPure f x u t.mt t.r :=
    fun u => eval_ternaryPlan (f := f) t x u
  simp only [epochPlan, QueryPlan.eval_bind, QueryPlan.eval_map, QueryPlan.eval_traverse,
    eval_loop, selectStep, eval_cmpPlan, ht, epochCands, selectPure, dirAt]
  rfl

lemma length_epochCands (f : E → ℝ) (t : Tuning) (x : E) :
    (epochCands f t x).length = 4 * t.J + 1 := by
  simp only [epochCands, List.length_cons, List.length_flatten, List.map_map,
    Function.comp_def, guessCands, List.length_cons, List.length_nil]
  simp [List.sum_ofFn]
  try ring

lemma mem_epochCands_guess (f : E → ℝ) (t : Tuning) (x : E) (j : Fin t.J) {y : E}
    (hy : y ∈ guessCands t x (QueryPlan.eval (cmpOf f) (guessPlan t
      { x := x, u := dirAt f t x,
        Tu := tangential t x (dirAt f t x) (dirAt f t x)
          (dirAt f t (x + probeStep t (dirAt f t x) • dirAt f t x)),
        κ := (ternaryPure f x (dirAt f t x) t.mt t.r).2⁻¹ } (guessScale t j)))) :
    y ∈ epochCands f t x := by
  simp only [epochCands, List.mem_cons, List.mem_flatten, List.mem_map, List.mem_ofFn]
  right
  exact ⟨_, ⟨_, ⟨j, rfl⟩, rfl⟩, hy⟩

section Analysis

variable {f : E → ℝ} {L ρ : ℝ}

def tmpl (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (t : Tuning) : Run E :=
  ⟨t.a, t.μ, t.LA, fun _ => 0, fun _ => 0, fun _ => 0⟩

structure Rel (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (t : Tuning) (L ρ ε G δ K θ : ℝ) : Prop where
  hL : 0 < L
  hρ : 0 < ρ
  hε : 0 < ε
  hG : 0 ≤ G
  hγ : 0 < t.γ
  hr : 0 < t.r
  hμ : t.μ = t.γ
  hLA : t.LA = 2 * L + 4 * t.γ
  ha : 0 < t.a
  ha1 : t.a ≤ 1
  htune : t.a ^ 2 * t.LA = t.μ
  hη : 24 * t.η ≤ t.γ / 8
  hρr : ρ * t.r = t.γ / 4
  hγr : t.γ * t.r = ε / 4
  hτ : 0 < t.τ
  hτ0 : 0 < t.τ0
  hLτ0 : L * t.τ0 ≤ ε / 4
  hζ : ((Module.finrank ℝ E : ℝ) + 2) * (9 * ρ * t.τ ^ 2 / 2) ≤
    ε / 2 / (2 * Real.sqrt (Module.finrank ℝ E))
  hδ : 2 * Real.sqrt (Module.finrank ℝ E) * (2 / 2 ^ t.m +
    2 * Real.sqrt (Module.finrank ℝ E) * (9 * ρ * t.τ ^ 2 / 2) / (ε / 2)) ≤ δ
  hδ1 : δ ≤ 1 / 2
  hK : 2 * L ^ 2 * t.τ0 / ε + 3 * G * δ / t.τ0 + ρ * t.τ0 ≤ K
  hK3 : K ≤ 3 * t.η
  hrad : δ ^ 2 * (2 * L + ρ * t.r) / 2 + L * (t.r * (2 / 3) ^ t.mt) * (2 * L + ρ * t.r) / ε +
    ρ * (16 / 63 * t.r + t.r * (2 / 3) ^ t.mt) / 2 ≤ t.γ / 16
  hJ : G ≤ 2 ^ (t.J - 1) * ε
  hJ1 : 1 ≤ t.J
  hN : 1 ≤ t.N
  hεt : t.ε = ε
  hslack : 8 * slack (tmpl E t) (2 * G) t.r (4 * K) (2 * G * δ) ≤ t.a * t.μ * t.r ^ 2
  hfin1 : (1 - t.a) ^ t.N * (2 * G * wmax (tmpl E t) (2 * G) t.r (4 * K) (2 * G * δ) +
      (t.LA + t.μ) / 2 * wmax (tmpl E t) (2 * G) t.r (4 * K) (2 * G * δ) ^ 2) ≤
        (ε / 20) ^ 2 / (32 * t.LA)
  hfin2 : 5 * slack (tmpl E t) (2 * G) t.r (4 * K) (2 * G * δ) / t.a ≤ (ε / 20) ^ 2 / (32 * t.LA)
  hfin3 : slackR (tmpl E t) (2 * G) t.r (4 * K) (2 * G * δ) ≤ ε / 20 / 2
  hθ1 : θ ≤ t.γ * t.r ^ 2 / 25
  hθ2 : θ ≤ (3 / 32 - δ ^ 2 / 16) * ε * t.r - ρ * t.r ^ 3 / 3072

lemma dirAt_accurate (h : Smooth f L ρ) (t : Tuning) {ε δ : ℝ} (hρ : 0 < ρ) (hτ : 0 < t.τ)
    (hε : 0 < ε)
    (hζ : ((Module.finrank ℝ E : ℝ) + 2) * (9 * ρ * t.τ ^ 2 / 2) ≤
      ε / 2 / (2 * Real.sqrt (Module.finrank ℝ E)))
    (hδ : 2 * Real.sqrt (Module.finrank ℝ E) * (2 / 2 ^ t.m +
      2 * Real.sqrt (Module.finrank ℝ E) * (9 * ρ * t.τ ^ 2 / 2) / (ε / 2)) ≤ δ)
    {y : E} (hy : ε / 2 ≤ ‖gradient f y‖) :
    ‖dirAt f t y - ‖gradient f y‖⁻¹ • gradient f y‖ ≤ δ := by
  have hgr : gradient f y ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hy
    linarith
  have hpos : 0 < ‖gradient f y‖ := norm_pos_iff.mpr hgr
  rw [dirAt_eq]
  have hsq : 0 ≤ Real.sqrt (Module.finrank ℝ E) := Real.sqrt_nonneg _
  have hs : ((Module.finrank ℝ E : ℝ) + 2) * (9 * ρ * t.τ ^ 2 / 2) ≤
      ‖gradient f y‖ / (2 * Real.sqrt (Module.finrank ℝ E)) :=
    hζ.trans (div_le_div_of_nonneg_right hy (by positivity))
  refine (dir_accuracy (h.test_spec hρ.le hτ y) (by positivity) hgr hs t.m).trans
    (le_trans ?_ hδ)
  gcongr

omit [FiniteDimensional ℝ E] in
lemma unit_of_close {u v : E} (hv : ‖v‖ = 1) (hu : ‖u - v‖ < 1)
    (hform : ∃ w : E, u = ‖w‖⁻¹ • w) : ‖u‖ = 1 := by
  obtain ⟨w, rfl⟩ := hform
  by_cases hw : w = 0
  · subst hw
    simp only [norm_zero, inv_zero, smul_zero, zero_sub, norm_neg, hv] at hu
    linarith
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)]

lemma noncurved_step (h : Smooth f L ρ) {x u : E} {c δ0 r : ℝ}
    (hc : ‖gradient f x‖ = c) (hcpos : 0 < c) (hu : ‖u‖ = 1)
    (hδ0 : ‖u - c⁻¹ • gradient f x‖ ≤ δ0) (hr : 0 < r)
    (hnc : ⟪u, fderiv ℝ (gradient f) x u⟫ < 4 * c / r) :
    f (x - (r / 8) • u) ≤ f x - (3 / 32 - δ0 ^ 2 / 16) * c * r + ρ * r ^ 3 / 3072 := by
  have ht := abs_le.mp (h.value_taylor x (-((r / 8) • u)))
  rw [← sub_eq_add_neg, norm_neg, norm_smul, hu, mul_one, Real.norm_eq_abs,
    abs_of_pos (by positivity)] at ht
  set ν := c⁻¹ • gradient f x
  have hν : ‖ν‖ = 1 := by
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hcpos, hc, inv_mul_cancel₀ hcpos.ne']
  have hgu : ⟪gradient f x, u⟫ = c * ⟪ν, u⟫ := by
    rw [show gradient f x = c • ν by rw [smul_smul, mul_inv_cancel₀ hcpos.ne', one_smul],
      real_inner_smul_left]
  have hgap := inner_unit_gap hν hu
  have hνu : ‖ν - u‖ ^ 2 ≤ δ0 ^ 2 := by
    rw [norm_sub_rev]; exact pow_le_pow_left₀ (norm_nonneg _) hδ0 2
  have h1 : ⟪gradient f x, -((r / 8) • u)⟫ ≤ -(r / 8) * c * (1 - δ0 ^ 2 / 2) := by
    rw [inner_neg_right, real_inner_smul_right, hgu]
    have : 1 - δ0 ^ 2 / 2 ≤ ⟪ν, u⟫ := by linarith
    have : 0 ≤ r / 8 * c := by positivity
    nlinarith
  have h2 : ⟪-((r / 8) • u), fderiv ℝ (gradient f) x (-((r / 8) • u))⟫ / 2 ≤ c * r / 32 := by
    simp only [map_neg, map_smul, inner_neg_left, inner_neg_right, neg_neg,
      real_inner_smul_left, real_inner_smul_right]
    have : r / 8 * (r / 8) * ⟪u, fderiv ℝ (gradient f) x u⟫ ≤ r / 8 * (r / 8) * (4 * c / r) :=
      mul_le_mul_of_nonneg_left hnc.le (by positivity)
    have : r / 8 * (r / 8) * (4 * c / r) = c * r / 16 := by field_simp; ring
    linarith
  have h3 : ρ * (r / 8) ^ 3 / 6 = ρ * r ^ 3 / 3072 := by ring
  linarith [ht.2]

end Analysis

section Progress

variable {f : E → ℝ} {L ρ : ℝ}

lemma exists_guess {c ε G : ℝ} {J : ℕ} (hc : ε < c) (hcG : c ≤ G)
    (hJ : G ≤ 2 ^ (J - 1) * ε) (hJ1 : 1 ≤ J) :
    ∃ j : ℕ, j < J ∧ c ≤ 2 ^ j * ε ∧ 2 ^ j * ε < 2 * c := by
  classical
  have hex : ∃ j : ℕ, c ≤ 2 ^ j * ε := ⟨J - 1, hcG.trans hJ⟩
  set j := Nat.find hex
  have hj : c ≤ 2 ^ j * ε := Nat.find_spec hex
  have hjle : j ≤ J - 1 := Nat.find_min' hex (hcG.trans hJ)
  refine ⟨j, by omega, hj, ?_⟩
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · rw [h0] at hj
    simp at hj
    linarith
  · have hmin := Nat.find_min hex (show j - 1 < j by omega)
    push Not at hmin
    have : (2 : ℝ) ^ j = 2 * 2 ^ (j - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [this]
    nlinarith

theorem epoch_progress (h : Smooth f L ρ) {t : Tuning} {ε G δ K θ : ℝ}
    (hR : Rel E t L ρ ε G δ K θ) (x : E) (hc1 : ε < ‖gradient f x‖)
    (hcG : ‖gradient f x‖ ≤ G) :
    (∃ y ∈ epochCands f t x, ‖gradient f y‖ ≤ ε) ∨
      ∃ y ∈ epochCands f t x, f y ≤ f x - θ := by
  set c := ‖gradient f x‖ with hcdef
  have hε := hR.hε
  have hcpos : 0 < c := lt_trans hε hc1
  have hL0 : 0 ≤ L := hR.hL.le
  have hρ0 : 0 ≤ ρ := hR.hρ.le
  set u := dirAt f t x with hudef
  have hacc : ‖u - c⁻¹ • gradient f x‖ ≤ δ :=
    dirAt_accurate h t hR.hρ hR.hτ hε hR.hζ hR.hδ (by linarith)
  have hδ0 : 0 ≤ δ := le_trans (norm_nonneg _) hacc
  have hν : ‖c⁻¹ • gradient f x‖ = 1 := by
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hcpos, ← hcdef,
      inv_mul_cancel₀ hcpos.ne']
  have hu : ‖u‖ = 1 := by
    refine unit_of_close hν (by linarith [hR.hδ1]) ?_
    rw [hudef, dirAt_eq]
    exact ⟨_, rfl⟩
  have hr := hR.hr
  have hγ := hR.hγ
  have hρr2 : ρ * t.r ^ 2 = ε / 16 := by
    have : ρ * t.r ^ 2 = (ρ * t.r) * t.r := by ring
    rw [this, hR.hρr]
    linarith [hR.hγr]
  by_cases hcurved : 4 * c / t.r ≤ ⟪u, fderiv ℝ (gradient f) x u⟫
  · -- curved: model-based guesses
    obtain ⟨hlo, hhi, hrad⟩ := radial_estimate (f := f) h hL0 hρ0 rfl hcpos hu hacc
      (by linarith [hR.hδ1]) hr (by rw [hρr2]; linarith) hcurved t.mt
    set lh := ternaryPure f x u t.mt t.r with hlhdef
    set du := dirAt f t (x + probeStep t u • u)
    set F : Frame E := { x := x, u := u, Tu := tangential t x u u du, κ := lh.2⁻¹ }
    set β := c * F.κ - ⟪u, fderiv ℝ (gradient f) x u⟫ with hβdef
    have hρpos := hR.hρ
    have hLpos := hR.hL
    have hden : 0 < 2 * L + ρ * t.r := by positivity
    have hhi_pos : 0 < lh.2 := lt_of_lt_of_le (by positivity) hlo
    have hβ : |β| ≤ t.γ / 16 := by
      have hb : β = c / lh.2 - ⟪u, fderiv ℝ (gradient f) x u⟫ := by
        rw [hβdef]; simp only [F, div_eq_mul_inv]
      rw [hb]
      refine hrad.trans (le_trans ?_ hR.hrad)
      have hq : 0 ≤ t.r * (2 / 3) ^ t.mt := by positivity
      have hA : (c * δ ^ 2 / 2 + L * (t.r * (2 / 3) ^ t.mt)) / lh.2 ≤
          δ ^ 2 * (2 * L + ρ * t.r) / 2 + L * (t.r * (2 / 3) ^ t.mt) * (2 * L + ρ * t.r) / ε := by
        rw [div_le_iff₀ hhi_pos]
        have hlo' : c ≤ (2 * L + ρ * t.r) * lh.2 := by
          have := (div_le_iff₀ hden).mp hlo
          linarith [mul_comm lh.2 (2 * L + ρ * t.r)]
        have h1 : c * δ ^ 2 / 2 ≤ δ ^ 2 * (2 * L + ρ * t.r) / 2 * lh.2 := by
          have := mul_le_mul_of_nonneg_left hlo' (sq_nonneg δ)
          nlinarith
        have h2 : L * (t.r * (2 / 3) ^ t.mt) ≤
            L * (t.r * (2 / 3) ^ t.mt) * (2 * L + ρ * t.r) / ε * lh.2 := by
          have hc' : ε ≤ (2 * L + ρ * t.r) * lh.2 := by linarith
          have h0 : 0 ≤ L * (t.r * (2 / 3) ^ t.mt) := by positivity
          have hB1 : 1 ≤ (2 * L + ρ * t.r) * lh.2 / ε := by rw [le_div_iff₀ hε]; linarith
          have := mul_le_mul_of_nonneg_left hB1 h0
          calc L * (t.r * (2 / 3) ^ t.mt) = L * (t.r * (2 / 3) ^ t.mt) * 1 := (mul_one _).symm
            _ ≤ L * (t.r * (2 / 3) ^ t.mt) * ((2 * L + ρ * t.r) * lh.2 / ε) := this
            _ = _ := by ring
        have h3 : 0 ≤ c * δ ^ 2 / 2 := by positivity
        nlinarith
      have hB : ρ * lh.2 / 2 ≤ ρ * (16 / 63 * t.r + t.r * (2 / 3) ^ t.mt) / 2 := by
        gcongr
      linarith
    -- Hessian-vector accuracy
    have hprobe : ∀ w : E, w ≠ 0 → ε / 2 ≤ ‖gradient f (x + probeStep t w • w)‖ := by
      intro w hw
      have hn : ‖probeStep t w • w‖ = t.τ0 := by
        simp only [probeStep, hw, ↓reduceIte, norm_smul, Real.norm_eq_abs]
        rw [abs_of_pos (by have := hR.hτ0; have := norm_pos_iff.mpr hw; positivity)]
        field_simp [norm_ne_zero_iff.mpr hw]
      have := h.lip (x + probeStep t w • w) x
      rw [add_sub_cancel_left, hn] at this
      have h2 := norm_sub_norm_le (gradient f x) (gradient f (x + probeStep t w • w))
      rw [← hcdef] at h2
      rw [norm_sub_rev] at this
      linarith [hR.hLτ0]
    have hdirw : ∀ w : E, w ≠ 0 → ‖dirAt f t (x + probeStep t w • w) -
        ‖gradient f (x + probeStep t w • w)‖⁻¹ • gradient f (x + probeStep t w • w)‖ ≤ δ :=
      fun w hw => dirAt_accurate h t hR.hρ hR.hτ hε hR.hζ hR.hδ (hprobe w hw)
    have hune : u ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hu; norm_num at hu
    have hKtan : ∀ w dd : E, w ≠ 0 →
        ‖dd - ‖gradient f (F.x + probeStep t w • w)‖⁻¹ • gradient f (F.x + probeStep t w • w)‖ ≤
          δ → ‖c • tangential t F.x F.u w dd - proj F.u (fderiv ℝ (gradient f) F.x w)‖ ≤
            K * ‖w‖ := by
      intro w dd hw hdd
      have := tangential_bound (f := f) h hL0 t (x := x) (u := u) (c := c) (δ0 := δ) rfl hcpos hu
        hacc hw hR.hτ0 (by linarith [hR.hLτ0]) hdd
      refine this.trans (mul_le_mul_of_nonneg_right (le_trans ?_ hR.hK) (norm_nonneg _))
      have hτ0 := hR.hτ0
      have e1 : 2 * L ^ 2 * t.τ0 / c ≤ 2 * L ^ 2 * t.τ0 / ε :=
        div_le_div_of_nonneg_left (by positivity) hε hc1.le
      have e2 : 2 * c * δ / t.τ0 + c * δ / t.τ0 ≤ 3 * G * δ / t.τ0 := by
        rw [← add_div]
        apply div_le_div_of_nonneg_right _ hτ0.le
        nlinarith
      linarith
    have hhvp : ∀ v, ‖c • hvpAt f t F v - HTm f F.x F.u β v‖ ≤ 2 * K * ‖v‖ := by
      intro v
      rw [hvpAt_eq]
      exact hvp_bound h t F hu rfl hKtan (hdirw u hune) (hdirw v)
    have hK0 : 0 ≤ K := by
      have := hR.hK
      have : 0 ≤ 2 * L ^ 2 * t.τ0 / ε := by have := hR.hτ0; positivity
      have : 0 ≤ 3 * G * δ / t.τ0 := by have := hR.hG; have := hR.hτ0; positivity
      have : 0 ≤ ρ * t.τ0 := by have := hR.hτ0; positivity
      linarith
    obtain ⟨j, hjJ, hj1, hj2⟩ := exists_guess hc1 hcG hR.hJ hR.hJ1
    have hchat : guessScale t j = 2 ^ j * ε := by simp [guessScale, hR.hεt]
    have hchatG : guessScale t j ≤ 2 * G := by rw [hchat]; linarith
    have hout := guess_outcome (F := F) (chat := guessScale t j) h hL0 hρ0 (c := c) (K := K)
      (δ0 := δ) (β := β) (ε := ε) (ξ := ε / 20) (θ := θ) (G := G) rfl hcpos hu hacc hδ0 hβ
      (by rw [hchat]; exact hj1) (by rw [hchat]; exact hj2) hchatG hK0 hR.hK3 hhvp hγ hr hR.hμ hR.hLA
      hR.ha hR.ha1 hR.htune hR.hη hR.hρr hR.hγr rfl hR.hθ1 hR.hN hR.hslack hR.hfin1 hR.hfin2
      hR.hfin3
    have hmem := fun y hy => mem_epochCands_guess f t x ⟨j, hjJ⟩ (y := y) hy
    rcases hout with ⟨y, hy, hyf⟩ | ⟨y, hy, hyg⟩
    · exact Or.inr ⟨y, hmem y hy, hyf⟩
    · exact Or.inl ⟨y, hmem y hy, hyg⟩
  · -- not curved: short normalized step
    push Not at hcurved
    right
    refine ⟨x - (t.r / 8) • u, by simp [epochCands, hudef], ?_⟩
    have hstep := noncurved_step (f := f) h rfl hcpos hu hacc hr hcurved
    have hδsq : δ ^ 2 ≤ 1 / 4 := by nlinarith [hR.hδ1]
    have hcoef : 0 ≤ 3 / 32 - δ ^ 2 / 16 := by nlinarith
    have : (3 / 32 - δ ^ 2 / 16) * ε * t.r ≤ (3 / 32 - δ ^ 2 / 16) * c * t.r := by
      have := mul_le_mul_of_nonneg_left hc1.le hcoef
      nlinarith
    linarith [hR.hθ2]

end Progress

end

end LongTails.Proofs.ComparisonTrustEpoch
