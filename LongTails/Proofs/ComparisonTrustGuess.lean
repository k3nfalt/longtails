import LongTails.Proofs.ComparisonTrustHvp
import LongTails.Proofs.ComparisonTrustQuadratic

namespace LongTails.Proofs.ComparisonTrustGuess

open OracleTemplate LongTails.Algorithms.ComparisonTrustRegion
  LongTails.Algorithms.GuardedMetricAcceleration
  LongTails.Proofs.ComparisonTrustPlans LongTails.Proofs.ComparisonTrustDirection
  LongTails.Proofs.ComparisonTrustTaylor LongTails.Proofs.ComparisonTrustHvp
  LongTails.Proofs.ComparisonTrustAgd LongTails.Proofs.ComparisonTrustQuadratic
open scoped RealInnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def cmpOf (f : E → ℝ) : E × E → Bool := fun q => decide (f q.1 ≤ f q.2)

def dirAt (f : E → ℝ) (t : Tuning) (y : E) : E := QueryPlan.eval (cmpOf f) (dirPlan t y)

lemma dirAt_eq (f : E → ℝ) (t : Tuning) (y : E) :
    dirAt f t y = dirPure (fun w => decide (f (y - t.τ • w) ≤ f (y + t.τ • w))) t.m :=
  eval_dirPlan _ t y

def hvpAt (f : E → ℝ) (t : Tuning) (F : Frame E) (v : E) : E :=
  QueryPlan.eval (cmpOf f) (hvpPlan t F v)

lemma hvpAt_eq (f : E → ℝ) (t : Tuning) (F : Frame E) (v : E) :
    hvpAt f t F v = hvpValue t F v (dirAt f t (F.x + probeStep t v • v)) := by
  simp only [hvpAt, hvpPlan, QueryPlan.eval_map, hvpValue, dirAt]

def agdPure (f : E → ℝ) (t : Tuning) (F : Frame E) (chat : ℝ) (k : ℕ) : AgdState E :=
  loopPure (fun k s => QueryPlan.eval (cmpOf f) (agdStep t F chat k s)) k 0 ⟨0, 0, fun _ => (0, 0)⟩

lemma eval_agdStep (f : E → ℝ) (t : Tuning) (F : Frame E) (chat : ℝ) (k : ℕ) (s : AgdState E) :
    QueryPlan.eval (cmpOf f) (agdStep t F chat k s) =
      { x := gradientStep t.LA (extrapolate t.a s.x s.z)
          (modelGrad t F chat (extrapolate t.a s.x s.z) (hvpAt f t F (extrapolate t.a s.x s.z)))
        z := centerStep t.a t.μ (extrapolate t.a s.x s.z) s.z
          (modelGrad t F chat (extrapolate t.a s.x s.z) (hvpAt f t F (extrapolate t.a s.x s.z)))
        hist := Function.update s.hist k (s.x, extrapolate t.a s.x s.z) } := by
  simp only [agdStep, QueryPlan.eval_map, hvpAt]

def runOf (f : E → ℝ) (t : Tuning) (F : Frame E) (chat : ℝ) : Run E where
  a := t.a
  μ := t.μ
  L := t.LA
  xs := fun k => (agdPure f t F chat k).x
  zs := fun k => (agdPure f t F chat k).z
  Gs := fun k => modelGrad t F chat (extrapolate t.a (agdPure f t F chat k).x (agdPure f t F chat k).z)
    (hvpAt f t F (extrapolate t.a (agdPure f t F chat k).x (agdPure f t F chat k).z))

lemma agdPure_succ (f : E → ℝ) (t : Tuning) (F : Frame E) (chat : ℝ) (k : ℕ) :
    agdPure f t F chat (k + 1) = QueryPlan.eval (cmpOf f) (agdStep t F chat k (agdPure f t F chat k)) := by
  rw [agdPure, loopPure_succ, zero_add]
  rfl

lemma runOf_valid (f : E → ℝ) (t : Tuning) (F : Frame E) (chat : ℝ) (n : ℕ)
    (ha : 0 < t.a) (ha₁ : t.a ≤ 1) (hμ : 0 < t.μ) (hL : 0 < t.LA) (htune : t.a ^ 2 * t.LA = t.μ) :
    (runOf f t F chat).Valid n := by
  refine ⟨ha, ha₁, hμ, hL, htune, rfl, rfl, fun k _ => ?_⟩
  simp only [runOf, Run.ys, agdPure_succ, eval_agdStep]
  exact ⟨trivial, trivial⟩

lemma agdPure_hist (f : E → ℝ) (t : Tuning) (F : Frame E) (chat : ℝ) (n : ℕ) :
    ∀ j < n, (agdPure f t F chat n).hist j = ((runOf f t F chat).xs j, (runOf f t F chat).ys j) := by
  have key := loopPure_induction (fun k s => QueryPlan.eval (cmpOf f) (agdStep t F chat k s))
    (fun k s => s = agdPure f t F chat k ∧
      ∀ j < k, s.hist j = ((runOf f t F chat).xs j, (runOf f t F chat).ys j))
    ⟨0, 0, fun _ => (0, 0)⟩ ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    (fun k s ⟨hs, hj⟩ => by
      subst hs
      refine ⟨(agdPure_succ f t F chat k).symm, fun j hj' => ?_⟩
      rw [eval_agdStep]
      dsimp only
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with hj' | hj'
      · rw [Function.update_of_ne (by omega)]
        exact hj j hj'
      · subst hj'
        simp only [Function.update_self]
        rfl) n
  exact key.2

omit [FiniteDimensional ℝ E] in
open Classical in
lemma firstFail_cases (t : Tuning) (chat : ℝ) (pairs : List (E × E)) :
    (firstFail t chat pairs = 0 ∧ ∀ p ∈ pairs, passes t chat p.1 p.2) ∨
      (∃ p ∈ pairs, ¬ passes t chat p.1 p.2 ∧ firstFail t chat pairs = p.1) := by
  unfold firstFail
  cases h : pairs.find? (fun p => ¬ passes t chat p.1 p.2) with
  | none =>
    left
    refine ⟨rfl, fun p hp => ?_⟩
    have := List.find?_eq_none.mp h p hp
    simpa using this
  | some p =>
    right
    refine ⟨p, List.mem_of_find?_eq_some h, ?_, rfl⟩
    have := List.find?_some h
    simpa using this

omit [FiniteDimensional ℝ E] in
lemma passes_zero (t : Tuning) (chat : ℝ) (Av : E) : passes t chat 0 Av := by
  simp [passes]

def checks (f : E → ℝ) (t : Tuning) (F : Frame E) (chat : ℝ) : List (E × E) :=
  let s := agdPure f t F chat t.N
  let s' : AgdState E := { s with hist := Function.update s.hist t.N (s.x, s.x) }
  let w := gradientStep t.LA s.x (modelGrad t F chat s.x (hvpAt f t F s.x))
  List.ofFn (fun i : Fin (4 * t.N) => (checkVec s' w i, hvpAt f t F (checkVec s' w i)))

lemma eval_guessPlan (f : E → ℝ) (t : Tuning) (F : Frame E) (chat : ℝ) :
    QueryPlan.eval (cmpOf f) (guessPlan t F chat) =
      { fail := firstFail t chat (checks f t F chat), xN := (agdPure f t F chat t.N).x } := by
  simp only [guessPlan, QueryPlan.eval_bind, QueryPlan.eval_map, QueryPlan.eval_traverse,
    eval_loop, checks, agdPure, hvpAt]

section Model

variable (f : E → ℝ) (x u : E) (α β γ : ℝ)

def HTm : E →L[ℝ] E := model (fderiv ℝ (gradient f) x) u β

def Mm : E →L[ℝ] E := α • HTm f x u β + (2 * γ) • ContinuousLinearMap.id ℝ E

def bm : E := α • gradient f x

variable {f x u α β γ}

lemma Mm_apply (v : E) : Mm f x u α β γ v = α • HTm f x u β v + (2 * γ) • v := by
  simp [Mm]

lemma Mm_symm {L ρ : ℝ} (h : Smooth f L ρ) : (Mm f x u α β γ).toLinearMap.IsSymmetric := by
  intro a b
  simp only [ContinuousLinearMap.coe_coe, Mm_apply, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  have := model_symmetric (h.sym x) u β a b
  simp only [ContinuousLinearMap.coe_coe] at this
  rw [show HTm f x u β = model (fderiv ℝ (gradient f) x) u β from rfl, this]

lemma norm_HTm_le {L ρ : ℝ} (h : Smooth f L ρ) (hL : 0 ≤ L) (hu : ‖u‖ = 1) :
    ‖HTm f x u β‖ ≤ L + |β| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [HTm, model_apply]
  calc ‖fderiv ℝ (gradient f) x v + (β * ⟪u, v⟫) • u‖
      ≤ ‖fderiv ℝ (gradient f) x v‖ + ‖(β * ⟪u, v⟫) • u‖ := norm_add_le _ _
    _ ≤ L * ‖v‖ + |β| * ‖v‖ := by
      refine add_le_add ((ContinuousLinearMap.le_opNorm _ v).trans
        (mul_le_mul_of_nonneg_right (h.hess_norm hL x) (norm_nonneg v))) ?_
      rw [norm_smul, hu, mul_one, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (by simpa [hu] using abs_real_inner_le_norm u v)
        (abs_nonneg β)
    _ = (L + |β|) * ‖v‖ := by ring

lemma norm_Mm_le {L ρ : ℝ} (h : Smooth f L ρ) (hL : 0 ≤ L) (hu : ‖u‖ = 1) (hα0 : 0 ≤ α)
    (hα : α ≤ 2) (hγ : 0 ≤ γ) (hβ : |β| ≤ γ) : ‖Mm f x u α β γ‖ ≤ 2 * L + 4 * γ := by
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hα0,
    abs_of_nonneg (by linarith : 0 ≤ 2 * γ)]
  have h1 := norm_HTm_le (β := β) h hL hu (x := x)
  have h2 : ‖ContinuousLinearMap.id ℝ E‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have : α * ‖HTm f x u β‖ ≤ 2 * (L + |β|) :=
    mul_le_mul hα h1 (norm_nonneg _) (by norm_num)
  nlinarith

lemma grad_split (s : E) :
    α • gradient f (x + s) = qgrad (bm f x α) (Mm f x u α β γ) s -
      (α * β * ⟪u, s⟫) • u - (2 * γ) • s +
        α • (gradient f (x + s) - gradient f x - fderiv ℝ (gradient f) x s) := by
  simp only [qgrad, bm, Mm_apply, HTm, model_apply]
  module

lemma value_split (s : E) :
    quad (bm f x α) (Mm f x u α β γ) s = α * (⟪gradient f x, s⟫ +
      ⟪s, fderiv ℝ (gradient f) x s⟫ / 2) + α * β / 2 * ⟪u, s⟫ ^ 2 + γ * ‖s‖ ^ 2 := by
  simp only [quad, bm, Mm_apply, HTm, model_apply, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq]
  rw [real_inner_comm u s]
  ring

end Model

section Translate

variable {f : E → ℝ} {L ρ : ℝ} {t : Tuning} {F : Frame E} {chat c K β : ℝ}

lemma rayleigh_gap (hcpos : 0 < c) (hcc : c ≤ chat) (hc2 : chat < 2 * c) (hK : 0 ≤ K)
    (hhvp : ∀ v, ‖c • hvpAt f t F v - HTm f F.x F.u β v‖ ≤ 2 * K * ‖v‖) (d : E) :
    |⟪d, chat • hvpAt f t F d + (2 * t.γ) • d⟫ - ⟪d, Mm f F.x F.u (chat / c) β t.γ d⟫| ≤
      4 * K * ‖d‖ ^ 2 := by
  have hα : chat / c ≤ 2 := by rw [div_le_iff₀ hcpos]; linarith
  have hα0 : 0 ≤ chat / c := div_nonneg (by linarith) hcpos.le
  have heq : ⟪d, chat • hvpAt f t F d + (2 * t.γ) • d⟫ - ⟪d, Mm f F.x F.u (chat / c) β t.γ d⟫ =
      (chat / c) * ⟪d, c • hvpAt f t F d - HTm f F.x F.u β d⟫ := by
    rw [Mm_apply, ← inner_sub_right, ← real_inner_smul_right]
    congr 1
    rw [smul_sub, smul_smul, div_mul_cancel₀ _ hcpos.ne']
    abel
  rw [heq, abs_mul, abs_of_nonneg hα0]
  calc _ ≤ chat / c * (‖d‖ * (2 * K * ‖d‖)) := by
        gcongr
        exact (abs_real_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_left (hhvp d) (norm_nonneg _))
    _ ≤ 2 * (‖d‖ * (2 * K * ‖d‖)) := by gcongr
    _ = 4 * K * ‖d‖ ^ 2 := by ring

lemma check_pass (hcpos : 0 < c) (hcc : c ≤ chat) (hc2 : chat < 2 * c) (hK : 0 ≤ K)
    (hK3 : K ≤ 3 * t.η)
    (hhvp : ∀ v, ‖c • hvpAt f t F v - HTm f F.x F.u β v‖ ≤ 2 * K * ‖v‖) {d : E}
    (hp : passes t chat d (hvpAt f t F d)) :
    t.μ * ‖d‖ ^ 2 ≤ ⟪d, Mm f F.x F.u (chat / c) β t.γ d⟫ := by
  have := abs_le.mp (rayleigh_gap hcpos hcc hc2 hK hhvp d)
  unfold passes at hp
  have : 4 * K * ‖d‖ ^ 2 ≤ 12 * t.η * ‖d‖ ^ 2 := by
    have := sq_nonneg ‖d‖
    nlinarith
  nlinarith

lemma check_fail (hcpos : 0 < c) (hcc : c ≤ chat) (hc2 : chat < 2 * c) (hK : 0 ≤ K)
    (hK3 : K ≤ 3 * t.η)
    (hhvp : ∀ v, ‖c • hvpAt f t F v - HTm f F.x F.u β v‖ ≤ 2 * K * ‖v‖) {d : E}
    (hp : ¬ passes t chat d (hvpAt f t F d)) :
    ⟪d, Mm f F.x F.u (chat / c) β t.γ d⟫ < (t.μ + 24 * t.η) * ‖d‖ ^ 2 := by
  have := abs_le.mp (rayleigh_gap hcpos hcc hc2 hK hhvp d)
  unfold passes at hp
  push Not at hp
  have : 4 * K * ‖d‖ ^ 2 ≤ 12 * t.η * ‖d‖ ^ 2 := by
    have := sq_nonneg ‖d‖
    nlinarith
  nlinarith

lemma grad_error (hcpos : 0 < c) (hcc : c ≤ chat) (hc2 : chat < 2 * c) {δ0 : ℝ}
    (hδ0 : ‖F.u - c⁻¹ • gradient f F.x‖ ≤ δ0)
    (hhvp : ∀ v, ‖c • hvpAt f t F v - HTm f F.x F.u β v‖ ≤ 2 * K * ‖v‖) (y : E) :
    ‖modelGrad t F chat y (hvpAt f t F y) - qgrad (bm f F.x (chat / c)) (Mm f F.x F.u (chat / c) β t.γ) y‖ ≤
      4 * K * ‖y‖ + chat * δ0 := by
  have hα : chat / c ≤ 2 := by rw [div_le_iff₀ hcpos]; linarith
  have hα0 : 0 ≤ chat / c := div_nonneg (by linarith) hcpos.le
  have heq : modelGrad t F chat y (hvpAt f t F y) -
      qgrad (bm f F.x (chat / c)) (Mm f F.x F.u (chat / c) β t.γ) y =
      chat • (F.u - c⁻¹ • gradient f F.x) + (chat / c) • (c • hvpAt f t F y - HTm f F.x F.u β y) := by
    simp only [modelGrad, qgrad, bm, Mm_apply, smul_sub, smul_smul]
    rw [div_mul_cancel₀ _ hcpos.ne', div_eq_mul_inv]
    module
  rw [heq]
  calc _ ≤ ‖chat • (F.u - c⁻¹ • gradient f F.x)‖ +
        ‖(chat / c) • (c • hvpAt f t F y - HTm f F.x F.u β y)‖ := norm_add_le _ _
    _ ≤ chat * δ0 + 2 * (2 * K * ‖y‖) := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (by linarith : 0 ≤ chat), abs_of_nonneg hα0]
      gcongr
      · linarith
      · exact hhvp y
    _ = 4 * K * ‖y‖ + chat * δ0 := by ring

end Translate

section Outcomes

variable {f : E → ℝ} {L ρ : ℝ} {x u : E} {α β γ : ℝ}

lemma nc_outcome (h : Smooth f L ρ) (hu : ‖u‖ = 1) (hα1 : 1 ≤ α) (hα2 : α ≤ 2)
    {η r : ℝ} (hr : 0 < r) (hγ : 0 < γ) (hη : 24 * η ≤ γ / 8) (hβ : |β| ≤ γ / 16)
    (hρr : ρ * r = γ / 4) {d : E} (hd : d ≠ 0)
    (hfail : ⟪d, Mm f x u α β γ d⟫ < (γ + 24 * η) * ‖d‖ ^ 2) :
    min (f (x + (r * ‖d‖⁻¹) • d)) (f (x - (r * ‖d‖⁻¹) • d)) ≤ f x - 7 / 48 * γ * r ^ 2 := by
  have hdn : 0 < ‖d‖ := norm_pos_iff.mpr hd
  rw [Mm_apply, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq] at hfail
  have hHT : ⟪d, HTm f x u β d⟫ ≤ -(7 / 16 * γ) * ‖d‖ ^ 2 := by
    have h1 : α * ⟪d, HTm f x u β d⟫ < (-γ + 24 * η) * ‖d‖ ^ 2 := by linarith
    have hneg : (-γ + 24 * η) * ‖d‖ ^ 2 ≤ -(7 / 8 * γ) * ‖d‖ ^ 2 := by
      have := sq_nonneg ‖d‖
      nlinarith
    by_contra hcon
    push Not at hcon
    have : -(7 / 16 * γ) * ‖d‖ ^ 2 * α ≤ ⟪d, HTm f x u β d⟫ * α :=
      mul_le_mul_of_nonneg_right hcon.le (by linarith)
    have : -(7 / 8 * γ) * ‖d‖ ^ 2 ≤ -(7 / 16 * γ) * ‖d‖ ^ 2 * α := by
      have : 0 ≤ γ * ‖d‖ ^ 2 := by positivity
      nlinarith
    nlinarith
  have hH : ⟪d, fderiv ℝ (gradient f) x d⟫ ≤ -(3 / 8 * γ) * ‖d‖ ^ 2 := by
    have hm : ⟪d, HTm f x u β d⟫ = ⟪d, fderiv ℝ (gradient f) x d⟫ + β * ⟪u, d⟫ ^ 2 := by
      simp only [HTm, model_apply, inner_add_right, real_inner_smul_right]
      rw [real_inner_comm u d]
      ring
    have hud : ⟪u, d⟫ ^ 2 ≤ ‖d‖ ^ 2 := by
      have := abs_real_inner_le_norm u d
      rw [hu, one_mul] at this
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    have : -(γ / 16) * ‖d‖ ^ 2 ≤ β * ⟪u, d⟫ ^ 2 := by
      have := neg_abs_le β
      have h0 : 0 ≤ ⟪u, d⟫ ^ 2 := sq_nonneg _
      nlinarith
    linarith
  set e := (r * ‖d‖⁻¹) • d
  have hen : ‖e‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), mul_assoc,
      inv_mul_cancel₀ hdn.ne', mul_one]
  have heH : ⟪e, fderiv ℝ (gradient f) x e⟫ ≤ -(3 / 8 * γ) * r ^ 2 := by
    simp only [e, map_smul, real_inner_smul_left, real_inner_smul_right]
    have hk : (r * ‖d‖⁻¹) * (r * ‖d‖⁻¹) * ‖d‖ ^ 2 = r ^ 2 := by field_simp
    have hpos : 0 ≤ (r * ‖d‖⁻¹) * (r * ‖d‖⁻¹) := by positivity
    have := mul_le_mul_of_nonneg_left hH hpos
    nlinarith
  have hs := abs_le.mp (h.symmetric_taylor x e)
  rw [hen] at hs
  have hr3 : ρ * r ^ 3 / 3 = γ * r ^ 2 / 12 := by
    have : ρ * r ^ 3 = (ρ * r) * r ^ 2 := by ring
    rw [this, hρr]
    ring
  rw [min_le_iff]
  by_contra hcon
  push Not at hcon
  nlinarith [hcon.1, hcon.2]

lemma b1_outcome (h : Smooth f L ρ) (hρ : 0 ≤ ρ) (hu : ‖u‖ = 1) (hα1 : 1 ≤ α) {r ξ ε : ℝ}
    (hγ : 0 ≤ γ) (hβ : |β| ≤ γ / 16) (hρr : ρ * r = γ / 4) (hγr : γ * r = ε / 4)
    (hξ : ξ ≤ ε / 20) {s : E} (hs : ‖s‖ ≤ r)
    (hg : ‖qgrad (bm f x α) (Mm f x u α β γ) s‖ ≤ ξ) : ‖gradient f (x + s)‖ ≤ ε := by
  have hsplit := grad_split (f := f) (u := u) (β := β) (γ := γ) s (x := x) (α := α)
  have he := h.grad_taylor x s
  have hα0 : 0 < α := by linarith
  have hn : α * ‖gradient f (x + s)‖ ≤ ξ + α * |β| * ‖s‖ + 2 * γ * ‖s‖ +
      α * (ρ * ‖s‖ ^ 2 / 2) := by
    have := congrArg norm hsplit
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hα0] at this
    rw [this]
    calc _ ≤ ‖qgrad (bm f x α) (Mm f x u α β γ) s‖ + ‖(α * β * ⟪u, s⟫) • u‖ +
          ‖(2 * γ) • s‖ + ‖α • (gradient f (x + s) - gradient f x -
            fderiv ℝ (gradient f) x s)‖ := by
          have e1 := norm_add_le (qgrad (bm f x α) (Mm f x u α β γ) s - (α * β * ⟪u, s⟫) • u -
            (2 * γ) • s) (α • (gradient f (x + s) - gradient f x - fderiv ℝ (gradient f) x s))
          have e2 := norm_sub_le (qgrad (bm f x α) (Mm f x u α β γ) s - (α * β * ⟪u, s⟫) • u)
            ((2 * γ) • s)
          have e3 := norm_sub_le (qgrad (bm f x α) (Mm f x u α β γ) s) ((α * β * ⟪u, s⟫) • u)
          linarith
      _ ≤ _ := by
        rw [norm_smul, norm_smul, norm_smul, hu, mul_one, Real.norm_eq_abs, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_pos hα0, abs_of_nonneg (by linarith : 0 ≤ 2 * γ), abs_mul,
          abs_mul, abs_of_pos hα0]
        gcongr
        · simpa [hu] using abs_real_inner_le_norm u s
  have hsr2 : ‖s‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hs 2
  have hfin : ‖gradient f (x + s)‖ ≤ ξ + |β| * ‖s‖ + 2 * γ * ‖s‖ + ρ * ‖s‖ ^ 2 / 2 := by
    have : ξ + α * |β| * ‖s‖ + 2 * γ * ‖s‖ + α * (ρ * ‖s‖ ^ 2 / 2) ≤
        α * (ξ + |β| * ‖s‖ + 2 * γ * ‖s‖ + ρ * ‖s‖ ^ 2 / 2) := by
      have h0 : 0 ≤ ξ := le_trans (norm_nonneg _) hg
      have : 0 ≤ 2 * γ * ‖s‖ := by positivity
      nlinarith
    have := hn.trans this
    exact le_of_mul_le_mul_left this hα0
  have h1 : |β| * ‖s‖ ≤ γ / 16 * r := mul_le_mul hβ hs (norm_nonneg _) (by linarith)
  have h2 : 2 * γ * ‖s‖ ≤ 2 * γ * r := by gcongr
  have h3 : ρ * ‖s‖ ^ 2 / 2 ≤ ρ * r ^ 2 / 2 := by gcongr
  have h4 : ρ * r ^ 2 = γ * r / 4 := by
    have : ρ * r ^ 2 = (ρ * r) * r := by ring
    rw [this, hρr]
    ring
  nlinarith

lemma b2_outcome (h : Smooth f L ρ) (hu : ‖u‖ = 1) (hα1 : 1 ≤ α) (hα2 : α ≤ 2) {r ξ : ℝ}
    (hr : 0 < r) (hγ : 0 < γ) (hβ : |β| ≤ γ / 16) (hρr : ρ * r = γ / 4) (hξ : ξ ≤ γ * r / 4)
    {xN : E} (hxN : r < ‖xN‖)
    (hcheck : γ * ‖xN‖ ^ 2 ≤ ⟪xN, Mm f x u α β γ xN⟫)
    (hg : ‖qgrad (bm f x α) (Mm f x u α β γ) xN‖ ≤ ξ) :
    f (x + (min 1 (r * ‖xN‖⁻¹)) • xN) ≤ f x - γ * r ^ 2 / 2 := by
  have hxn : 0 < ‖xN‖ := lt_trans hr hxN
  have hmin : min 1 (r * ‖xN‖⁻¹) = r * ‖xN‖⁻¹ := by
    apply min_eq_right
    rw [← div_eq_mul_inv, div_le_one hxn]
    exact hxN.le
  rw [hmin]
  set τ := r * ‖xN‖⁻¹
  have hτ0 : 0 ≤ τ := by positivity
  have hτ1 : τ ≤ 1 := by rw [← hmin]; exact min_le_left _ _
  have hτn : τ * ‖xN‖ = r := by simp only [τ]; field_simp
  have hpos : 0 ≤ ⟪xN, Mm f x u α β γ xN⟫ := le_trans (by positivity) hcheck
  have hseg := quad_segment (b := bm f x α) hτ0 hτ1 hpos
  have hval := quad_value_grad (b := bm f x α) (M := Mm f x u α β γ) xN
  have hgx : ⟪qgrad (bm f x α) (Mm f x u α β γ) xN, xN⟫ ≤ ξ * ‖xN‖ :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hg (norm_nonneg _))
  have hq : quad (bm f x α) (Mm f x u α β γ) (τ • xN) ≤ ξ * r - γ * r ^ 2 / 2 := by
    have : quad (bm f x α) (Mm f x u α β γ) xN ≤ ξ * ‖xN‖ - γ * ‖xN‖ ^ 2 / 2 := by
      rw [hval]; linarith
    have h2 := mul_le_mul_of_nonneg_left this hτ0
    have : τ * (ξ * ‖xN‖ - γ * ‖xN‖ ^ 2 / 2) = ξ * r - γ * r * ‖xN‖ / 2 := by
      rw [← hτn]; ring
    have : γ * r * r ≤ γ * r * ‖xN‖ := by
      have := mul_le_mul_of_nonneg_left hxN.le (by positivity : 0 ≤ γ * r)
      linarith
    have hseg' : quad (bm f x α) (Mm f x u α β γ) (τ • xN) ≤
        τ * quad (bm f x α) (Mm f x u α β γ) xN := hseg
    linarith
  have hvs := value_split (f := f) (u := u) (β := β) (γ := γ) (α := α) (x := x) (τ • xN)
  have hnorm : ‖τ • xN‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ0, hτn]
  rw [hnorm] at hvs
  have htay := abs_le.mp (h.value_taylor x (τ • xN))
  rw [hnorm] at htay
  have hud : β * ⟪u, τ • xN⟫ ^ 2 ≥ -(γ / 16) * r ^ 2 := by
    have : ⟪u, τ • xN⟫ ^ 2 ≤ r ^ 2 := by
      have := abs_real_inner_le_norm u (τ • xN)
      rw [hu, one_mul, hnorm] at this
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    have h0 : 0 ≤ ⟪u, τ • xN⟫ ^ 2 := sq_nonneg _
    have e1 := mul_le_mul_of_nonneg_right (neg_abs_le β) h0
    have e2 := mul_le_mul_of_nonneg_right hβ h0
    have e3 := mul_le_mul_of_nonneg_left this (by linarith : 0 ≤ γ / 16)
    linarith
  have hr3 : ρ * r ^ 3 / 6 = γ * r ^ 2 / 24 := by
    have : ρ * r ^ 3 = (ρ * r) * r ^ 2 := by ring
    rw [this, hρr]
    ring
  have hlin : ⟪gradient f x, τ • xN⟫ + ⟪τ • xN, fderiv ℝ (gradient f) x (τ • xN)⟫ / 2 ≤
      -(5 / 8) * γ * r ^ 2 + γ / 32 * r ^ 2 := by
    have hA : α * (⟪gradient f x, τ • xN⟫ + ⟪τ • xN, fderiv ℝ (gradient f) x (τ • xN)⟫ / 2) ≤
        -(5 / 4) * γ * r ^ 2 + α * (γ / 32) * r ^ 2 := by
      have hξr : ξ * r ≤ γ * r / 4 * r := mul_le_mul_of_nonneg_right hξ hr.le
      have hαβ := mul_le_mul_of_nonneg_left hud (by linarith : 0 ≤ α)
      linarith
    by_contra hcon
    push Not at hcon
    have h1 : α * (-(5 / 8) * γ * r ^ 2 + γ / 32 * r ^ 2) <
        α * (⟪gradient f x, τ • xN⟫ + ⟪τ • xN, fderiv ℝ (gradient f) x (τ • xN)⟫ / 2) :=
      mul_lt_mul_of_pos_left hcon (by linarith)
    have h2 : α * (γ * r ^ 2) ≤ 2 * (γ * r ^ 2) :=
      mul_le_mul_of_nonneg_right hα2 (by positivity)
    linarith
  have : f (x + τ • xN) - f x ≤ -(5 / 8) * γ * r ^ 2 + γ / 32 * r ^ 2 + γ * r ^ 2 / 24 := by
    linarith [htay.2]
  have : 0 ≤ γ * r ^ 2 := by positivity
  linarith

end Outcomes

section Combine

variable {f : E → ℝ} {L ρ : ℝ} {t : Tuning} {F : Frame E} {chat : ℝ}

lemma checkVec_spec (f : E → ℝ) (t : Tuning) (F : Frame E) (chat : ℝ) (w : E) {k : ℕ}
    (hk : k < t.N) :
    let s := agdPure f t F chat t.N
    let s' : AgdState E := { s with hist := Function.update s.hist t.N (s.x, s.x) }
    let R := runOf f t F chat
    checkVec s' w (4 * k) = R.xs k - R.ys k ∧ checkVec s' w (4 * k + 1) = R.ys k ∧
      checkVec s' w (4 * k + 2) = R.xs (k + 1) ∧ checkVec s' w (4 * k + 3) = w - R.ys k := by
  intro s s' R
  have hh := agdPure_hist f t F chat t.N
  have hk' : s'.hist k = (R.xs k, R.ys k) := by
    simp only [s', Function.update_of_ne (show k ≠ t.N by omega)]
    exact hh k hk
  have hk1 : (s'.hist (k + 1)).1 = R.xs (k + 1) := by
    by_cases hkN : k + 1 = t.N
    · simp only [s', hkN, Function.update_self]
      rfl
    · simp only [s', Function.update_of_ne hkN]
      rw [hh (k + 1) (by omega)]
  have d0 : 4 * k / 4 = k := by omega
  have d1 : (4 * k + 1) / 4 = k := by omega
  have d2 : (4 * k + 2) / 4 = k := by omega
  have d3 : (4 * k + 3) / 4 = k := by omega
  have m0 : 4 * k % 4 = 0 := by omega
  have m1 : (4 * k + 1) % 4 = 1 := by omega
  have m2 : (4 * k + 2) % 4 = 2 := by omega
  have m3 : (4 * k + 3) % 4 = 3 := by omega
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [checkVec, d0, d1, d2, d3, m0, m1, m2, m3, hk', hk1]

lemma mem_checks (f : E → ℝ) (t : Tuning) (F : Frame E) (chat : ℝ) {i : ℕ} (hi : i < 4 * t.N) :
    let s := agdPure f t F chat t.N
    let s' : AgdState E := { s with hist := Function.update s.hist t.N (s.x, s.x) }
    let w := gradientStep t.LA s.x (modelGrad t F chat s.x (hvpAt f t F s.x))
    (checkVec s' w i, hvpAt f t F (checkVec s' w i)) ∈ checks f t F chat := by
  intro s s' w
  simp only [checks]
  exact List.mem_ofFn.mpr ⟨⟨i, hi⟩, rfl⟩

lemma of_mem_checks (f : E → ℝ) (t : Tuning) (F : Frame E) (chat : ℝ) {p : E × E}
    (hp : p ∈ checks f t F chat) : p.2 = hvpAt f t F p.1 := by
  simp only [checks, List.mem_ofFn] at hp
  obtain ⟨i, rfl⟩ := hp
  rfl

set_option maxHeartbeats 800000 in
theorem guess_outcome (h : Smooth f L ρ) (hL0 : 0 ≤ L) (hρ : 0 ≤ ρ) {c K δ0 β ε ξ θ G : ℝ}
    (hc : ‖gradient f F.x‖ = c) (hcpos : 0 < c) (hu : ‖F.u‖ = 1)
    (hδ0 : ‖F.u - c⁻¹ • gradient f F.x‖ ≤ δ0) (hδ0nn : 0 ≤ δ0)
    (hβ : |β| ≤ t.γ / 16) (hcc : c ≤ chat) (hc2 : chat < 2 * c) (hchatG : chat ≤ 2 * G) (hK : 0 ≤ K)
    (hK3 : K ≤ 3 * t.η)
    (hhvp : ∀ v, ‖c • hvpAt f t F v - HTm f F.x F.u β v‖ ≤ 2 * K * ‖v‖)
    (hγ : 0 < t.γ) (hr : 0 < t.r) (hμ : t.μ = t.γ) (hLA : t.LA = 2 * L + 4 * t.γ)
    (ha : 0 < t.a) (ha1 : t.a ≤ 1) (htune : t.a ^ 2 * t.LA = t.μ)
    (hη : 24 * t.η ≤ t.γ / 8) (hρr : ρ * t.r = t.γ / 4) (hγr : t.γ * t.r = ε / 4)
    (hξ : ξ = ε / 20) (hθ : θ ≤ t.γ * t.r ^ 2 / 25) (hN : 1 ≤ t.N)
    (hslack : 8 * slack (runOf f t F chat) (2 * G) t.r (4 * K) (2 * G * δ0) ≤ t.a * t.μ * t.r ^ 2)
    (hfin1 : (1 - t.a) ^ t.N * (2 * G * wmax (runOf f t F chat) (2 * G) t.r (4 * K) (2 * G * δ0) +
      (t.LA + t.μ) / 2 * wmax (runOf f t F chat) (2 * G) t.r (4 * K) (2 * G * δ0) ^ 2) ≤
        ξ ^ 2 / (32 * t.LA))
    (hfin2 : 5 * slack (runOf f t F chat) (2 * G) t.r (4 * K) (2 * G * δ0) / t.a ≤ ξ ^ 2 / (32 * t.LA))
    (hfin3 : slackR (runOf f t F chat) (2 * G) t.r (4 * K) (2 * G * δ0) ≤ ξ / 2) :
    (∃ y ∈ guessCands t F.x (QueryPlan.eval (cmpOf f) (guessPlan t F chat)), f y ≤ f F.x - θ) ∨
      (∃ y ∈ guessCands t F.x (QueryPlan.eval (cmpOf f) (guessPlan t F chat)),
        ‖gradient f y‖ ≤ ε) := by
  rw [eval_guessPlan]
  set α := chat / c with hαdef
  have hα1 : 1 ≤ α := by rw [hαdef, le_div_iff₀ hcpos]; linarith
  have hα2 : α ≤ 2 := by rw [hαdef, div_le_iff₀ hcpos]; linarith
  have hθγ : θ ≤ t.γ * t.r ^ 2 / 25 := hθ
  have hγr2 : 0 < t.γ * t.r ^ 2 := by positivity
  have hδG : chat * δ0 ≤ 2 * G * δ0 := mul_le_mul_of_nonneg_right hchatG hδ0nn
  rcases firstFail_cases t chat (checks f t F chat) with ⟨hzero, hall⟩ | ⟨p, hp, hfail, hff⟩
  · -- all checks pass
    set R := runOf f t F chat
    have hv := runOf_valid f t F chat t.N ha ha1 (by rw [hμ]; exact hγ) (by rw [hLA]; positivity) htune
    have hpass : ∀ i < 4 * t.N, passes t chat (checkVec { agdPure f t F chat t.N with
        hist := Function.update (agdPure f t F chat t.N).hist t.N
          ((agdPure f t F chat t.N).x, (agdPure f t F chat t.N).x) }
        (gradientStep t.LA (agdPure f t F chat t.N).x (modelGrad t F chat (agdPure f t F chat t.N).x
          (hvpAt f t F (agdPure f t F chat t.N).x))) i)
        (hvpAt f t F (checkVec { agdPure f t F chat t.N with
        hist := Function.update (agdPure f t F chat t.N).hist t.N
          ((agdPure f t F chat t.N).x, (agdPure f t F chat t.N).x) }
        (gradientStep t.LA (agdPure f t F chat t.N).x (modelGrad t F chat (agdPure f t F chat t.N).x
          (hvpAt f t F (agdPure f t F chat t.N).x))) i)) := fun i hi =>
      hall _ (mem_checks f t F chat hi)
    set w := gradientStep t.LA (agdPure f t F chat t.N).x (modelGrad t F chat (agdPure f t F chat t.N).x
      (hvpAt f t F (agdPure f t F chat t.N).x)) with hw
    have hcv := fun k (hk : k < t.N) => checkVec_spec f t F chat w hk
    have tp := fun d (hd : passes t chat d (hvpAt f t F d)) =>
      check_pass (F := F) (β := β) hcpos hcc hc2 hK hK3 hhvp hd
    have hgerr := grad_error (F := F) (β := β) hcpos hcc hc2 hδ0 hhvp
    have hbnd : Bounds R (bm f F.x α) (Mm f F.x F.u α β t.γ) t.N (2 * G) (4 * K) (2 * G * δ0) := by
      have hG0 : 0 ≤ G := by linarith
      refine ⟨hv, Mm_symm h, ?_, ?_, by linarith, by positivity, by positivity, ?_, ?_, ?_, ?_⟩
      · show ‖Mm f F.x F.u α β t.γ‖ ≤ t.LA
        rw [hLA]
        exact norm_Mm_le h hL0 hu (by linarith) hα2 hγ.le (by linarith [abs_nonneg β])
      · show ‖α • gradient f F.x‖ ≤ 2 * G
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith), hc, hαdef,
          div_mul_cancel₀ _ hcpos.ne']
        exact hchatG
      · intro k hk
        exact (hgerr (R.ys k)).trans (by linarith)
      · intro k hk
        have := tp _ (by have := hpass (4 * k) (by omega); rwa [(hcv k hk).1] at this)
        exact this
      · intro k hk
        have := tp _ (by have := hpass (4 * k + 1) (by omega); rwa [(hcv k hk).2.1] at this)
        exact this
      · intro k hk
        have := tp _ (by have := hpass (4 * k + 2) (by omega); rwa [(hcv k hk).2.2.1] at this)
        exact this
    have hc4 : ∀ k < t.N, R.μ * ‖gradientStep R.L (R.xs t.N)
        (modelGrad t F chat (R.xs t.N) (hvpAt f t F (R.xs t.N))) - R.ys k‖ ^ 2 ≤
        ⟪gradientStep R.L (R.xs t.N) (modelGrad t F chat (R.xs t.N) (hvpAt f t F (R.xs t.N))) -
          R.ys k, Mm f F.x F.u α β t.γ (gradientStep R.L (R.xs t.N)
            (modelGrad t F chat (R.xs t.N) (hvpAt f t F (R.xs t.N))) - R.ys k)⟫ := by
      intro k hk
      have := tp _ (by have := hpass (4 * k + 3) (by omega); rwa [(hcv k hk).2.2.2] at this)
      exact this
    obtain ⟨hxN, hq, hGN⟩ := final_grad hr hbnd (by
        show 8 * slack R (2 * G) t.r (4 * K) (2 * G * δ0) ≤ R.a * R.μ * t.r ^ 2
        exact hslack) ((hgerr _).trans (by linarith)) hc4
    have hLApos : 0 < t.LA := by rw [hLA]; positivity
    have hξ0 : 0 ≤ ξ := by rw [hξ]; have := mul_pos hγ hr; linarith
    have hGN2 : ‖modelGrad t F chat (R.xs t.N) (hvpAt f t F (R.xs t.N))‖ ^ 2 ≤ (ξ / 2) ^ 2 := by
      have hGN' : ‖modelGrad t F chat (R.xs t.N) (hvpAt f t F (R.xs t.N))‖ ^ 2 ≤
          2 * t.LA * ((1 - t.a) ^ t.N * (2 * G * wmax R (2 * G) t.r (4 * K) (2 * G * δ0) +
            (t.LA + t.μ) / 2 * wmax R (2 * G) t.r (4 * K) (2 * G * δ0) ^ 2) +
              5 * slack R (2 * G) t.r (4 * K) (2 * G * δ0) / t.a) := hGN
      have : 2 * t.LA * (ξ ^ 2 / (32 * t.LA) + ξ ^ 2 / (32 * t.LA)) = ξ ^ 2 / 8 := by
        field_simp
        ring
      have h1 : 2 * t.LA * ((1 - t.a) ^ t.N * (2 * G * wmax R (2 * G) t.r (4 * K) (2 * G * δ0) +
          (t.LA + t.μ) / 2 * wmax R (2 * G) t.r (4 * K) (2 * G * δ0) ^ 2) +
            5 * slack R (2 * G) t.r (4 * K) (2 * G * δ0) / t.a) ≤
          2 * t.LA * (ξ ^ 2 / (32 * t.LA) + ξ ^ 2 / (32 * t.LA)) := by
        gcongr
      linarith [sq_nonneg ξ]
    have hGNb : ‖modelGrad t F chat (R.xs t.N) (hvpAt f t F (R.xs t.N))‖ ≤ ξ / 2 :=
      (pow_le_pow_iff_left₀ (norm_nonneg _) (by linarith) (by norm_num)).mp hGN2
    have hqx : ‖qgrad (bm f F.x α) (Mm f F.x F.u α β t.γ) (R.xs t.N)‖ ≤ ξ := by
      linarith only [hq, hfin3, hGNb]
    by_cases hsmall : ‖R.xs t.N‖ ≤ t.r
    · right
      refine ⟨F.x + (agdPure f t F chat t.N).x, by simp [guessCands], ?_⟩
      exact b1_outcome h hρ hu hα1 hγ.le hβ hρr hγr (by rw [hξ]) hsmall hqx
    · left
      push Not at hsmall
      refine ⟨F.x + (min 1 (t.r * ‖(agdPure f t F chat t.N).x‖⁻¹)) • (agdPure f t F chat t.N).x,
        by simp [guessCands], ?_⟩
      have hchk : t.γ * ‖R.xs t.N‖ ^ 2 ≤ ⟪R.xs t.N, Mm f F.x F.u α β t.γ (R.xs t.N)⟫ := by
        have := hbnd.c3 (t.N - 1) (by omega)
        rw [Nat.sub_add_cancel hN] at this
        rwa [show R.μ = t.γ from hμ] at this
      have := b2_outcome h hu hα1 hα2 hr hγ hβ hρr
        (by rw [hξ]; have := mul_pos hγ hr; linarith) hsmall hchk hqx
      exact this.trans (by linarith only [hθγ, hγr2])
  · -- a check fails
    left
    have hp2 := of_mem_checks f t F chat hp
    rw [hp2] at hfail
    have hd0 : p.1 ≠ 0 := by
      intro h0
      rw [h0] at hfail
      exact hfail (passes_zero t chat _)
    have hf := check_fail (F := F) (β := β) hcpos hcc hc2 hK hK3 hhvp hfail
    rw [hμ] at hf
    have hnc := nc_outcome h hu hα1 hα2 hr hγ hη (by linarith) hρr hd0 hf
    have hnc' : min (f (F.x + (t.r * ‖p.1‖⁻¹) • p.1)) (f (F.x - (t.r * ‖p.1‖⁻¹) • p.1)) ≤
        f F.x - θ := by linarith only [hnc, hθγ, hγr2]
    rcases min_le_iff.mp hnc' with h1 | h1
    · exact ⟨_, by simp [guessCands, hff], h1⟩
    · exact ⟨_, by simp [guessCands, hff], h1⟩

end Combine

end

end LongTails.Proofs.ComparisonTrustGuess
