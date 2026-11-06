import LongTails.Proofs.ConstrainedSaddlePerturbation
import LongTails.Algorithms.Extragradient
import LongTails.Proofs.PLMinimaxTuning

open scoped RealInnerProductSpace

namespace LongTails.Proofs.ConstrainedSaddleInner

open OracleTemplate.SaddlePoint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma closed_project_spec {C : Set E} (hne : C.Nonempty) (hcl : IsClosed C)
    (hc : Convex ℝ C) (x : E) :
    project C x ∈ C ∧ ∀ u ∈ C, ⟪x - project C x, u - project C x⟫ ≤ 0 := by
  have h := exists_norm_eq_iInf_of_complete_convex hne hcl.isComplete hc x
  rw [project, dite_eq_left h]
  exact ⟨h.choose_spec.1,
    (norm_eq_iInf_iff_real_inner_le_zero hc h.choose_spec.1).mp h.choose_spec.2⟩

lemma closed_project_inequality {C : Set E} (hne : C.Nonempty) (hcl : IsClosed C)
    (hc : Convex ℝ C) (η : ℝ) (z g u : E) (hu : u ∈ C) :
    2 * η * ⟪g, project C (z - η • g) - u⟫ ≤
      ‖z - u‖ ^ 2 - ‖project C (z - η • g) - u‖ ^ 2 -
      ‖z - project C (z - η • g)‖ ^ 2 := by
  let v := project C (z - η • g)
  have h := (closed_project_spec hne hcl hc (z - η • g)).2 u hu
  change ⟪z - η • g - v, u - v⟫ ≤ 0 at h
  have he : z - η • g - v = (z - v) - η • g := by module
  have hn : z - u = (z - v) + (v - u) := by module
  rw [he, inner_sub_left, inner_smul_left, starRingEnd_apply, star_trivial] at h
  change 2 * η * ⟪g, v - u⟫ ≤ ‖z - u‖ ^ 2 - ‖v - u‖ ^ 2 - ‖z - v‖ ^ 2
  rw [hn, norm_add_sq_real]
  have hi : u - v = -(v - u) := by module
  rw [hi, inner_neg_right, inner_neg_right] at h
  linarith

lemma extragradient_energy {C : Set E} (hne : C.Nonempty) (hcl : IsClosed C)
    (hc : Convex ℝ C) (G : E → E) {η M : ℝ} (hη : 0 ≤ η)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ M * ‖x - y‖) (w s : E) (hs : s ∈ C) :
    let u := project C (w - η • G w)
    let v := project C (w - η • G u)
    ‖v - s‖ ^ 2 ≤ ‖w - s‖ ^ 2 - (1 - 2 * η ^ 2 * M ^ 2) * ‖w - u‖ ^ 2 -
      ‖u - v‖ ^ 2 / 2 - 2 * η * ⟪G u, u - s⟫ := by
  dsimp only
  let u := project C (w - η • G w)
  let v := project C (w - η • G u)
  have hv := (closed_project_spec hne hcl hc (w - η • G u)).1
  have h1 := closed_project_inequality hne hcl hc η w (G u) s hs
  have h2 := closed_project_inequality hne hcl hc η w (G w) v hv
  change 2 * η * ⟪G u, v - s⟫ ≤ ‖w - s‖ ^ 2 - ‖v - s‖ ^ 2 - ‖w - v‖ ^ 2 at h1
  change 2 * η * ⟪G w, u - v⟫ ≤ ‖w - v‖ ^ 2 - ‖u - v‖ ^ 2 - ‖w - u‖ ^ 2 at h2
  have hl := hlip u w
  rw [norm_sub_rev u w] at hl
  have hi := real_inner_le_norm (G u - G w) (u - v)
  have hm := mul_le_mul_of_nonneg_right hl (norm_nonneg (u - v))
  have he : 2 * η * ⟪G u - G w, u - v⟫ ≤
      2 * η ^ 2 * M ^ 2 * ‖w - u‖ ^ 2 + ‖u - v‖ ^ 2 / 2 := by
    have hh := mul_le_mul_of_nonneg_left (hi.trans hm) (by positivity : 0 ≤ 2 * η)
    nlinarith [sq_nonneg (2 * η * M * ‖w - u‖ - ‖u - v‖)]
  have hid : ⟪G u, u - s⟫ = ⟪G u, v - s⟫ + ⟪G u, u - v⟫ := by
    rw [← inner_add_right]
    congr 1
    abel
  rw [inner_sub_left] at he
  change ‖v - s‖ ^ 2 ≤ _
  rw [hid]
  nlinarith

lemma extragradient_contraction {C : Set E} (hne : C.Nonempty) (hcl : IsClosed C)
    (hc : Convex ℝ C) (G : E → E) {L μ : ℝ} (hμ : 0 < μ) (hμL : μ ≤ L)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ (3 * L) * ‖x - y‖)
    (s : E) (hs : s ∈ C) (hgap : ∀ u ∈ C, μ * ‖u - s‖ ^ 2 ≤ ⟪G u, u - s⟫)
    (w : E) :
    let η := 1 / (6 * L)
    let u := project C (w - η • G w)
    let v := project C (w - η • G u)
    ‖v - s‖ ^ 2 ≤ (1 - μ / (6 * L)) * ‖w - s‖ ^ 2 := by
  have hL : 0 < L := hμ.trans_le hμL
  let η := 1 / (6 * L)
  let u := project C (w - η • G w)
  let v := project C (w - η • G u)
  have he := extragradient_energy hne hcl hc G (by positivity : 0 ≤ η)
    hlip w s hs
  have hg := hgap u (closed_project_spec hne hcl hc _).1
  have hm := mul_le_mul_of_nonneg_left hg (by positivity : 0 ≤ 2 * η)
  have ht : ‖w - s‖ ^ 2 ≤ 2 * ‖w - u‖ ^ 2 + 2 * ‖u - s‖ ^ 2 := by
    have htri := norm_sub_le_norm_sub_add_norm_sub w u s
    nlinarith [sq_nonneg (‖w - u‖ - ‖u - s‖), norm_nonneg (w - s),
      norm_nonneg (w - u), norm_nonneg (u - s)]
  have ha : 2 * η ^ 2 * (3 * L) ^ 2 = 1 / 2 := by dsimp [η]; field_simp; ring
  have hb : 0 ≤ η * μ := by positivity
  have hc' : 2 * (η * μ) ≤ 1 / 2 := by
    dsimp [η]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    have hh : μ / L ≤ 1 := (div_le_one hL).mpr hμL
    field_simp at *
    nlinarith
  have hd := mul_le_mul_of_nonneg_left ht hb
  change ‖v - s‖ ^ 2 ≤ (1 - μ / (6 * L)) * ‖w - s‖ ^ 2
  change ‖v - s‖ ^ 2 ≤ ‖w - s‖ ^ 2 - (1 - 2 * η ^ 2 * (3 * L) ^ 2) * ‖w - u‖ ^ 2 -
    ‖u - v‖ ^ 2 / 2 - 2 * η * ⟪G u, u - s⟫ at he
  rw [ha] at he
  have hημ : μ / (6 * L) = η * μ := by dsimp [η]; ring
  rw [hημ]
  nlinarith [sq_nonneg ‖u - v‖,
    mul_nonneg (sub_nonneg.mpr hc') (sq_nonneg ‖w - u‖)]

open LongTails.Setups.ConstrainedMinimaxSecondOrder
open LongTails.Algorithms.ConstrainedSaddleCubic
open ConstrainedMinimaxEnvelope

lemma feasible_geometry {p : Params} (hv : spec.valid p) :
    (feasible p).Nonempty ∧ IsClosed (feasible p) ∧ Convex ℝ (feasible p) := by
  refine ⟨⟨WithLp.toLp 2 (p.x0, p.y0), hv.2.2.2.2.2.2.2.2⟩, ?_, ?_⟩
  · exact hv.2.2.2.2.2.2.1.preimage (WithLp.continuous_snd 2 p.E p.F)
  · exact hv.2.2.2.2.2.2.2.1.linear_preimage (WithLp.sndL 2 ℝ p.E p.F).toLinearMap

lemma operator_lipschitz {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (z : p.E) (w v : Space p) :
    ‖operatorReply z w (gradient f w) - operatorReply z v (gradient f v)‖ ≤
      (3 * p.L) * ‖w - v‖ := by
  let r := gradient f w - gradient f v
  let a : Space p := WithLp.toLp 2 (r.fst, -r.snd)
  let b : Space p := WithLp.toLp 2 ((2 * p.L) • (w.fst - v.fst), 0)
  have ha : ‖a‖ = ‖r‖ := by
    have h1 := WithLp.prod_norm_sq_eq_of_L2 a
    have h2 := WithLp.prod_norm_sq_eq_of_L2 r
    change ‖a‖ ^ 2 = ‖r.fst‖ ^ 2 + ‖-r.snd‖ ^ 2 at h1
    rw [norm_neg] at h1
    nlinarith [norm_nonneg a, norm_nonneg r]
  have hb : ‖b‖ ≤ 2 * p.L * ‖w - v‖ := by
    dsimp [b]
    rw [WithLp.norm_toLp_fst, norm_smul, Real.norm_of_nonneg (by linarith [hv.1, hv.2.1])]
    exact mul_le_mul_of_nonneg_left (WithLp.norm_fst_le p.E (w - v)) (by linarith [hv.1, hv.2.1])
  have he : operatorReply z w (gradient f w) - operatorReply z v (gradient f v) = a + b := by
    apply (WithLp.equiv 2 (p.E × p.F)).injective
    ext <;> simp [operatorReply, a, b, r] <;> module
  rw [he]
  have ht := norm_add_le a b
  rw [ha] at ht
  have hg := H.gradient_lipschitz w v
  change ‖r‖ ≤ p.L * ‖w - v‖ at hg
  linarith

lemma operator_gap {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (z : p.E) (w : Space p) (hw : w ∈ feasible p) :
    let s := WithLp.toLp 2 (primal f z, dual f z)
    p.μ * ‖w - s‖ ^ 2 ≤ ⟪operatorReply z w (gradient f w), w - s⟫ := by
  let s := WithLp.toLp 2 (primal f z, dual f z)
  have hm := ConstrainedSaddleGeometry.regularized_monotonicity
    (fun x x' y => ConstrainedMinimaxValue.primal_lower H (hv.1.trans_le hv.2.1).le x x' y)
    H.strongly_concave w.fst (primal f z) z w.snd (dual f z)
  have hη : WithLp.toLp 2 (w.fst, w.snd) = w := rfl
  rw [hη, saddle_primal_zero H hv z, sub_zero, inner_sub_left] at hm
  have hn := saddle_dual_normal H hv z w.snd hw
  have hd := WithLp.prod_norm_sq_eq_of_L2 (w - s)
  change ‖w - s‖ ^ 2 = ‖w.fst - primal f z‖ ^ 2 + ‖w.snd - dual f z‖ ^ 2 at hd
  change p.μ * ‖w - s‖ ^ 2 ≤
    ⟪(gradient f w).fst + (2 * p.L) • (w.fst - z), w.fst - primal f z⟫ +
      ⟪-(gradient f w).snd, w.snd - dual f z⟫
  rw [inner_neg_left, hd, mul_add]
  have he : p.μ * ‖w.fst - primal f z‖ ^ 2 ≤ p.L * ‖w.fst - primal f z‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hv.2.1 (sq_nonneg _)
  linarith

noncomputable def jet {p : Params} (f : Space p → ℝ) (w : Space p) : spec.Reply p :=
  (f w, gradient f w, fderiv ℝ (gradient f) w)

lemma extra_plan_contraction {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (z : p.E) (w : Space p) :
    let s := WithLp.toLp 2 (primal f z, dual f z)
    ‖OracleTemplate.QueryPlan.eval (jet f) (extraPlan z w) - s‖ ^ 2 ≤
      (1 - p.μ / (6 * p.L)) * ‖w - s‖ ^ 2 := by
  have hc := feasible_geometry hv
  exact extragradient_contraction hc.1 hc.2.1 hc.2.2
    (fun v => operatorReply z v (gradient f v)) hv.1 hv.2.1
    (operator_lipschitz H hv z) (WithLp.toLp 2 (primal f z, dual f z))
    (dual_spec H hv z).1 (operator_gap H hv z) w

lemma initial_plan_error {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (z : p.E) (n : ℕ) (w : Space p) :
    let s := WithLp.toLp 2 (primal f z, dual f z)
    ‖OracleTemplate.QueryPlan.eval (jet f) (initialPlan z n w) - s‖ ^ 2 ≤
      (1 - p.μ / (6 * p.L)) ^ n * ‖w - s‖ ^ 2 := by
  have hL : 0 < p.L := hv.1.trans_le hv.2.1
  have hq : 0 ≤ 1 - p.μ / (6 * p.L) := by
    have hd : p.μ / (6 * p.L) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith [hv.2.1])
    linarith
  induction n generalizing w with
  | zero => simp [initialPlan, OracleTemplate.QueryPlan.eval]
  | succ n ih =>
    dsimp only
    rw [initialPlan, OracleTemplate.QueryPlan.eval_bind]
    exact (ih _).trans (by
      have hh := mul_le_mul_of_nonneg_left (extra_plan_contraction H hv z w) (pow_nonneg hq n)
      simpa only [pow_succ, mul_assoc] using hh)

lemma initial_distance {p : Params} {f : Space p → ℝ} (H : Assumptions p f)
    (hv : spec.valid p) :
    p.μ * ‖WithLp.toLp 2 (p.x0, p.y0) -
      WithLp.toLp 2 (primal f p.x0, dual f p.x0)‖ ≤ p.B := by
  let w : Space p := WithLp.toLp 2 (p.x0, p.y0)
  let s : Space p := WithLp.toLp 2 (primal f p.x0, dual f p.x0)
  let g := operatorReply p.x0 w (gradient f w)
  have hg : ‖g‖ = ‖gradient f w‖ := by
    have h1 := WithLp.prod_norm_sq_eq_of_L2 g
    have h2 := WithLp.prod_norm_sq_eq_of_L2 (gradient f w)
    change ‖g‖ ^ 2 = ‖(gradient f w).fst + (2 * p.L) • (p.x0 - p.x0)‖ ^ 2 +
      ‖-(gradient f w).snd‖ ^ 2 at h1
    rw [sub_self, smul_zero, add_zero, norm_neg] at h1
    nlinarith [norm_nonneg g, norm_nonneg (gradient f w)]
  have he := operator_gap H.toRegularity hv p.x0 w hv.2.2.2.2.2.2.2.2
  have hi := real_inner_le_norm g (w - s)
  rw [hg] at hi
  have hb := mul_le_mul_of_nonneg_right H.initial_gradient (norm_nonneg (w - s))
  change p.μ * ‖w - s‖ ^ 2 ≤ ⟪g, w - s⟫ at he
  change p.μ * ‖w - s‖ ≤ p.B
  by_cases hz : ‖w - s‖ = 0
  · rw [hz, mul_zero]
    exact hv.2.2.2.2.1
  · have hp : 0 < ‖w - s‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith

lemma startup_geometric_bound {L μ ρ B : ℝ} (hμ : 0 < μ) (hμL : μ ≤ L)
    (hρ : 0 < ρ) (hB : 0 ≤ B) (n : ℕ)
    (hn : 16 * L / μ * Real.log (1 + 32 * ρ * B / μ ^ 2) ≤ n) :
    (1 - μ / (6 * L)) ^ n * (B / μ) ^ 2 ≤ (μ / (32 * ρ)) ^ 2 := by
  have hL : 0 < L := hμ.trans_le hμL
  let t := 1 + 32 * ρ * B / μ ^ 2
  have ht : 1 ≤ t := by
    have hh : 0 ≤ 32 * ρ * B / μ ^ 2 := by positivity
    dsimp [t]
    linarith
  have ht0 : 0 < t := by linarith
  have hl : 0 ≤ Real.log t := Real.log_nonneg ht
  have hC : 1 ≤ 6 * L / μ := (le_div_iff₀ hμ).mpr (by linarith)
  have hnt : (6 * L / μ) * Real.log (t ^ 2) ≤ n := by
    rw [Real.log_pow]
    norm_num
    have hm := mul_nonneg (by positivity : 0 ≤ 4 * L / μ) hl
    dsimp [t] at hl hm ⊢
    ring_nf at hn hm ⊢
    linarith
  have hp := OracleTemplate.PLMinimax.geometric_log_bound hC (pow_pos ht0 2) n hnt
  have he : 1 - 1 / (6 * L / μ) = 1 - μ / (6 * L) := by field_simp
  rw [he] at hp
  have hb : (B / μ) / t ≤ μ / (32 * ρ) := by
    apply (div_le_iff₀ ht0).mpr
    dsimp [t]
    field_simp
    nlinarith [sq_pos_of_pos hμ]
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ (B / μ) / t) hb 2
  have hm := mul_le_mul_of_nonneg_right hp (sq_nonneg (B / μ))
  calc
    _ ≤ (1 / t ^ 2) * (B / μ) ^ 2 := hm
    _ = ((B / μ) / t) ^ 2 := by simp only [div_pow]; ring
    _ ≤ _ := hsq

lemma startup_accuracy {p : Params} {f : Space p → ℝ} (H : Assumptions p f)
    (hv : spec.valid p) :
    ‖OracleTemplate.QueryPlan.eval (jet f)
        (initialPlan p.x0 (startupSteps p) (WithLp.toLp 2 (p.x0, p.y0))) -
      WithLp.toLp 2 (primal f p.x0, dual f p.x0)‖ ≤ p.μ / (32 * p.ρ) := by
  have hL : 0 < p.L := hv.1.trans_le hv.2.1
  have hq : 0 ≤ 1 - p.μ / (6 * p.L) := by
    have hd : p.μ / (6 * p.L) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith [hv.2.1])
    linarith
  have hd := initial_distance H hv
  have hd' : ‖WithLp.toLp 2 (p.x0, p.y0) -
      WithLp.toLp 2 (primal f p.x0, dual f p.x0)‖ ≤ p.B / p.μ := by
    apply (le_div_iff₀ hv.1).mpr
    nlinarith
  have he := initial_plan_error H.toRegularity hv p.x0 (startupSteps p)
    (WithLp.toLp 2 (p.x0, p.y0))
  have hs := pow_le_pow_left₀ (norm_nonneg _) hd' 2
  have hm := mul_le_mul_of_nonneg_left hs (pow_nonneg hq (startupSteps p))
  have hn : 16 * p.L / p.μ * Real.log (1 + 32 * p.ρ * p.B / p.μ ^ 2) ≤ startupSteps p :=
    Nat.le_ceil _
  have hb := startup_geometric_bound hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.2.1 (startupSteps p) hn
  have hr : 0 ≤ p.μ / (32 * p.ρ) := div_nonneg hv.1.le (mul_nonneg (by norm_num) hv.2.2.1.le)
  nlinarith [he.trans (hm.trans hb)]

lemma newton_plan_halving {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (z : p.E) (w : Space p)
    (hw : ‖w - WithLp.toLp 2 (primal f z, dual f z)‖ ≤ 3 * p.μ / (32 * p.ρ)) :
    let s := WithLp.toLp 2 (primal f z, dual f z)
    ‖(OracleTemplate.QueryPlan.eval (jet f) (newtonPlan z w)).1 - s‖ ≤ ‖w - s‖ / 2 := by
  have he := ConstrainedSaddlePerturbation.affine_step_quadratic_error H hv z w
  dsimp only at he ⊢
  change ‖affineStep z w (gradient f w) (fderiv ℝ (gradient f) w) -
    WithLp.toLp 2 (primal f z, dual f z)‖ ≤ _
  have hρ : 0 < p.ρ := hv.2.2.1
  have hb := (le_div_iff₀ (by positivity : 0 < 32 * p.ρ)).mp hw
  have hm := mul_le_mul_of_nonneg_right hb
    (norm_nonneg (w - WithLp.toLp 2 (primal f z, dual f z)))
  nlinarith [hv.1, norm_nonneg (w - WithLp.toLp 2 (primal f z, dual f z))]

lemma newton_plan_certificate {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (z : p.E) (w : Space p) :
    let state := OracleTemplate.QueryPlan.eval (jet f) (newtonPlan z w)
    primal (ConstrainedSaddlePerturbation.tilt f state.1 state.2) z = state.1.fst ∧
      dual (ConstrainedSaddlePerturbation.tilt f state.1 state.2) z = state.1.snd :=
  ConstrainedSaddlePerturbation.correction_saddle H hv z w (gradient f w)
    (fderiv ℝ (gradient f) w) _ (ConstrainedSaddlePerturbation.affine_step_spec H hv z w)

lemma refine_plan_error {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (z : p.E) (n : ℕ) (state : Space p × Space p)
    (hw : ‖state.1 - WithLp.toLp 2 (primal f z, dual f z)‖ ≤ 3 * p.μ / (32 * p.ρ)) :
    let s := WithLp.toLp 2 (primal f z, dual f z)
    ‖(OracleTemplate.QueryPlan.eval (jet f) (refinePlan z n state)).1 - s‖ ≤
      (1 / 2 : ℝ) ^ n * ‖state.1 - s‖ := by
  induction n generalizing state with
  | zero => simp [refinePlan, OracleTemplate.QueryPlan.eval]
  | succ n ih =>
    have hh := newton_plan_halving H hv z state.1 hw
    have hb : ‖(OracleTemplate.QueryPlan.eval (jet f) (newtonPlan z state.1)).1 -
        WithLp.toLp 2 (primal f z, dual f z)‖ ≤ 3 * p.μ / (32 * p.ρ) := by
      have hn := norm_nonneg (state.1 - WithLp.toLp 2 (primal f z, dual f z))
      linarith
    dsimp only
    rw [refinePlan, OracleTemplate.QueryPlan.eval_bind]
    apply (ih _ hb).trans
    have hm := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ (1 / 2 : ℝ) ^ n)
    simpa only [pow_succ, div_eq_mul_inv, mul_assoc, one_mul, mul_comm, mul_left_comm] using hm

lemma refine_plan_certificate {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (z : p.E) (n : ℕ) (state : Space p × Space p) (hn : 0 < n) :
    let out := OracleTemplate.QueryPlan.eval (jet f) (refinePlan z n state)
    primal (ConstrainedSaddlePerturbation.tilt f out.1 out.2) z = out.1.fst ∧
      dual (ConstrainedSaddlePerturbation.tilt f out.1 out.2) z = out.1.snd := by
  induction n generalizing state with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => exact newton_plan_certificate H hv z state.1
    | succ n =>
      dsimp only
      rw [refinePlan, OracleTemplate.QueryPlan.eval_bind]
      exact ih _ (by omega)

lemma newton_plan_residual {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (z : p.E) (w : Space p)
    (hw : ‖w - WithLp.toLp 2 (primal f z, dual f z)‖ ≤ 3 * p.μ / (32 * p.ρ)) :
    ‖(OracleTemplate.QueryPlan.eval (jet f) (newtonPlan z w)).2‖ ≤
      p.μ / 2 * ‖w - WithLp.toLp 2 (primal f z, dual f z)‖ := by
  let v := affineStep z w (gradient f w) (fderiv ℝ (gradient f) w)
  let s := WithLp.toLp 2 (primal f z, dual f z)
  have hh := newton_plan_halving H hv z w hw
  change ‖v - s‖ ≤ ‖w - s‖ / 2 at hh
  have ht := norm_sub_le_norm_sub_add_norm_sub v s w
  rw [norm_sub_rev s w] at ht
  have hd : ‖v - w‖ ≤ 3 / 2 * ‖w - s‖ := by linarith
  have hs := pow_le_pow_left₀ (norm_nonneg (v - w)) hd 2
  have hρ : 0 < p.ρ := hv.2.2.1
  have hm := mul_le_mul_of_nonneg_left hs hρ.le
  have hb := (le_div_iff₀ (by positivity : 0 < 32 * p.ρ)).mp hw
  have hc := mul_le_mul_of_nonneg_right hb (norm_nonneg (w - s))
  have he := ConstrainedSaddlePerturbation.correction_bound H w v
  change ‖correction w (gradient f w) (fderiv ℝ (gradient f) w) v (gradient f v)‖ ≤ _
  change ‖w - s‖ * (32 * p.ρ) ≤ 3 * p.μ at hb
  change ‖w - s‖ * (32 * p.ρ) * ‖w - s‖ ≤ 3 * p.μ * ‖w - s‖ at hc
  nlinarith [mul_nonneg hv.1.le (norm_nonneg (w - s))]

lemma refine_plan_residual {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (z : p.E) (n : ℕ) (state : Space p × Space p) (hn : 0 < n)
    (hw : ‖state.1 - WithLp.toLp 2 (primal f z, dual f z)‖ ≤ 3 * p.μ / (32 * p.ρ)) :
    ‖(OracleTemplate.QueryPlan.eval (jet f) (refinePlan z n state)).2‖ ≤
      p.μ * (1 / 2 : ℝ) ^ n * ‖state.1 - WithLp.toLp 2 (primal f z, dual f z)‖ := by
  induction n generalizing state with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      have hh := newton_plan_residual H hv z state.1 hw
      simpa [refinePlan, OracleTemplate.QueryPlan.eval_bind, OracleTemplate.QueryPlan.eval,
        div_eq_mul_inv, mul_assoc] using hh
    | succ n =>
      have hh := newton_plan_halving H hv z state.1 hw
      have hb : ‖(OracleTemplate.QueryPlan.eval (jet f) (newtonPlan z state.1)).1 -
          WithLp.toLp 2 (primal f z, dual f z)‖ ≤ 3 * p.μ / (32 * p.ρ) := by
        have hn0 := norm_nonneg (state.1 - WithLp.toLp 2 (primal f z, dual f z))
        linarith
      rw [refinePlan, OracleTemplate.QueryPlan.eval_bind]
      apply (ih _ (by omega) hb).trans
      have hp : 0 ≤ p.μ * (1 / 2 : ℝ) ^ (n + 1) := mul_nonneg hv.1.le (by positivity)
      have hm := mul_le_mul_of_nonneg_left hh hp
      simpa only [pow_succ, div_eq_mul_inv, mul_assoc, one_mul, mul_comm, mul_left_comm] using hm

lemma refine_plan_residual_uniform {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (z : p.E) (n : ℕ) (state : Space p × Space p) (hn : 0 < n)
    (hw : ‖state.1 - WithLp.toLp 2 (primal f z, dual f z)‖ ≤ 3 * p.μ / (32 * p.ρ)) :
    ‖(OracleTemplate.QueryPlan.eval (jet f) (refinePlan z n state)).2‖ ≤
      p.μ ^ 2 / p.ρ * (1 / 2 : ℝ) ^ n := by
  apply (refine_plan_residual H hv z n state hn hw).trans
  have hρ : 0 < p.ρ := hv.2.2.1
  have hb : 3 * p.μ / (32 * p.ρ) ≤ p.μ / p.ρ := by
    apply (div_le_div_iff₀ (by positivity) hρ).mpr
    nlinarith [hv.1]
  have hm := mul_le_mul_of_nonneg_left (hw.trans hb)
    (mul_nonneg hv.1.le (by positivity : 0 ≤ (1 / 2 : ℝ) ^ n))
  convert hm using 1
  ring

end LongTails.Proofs.ConstrainedSaddleInner
