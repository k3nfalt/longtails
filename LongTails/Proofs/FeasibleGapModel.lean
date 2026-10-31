import LongTails.Setups.FeasibleHessianGapComposite
import LongTails.Proofs.FeasibleGapGeometry
import LongTails.Proofs.CompositeGapGeometry
import LongTails.Proofs.CompositeExtrapolation

open Set
open scoped RealInnerProductSpace

namespace LongTails.Proofs.FeasibleGapModel

open LongTails.Setups.FeasibleHessianGapComposite
open CompositeGapGeometry

variable {p : Params} {I : Instance p} {s : p.E}

noncomputable def smoothShift (I : Instance p) (s x : p.E) : ℝ :=
  I.f x - I.f s - ⟪I.grad s, x - s⟫

noncomputable def regularizerShift (I : Instance p) (s x : p.E) : ℝ :=
  I.ψ x - I.ψ s + ⟪I.grad s, x - s⟫

lemma shift_sum (x : p.E) :
    smoothShift I s x + regularizerShift I s x = objective I x - objective I s := by
  unfold smoothShift regularizerShift objective
  ring

lemma smoothShift_nonneg (h : Conditions p I s) {x : p.E} (hx : x ∈ I.Q) : 0 ≤ smoothShift I s x := by
  have hh := OracleTemplate.FrankWolfe.convex_support_on h.convex_f h.minimizer_feasible hx
    (h.gradient s h.minimizer_feasible)
  dsimp [smoothShift]
  linarith

lemma regularizerShift_nonneg (h : Conditions p I s) {x : p.E} (hx : x ∈ I.Q) :
    0 ≤ regularizerShift I s x := by
  have hh := CompositeExtrapolation.composite_optimality h.convex_regularizer
    h.minimizer_feasible (h.gradient s h.minimizer_feasible) (fun u hu => h.minimizer hu) hx
  dsimp [regularizerShift]
  linarith

lemma smoothShift_le_gap (h : Conditions p I s) {x : p.E} (hx : x ∈ I.Q) :
    smoothShift I s x ≤ objective I x - objective I s := by
  have hh := regularizerShift_nonneg h hx
  rw [← shift_sum]
  linarith

lemma regularizerShift_le_gap (h : Conditions p I s) {x : p.E} (hx : x ∈ I.Q) :
    regularizerShift I s x ≤ objective I x - objective I s := by
  have hh := smoothShift_nonneg h hx
  rw [← shift_sum]
  linarith

lemma smoothShift_gradient (h : Conditions p I s) {x : p.E} (hx : x ∈ I.Q) :
    HasGradientAt (smoothShift I s) (I.grad x - I.grad s) x := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have hl := ((InnerProductSpace.toDual ℝ p.E) (I.grad s)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).sub_const s)
  have hh := ((h.gradient x hx).hasFDerivAt.sub_const (I.f s)).sub hl
  convert hh using 1
  · rfl
  · simp [map_sub]

lemma smoothShift_convex (h : Conditions p I s) : ConvexOn ℝ I.Q (smoothShift I s) := by
  refine ⟨h.convex_domain, ?_⟩
  intro x hx y hy a b ha hb hab
  have hh := h.convex_f.2 hx hy ha hb hab
  simp only [smoothShift, inner_sub_right, inner_add_right,
    inner_smul_right, smul_eq_mul] at ⊢
  simp only [smul_eq_mul] at hh
  have he := congrArg (fun t : ℝ => t * (I.f s - ⟪I.grad s, s⟫)) hab
  nlinarith only [hh, he]

lemma regularizerShift_convex (h : Conditions p I s) :
    ConvexOn ℝ I.Q (regularizerShift I s) := by
  refine ⟨h.convex_domain, ?_⟩
  intro x hx y hy a b ha hb hab
  have hh := h.convex_regularizer.2 hx hy ha hb hab
  simp only [regularizerShift, inner_sub_right, inner_add_right,
    inner_smul_right, smul_eq_mul] at ⊢
  simp only [smul_eq_mul] at hh
  have he := congrArg (fun t : ℝ => t * (I.ψ s + ⟪I.grad s, s⟫)) hab
  nlinarith only [hh, he]

lemma sublevel_gradient_bound (h : Conditions p I s)
    (h1 : 0 ≤ p.H1) {d M R : ℝ} (hd : 0 ≤ d) (hM : 0 < M)
    (hcurv : p.H0 + p.H1 * d ≤ M)
    {x : p.E} (hx : x ∈ I.Q) (hgap : objective I x - objective I s ≤ d)
    (hR : ‖x - s‖ ≤ R) (K : ℕ) :
    ‖I.grad x - I.grad s‖ ≤ (K : ℝ) * Real.sqrt (M * d) +
      M * R * (1 / 2 : ℝ) ^ K := by
  classical
  let C := {y ∈ I.Q | objective I y ≤ objective I s + d}
  have hobj : ConvexOn ℝ I.Q (objective I) := h.convex_f.add h.convex_regularizer
  have hC : Convex ℝ C := hobj.convex_le _
  have hCs : s ∈ C := ⟨h.minimizer_feasible, by linarith⟩
  have hCx : x ∈ C := ⟨hx, by linarith⟩
  let H := fun y => if hy : y ∈ I.Q then (h.hessian y hy).choose else 0
  have hH (y : p.E) (hy : y ∈ I.Q) :
      HasFDerivAt (_root_.gradient I.f) (H y) y ∧ (H y).IsPositive ∧
      ‖H y‖ ≤ p.H0 + p.H1 * (objective I y - objective I s) := by
    simpa [H, hy] using (h.hessian y hy).choose_spec
  let g := fun y => _root_.gradient I.f y - I.grad s
  have hg : ∀ y ∈ C, HasGradientAt (smoothShift I s) (g y) y := by
    intro y hy
    dsimp [g]
    rw [(h.gradient y hy.1).gradient]
    exact smoothShift_gradient h hy.1
  have hder : ∀ y ∈ C, HasFDerivAt g (H y) y := by
    intro y hy
    exact (hH y hy.1).1.sub_const _
  have hb : ∀ y ∈ C, ‖H y‖ ≤ M := by
    intro y hy
    have hygap : objective I y - objective I s ≤ d := by linarith [hy.2]
    apply (hH y hy.1).2.2.trans
    apply le_trans _ hcurv
    gcongr
  have hconv : ConvexOn ℝ C (smoothShift I s) :=
    (smoothShift_convex h).subset (fun _ hy => hy.1) hC
  have hgs : g s = 0 := by simp [g, (h.gradient s h.minimizer_feasible).gradient]
  have hfgap : smoothShift I s x - smoothShift I s s ≤ d := by
    have hh := (smoothShift_le_gap h hx).trans hgap
    simpa [smoothShift] using hh
  have hh := FeasibleGapGeometry.dyadic_gradient_bound hconv hg hM hd hder
    (fun y hy => (hH y hy.1).2.1) hb hCs hCx hgs hfgap hR K
  simpa [g, (h.gradient x hx).gradient] using hh

lemma segment_localization (h : Conditions p I s)
    (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1)
    {x y : p.E} (hx : x ∈ I.Q) (hy : y ∈ I.Q)
    {d G r : ℝ} (hd : 0 ≤ d) (hG : 0 ≤ G) (hr : 0 ≤ r)
    (hstart : smoothShift I s x ≤ d)
    (hjx : regularizerShift I s x ≤ 2 * d)
    (hjy : regularizerShift I s y ≤ 2 * d)
    (hgrad : ‖I.grad x - I.grad s‖ ≤ G) (hdist : ‖y - x‖ ≤ r)
    (hGr : G * r ≤ d / 4) (hr0 : r ^ 2 / 2 * p.H0 ≤ d / 4)
    (hr1 : r ^ 2 / 2 * p.H1 ≤ 1 / 8) :
    ∀ z ∈ segment ℝ x y, smoothShift I s z ≤ 2 * d ∧
      objective I z - objective I s ≤ 4 * d := by
  classical
  let C := segment ℝ x y
  have hCQ : C ⊆ I.Q := h.convex_domain.segment_subset hx hy
  have hcomp : IsCompact C := by
    dsimp [C]
    rw [segment_eq_image']
    exact isCompact_Icc.image (by fun_prop)
  have hj : ∀ z ∈ C, regularizerShift I s z ≤ 2 * d := by
    intro z hz
    exact (((regularizerShift_convex h).convex_le (2 * d)).segment_subset
      ⟨hx, hjx⟩ ⟨hy, hjy⟩ hz).2
  let H := fun z => if hz : z ∈ I.Q then (h.hessian z hz).choose else 0
  have hH (z : p.E) (hz : z ∈ I.Q) :
      HasFDerivAt (_root_.gradient I.f) (H z) z ∧ (H z).IsPositive ∧
      ‖H z‖ ≤ p.H0 + p.H1 * (objective I z - objective I s) := by
    simpa [H, hz] using (h.hessian z hz).choose_spec
  let g := fun z => _root_.gradient I.f z - I.grad s
  have hg : ∀ z ∈ C, HasGradientAt (smoothShift I s) (g z) z := by
    intro z hz
    dsimp [g]
    rw [(h.gradient z (hCQ hz)).gradient]
    exact smoothShift_gradient h (hCQ hz)
  have hder : ∀ z ∈ C, HasFDerivAt g (H z) z :=
    fun z hz => (hH z (hCQ hz)).1.sub_const _
  have hcurv : ∀ z ∈ C, ‖H z‖ ≤ p.H0 + p.H1 *
      (smoothShift I s z + regularizerShift I s z) := by
    intro z hz
    rw [shift_sum]
    exact (hH z (hCQ hz)).2.2
  have hgx : ‖g x‖ ≤ G := by simpa [g, (h.gradient x hx).gradient] using hgrad
  have hloc := FeasibleGapGeometry.compact_gap_bound hcomp (convex_segment x y) hg hder
    h0 h1 hd hG hr hcurv (fun z hz => smoothShift_nonneg h (hCQ hz)) hj
    (left_mem_segment ℝ x y) hstart hgx
    (fun z hz => (norm_sub_le_of_mem_segment hz).trans hdist) hGr hr0 hr1
  intro z hz
  refine ⟨hloc z hz, ?_⟩
  rw [← shift_sum]
  linarith [hloc z hz, hj z hz]

lemma prox_is_model_min (h : Conditions p I s) {A : ℝ} (hA : 0 < A)
    (x0 v : p.E) (c : ℝ) :
    I.prox A x0 ((1 / A) • v) ∈ I.Q ∧
    IsMinOn (model I.ψ x0 A v c) I.Q (I.prox A x0 ((1 / A) • v)) := by
  have hh := h.prox A hA x0 ((1 / A) • v)
  refine ⟨hh.1, ?_⟩
  have he (u : p.E) : model I.ψ x0 A v c u =
      A * LongTails.Setups.CompositeGeneralizedSmooth.proxObjective I A x0 ((1 / A) • v) u + c := by
    unfold model LongTails.Setups.CompositeGeneralizedSmooth.proxObjective
    rw [real_inner_smul_left]
    field_simp
  intro u hu
  change model I.ψ x0 A v c (I.prox A x0 ((1 / A) • v)) ≤ model I.ψ x0 A v c u
  rw [he, he]
  have hmin : LongTails.Setups.CompositeGeneralizedSmooth.proxObjective I A x0 ((1 / A) • v)
      (I.prox A x0 ((1 / A) • v)) ≤
      LongTails.Setups.CompositeGeneralizedSmooth.proxObjective I A x0 ((1 / A) • v) u := hh.2 hu
  linarith [mul_le_mul_of_nonneg_left hmin hA.le]

lemma shifted_model_min {x0 z v : p.E} {A c : ℝ}
    (hm : IsMinOn (model I.ψ x0 A v c) I.Q z) :
    IsMinOn (model (regularizerShift I s) x0 A (v - A • I.grad s) c) I.Q z := by
  intro u hu
  have he (w : p.E) : model (regularizerShift I s) x0 A (v - A • I.grad s) c w =
      model I.ψ x0 A v c w + A * (-I.ψ s + ⟪I.grad s, x0 - s⟫) :=
    model_shift I.ψ x0 v (I.grad s) w s A c
  change model (regularizerShift I s) x0 A (v - A • I.grad s) c z ≤
    model (regularizerShift I s) x0 A (v - A • I.grad s) c u
  rw [he, he]
  have hmin : model I.ψ x0 A v c z ≤ model I.ψ x0 A v c u := hm hu
  linarith

lemma shifted_support (h : Conditions p I s) {x y : p.E}
    (hx : x ∈ I.Q) (hy : y ∈ I.Q) :
    smoothShift I s y + ⟪I.grad y - I.grad s, x - y⟫ ≤ smoothShift I s x := by
  have hh := OracleTemplate.FrankWolfe.convex_support_on h.convex_f hy hx (h.gradient y hy)
  simp only [smoothShift, inner_sub_left, inner_sub_right] at ⊢
  simp only [inner_sub_right] at hh
  linarith

lemma model_energy {x0 x z v u : p.E} {A c : ℝ}
    (h : Conditions p I s) (hA : 0 ≤ A) (hz : z ∈ I.Q) (hu : u ∈ I.Q)
    (hm : IsMinOn (model (regularizerShift I s) x0 A v c) I.Q z)
    (hlower : A * (objective I x - objective I s) ≤
      model (regularizerShift I s) x0 A v c z)
    (hupper : model (regularizerShift I s) x0 A v c u ≤
      ‖u - x0‖ ^ 2 / 2 + A * (objective I u - objective I s)) :
    A * (objective I x - objective I u) + ‖z - u‖ ^ 2 / 2 ≤ ‖u - x0‖ ^ 2 / 2 := by
  have hh := model_growth h.convex_domain (regularizerShift_convex h) hA hz hu hm
  rw [norm_sub_rev u z] at hh
  linarith

lemma gap_segment_upper (h : Conditions p I s) (h1 : 0 ≤ p.H1)
    {x y : p.E} (hx : x ∈ I.Q) (hy : y ∈ I.Q) {d M : ℝ}
    (hgap : ∀ z ∈ segment ℝ x y, objective I z - objective I s ≤ d)
    (hM : p.H0 + p.H1 * d ≤ M) :
    smoothShift I s y ≤ smoothShift I s x + ⟪I.grad x - I.grad s, y - x⟫ +
      M / 2 * ‖y - x‖ ^ 2 := by
  classical
  let C := segment ℝ x y
  have hCQ : C ⊆ I.Q := h.convex_domain.segment_subset hx hy
  let H := fun z => if hz : z ∈ I.Q then (h.hessian z hz).choose else 0
  have hH (z : p.E) (hz : z ∈ I.Q) :
      HasFDerivAt (_root_.gradient I.f) (H z) z ∧ (H z).IsPositive ∧
      ‖H z‖ ≤ p.H0 + p.H1 * (objective I z - objective I s) := by
    simpa [H, hz] using (h.hessian z hz).choose_spec
  have hg : ∀ z ∈ C, HasGradientAt I.f (_root_.gradient I.f z) z := by
    intro z hz
    rw [(h.gradient z (hCQ hz)).gradient]
    exact h.gradient z (hCQ hz)
  have hb : ∀ z ∈ C, ‖H z‖ ≤ M := by
    intro z hz
    apply (hH z (hCQ hz)).2.2.trans
    apply le_trans _ hM
    gcongr
    exact hgap z hz
  have hh := FeasibleGapGeometry.hessian_upper_bound (convex_segment x y) hg
    (fun z hz => (hH z (hCQ hz)).1) hb (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  rw [(h.gradient x hx).gradient] at hh
  simp only [smoothShift, inner_sub_left, inner_sub_right] at ⊢
  simp only [inner_sub_right] at hh
  linarith

lemma query_localization (h : Conditions p I s) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1)
    {x z : p.E} (hx : x ∈ I.Q) (hz : z ∈ I.Q)
    {d G R τ : ℝ} (hd : 0 ≤ d) (hG : 0 ≤ G) (hR : 0 ≤ R)
    (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hrx : ‖x - s‖ ≤ R) (hrz : ‖z - s‖ ≤ R)
    (hgap : objective I x - objective I s ≤ d)
    (hjz : regularizerShift I s z ≤ d + 2 * R * G)
    (hgrad : ‖I.grad x - I.grad s‖ ≤ G)
    (hsmall : τ * R * G ≤ d / 128)
    (hquad0 : (2 * R * τ) ^ 2 / 2 * p.H0 ≤ d / 4)
    (hquad1 : (2 * R * τ) ^ 2 / 2 * p.H1 ≤ 1 / 8) :
    let y := (1 - τ) • x + τ • z
    y ∈ I.Q ∧ smoothShift I s y ≤ 2 * d ∧
      regularizerShift I s y ≤ 2 * d ∧ objective I y - objective I s ≤ 4 * d := by
  let y := (1 - τ) • x + τ • z
  have hy : y ∈ I.Q := h.convex_domain hx hz (sub_nonneg.mpr hτ1) hτ (by ring)
  have hjx := (regularizerShift_le_gap h hx).trans hgap
  have hjy : regularizerShift I s y ≤ 2 * d := by
    have hh := (regularizerShift_convex h).2 hx hz (sub_nonneg.mpr hτ1) hτ (by ring)
    simp only [smul_eq_mul] at hh
    have ha := mul_le_mul_of_nonneg_left hjx (sub_nonneg.mpr hτ1)
    have hb := mul_le_mul_of_nonneg_left hjz hτ
    change regularizerShift I s y ≤ 2 * d
    nlinarith only [hh, ha, hb, hsmall, hd]
  have hdist : ‖y - x‖ ≤ 2 * R * τ := by
    have he : y - x = τ • (z - x) := by dsimp [y]; module
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ]
    have ht := norm_sub_le_norm_sub_add_norm_sub z s x
    rw [norm_sub_rev s x] at ht
    have hb := mul_le_mul_of_nonneg_left (show ‖z - x‖ ≤ 2 * R by linarith) hτ
    nlinarith only [hb]
  have hl := segment_localization h h0 h1 hx hy hd hG (by positivity)
    ((smoothShift_le_gap h hx).trans hgap) (by linarith) hjy hgrad hdist
    (by nlinarith only [hsmall, hd]) hquad0 hquad1
  have he := hl y (right_mem_segment ℝ x y)
  exact ⟨hy, he.1, hjy, he.2⟩

lemma initial_model_lower (h : Conditions p I s) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1)
    {x z : p.E} (hx : x ∈ I.Q) (hz : z ∈ I.Q)
    {d G M a : ℝ} (hd : 0 < d) (hG : 0 < G) (ha : 0 < a)
    (hscale : 128 * a * G ^ 2 = d) (hGM : M * d ≤ G ^ 2)
    (hM : p.H0 + p.H1 * d ≤ M)
    (hgap : objective I x - objective I s ≤ d)
    (hg : ‖I.grad x - I.grad s‖ ≤ G)
    (hm : IsMinOn (model (regularizerShift I s) x a (a • (I.grad x - I.grad s))
      (a * smoothShift I s x)) I.Q z) :
    a * (objective I z - objective I s) ≤
      model (regularizerShift I s) x a (a • (I.grad x - I.grad s))
        (a * smoothShift I s x) z := by
  let w := ‖z - x‖
  have hw : 0 ≤ w := norm_nonneg _
  have hjx := (regularizerShift_le_gap h hx).trans hgap
  have hjz := regularizerShift_nonneg h hz
  have hmin := hm hx
  change model (regularizerShift I s) x a (a • (I.grad x - I.grad s))
      (a * smoothShift I s x) z ≤
    model (regularizerShift I s) x a (a • (I.grad x - I.grad s))
      (a * smoothShift I s x) x at hmin
  simp only [model, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0),
    zero_div, inner_zero_right, real_inner_smul_left, zero_add] at hmin
  have hi : -⟪I.grad x - I.grad s, z - x⟫ ≤ G * w :=
    ((neg_le_abs _).trans (abs_real_inner_le_norm _ _)).trans
      (mul_le_mul_of_nonneg_right hg hw)
  have hpre : w ^ 2 / 2 ≤ a * G * w + a * d := by
    have ht := mul_le_mul_of_nonneg_left hi ha.le
    have hj := mul_le_mul_of_nonneg_left hjx ha.le
    have hn := mul_nonneg ha.le hjz
    dsimp [w]
    nlinarith only [hmin, ht, hj, hn]
  have hnorm : 64 * (G * w) ^ 2 ≤ d * (G * w) + d ^ 2 := by
    calc
      _ = (128 * G ^ 2) * (w ^ 2 / 2) := by ring
      _ ≤ (128 * G ^ 2) * (a * G * w + a * d) :=
        mul_le_mul_of_nonneg_left hpre (by positivity)
      _ = (128 * a * G ^ 2) * (G * w + d) := by ring
      _ = _ := by rw [hscale]; ring
  obtain ⟨hsmall, hquad⟩ := FeasibleGapGeometry.initial_smallness hd hG.le hw hGM hnorm
  have hjz' : regularizerShift I s z ≤ 2 * d := by
    have ht := mul_le_mul_of_nonneg_left hi ha.le
    have hj := mul_le_mul_of_nonneg_left hjx ha.le
    have hs := mul_le_mul_of_nonneg_left hsmall ha.le
    have hb : a * regularizerShift I s z ≤ a * (2 * d) := by
      dsimp [w] at hs
      nlinarith [sq_nonneg ‖z - x‖]
    exact (mul_le_mul_iff_right₀ ha).mp hb
  have hM0 : p.H0 ≤ M := by nlinarith
  have hM1 : p.H1 * d ≤ M := by linarith
  have hq0 : w ^ 2 / 2 * p.H0 ≤ d / 4 := by
    nlinarith [mul_le_mul_of_nonneg_right hM0 (sq_nonneg w)]
  have hq1 : w ^ 2 / 2 * p.H1 ≤ 1 / 8 := by
    have hh := mul_le_mul_of_nonneg_right hM1 (sq_nonneg w)
    nlinarith
  have hloc := segment_localization h h0 h1 hx hz hd.le hG.le hw
    ((smoothShift_le_gap h hx).trans hgap) (by linarith) hjz' hg
    (le_refl w) hsmall hq0 hq1
  have hcurv : p.H0 + p.H1 * (4 * d) ≤ 4 * M := by nlinarith
  have hu := gap_segment_upper h h1 hx hz (fun u hu => (hloc u hu).2) hcurv
  have haM : a * M ≤ 1 / 128 := by
    have hh := mul_le_mul_of_nonneg_left hGM (show 0 ≤ 128 * a by positivity)
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hu ha.le
  rw [← shift_sum]
  dsimp [model]
  rw [real_inner_smul_left]
  have hn := mul_le_mul_of_nonneg_right haM (sq_nonneg ‖z - x‖)
  nlinarith only [hh, hn, sq_nonneg ‖z - x‖]

end LongTails.Proofs.FeasibleGapModel
