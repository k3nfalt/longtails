import LongTails.Proofs.ScalarExcursion
import Mathlib.Analysis.Convex.Jensen

open MeasureTheory

namespace OracleTemplate.BoundedScalarConvex

open LongTails.Setups.BoundedScalarConvex

noncomputable def rightScore (F : ℝ → ℝ) (l u h H x0 x : ℝ) : ℝ :=
  let b := rightEndpoint F l u (F x0)
  profile F b (F x0) h H (max 0 (x-b)/h)

lemma reflected_convex {F : ℝ → ℝ} (hF : ConvexOn ℝ Set.univ F) :
    ConvexOn ℝ Set.univ (fun x => F (-x)) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have h := hF.2 (Set.mem_univ (-x)) (Set.mem_univ (-y)) ha hb hab
  simp only [smul_eq_mul] at h ⊢
  convert h using 1
  congr 1
  ring

lemma reflected_lipschitz {F : ℝ → ℝ} {H : ℝ}
    (hL : ∀ x y, |F x-F y| ≤ H*|x-y|) (x y : ℝ) :
    |F (-x)-F (-y)| ≤ H*|x-y| := by
  simpa only [neg_sub_neg, abs_sub_comm y x] using hL (-x) (-y)

lemma project_reflect {l u : ℝ} (hlu : l ≤ u) (x : ℝ) :
    project (-u) (-l) (-x) = -project l u x := by
  by_cases hxl : x ≤ l
  · rw [project_left hlu hxl, project_right (by linarith) (by linarith)]
  · by_cases hxu : u ≤ x
    · rw [project_right hlu hxu, project_left (by linarith) (by linarith)]
    · rw [project_eq_self (show x ∈ Set.Icc l u from ⟨by linarith, by linarith⟩),
        project_eq_self (show -x ∈ Set.Icc (-u) (-l) from ⟨by linarith, by linarith⟩)]

lemma rightScore_nonneg {F : ℝ → ℝ} {l u h H x0 x : ℝ} (hh : 0 < h) (hH : 0 < H) :
    0 ≤ rightScore F l u h H x0 x := profile_nonneg hh hH

lemma rightScore_dominates {F : ℝ → ℝ} (hF : ConvexOn ℝ Set.univ F)
    (hFc : Continuous F) {l u h H x0 x : ℝ} (hh : 0 < h) (hH : 0 < H)
    (hx0 : x0 ∈ Set.Icc l u) (hxx0 : x0 ≤ x) :
    F x-F x0 ≤ h*H*rightScore F l u h H x0 x := by
  let b := rightEndpoint F l u (F x0)
  have hb : F b ≤ F x0 := rightEndpoint_sublevel hFc ⟨x0, hx0, le_rfl⟩
  unfold rightScore
  rw [profile_at_excursion hh hb]
  by_cases hx : x ≤ b
  · rw [ite_eq_left hx, mul_zero]
    have hc := hF.le_max_of_mem_Icc (Set.mem_univ x0) (Set.mem_univ b) ⟨hxx0, hx⟩
    rw [max_eq_left hb] at hc
    linarith
  · rw [ite_eq_right hx]
    have he : h*H*(max 0 (F x-F x0)/(h*H)) = max 0 (F x-F x0) :=
      mul_div_cancel₀ _ (ne_of_gt (mul_pos hh hH))
    rw [he]
    exact le_max_right _ _

lemma two_scores_dominate {F : ℝ → ℝ} (hF : ConvexOn ℝ Set.univ F)
    (hFc : Continuous F) {l u h H x0 x : ℝ} (hh : 0 < h) (hH : 0 < H)
    (hx0 : x0 ∈ Set.Icc l u) :
    F x-F x0 ≤ h*H*(rightScore F l u h H x0 x+
      rightScore (fun z => F (-z)) (-u) (-l) h H (-x0) (-x)) := by
  have hp := mul_pos hh hH
  by_cases hx : x0 ≤ x
  · have hd := rightScore_dominates hF hFc hh hH hx0 hx
    have hn := rightScore_nonneg (F := fun z => F (-z)) (l := -u) (u := -l)
      (x0 := -x0) (x := -x) hh hH
    nlinarith
  · have hd := rightScore_dominates (reflected_convex hF) (hFc.comp continuous_neg)
      hh hH (show -x0 ∈ Set.Icc (-u) (-l) from ⟨by linarith [hx0.2], by linarith [hx0.1]⟩)
      (show -x0 ≤ -x by linarith)
    simp only [neg_neg] at hd
    have hn := rightScore_nonneg (F := F) (l := l) (u := u) (x0 := x0) (x := x) hh hH
    nlinarith

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma integrable_objective_interval {F : ℝ → ℝ} (hFc : Continuous F)
    {l u H : ℝ} (hH : 0 ≤ H) (hL : ∀ x y, |F x-F y| ≤ H*|x-y|)
    {X : Ω → ℝ} (hX : Measurable X) (hXm : ∀ ω, X ω ∈ Set.Icc l u) :
    Integrable (fun ω => F (X ω)) μ := by
  apply Integrable.of_bound (hFc.measurable.comp hX).aestronglyMeasurable (|F l|+H*(u-l))
  filter_upwards [] with ω
  have hl := hL (X ω) l
  rw [abs_of_nonneg (sub_nonneg.mpr (hXm ω).1)] at hl
  have ht := abs_add_le (F (X ω)-F l) (F l)
  rw [sub_add_cancel] at ht
  rw [Real.norm_eq_abs]
  change |F (X ω)| ≤ |F l|+H*(u-l)
  nlinarith [(hXm ω).2]

lemma integrable_rightScore {F : ℝ → ℝ} (hFc : Continuous F)
    {l u h H : ℝ} (hlu : l ≤ u) (hh : 0 < h) (hH : 0 < H)
    (hL : ∀ x y, |F x-F y| ≤ H*|x-y|)
    {X0 X : Ω → ℝ} (hX0 : Measurable X0) (hX : Measurable X)
    (hX0m : ∀ ω, X0 ω ∈ Set.Icc l u) (hXm : ∀ ω, X ω ∈ Set.Icc l u) :
    Integrable (fun ω => rightScore F l u h H (X0 ω) (X ω)) μ := by
  let v := fun ω => F (X0 ω)
  let b := fun ω => rightEndpoint F l u (v ω)
  have hv : Measurable v := hFc.measurable.comp hX0
  have hb : Measurable b := (rightEndpoint_measurable hlu).comp hv
  have hbi : Integrable b μ := integrable_interval hb (fun ω => rightEndpoint_mem hlu (v ω))
  have hXi : Integrable X μ := integrable_interval hX hXm
  have hZi := ((integrable_const (0 : ℝ)).sup (hXi.sub hbi)).div_const h
  have hZ := ((measurable_const (a := (0 : ℝ))).max (hX.sub hb)).div_const h
  apply hZi.mono' (measurable_profile hFc hb hv hZ h H).aestronglyMeasurable
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (profile_nonneg hh hH)]
  apply profile_le_coordinate hh hH
    (rightEndpoint_sublevel hFc ⟨X0 ω, hX0m ω, le_rfl⟩) hL
  exact div_nonneg (le_max_left _ _) hh.le

lemma integral_rightScore_bound (m : ℕ → MeasurableSpace Ω) (hm : Monotone m)
    (hambient : ∀ n, m n ≤ mΩ) {F : ℝ → ℝ}
    (hF : ConvexOn ℝ Set.univ F) (hFc : Continuous F)
    {l u η H : ℝ} (hlu : l ≤ u) (hη : 0 < η) (hH : 0 < H)
    (hL : ∀ x y, |F x-F y| ≤ H*|x-y|)
    (X Y : ℕ → Ω → ℝ) (hX : ∀ n, Measurable[m n] (X n))
    (hXm : ∀ n ω, X n ω ∈ Set.Icc l u)
    (hYi : ∀ n, Integrable (Y n) μ) (hY : ∀ n, ∀ᵐ ω ∂μ, |Y n ω| ≤ H)
    (hstep : ∀ n, ∀ᵐ ω ∂μ, X (n+1) ω = project l u (X n ω-η*Y n ω))
    (hsub : ∀ n, ∀ᵐ ω ∂μ, ∀ y, F (X n ω)+μ[Y n | m n] ω*(y-X n ω) ≤ F y)
    (N : ℕ) : (∫ ω, rightScore F l u (η*H) H (X 0 ω) (X N ω) ∂μ) ≤ 6 := by
  have hc := conditional_right_profile (mΩ := mΩ) (μ := μ) m hm hambient hF hFc
    hlu hη hH hL X Y hX hXm hYi hY hstep hsub N
  have hi := integral_mono_ae integrable_condExp (integrable_const (6 : ℝ)) hc
  rw [integral_condExp (hambient 0)] at hi
  simpa [rightScore] using hi

lemma integral_excursion_bound (m : ℕ → MeasurableSpace Ω) (hm : Monotone m)
    (hambient : ∀ n, m n ≤ mΩ) {F : ℝ → ℝ}
    (hF : ConvexOn ℝ Set.univ F) (hFc : Continuous F)
    {l u η H : ℝ} (hlu : l ≤ u) (hη : 0 < η) (hH : 0 < H)
    (hL : ∀ x y, |F x-F y| ≤ H*|x-y|)
    (X Y : ℕ → Ω → ℝ) (hX : ∀ n, Measurable[m n] (X n))
    (hXm : ∀ n ω, X n ω ∈ Set.Icc l u)
    (hYi : ∀ n, Integrable (Y n) μ) (hY : ∀ n, ∀ᵐ ω ∂μ, |Y n ω| ≤ H)
    (hstep : ∀ n, ∀ᵐ ω ∂μ, X (n+1) ω = project l u (X n ω-η*Y n ω))
    (hsub : ∀ n, ∀ᵐ ω ∂μ, ∀ y, F (X n ω)+μ[Y n | m n] ω*(y-X n ω) ≤ F y)
    (N : ℕ) : (∫ ω, F (X N ω)-F (X 0 ω) ∂μ) ≤ 12*η*H^2 := by
  have hr := integral_rightScore_bound (mΩ := mΩ) (μ := μ) m hm hambient hF hFc
    hlu hη hH hL X Y hX hXm hYi hY hstep hsub N
  have hnegmem : ∀ n ω, -X n ω ∈ Set.Icc (-u) (-l) := by
    intro n ω
    exact ⟨by linarith [(hXm n ω).2], by linarith [(hXm n ω).1]⟩
  have hnegstep : ∀ n, ∀ᵐ ω ∂μ, -X (n+1) ω = project (-u) (-l) (-X n ω-η*(-Y n ω)) := by
    intro n
    filter_upwards [hstep n] with ω hω
    have he : -X n ω-η*(-Y n ω) = -(X n ω-η*Y n ω) := by ring
    rw [he, project_reflect hlu, hω]
  have hnegsub : ∀ n, ∀ᵐ ω ∂μ, ∀ y,
      F (-(-X n ω))+μ[fun ω => -Y n ω | m n] ω*(y-(-X n ω)) ≤ F (-y) := by
    intro n
    filter_upwards [hsub n, condExp_neg (μ := μ) (Y n) (m n)] with ω hs he y
    change μ[fun ω => -Y n ω | m n] ω = -μ[Y n | m n] ω at he
    rw [he, neg_neg]
    have ht := hs (-y)
    nlinarith
  have hl := integral_rightScore_bound (mΩ := mΩ) (μ := μ) m hm hambient
    (reflected_convex hF) (hFc.comp continuous_neg) (by linarith : -u ≤ -l) hη hH
    (reflected_lipschitz hL) (fun n ω => -X n ω) (fun n ω => -Y n ω)
    (fun n => (hX n).neg) hnegmem (fun n => (hYi n).neg)
    (fun n => by simpa only [abs_neg] using hY n) hnegstep hnegsub N
  have hXm' : ∀ n, Measurable (X n) := fun n => (hX n).mono (hambient n) le_rfl
  have hri := integrable_rightScore (μ := μ) hFc hlu (mul_pos hη hH) hH hL
    (hXm' 0) (hXm' N) (hXm 0) (hXm N)
  have hli := integrable_rightScore (μ := μ) (hFc.comp continuous_neg) (by linarith : -u ≤ -l)
    (mul_pos hη hH) hH (reflected_lipschitz hL)
    (hXm' 0).neg (hXm' N).neg (hnegmem 0) (hnegmem N)
  have hfi := (integrable_objective_interval (μ := μ) hFc hH.le hL (hXm' N) (hXm N)).sub
    (integrable_objective_interval (μ := μ) hFc hH.le hL (hXm' 0) (hXm 0))
  have hp := integral_mono_ae hfi ((hri.add hli).const_mul (η*H*H))
    (Filter.Eventually.of_forall (fun ω => two_scores_dominate hF hFc
      (mul_pos hη hH) hH (hXm 0 ω)))
  rw [integral_const_mul] at hp
  simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply] at hp hli
  rw [integral_add hri hli] at hp
  have hs := add_le_add hr hl
  have hb := mul_le_mul_of_nonneg_left hs (show 0 ≤ η*H*H by positivity)
  change η*H*H*((∫ ω, rightScore F l u (η*H) H (X 0 ω) (X N ω) ∂μ)+
    (∫ ω, rightScore (F ∘ fun a => -a) (-u) (-l) (η*H) H (-X 0 ω) (-X N ω) ∂μ)) ≤
      η*H*H*(6+6) at hb
  exact hp.trans (hb.trans_eq (by ring))


end OracleTemplate.BoundedScalarConvex
