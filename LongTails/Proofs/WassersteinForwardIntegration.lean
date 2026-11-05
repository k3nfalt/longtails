import LongTails.Proofs.WassersteinCouplings
import LongTails.Proofs.WassersteinForwardGeometry
import LongTails.Proofs.WassersteinProximalGeometry

open MeasureTheory
open LongTails.Setups.WassersteinSmoothComposite
open LongTails.Proofs.WassersteinCouplings
open LongTails.Proofs.WassersteinForwardGeometry

namespace LongTails.Proofs.WassersteinForwardIntegration

lemma gradient_second_moment {d : ℕ} (μ : Distribution d) (g : Space d → Space d)
    (hgmeas : Measurable g) (L : ℝ)
    (hg : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) :
    Integrable (fun x => ‖g x‖ ^ 2) (μ.law : Measure (Space d)) := by
  apply integrable_sq_of_linear_growth μ g hgmeas ‖g 0‖ L
  intro x
  have hn := norm_add_le (g x - g 0) (g 0)
  rw [sub_add_cancel] at hn
  have hl := hg x 0
  rw [sub_zero] at hl
  linarith

lemma potential_integrable {d : ℕ} (μ : Distribution d) (V : Space d → ℝ)
    (g : Space d → Space d) (L : ℝ) (hL : 0 ≤ L) (hV : Measurable V)
    (hconv : ∀ x y, V x + inner ℝ (g x) (y - x) ≤ V y)
    (hsmooth : ∀ x y, V y ≤ V x + inner ℝ (g x) (y - x) + L / 2 * ‖y - x‖ ^ 2) :
    Integrable V (μ.law : Measure (Space d)) := by
  have hi : Integrable (fun x : Space d => |V 0| + ‖g 0‖ ^ 2 / 2 +
      ((1 + L) / 2) * ‖x‖ ^ 2) (μ.law : Measure (Space d)) :=
    (integrable_const (|V 0| + ‖g 0‖ ^ 2 / 2)).add
      (μ.secondMoment.const_mul ((1 + L) / 2))
  apply hi.mono' hV.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs]
  have hc := hconv 0 x
  have hs := hsmooth 0 x
  simp only [sub_zero] at hc hs
  have hi := abs_real_inner_le_norm (g 0) x
  have hil := (abs_le.mp hi).1
  have hir := (abs_le.mp hi).2
  have hv := le_abs_self (V 0)
  have hvn := neg_le_abs (V 0)
  have hy := sq_nonneg (‖g 0‖ - ‖x‖)
  have hLn := mul_nonneg hL (sq_nonneg ‖x‖)
  apply abs_le.mpr
  constructor <;> nlinarith

lemma integrated_forward_convex_cost {d : ℕ} (μ ν b : Distribution d)
    (V : Space d → ℝ) (g : Space d → Space d) (h : ℝ) (hh : 0 ≤ h)
    (hV : Measurable V) (hg : Measurable g)
    (hVμ : Integrable V (μ.law : Measure (Space d)))
    (hVν : Integrable V (ν.law : Measure (Space d)))
    (hgμ : Integrable (fun x => ‖g x‖ ^ 2) (μ.law : Measure (Space d)))
    (hforward : (μ.law : Measure (Space d)).map (fun x => x - h • g x) = b.law)
    (hconv : ∀ x v, V x + inner ℝ (g x) (v - x) ≤ V v)
    (π : Coupling μ ν) :
    squaredDistance b ν ≤ couplingCost π -
      2 * h * ((∫ x, V x ∂(μ.law : Measure (Space d))) -
        ∫ x, V x ∂(ν.law : Measure (Space d))) +
      h ^ 2 * ∫ x, ‖g x‖ ^ 2 ∂(μ.law : Measure (Space d)) := by
  let A := fun x : Space d => x - h • g x
  have hA : Measurable A := by dsimp [A]; fun_prop
  have hAf : (π.law : Measure (Space d × Space d)).map (fun z => A z.1) = b.law := by
    change (π.law : Measure (Space d × Space d)).map (A ∘ Prod.fst) = _
    rw [← Measure.map_map hA measurable_fst, π.first]
    exact hforward
  have hc := squaredDistance_le_cost (couplingOfMaps π.law b ν (fun z => A z.1)
    Prod.snd (hA.comp measurable_fst) measurable_snd hAf π.second)
  rw [couplingOfMaps_cost] at hc
  have hi1 := integrable_of_marginal (π.law : Measure (Space d × Space d)) μ
    Prod.fst measurable_fst π.first V hVμ
  have hi2 := integrable_of_marginal (π.law : Measure (Space d × Space d)) ν
    Prod.snd measurable_snd π.second V hVν
  have hi3 := integrable_of_marginal (π.law : Measure (Space d × Space d)) μ
    Prod.fst measurable_fst π.first (fun x => ‖g x‖ ^ 2) hgμ
  simp only [Function.comp_def] at hi1 hi2 hi3
  have hcost := integrable_sq_sub_of_maps (π.law : Measure (Space d × Space d)) b ν
    (fun z => A z.1) Prod.snd (hA.comp measurable_fst) measurable_snd hAf π.second
  have hb := integral_mono hcost
    ((π.finiteCost.sub ((hi1.sub hi2).const_mul (2 * h))).add (hi3.const_mul (h ^ 2)))
    (fun z => forward_convex_cost V z.1 z.2 (g z.1) h hh (hconv z.1 z.2))
  simp only [Pi.sub_apply, Pi.add_apply] at hb
  have hs := integral_sub π.finiteCost ((hi1.sub hi2).const_mul (2 * h))
  have ha := integral_add (π.finiteCost.sub ((hi1.sub hi2).const_mul (2 * h)))
    (hi3.const_mul (h ^ 2))
  simp only [Pi.sub_apply] at hs ha
  rw [ha, hs, integral_const_mul, integral_sub hi1 hi2, integral_const_mul] at hb
  rw [integral_of_marginal _ μ Prod.fst measurable_fst π.first V hV,
    integral_of_marginal _ ν Prod.snd measurable_snd π.second V hV,
    integral_of_marginal _ μ Prod.fst measurable_fst π.first
      (fun x => ‖g x‖ ^ 2) (by fun_prop)] at hb
  exact hc.trans hb

lemma integrated_forward_smooth_cost {d : ℕ} (μ u b : Distribution d)
    (V : Space d → ℝ) (g : Space d → Space d) (h L : ℝ)
    (hh : 0 ≤ h) (hsmall : h * L ≤ 1)
    (hV : Measurable V) (hg : Measurable g)
    (hVμ : Integrable V (μ.law : Measure (Space d)))
    (hVu : Integrable V (u.law : Measure (Space d)))
    (hgμ : Integrable (fun x => ‖g x‖ ^ 2) (μ.law : Measure (Space d)))
    (hforward : (μ.law : Measure (Space d)).map (fun x => x - h • g x) = b.law)
    (hsmooth : ∀ x v, V v ≤ V x + inner ℝ (g x) (v - x) + L / 2 * ‖v - x‖ ^ 2)
    (π : Coupling μ u)
    (hopt : (∫ z, ‖z.1 - h • g z.1 - z.2‖ ^ 2
      ∂(π.law : Measure (Space d × Space d))) = squaredDistance b u) :
    2 * h * ((∫ x, V x ∂(u.law : Measure (Space d))) -
      ∫ x, V x ∂(μ.law : Measure (Space d))) ≤
      squaredDistance b u - (1 - h * L) * squaredDistance μ u -
      h ^ 2 * ∫ x, ‖g x‖ ^ 2 ∂(μ.law : Measure (Space d)) := by
  let A := fun x : Space d => x - h • g x
  have hA : Measurable A := by dsimp [A]; fun_prop
  have hAf : (π.law : Measure (Space d × Space d)).map (fun z => A z.1) = b.law := by
    change (π.law : Measure (Space d × Space d)).map (A ∘ Prod.fst) = _
    rw [← Measure.map_map hA measurable_fst, π.first]
    exact hforward
  have hi1 := integrable_of_marginal (π.law : Measure (Space d × Space d)) μ
    Prod.fst measurable_fst π.first V hVμ
  have hi2 := integrable_of_marginal (π.law : Measure (Space d × Space d)) u
    Prod.snd measurable_snd π.second V hVu
  have hi3 := integrable_of_marginal (π.law : Measure (Space d × Space d)) μ
    Prod.fst measurable_fst π.first (fun x => ‖g x‖ ^ 2) hgμ
  simp only [Function.comp_def] at hi1 hi2 hi3
  have hcost := integrable_sq_sub_of_maps (π.law : Measure (Space d × Space d)) b u
    (fun z => A z.1) Prod.snd (hA.comp measurable_fst) measurable_snd hAf π.second
  have hb := integral_mono ((hi2.sub hi1).const_mul (2 * h))
    ((hcost.sub (π.finiteCost.const_mul (1 - h * L))).sub (hi3.const_mul (h ^ 2)))
    (fun z => forward_smooth_cost V z.1 z.2 (g z.1) h L hh (hsmooth z.1 z.2))
  have hs1 := integral_sub hcost (π.finiteCost.const_mul (1 - h * L))
  have hs2 := integral_sub (hcost.sub (π.finiteCost.const_mul (1 - h * L)))
    (hi3.const_mul (h ^ 2))
  simp only [Pi.sub_apply] at hb hs1 hs2
  rw [hs2, hs1, integral_const_mul, integral_sub hi2 hi1,
    integral_const_mul, integral_const_mul] at hb
  rw [integral_of_marginal _ u Prod.snd measurable_snd π.second V hV,
    integral_of_marginal _ μ Prod.fst measurable_fst π.first V hV,
    integral_of_marginal _ μ Prod.fst measurable_fst π.first
      (fun x => ‖g x‖ ^ 2) (by fun_prop)] at hb
  change 2 * h * ((∫ x, V x ∂(u.law : Measure (Space d))) -
      ∫ x, V x ∂(μ.law : Measure (Space d))) ≤
    (∫ z, ‖z.1 - h • g z.1 - z.2‖ ^ 2 ∂(π.law : Measure (Space d × Space d))) -
      (1 - h * L) * couplingCost π -
      h ^ 2 * ∫ x, ‖g x‖ ^ 2 ∂(μ.law : Measure (Space d)) at hb
  rw [hopt] at hb
  have hd := mul_le_mul_of_nonneg_left (squaredDistance_le_cost π)
    (sub_nonneg.mpr hsmall)
  linarith

lemma split_proximal_evi {d : ℕ} {Q : Set (Distribution d)} (H : Distribution d → ℝ)
    (hH : GeneralizedGeodesicConvex Q H) (μ b u v : Distribution d)
    (hu : u ∈ Q) (hv : v ∈ Q) (V : Space d → ℝ) (g : Space d → Space d)
    (h L : ℝ) (hh : 0 < h) (hL : 0 ≤ L) (hsmall : h * L < 1)
    (hV : Measurable V) (hg : Measurable g)
    (hVμ : Integrable V (μ.law : Measure (Space d)))
    (hVu : Integrable V (u.law : Measure (Space d)))
    (hVv : Integrable V (v.law : Measure (Space d)))
    (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖)
    (hconv : ∀ x y, V x + inner ℝ (g x) (y - x) ≤ V y)
    (hsmooth : ∀ x y, V y ≤ V x + inner ℝ (g x) (y - x) + L / 2 * ‖y - x‖ ^ 2)
    (hforward : (μ.law : Measure (Space d)).map (fun x => x - h • g x) = b.law)
    (hmin : ∀ ρ ∈ Q, 2 * h * H u + squaredDistance b u ≤
      2 * h * H ρ + squaredDistance b ρ)
    (Tu : OptimalTransport u b) (Tv : OptimalTransport v μ) :
    2 * h * (((∫ x, V x ∂(u.law : Measure (Space d))) + H u) -
      ((∫ x, V x ∂(v.law : Measure (Space d))) + H v)) ≤
      squaredDistance μ v - squaredDistance u v - (1 - h * L) * squaredDistance μ u := by
  have hm := gradient_second_moment μ g hg L hlip
  let πv := reverseCoupling (optimalMapCoupling Tv)
  have hc := integrated_forward_convex_cost μ v b V g h hh.le hV hg hVμ hVv hm
    hforward hconv πv
  have hπv : couplingCost πv = squaredDistance μ v := by
    dsimp only [πv]
    rw [reverseCoupling_cost, optimalMapCoupling_cost, squaredDistance_symm v μ]
  rw [hπv] at hc
  obtain ⟨B, hB, hleft, hright⟩ := forward_continuous_inverse g h L hh.le hL hsmall hlip
  let A := fun x : Space d => x - h • g x
  have hA : Measurable A := by dsimp [A]; fun_prop
  let π0 := reverseCoupling (optimalMapCoupling Tu)
  let π := pullbackFirst π0 A B hA hB.measurable hleft hforward
  have hπ : (∫ z, ‖z.1 - h • g z.1 - z.2‖ ^ 2
      ∂(π.law : Measure (Space d × Space d))) = squaredDistance b u := by
    have he := pullbackFirst_forward_cost π0 A B hA hB.measurable hleft hright hforward
    change (∫ z, ‖z.1 - h • g z.1 - z.2‖ ^ 2
      ∂(π.law : Measure (Space d × Space d))) = couplingCost π0 at he
    dsimp only [π0] at he
    rw [reverseCoupling_cost, optimalMapCoupling_cost, squaredDistance_symm u b] at he
    exact he
  have hs := integrated_forward_smooth_cost μ u b V g h L hh.le hsmall.le hV hg
    hVμ hVu hm hforward hsmooth π hπ
  have hp := WassersteinProximalGeometry.proximal_evi hH b u v hu hv h hh hmin
  linarith

end LongTails.Proofs.WassersteinForwardIntegration
