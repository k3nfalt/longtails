import LongTails.Algorithms.ScalarSgd
import LongTails.Proofs.ScalarConvex
import Mathlib.Topology.Order.ProjIcc
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

namespace OracleTemplate.BoundedScalarConvex

lemma project_mem {l u : ℝ} (h : l ≤ u) (x : ℝ) : project l u x ∈ Set.Icc l u := by
  exact ⟨le_max_left _ _, max_le h (min_le_left _ _)⟩

lemma project_eq_self {l u x : ℝ} (h : x ∈ Set.Icc l u) : project l u x = x := by
  simp [project, min_eq_right h.2, max_eq_right h.1]

lemma project_left {l u x : ℝ} (h : l ≤ u) (hx : x ≤ l) : project l u x = l := by
  simp [project, min_eq_right (hx.trans h), max_eq_left hx]

lemma project_right {l u x : ℝ} (h : l ≤ u) (hx : u ≤ x) : project l u x = u := by
  simp [project, min_eq_left hx, max_eq_right h]

lemma project_nonexpansive (l u x y : ℝ) : |project l u x-project l u y| ≤ |x-y| := by
  have h1 := abs_max_sub_max_le_max l (min u x) l (min u y)
  have h2 := abs_min_sub_min_le_max u x u y
  simp only [sub_self, abs_zero] at h1 h2
  rw [max_eq_right (abs_nonneg (min u x-min u y))] at h1
  rw [max_eq_right (abs_nonneg (x-y))] at h2
  exact h1.trans h2

lemma project_distance {l u y : ℝ} (hy : y ∈ Set.Icc l u) (x : ℝ) :
    |project l u x-y| ≤ |x-y| := by
  simpa [project_eq_self hy] using project_nonexpansive l u x y

lemma continuous_project (l u : ℝ) : Continuous (project l u) := by
  unfold project
  fun_prop

noncomputable def extension (f : ℝ → ℝ) (l u H x : ℝ) : ℝ :=
  f (project l u x)+H*|x-project l u x|

lemma extension_eq {f : ℝ → ℝ} {l u H x : ℝ} (hx : x ∈ Set.Icc l u) :
    extension f l u H x = f x := by simp [extension, project_eq_self hx]

lemma extension_left {f : ℝ → ℝ} {l u H x : ℝ} (h : l ≤ u) (hx : x ≤ l) :
    extension f l u H x = f l+H*(l-x) := by
  simp [extension, project_left h hx, abs_of_nonpos (sub_nonpos.mpr hx)]

lemma extension_right {f : ℝ → ℝ} {l u H x : ℝ} (h : l ≤ u) (hx : u ≤ x) :
    extension f l u H x = f u+H*(x-u) := by
  simp [extension, project_right h hx, abs_of_nonneg (sub_nonneg.mpr hx)]

lemma extension_le_of_mem {f : ℝ → ℝ} {l u H : ℝ} (h : l ≤ u)
    (hlip : ∀ x ∈ Set.Icc l u, ∀ y ∈ Set.Icc l u, |f x-f y| ≤ H*|x-y|)
    {p : ℝ} (hp : p ∈ Set.Icc l u) (x : ℝ) :
    extension f l u H x ≤ f p+H*|x-p| := by
  by_cases hxl : x ≤ l
  · rw [extension_left h hxl, abs_of_nonpos (by linarith [hp.1] : x-p ≤ 0)]
    have hf := (le_abs_self (f l-f p)).trans (hlip l ⟨le_rfl, h⟩ p hp)
    rw [abs_of_nonpos (by linarith [hp.1] : l-p ≤ 0)] at hf
    nlinarith
  · by_cases hxu : u ≤ x
    · rw [extension_right h hxu, abs_of_nonneg (by linarith [hp.2] : 0 ≤ x-p)]
      have hf := (le_abs_self (f u-f p)).trans (hlip u ⟨h, le_rfl⟩ p hp)
      rw [abs_of_nonneg (by linarith [hp.2] : 0 ≤ u-p)] at hf
      nlinarith
    · have hx : x ∈ Set.Icc l u := ⟨by linarith, by linarith⟩
      rw [extension_eq hx]
      have hf := (le_abs_self (f x-f p)).trans (hlip x hx p hp)
      linarith

lemma extension_lipschitz {f : ℝ → ℝ} {l u H : ℝ} (h : l ≤ u) (hH : 0 ≤ H)
    (hlip : ∀ x ∈ Set.Icc l u, ∀ y ∈ Set.Icc l u, |f x-f y| ≤ H*|x-y|)
    (x y : ℝ) : |extension f l u H x-extension f l u H y| ≤ H*|x-y| := by
  have hxy := extension_le_of_mem h hlip (project_mem h y) x
  have hyx := extension_le_of_mem h hlip (project_mem h x) y
  have ht1 := abs_sub_le x y (project l u y)
  have ht2 := abs_sub_le y x (project l u x)
  have hm1 := mul_le_mul_of_nonneg_left ht1 hH
  have hm2 := mul_le_mul_of_nonneg_left ht2 hH
  rw [abs_sub_comm y x] at hm2
  apply abs_le.mpr
  dsimp [extension] at hxy hyx ⊢
  constructor <;> linarith

lemma extension_convex {f : ℝ → ℝ} {l u H : ℝ} (h : l ≤ u) (hH : 0 ≤ H)
    (hf : ConvexOn ℝ (Set.Icc l u) f)
    (hlip : ∀ x ∈ Set.Icc l u, ∀ y ∈ Set.Icc l u, |f x-f y| ≤ H*|x-y|) :
    ConvexOn ℝ Set.univ (extension f l u H) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hxp := project_mem h x
  have hyp := project_mem h y
  have hp := (convex_Icc l u) hxp hyp ha hb hab
  have he := extension_le_of_mem h hlip hp (a*x+b*y)
  have hc := hf.2 hxp hyp ha hb hab
  simp only [smul_eq_mul] at hp he hc ⊢
  have ht : |a*x+b*y-(a*project l u x+b*project l u y)| ≤
      a*|x-project l u x|+b*|y-project l u y| := by
    have heq : a*x+b*y-(a*project l u x+b*project l u y) =
        a*(x-project l u x)+b*(y-project l u y) := by ring
    rw [heq]
    simpa [abs_mul, abs_of_nonneg ha, abs_of_nonneg hb] using
      abs_add_le (a*(x-project l u x)) (b*(y-project l u y))
  have hmul := mul_le_mul_of_nonneg_left ht hH
  dsimp [extension] at he ⊢
  nlinarith

lemma extension_continuous {f : ℝ → ℝ} {l u H : ℝ} (h : l ≤ u) (hH : 0 ≤ H)
    (hlip : ∀ x ∈ Set.Icc l u, ∀ y ∈ Set.Icc l u, |f x-f y| ≤ H*|x-y|) :
    Continuous (extension f l u H) := by
  have hL : LipschitzWith ⟨H, hH⟩ (extension f l u H) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change |extension f l u H x-extension f l u H y| ≤ H*|x-y|
    exact extension_lipschitz h hH hlip x y
  exact hL.continuous

lemma extension_support {f : ℝ → ℝ} {l u H x g : ℝ} (h : l ≤ u)
    (hx : x ∈ Set.Icc l u) (hg : |g| ≤ H)
    (hsub : ∀ y ∈ Set.Icc l u, f x+g*(y-x) ≤ f y) (y : ℝ) :
    extension f l u H x+g*(y-x) ≤ extension f l u H y := by
  rw [extension_eq hx]
  obtain ⟨hglo, hghi⟩ := abs_le.mp hg
  by_cases hyl : y ≤ l
  · rw [extension_left h hyl]
    have hs := hsub l ⟨le_rfl, h⟩
    have hp := mul_nonneg (show 0 ≤ H+g by linarith) (sub_nonneg.mpr hyl)
    nlinarith
  · by_cases hyu : u ≤ y
    · rw [extension_right h hyu]
      have hs := hsub u ⟨h, le_rfl⟩
      have hp := mul_nonneg (sub_nonneg.mpr hghi) (sub_nonneg.mpr hyu)
      nlinarith
    · have hy : y ∈ Set.Icc l u := ⟨by linarith, by linarith⟩
      rw [extension_eq hy]
      exact hsub y hy

noncomputable def rightEndpoint (f : ℝ → ℝ) (l u v : ℝ) : ℝ :=
  sSup (insert l {x | x ∈ Set.Icc l u ∧ f x ≤ v})

lemma endpoint_set_bounded {f : ℝ → ℝ} {l u : ℝ} (h : l ≤ u) (v : ℝ) :
    BddAbove (insert l {x | x ∈ Set.Icc l u ∧ f x ≤ v}) := by
  refine ⟨u, ?_⟩
  intro x hx
  rcases hx with rfl | hx
  · exact h
  · exact hx.1.2

lemma rightEndpoint_mem {f : ℝ → ℝ} {l u : ℝ} (h : l ≤ u) (v : ℝ) :
    rightEndpoint f l u v ∈ Set.Icc l u := by
  constructor
  · exact le_csSup (endpoint_set_bounded h v) (Set.mem_insert _ _)
  · apply csSup_le ⟨l, Set.mem_insert _ _⟩
    intro x hx
    rcases hx with rfl | hx
    · exact h
    · exact hx.1.2

lemma rightEndpoint_mono {f : ℝ → ℝ} {l u : ℝ} (h : l ≤ u) :
    Monotone (rightEndpoint f l u) := by
  intro v w hvw
  apply csSup_le_csSup (endpoint_set_bounded h w) ⟨l, Set.mem_insert _ _⟩
  apply Set.insert_subset_insert
  intro x hx
  exact ⟨hx.1, hx.2.trans hvw⟩

lemma rightEndpoint_measurable {f : ℝ → ℝ} {l u : ℝ} (h : l ≤ u) :
    Measurable (rightEndpoint f l u) := (rightEndpoint_mono h).measurable

lemma le_rightEndpoint {f : ℝ → ℝ} {l u v x : ℝ} (h : l ≤ u)
    (hx : x ∈ Set.Icc l u) (hfx : f x ≤ v) : x ≤ rightEndpoint f l u v := by
  exact le_csSup (endpoint_set_bounded h v) (Set.mem_insert_of_mem l ⟨hx, hfx⟩)

lemma rightEndpoint_sublevel {f : ℝ → ℝ} {l u v : ℝ} (hf : Continuous f)
    (hne : ∃ x ∈ Set.Icc l u, f x ≤ v) : f (rightEndpoint f l u v) ≤ v := by
  let S : Set ℝ := {x | x ∈ Set.Icc l u ∧ f x ≤ v}
  have hS : S.Nonempty := by rcases hne with ⟨x, hx, hfx⟩; exact ⟨x, hx, hfx⟩
  have hB : BddAbove S := ⟨u, fun _ hx => hx.1.2⟩
  have hclosed : IsClosed S := isClosed_Icc.inter (isClosed_le hf continuous_const)
  have hmem : sSup S ∈ S := hclosed.csSup_mem hS hB
  have hl : l ≤ sSup S := hmem.1.1
  have he : rightEndpoint f l u v = sSup S := by
    change sSup (insert l S) = sSup S
    rw [csSup_insert hB hS, sup_eq_right.mpr hl]
  rw [he]
  exact hmem.2

end OracleTemplate.BoundedScalarConvex
