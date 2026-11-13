import LongTails.Algorithms.GatedPerturbedEscape
import LongTails.Proofs.ComparisonTrustTaylor
import LongTails.Proofs.GdConvex

namespace LongTails.Proofs.GatedEscapeDescent

open scoped RealInnerProductSpace
open LongTails.Proofs.ComparisonTrustTaylor LongTails.Algorithms.GatedPerturbedEscape

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma select_close {α : Type} [NormedAddCommGroup α] (M : ℕ) (τ : ℝ) (s : ℕ → α) (μ : α)
    (hgood : M < 2 * ((Finset.range M).filter (fun c => ‖s c - μ‖ ≤ τ)).card) :
    ‖select M τ s - μ‖ ≤ 3 * τ := by
  set G := (Finset.range M).filter (fun c => ‖s c - μ‖ ≤ τ) with hG
  have hGM : G.card ≤ M := by
    have := Finset.card_filter_le (Finset.range M) (fun c => ‖s c - μ‖ ≤ τ)
    simpa using this
  have hGne : G.Nonempty := by
    rw [← Finset.card_pos]; omega
  obtain ⟨a0, ha0⟩ := hGne
  have ha0' := Finset.mem_filter.mp ha0
  have hvote : ∀ a ∈ G, G.card ≤ votes M τ s a := by
    intro a ha
    have ha' := Finset.mem_filter.mp ha
    apply Finset.card_le_card
    intro c hc
    have hc' := Finset.mem_filter.mp hc
    refine Finset.mem_filter.mpr ⟨hc'.1, ?_⟩
    calc ‖s a - s c‖ = ‖(s a - μ) - (s c - μ)‖ := by congr 1; abel
      _ ≤ ‖s a - μ‖ + ‖s c - μ‖ := norm_sub_le _ _
      _ ≤ τ + τ := add_le_add ha'.2 hc'.2
      _ = 2 * τ := by ring
  have hex : (a0 < M ∧ M < 2 * votes M τ s a0) ∨ a0 = M :=
    Or.inl ⟨Finset.mem_range.mp ha0'.1, by have := hvote a0 ha0; omega⟩
  have hspec := Nat.find_spec (pick_exists M τ s)
  have hmin := Nat.find_min' (pick_exists M τ s) hex
  have hpick : pick M τ s < M ∧ M < 2 * votes M τ s (pick M τ s) := by
    rcases hspec with h | h
    · exact h
    · exfalso
      have : a0 < M := Finset.mem_range.mp ha0'.1
      omega
  unfold select
  set i := pick M τ s
  set C := (Finset.range M).filter (fun c => ‖s i - s c‖ ≤ 2 * τ) with hC
  have hinter : (C ∩ G).Nonempty := by
    apply Finset.inter_nonempty_of_card_lt_card_add_card (s := Finset.range M)
    · exact Finset.filter_subset _ _
    · exact Finset.filter_subset _ _
    · rw [Finset.card_range]
      have : votes M τ s i = C.card := rfl
      omega
  obtain ⟨c, hc⟩ := hinter
  rw [Finset.mem_inter] at hc
  have h1 := (Finset.mem_filter.mp hc.1).2
  have h2 := (Finset.mem_filter.mp hc.2).2
  calc ‖s i - μ‖ = ‖(s i - s c) + (s c - μ)‖ := by congr 1; abel
    _ ≤ ‖s i - s c‖ + ‖s c - μ‖ := norm_add_le _ _
    _ ≤ 2 * τ + τ := add_le_add h1 h2
    _ = 3 * τ := by ring

lemma gd_decrease {f : E → ℝ} {L : ℝ} (hL : 0 < L) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (x gh : E) {ε : ℝ}
    (hacc : ‖gh - gradient f x‖ ≤ ε / 8) (hbig : ε / 2 < ‖gh‖) :
    f (x - (1 / L) • gh) ≤ f x - ε ^ 2 / (16 * L) := by
  have h := OracleTemplate.Gradient.smooth_upper_bound hg hlip x (x - (1 / L) • gh)
  have he : x - (1 / L) • gh - x = -(1 / L) • gh := by module
  rw [he, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)] at h
  have hin : ⟪gradient f x, gh⟫ = ‖gh‖ ^ 2 - ⟪gh - gradient f x, gh⟫ := by
    rw [inner_sub_left, real_inner_self_eq_norm_sq, real_inner_comm]; ring
  have hcs : ⟪gh - gradient f x, gh⟫ ≤ ε / 8 * ‖gh‖ :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hacc (norm_nonneg _))
  have hε : 0 ≤ ε := by
    have := norm_nonneg (gh - gradient f x); linarith
  have hkey : ε ^ 2 / 16 ≤ ‖gh‖ ^ 2 / 2 - ε / 8 * ‖gh‖ := by nlinarith
  rw [hin] at h
  have hL1 : 0 < 1 / L := by positivity
  have : f (x - (1 / L) • gh) ≤ f x - (1 / L) * (‖gh‖ ^ 2 / 2 - ε / 8 * ‖gh‖) := by
    have e1 : L / 2 * ((1 / L) * ‖gh‖) ^ 2 = (1 / L) * (‖gh‖ ^ 2 / 2) := by field_simp
    nlinarith
  have h2 : (1 / L) * (ε ^ 2 / 16) ≤ (1 / L) * (‖gh‖ ^ 2 / 2 - ε / 8 * ‖gh‖) :=
    mul_le_mul_of_nonneg_left hkey hL1.le
  have h3 : (1 / L) * (ε ^ 2 / 16) = ε ^ 2 / (16 * L) := by field_simp
  linarith

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma grad_norm_of_small {gh g : E} {ε : ℝ} (hacc : ‖gh - g‖ ≤ ε / 8) (hsmall : ‖gh‖ ≤ ε / 2) :
    ‖g‖ ≤ ε := by
  have h := norm_sub_norm_le g gh
  have h2 : ‖g - gh‖ = ‖gh - g‖ := norm_sub_rev _ _
  have hε : 0 ≤ ε := by have := norm_nonneg gh; linarith
  linarith

lemma rayleigh_bias {f : E → ℝ} {L ρ : ℝ} (h : Smooth f L ρ) (x w : E) (hw : ‖w‖ = 1) {r : ℝ}
    (hr : 0 < r) :
    |⟪w, gradient f (x + r • w) - gradient f (x - r • w)⟫ / (2 * r) -
      ⟪w, fderiv ℝ (gradient f) x w⟫| ≤ ρ * r / 2 := by
  set H := fderiv ℝ (gradient f) x
  have h1 := h.grad_taylor x (r • w)
  have h2 := h.grad_taylor x (-(r • w))
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hw, mul_one] at h1
  rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hr, hw, mul_one, ← sub_eq_add_neg] at h2
  have hsum : gradient f (x + r • w) - gradient f (x - r • w) - (2 * r) • H w =
      (gradient f (x + r • w) - gradient f x - H (r • w)) -
        (gradient f (x - r • w) - gradient f x - H (-(r • w))) := by
    simp only [map_neg, map_smul]; module
  have hb : ‖gradient f (x + r • w) - gradient f (x - r • w) - (2 * r) • H w‖ ≤ ρ * r ^ 2 := by
    rw [hsum]
    calc _ ≤ ‖gradient f (x + r • w) - gradient f x - H (r • w)‖ +
          ‖gradient f (x - r • w) - gradient f x - H (-(r • w))‖ := norm_sub_le _ _
      _ ≤ ρ * r ^ 2 / 2 + ρ * r ^ 2 / 2 := add_le_add h1 h2
      _ = ρ * r ^ 2 := by ring
  have hin := abs_real_inner_le_norm w (gradient f (x + r • w) - gradient f (x - r • w) - (2 * r) • H w)
  rw [hw, one_mul, inner_sub_right, inner_smul_right] at hin
  have hin2 : |⟪w, gradient f (x + r • w) - gradient f (x - r • w)⟫ - 2 * r * ⟪w, H w⟫| ≤ ρ * r ^ 2 :=
    hin.trans hb
  have heq : ⟪w, gradient f (x + r • w) - gradient f (x - r • w)⟫ / (2 * r) - ⟪w, H w⟫ =
      (⟪w, gradient f (x + r • w) - gradient f (x - r • w)⟫ - 2 * r * ⟪w, H w⟫) / (2 * r) := by
    field_simp
  rw [heq, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * r), div_le_iff₀ (by positivity)]
  calc _ ≤ ρ * r ^ 2 := hin2
    _ = ρ * r / 2 * (2 * r) := by ring

lemma escape_decrease {f : E → ℝ} {L ρ : ℝ} (h : Smooth f L ρ) (x w g0 : E)
    (hw : ‖w‖ = 1) {r θ : ℝ} (hr : 0 < r) (hθ : 0 ≤ θ) (hρr : ρ * r ≤ θ)
    (hcurv : ⟪w, fderiv ℝ (gradient f) x w⟫ ≤ -θ)
    (hg0 : |⟪g0 - gradient f x, w⟫| ≤ r * θ / 8) :
    f (x - ((if 0 ≤ ⟪g0, w⟫ then (1 : ℝ) else -1) * r) • w) ≤ f x - r ^ 2 * θ / 5 := by
  set H := fderiv ℝ (gradient f) x
  set sg : ℝ := if 0 ≤ ⟪g0, w⟫ then 1 else -1 with hsg
  have hsg2 : sg ^ 2 = 1 := by rw [hsg]; split_ifs <;> norm_num
  have hsgabs : |sg| = 1 := by rw [hsg]; split_ifs <;> norm_num
  have hsgprod : 0 ≤ sg * ⟪g0, w⟫ := by
    rw [hsg]; split_ifs with hh
    · simpa using hh
    · push Not at hh; nlinarith
  have hv := h.value_taylor x (-((sg * r) • w))
  have hnorm : ‖-((sg * r) • w)‖ = r := by
    rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_mul, hsgabs, abs_of_pos hr, hw]; ring
  rw [hnorm] at hv
  have hlin : ⟪gradient f x, -((sg * r) • w)⟫ ≤ r * (r * θ / 8) := by
    have e1 : ⟪gradient f x, -((sg * r) • w)⟫ = -(sg * r) * ⟪g0, w⟫ + (sg * r) * ⟪g0 - gradient f x, w⟫ := by
      rw [inner_neg_right, inner_smul_right, inner_sub_left]
      ring
    rw [e1]
    have t1 : -(sg * r) * ⟪g0, w⟫ ≤ 0 := by nlinarith
    have t2 : (sg * r) * ⟪g0 - gradient f x, w⟫ ≤ r * (r * θ / 8) := by
      have := abs_le.mp hg0
      calc (sg * r) * ⟪g0 - gradient f x, w⟫ ≤ |(sg * r) * ⟪g0 - gradient f x, w⟫| := le_abs_self _
        _ = r * |⟪g0 - gradient f x, w⟫| := by rw [abs_mul, abs_mul, hsgabs, abs_of_pos hr]; ring
        _ ≤ r * (r * θ / 8) := mul_le_mul_of_nonneg_left hg0 hr.le
    linarith
  have hquad : ⟪-((sg * r) • w), H (-((sg * r) • w))⟫ = r ^ 2 * ⟪w, H w⟫ := by
    calc ⟪-((sg * r) • w), H (-((sg * r) • w))⟫ = (sg * r) ^ 2 * ⟪w, H w⟫ := by
          simp only [map_neg, map_smul, inner_neg_left, inner_neg_right, inner_smul_left,
            inner_smul_right, RCLike.conj_to_real]
          ring
      _ = r ^ 2 * ⟪w, H w⟫ := by rw [mul_pow, hsg2, one_mul]
  rw [hquad] at hv
  have hcube : ρ * r ^ 3 / 6 ≤ r ^ 2 * θ / 6 := by
    have : ρ * r ^ 3 = (ρ * r) * r ^ 2 := by ring
    rw [this]
    have := mul_le_mul_of_nonneg_right hρr (sq_nonneg r)
    linarith
  have hab := (abs_le.mp hv).2
  have hq : r ^ 2 * ⟪w, H w⟫ / 2 ≤ -(r ^ 2 * θ) / 2 := by
    have := mul_le_mul_of_nonneg_left hcurv (sq_nonneg r); linarith
  have hx : x + -((sg * r) • w) = x - (sg * r) • w := by abel
  rw [hx] at hab
  nlinarith

end LongTails.Proofs.GatedEscapeDescent
