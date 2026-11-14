import LongTails.Proofs.PointwiseHessianTuning
import LongTails.Proofs.GeneralizedAcceleratedEnergy
import LongTails.Proofs.CoarseGeneralizedCounting
import LongTails.Proofs.PointwiseHessianLocalization
import LongTails.Proofs.PointwiseHessianCounting

open scoped RealInnerProductSpace

namespace LongTails.Proofs.PointwiseHessianOuter

open OracleTemplate
open LongTails.Setups.PointwiseHessianConvex
open LongTails.Algorithms.PointwiseHessianAccelerated
open LongTails.Proofs.PointwiseHessianTuning

noncomputable def energy {p : Public} (f : p.E → ℝ) (s : State p) (xs : p.E) : ℝ :=
  s.A * (f s.w - f xs) + ‖s.z - xs‖ ^ 2 / 2

lemma accept_fields {p : Public} (s : State p) :
    (accept s).A = s.A + (s.η / s.τ) * s.a ∧
    (accept s).w = ((1 - s.η / s.τ) * s.A / (s.A + (s.η / s.τ) * s.a)) • s.w +
      ((s.η / s.τ) * (s.A + s.a) / (s.A + (s.η / s.τ) * s.a)) • s.x ∧
    (accept s).z = s.z - ((s.η / s.τ) * s.a) • s.g ∧
    (accept s).η = if s.τ = s.η then s.η / 2 else 2 * s.η := by
  by_cases ht : targetWeight p ≤ s.A + (s.η / s.τ) * s.a <;>
    simp [accept, finish, ht]

lemma accept_energy {p : Public} {f : p.E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ Set.univ f) (s : State p) (xs : p.E)
    (hA : 0 ≤ s.A) (hη : 0 < s.η) (hητ : s.η ≤ s.τ)
    (hg : s.g = gradient f s.x)
    (hres : ‖(1 / s.τ) • s.g + s.x - s.center‖ ≤ ‖s.x - s.center‖ / 2) :
    energy f (accept s) xs + (s.A + s.a) * s.η * (3 / 8) * ‖s.x - s.center‖ ^ 2 ≤
      energy f s xs := by
  have hτ : 0 < s.τ := hη.trans_le hητ
  have ha : 0 < s.a := weight_pos hA hη
  have hw : s.η * s.a ^ 2 = s.A + s.a := weight_identity hA hη
  have hγ : 0 < s.η / s.τ := div_pos hη hτ
  have hγ1 : s.η / s.τ ≤ 1 := (div_le_one hτ).mpr hητ
  have hweight : (s.η / s.τ) * s.a ^ 2 * s.τ ≤ s.A + s.a := by
    have he : (s.η / s.τ) * s.a ^ 2 * s.τ = s.η * s.a ^ 2 := by field_simp
    rw [he, hw]
  have hgrad (x : p.E) : HasGradientAt f (gradient f x) x :=
    (hf.differentiable (by norm_num) x).hasGradientAt
  have hscaled : ‖gradient f s.x + s.τ • (s.x - s.center)‖ ≤
      s.τ / 2 * ‖s.x - s.center‖ := by
    have he : s.τ • ((1 / s.τ) • s.g + s.x - s.center) =
        s.g + s.τ • (s.x - s.center) := by
      rw [smul_sub, smul_add, smul_smul]
      simp only [mul_one_div_cancel hτ.ne', one_smul, smul_sub]
      abel
    have hh := mul_le_mul_of_nonneg_left hres hτ.le
    have hn := norm_smul s.τ ((1 / s.τ) • s.g + s.x - s.center)
    rw [he, Real.norm_eq_abs, abs_of_pos hτ, hg] at hn
    rw [hg] at hh
    nlinarith
  have hh := GeneralizedAccelerated.damped_step hτ hc hgrad s.w s.z xs s.x
    hA ha hγ hγ1 hweight hscaled
  dsimp only at hh
  obtain ⟨hAf, hwf, hzf, _⟩ := accept_fields s
  unfold energy
  rw [hAf, hwf, hzf, hg]
  have hcoef : (s.η / s.τ) * (s.A + s.a) * (3 * s.τ / 8) =
      (s.A + s.a) * s.η * (3 / 8) := by field_simp
  rw [hcoef] at hh
  simpa [State.center, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hh

lemma energy_nonneg {p : Public} {f : p.E → ℝ} (s : State p) (xs : p.E)
    (hA : 0 ≤ s.A) (hmin : ∀ x, f xs ≤ f x) : 0 ≤ energy f s xs := by
  unfold energy
  exact add_nonneg (mul_nonneg hA (sub_nonneg.mpr (hmin _))) (by positivity)

lemma energy_radius {p : Public} {f : p.E → ℝ} (s : State p) (xs : p.E)
    {R : ℝ} (hR : 0 ≤ R) (hA : 0 ≤ s.A) (hmin : ∀ x, f xs ≤ f x)
    (he : energy f s xs ≤ R ^ 2) : ‖s.z - xs‖ ≤ 2 * R := by
  have hg := mul_nonneg hA (sub_nonneg.mpr (hmin s.w))
  unfold energy at he
  nlinarith [norm_nonneg (s.z - xs), sq_nonneg (‖s.z - xs‖ - 2 * R)]

lemma weight_le_twice {A η : ℝ} (hA : 0 < A) (hη : 0 < η)
    (hq : 1 ≤ η * A) : weight A η ≤ 2 * A := by
  have ha := weight_pos hA.le hη
  have hw := weight_identity hA.le hη
  by_contra hn
  have ht : 2 * A < weight A η := lt_of_not_ge hn
  have hmul := mul_le_mul_of_nonneg_right hq (sq_nonneg (weight A η))
  have he : η * A * weight A η ^ 2 = A * (A + weight A η) := by
    nlinarith [hw]
  nlinarith [sq_nonneg (weight A η - A)]

lemma accepted_weight_bounds {p : Public} (s : State p)
    (hA : 0 < s.A) (hη : 0 < s.η) (hητ : s.η ≤ s.τ)
    (hq : 1 ≤ s.η * s.A) : s.A < (accept s).A ∧ (accept s).A ≤ 3 * s.A := by
  have hτ := hη.trans_le hητ
  have ha : 0 < s.a := weight_pos hA.le hη
  have ha2 : s.a ≤ 2 * s.A := weight_le_twice hA hη hq
  have hγ : 0 < s.η / s.τ := div_pos hη hτ
  have hγ1 : s.η / s.τ ≤ 1 := (div_le_one hτ).mpr hητ
  rw [(accept_fields s).1]
  constructor
  · linarith [mul_pos hγ ha]
  · nlinarith [mul_le_mul_of_nonneg_right hγ1 ha.le]

lemma accepted_scale {p : Public} (s : State p)
    (hA : 0 < s.A) (hη : 0 < s.η) (hητ : s.η ≤ s.τ)
    (hq : 1 ≤ s.η * s.A) : 1 ≤ (accept s).η * (accept s).A := by
  obtain ⟨hAf, _, _, hηf⟩ := accept_fields s
  have ha : 0 < s.a := weight_pos hA.le hη
  have hw : s.η * s.a ^ 2 = s.A + s.a := weight_identity hA.le hη
  have hτ := hη.trans_le hητ
  rw [hAf, hηf]
  split_ifs with ht
  · rw [ht, div_self hη.ne', one_mul]
    have hηa : 1 ≤ s.η * s.a := by
      by_contra hn
      have hl : s.η * s.a < 1 := lt_of_not_ge hn
      have hm := mul_lt_mul_of_pos_right hl ha
      nlinarith
    nlinarith
  · have hp : 0 < s.η / s.τ * s.a := mul_pos (div_pos hη hτ) ha
    nlinarith

lemma energy_step_radius {p : Public} {f : p.E → ℝ} (s : State p) (xs : p.E)
    {R : ℝ} (hR : 0 ≤ R) (hA : 0 < s.A) (hη : 0 < s.η)
    (hητ : s.η ≤ s.τ) (hmin : ∀ x, f xs ≤ f x)
    (he : energy f s xs ≤ R ^ 2)
    (hd : energy f (accept s) xs +
      (s.A + s.a) * s.η * (3 / 8) * ‖s.x - s.center‖ ^ 2 ≤ energy f s xs) :
    ‖s.x - s.center‖ ≤ 2 * R * (s.a / (s.A + s.a)) := by
  have ha : 0 < s.a := weight_pos hA.le hη
  have hw : s.η * s.a ^ 2 = s.A + s.a := weight_identity hA.le hη
  have hc : 0 < s.A + s.a := by positivity
  have hAf : 0 ≤ (accept s).A := by
    rw [(accept_fields s).1]
    have hτ := hη.trans_le hητ
    positivity
  have hn := energy_nonneg (accept s) xs hAf hmin
  have hh : (s.A + s.a) * s.η * (3 / 8) * ‖s.x - s.center‖ ^ 2 ≤ R ^ 2 := by
    linarith
  have hm := mul_le_mul_of_nonneg_right hh (sq_nonneg s.a)
  have hid : ((s.A + s.a) * s.η * (3 / 8) * ‖s.x - s.center‖ ^ 2) * s.a ^ 2 =
      (3 / 8) * ((s.A + s.a) * ‖s.x - s.center‖) ^ 2 := by
    calc
      _ = (3 / 8) * (s.A + s.a) * (s.η * s.a ^ 2) * ‖s.x - s.center‖ ^ 2 := by ring
      _ = _ := by rw [hw]; ring
  rw [hid] at hm
  have hs : (s.A + s.a) * ‖s.x - s.center‖ ≤ 2 * R * s.a := by
    have hn' : 0 ≤ 2 * R * s.a := by positivity
    nlinarith [sq_nonneg ((s.A + s.a) * ‖s.x - s.center‖), sq_nonneg (R * s.a)]
  calc
    _ ≤ (2 * R * s.a) / (s.A + s.a) :=
      (le_div_iff₀ hc).mpr (by simpa [mul_comm] using hs)
    _ = _ := by ring

lemma center_radius {p : Public} (s : State p) (xs : p.E) {R : ℝ}
    (hR : 0 ≤ R) (hA : 0 ≤ s.A) (hη : 0 < s.η)
    (hw : ‖s.w - xs‖ ≤ 4 * R) (hz : ‖s.z - xs‖ ≤ 2 * R) :
    ‖s.center - xs‖ ≤ 4 * R := by
  have ha : 0 < s.a := weight_pos hA hη
  have hc : 0 < s.A + s.a := by positivity
  have hc1 : s.A / (s.A + s.a) + s.a / (s.A + s.a) = 1 := by field_simp
  have hid : s.center - xs = (s.A / (s.A + s.a)) • (s.w - xs) +
      (s.a / (s.A + s.a)) • (s.z - xs) := by
    unfold State.center
    match_scalars
    all_goals field_simp <;> ring
  rw [hid]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hA hc.le), abs_of_pos (div_pos ha hc)]
  have h1 := mul_le_mul_of_nonneg_left hw (div_nonneg hA hc.le)
  have h2 := mul_le_mul_of_nonneg_left hz (div_nonneg ha.le hc.le)
  nlinarith [mul_nonneg (div_nonneg ha.le hc.le) hR]

lemma center_displacement {p : Public} (s : State p) (xs : p.E) {R : ℝ}
    (hA : 0 ≤ s.A) (hη : 0 < s.η)
    (hw : ‖s.w - xs‖ ≤ 4 * R) (hz : ‖s.z - xs‖ ≤ 2 * R) :
    ‖s.center - s.w‖ ≤ 6 * R * (s.a / (s.A + s.a)) := by
  have ha : 0 < s.a := weight_pos hA hη
  have hc : 0 < s.A + s.a := by positivity
  have hid : s.center - s.w = (s.a / (s.A + s.a)) • (s.z - s.w) := by
    unfold State.center
    match_scalars
    all_goals field_simp <;> ring
  rw [hid, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos ha hc)]
  have hd : ‖s.z - s.w‖ ≤ 6 * R := by
    have hh := norm_sub_le (s.z - xs) (s.w - xs)
    rw [sub_sub_sub_cancel_right] at hh
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hd (div_nonneg ha.le hc.le)]

lemma accept_w_identity {p : Public} (s : State p)
    (hA : 0 ≤ s.A) (hη : 0 < s.η) :
    (accept s).w = (s.A / (s.A + (s.η / s.τ) * s.a)) • s.w +
      ((s.η / s.τ) * s.a / (s.A + (s.η / s.τ) * s.a)) • s.z +
      ((s.η / s.τ) * (s.A + s.a) / (s.A + (s.η / s.τ) * s.a)) •
        (s.x - s.center) := by
  have ha : 0 < s.a := weight_pos hA hη
  have hc : 0 < s.A + s.a := by positivity
  rw [(accept_fields s).2.1]
  unfold State.center
  match_scalars
  all_goals field_simp [hc.ne'] <;> ring

lemma accept_radius {p : Public} (s : State p) (xs : p.E) {R : ℝ}
    (hA : 0 < s.A) (hη : 0 < s.η) (hητ : s.η ≤ s.τ)
    (hw : ‖s.w - xs‖ ≤ 4 * R) (hz : ‖s.z - xs‖ ≤ 2 * R)
    (hd : ‖s.x - s.center‖ ≤ 2 * R * (s.a / (s.A + s.a))) :
    ‖(accept s).w - xs‖ ≤ 4 * R := by
  have ha : 0 < s.a := weight_pos hA.le hη
  have hc : 0 < s.A + s.a := by positivity
  have hτ := hη.trans_le hητ
  have hγ : 0 < s.η / s.τ := div_pos hη hτ
  have hB : 0 < s.A + (s.η / s.τ) * s.a := by positivity
  have hid : (accept s).w - xs =
      (s.A / (s.A + (s.η / s.τ) * s.a)) • (s.w - xs) +
      ((s.η / s.τ) * s.a / (s.A + (s.η / s.τ) * s.a)) • (s.z - xs) +
      ((s.η / s.τ) * (s.A + s.a) / (s.A + (s.η / s.τ) * s.a)) •
        (s.x - s.center) := by
    rw [accept_w_identity s hA.le hη]
    match_scalars
    all_goals field_simp <;> ring
  rw [hid]
  refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
  simp only [norm_smul, Real.norm_eq_abs,
    abs_of_pos (div_pos hA hB), abs_of_pos (div_pos (mul_pos hγ ha) hB),
    abs_of_pos (div_pos (mul_pos hγ hc) hB)]
  have h1 := mul_le_mul_of_nonneg_left hw (div_pos hA hB).le
  have h2 := mul_le_mul_of_nonneg_left hz (div_pos (mul_pos hγ ha) hB).le
  have h3 := mul_le_mul_of_nonneg_left hd (div_pos (mul_pos hγ hc) hB).le
  have he : s.A / (s.A + (s.η / s.τ) * s.a) * (4 * R) +
      ((s.η / s.τ) * s.a / (s.A + (s.η / s.τ) * s.a)) * (2 * R) +
      ((s.η / s.τ) * (s.A + s.a) / (s.A + (s.η / s.τ) * s.a)) *
        (2 * R * (s.a / (s.A + s.a))) = 4 * R := by
    field_simp
    ring
  linarith

structure Invariant {p : Public} (f : p.E → ℝ) (xs : p.E) (s : State p) : Prop where
  A_pos : 0 < s.A
  η_pos : 0 < s.η
  scale : 1 ≤ s.η * s.A
  weight_lower : initialWeight p ≤ s.A
  energy_le : energy f s xs ≤ p.R ^ 2
  radius : ‖s.w - xs‖ ≤ 4 * p.R

lemma initial_invariant {p : Public} {f : p.E → ℝ} (xs : p.E)
    (hR : 0 < p.R) (hΔ : 0 < p.Δ)
    (hx : ‖p.x0 - xs‖ ≤ p.R) (hg : f p.x0 - f xs ≤ p.Δ) :
    Invariant f xs (initial p) := by
  have hA := initialWeight_pos p hR hΔ
  have hh := mul_le_mul_of_nonneg_left hg hA.le
  have he : initialWeight p * p.Δ = p.R ^ 2 / 2 := by
    unfold initialWeight
    field_simp
  have hn := pow_le_pow_left₀ (norm_nonneg _) hx 2
  constructor
  · exact hA
  · exact one_div_pos.mpr hA
  · change 1 ≤ (1 / initialWeight p) * initialWeight p
    rw [one_div_mul_cancel hA.ne']
  · exact le_rfl
  · change initialWeight p * (f p.x0 - f xs) + ‖p.x0 - xs‖ ^ 2 / 2 ≤ p.R ^ 2
    rw [he] at hh
    linarith
  · change ‖p.x0 - xs‖ ≤ 4 * p.R
    linarith

lemma accept_invariant {p : Public} {f : p.E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ Set.univ f) (s : State p) (xs : p.E)
    (hR : 0 < p.R) (hmin : ∀ x, f xs ≤ f x) (hi : Invariant f xs s)
    (hητ : s.η ≤ s.τ) (hg : s.g = gradient f s.x)
    (hres : ‖(1 / s.τ) • s.g + s.x - s.center‖ ≤ ‖s.x - s.center‖ / 2) :
    Invariant f xs (accept s) := by
  have he := accept_energy hf hc s xs hi.A_pos.le hi.η_pos hητ hg hres
  have hA := accepted_weight_bounds s hi.A_pos hi.η_pos hητ hi.scale
  have hz := energy_radius s xs hR.le hi.A_pos.le hmin hi.energy_le
  have hd := energy_step_radius s xs hR.le hi.A_pos hi.η_pos hητ hmin hi.energy_le he
  constructor
  · exact hi.A_pos.trans hA.1
  · rw [(accept_fields s).2.2.2]
    have hηp := hi.η_pos
    split_ifs <;> positivity
  · exact accepted_scale s hi.A_pos hi.η_pos hητ hi.scale
  · exact hi.weight_lower.trans hA.1.le
  · have hn : 0 ≤ (s.A + s.a) * s.η * (3 / 8) * ‖s.x - s.center‖ ^ 2 := by
      have ha : 0 < s.a := weight_pos hi.A_pos.le hi.η_pos
      have hAp := hi.A_pos
      have hηp := hi.η_pos
      positivity
    linarith [hi.energy_le]
  · exact accept_radius s xs hi.A_pos hi.η_pos hητ hi.radius hz hd

lemma invariant_gap {p : Public} {f : p.E → ℝ} {xs : p.E} {s : State p}
    (hi : Invariant f xs s) : f s.w - f xs ≤ p.R ^ 2 / s.A := by
  apply (le_div_iff₀ hi.A_pos).mpr
  have he := hi.energy_le
  unfold energy at he
  nlinarith [sq_nonneg ‖s.z - xs‖]

lemma target_accuracy {p : Public} {f : p.E → ℝ} {xs : p.E} {s : State p}
    (hi : Invariant f xs s) (hε : 0 < p.ε) (ht : targetWeight p ≤ s.A) :
    f s.w - f xs ≤ p.ε := by
  apply (invariant_gap hi).trans
  apply (div_le_iff₀ hi.A_pos).mpr
  unfold targetWeight at ht
  have hh := (div_le_iff₀ hε).mp ht
  nlinarith

lemma accept_output {p : Public} (s : State p) : (accept s).out = (accept s).w := by
  by_cases ht : targetWeight p ≤ s.A + (s.η / s.τ) * s.a <;>
    simp [accept, finish, ht]

lemma finished_output {p : Public} (s : State p) (reply : p.E ⊕ (p.E →L[ℝ] p.E))
    (hs : s.phase = .finished) : update s reply = s := by
  simp [update, hs]

noncomputable def fraction {p : Public} (s : State p) : ℝ := s.a / (s.A + s.a)

lemma fraction_pos {p : Public} (s : State p) (hA : 0 ≤ s.A) (hη : 0 < s.η) :
    0 < fraction s := by
  have ha : 0 < s.a := weight_pos hA hη
  unfold fraction
  positivity

lemma fraction_identity {p : Public} (s : State p) (hA : 0 ≤ s.A) (hη : 0 < s.η) :
    (s.η * s.A) * fraction s ^ 2 = 1 - fraction s := by
  have ha : 0 < s.a := weight_pos hA hη
  have hc : 0 < s.A + s.a := by positivity
  have hw : s.η * s.a ^ 2 = s.A + s.a := weight_identity hA hη
  unfold fraction
  field_simp
  nlinarith [congrArg (fun t : ℝ => s.A * t) hw]

lemma fraction_le {p : Public} (s : State p) (hA : 0 ≤ s.A) (hη : 0 < s.η)
    (hq : 1 ≤ s.η * s.A) : fraction s ≤ 7 / 10 := by
  have hh := fraction_identity s hA hη
  have hm := mul_le_mul_of_nonneg_right hq (sq_nonneg (fraction s))
  have hp := fraction_pos s hA hη
  nlinarith

lemma fraction_accept_potential {p : Public} (s : State p)
    (hA : 0 < s.A) (hη : 0 < s.η) (hητ : s.η ≤ s.τ) (hq : 1 ≤ s.η * s.A) :
    fraction s + 6 * fraction (accept s) - 6 * fraction s ≤
      4 * (Real.log (accept s).A - Real.log s.A) := by
  have hAb := accepted_weight_bounds s hA hη hητ hq
  have hAn : 0 < (accept s).A := hA.trans hAb.1
  have hηn : 0 < (accept s).η := by
    rw [(accept_fields s).2.2.2]
    split_ifs <;> positivity
  have ht := fraction_pos s hA.le hη
  have htn := fraction_pos (accept s) hAn.le hηn
  have he := fraction_identity s hA.le hη
  have hen := fraction_identity (accept s) hAn.le hηn
  have hqp : 0 ≤ s.η * s.A := by positivity
  by_cases hf : s.τ = s.η
  · have hqnext : (s.η * s.A) / 2 ≤ (accept s).η * (accept s).A := by
      rw [(accept_fields s).2.2.2, ite_eq_left hf]
      nlinarith [hAb.1]
    have htbound := PointwiseHessianLocalization.accepted_fraction hqp ht htn he hen hqnext
    have hlog : fraction s ≤ Real.log (accept s).A - Real.log s.A := by
      have hh := CoarseGeneralized.relative_increment_le_log hA (weight_pos hA.le hη).le
      rw [(accept_fields s).1, hf, div_self hη.ne', one_mul]
      exact hh
    linarith
  · have hqnext : 2 * (s.η * s.A) ≤ (accept s).η * (accept s).A := by
      rw [(accept_fields s).2.2.2, ite_eq_right hf]
      nlinarith [hAb.1]
    have htbound := PointwiseHessianLocalization.rejected_fraction hqp ht
      (fraction_le s hA.le hη hq) htn he hen hqnext
    have hlog := Real.log_le_log hA hAb.1.le
    linarith

lemma good_full_progress {p : Public} (s : State p) {F : ℝ}
    (hA : 0 < s.A) (hη : 0 < s.η) (hq : 1 ≤ s.η * s.A)
    (hF : 1 ≤ F) (hupper : s.η * s.A ≤ 2 * F ^ 2) (hfull : s.τ = s.η) :
    1 ≤ 3 * F * (Real.log (accept s).A - Real.log s.A) := by
  have ht := fraction_pos s hA.le hη
  have htb := fraction_le s hA.le hη hq
  have he := fraction_identity s hA.le hη
  have hm := mul_le_mul_of_nonneg_right hupper (sq_nonneg (fraction s))
  have hprod : 1 ≤ 3 * F * fraction s := by
    have hp : 0 ≤ F * fraction s := mul_nonneg (by linarith) ht.le
    nlinarith [sq_nonneg (F * fraction s - 1 / 3)]
  have hlog : fraction s ≤ Real.log (accept s).A - Real.log s.A := by
    rw [(accept_fields s).1, hfull, div_self hη.ne', one_mul]
    exact CoarseGeneralized.relative_increment_le_log hA (weight_pos hA.le hη).le
  exact hprod.trans (mul_le_mul_of_nonneg_left hlog (by positivity))

lemma good_full_card {p : Public} (s : ℕ → State p) (S : Finset ℕ) (N : ℕ) {D : ℝ}
    (hD : 0 ≤ D) (hS : S ⊆ Finset.range N)
    (hA : ∀ i ≤ N, 0 < (s i).A) (hη : ∀ i < N, 0 < (s i).η)
    (hq : ∀ i < N, 1 ≤ (s i).η * (s i).A)
    (hmono : ∀ i < N, (s i).A ≤ (s (i + 1)).A)
    (hend : ∀ i < N, (s i).A ≤ (s N).A)
    (hstep : ∀ i ∈ S, (s (i + 1)).A = (accept (s i)).A)
    (hfull : ∀ i ∈ S, (s i).τ = (s i).η)
    (hgood : ∀ i ∈ S, (s i).η ≤ 2 * PointwiseHessianCounting.threshold D (s i).A) :
    (S.card : ℝ) ≤ 3 * PointwiseHessianCounting.level D (s N).A *
      (Real.log (s N).A - Real.log (s 0).A) := by
  let F := PointwiseHessianCounting.level D (s N).A
  apply PointwiseHessianCounting.selected_log_count (fun i => (s i).A) S N
    (show 0 ≤ 3 * F by have := PointwiseHessianCounting.level_pos D (s N).A; positivity)
    hS hA hmono
  intro i hi
  have hin : i < N := Finset.mem_range.mp (hS hi)
  have hAi := hA i hin.le
  have hF : PointwiseHessianCounting.level D (s i).A ≤ F :=
    PointwiseHessianCounting.level_mono hD hAi.le (hend i hin)
  have hsq := pow_le_pow_left₀ (PointwiseHessianCounting.level_pos D (s i).A).le hF 2
  have hh := mul_le_mul_of_nonneg_right (hgood i hi) hAi.le
  have he : 2 * PointwiseHessianCounting.threshold D (s i).A * (s i).A =
      2 * PointwiseHessianCounting.level D (s i).A ^ 2 := by
    unfold PointwiseHessianCounting.threshold
    field_simp
  rw [he] at hh
  have hupper : (s i).η * (s i).A ≤ 2 * F ^ 2 := by linarith
  rw [hstep i hi]
  exact good_full_progress (s i) hAi (hη i hin) (hq i hin)
    (le_max_left _ _) hupper (hfull i hi)

lemma good_damped_card (A η : ℕ → ℝ) (S : Finset ℕ) {D F : ℝ}
    (hD : 0 < D) (hA : ∀ i ∈ S, 0 < A i)
    (hF : ∀ i ∈ S, PointwiseHessianCounting.level D (A i) ≤ F)
    (hgood : ∀ i ∈ S, PointwiseHessianCounting.threshold D (A i) / 2 ≤ η i)
    (henergy : ∑ i ∈ S, A i * η i ^ 3 ≤ D ^ 2) (hFp : 0 ≤ F) :
    (S.card : ℝ) ≤ 8 * F := by
  have hcharge : (S.card : ℝ) * D ^ 2 ≤ 8 * F * (∑ i ∈ S, A i * η i ^ 3) := by
    calc
      _ = ∑ _i ∈ S, D ^ 2 := by simp
      _ ≤ ∑ i ∈ S, 8 * F * A i * η i ^ 3 :=
        Finset.sum_le_sum (fun i hi => PointwiseHessianCounting.rejection_charge hD.le
          (hA i hi) (hF i hi) (hgood i hi))
      _ = _ := by rw [Finset.mul_sum]; congr 1; ext i; ring
  have hh := mul_le_mul_of_nonneg_left henergy (show 0 ≤ 8 * F by positivity)
  have he : (S.card : ℝ) * D ^ 2 ≤ (8 * F) * D ^ 2 := hcharge.trans hh
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos hD)).mp he

lemma outer_count {p : Public} (s : ℕ → State p) (N : ℕ) {D : ℝ}
    (hD : 0 < D) (hA : ∀ i ≤ N, 0 < (s i).A) (hη : ∀ i ≤ N, 0 < (s i).η)
    (hq : ∀ i < N, 1 ≤ (s i).η * (s i).A) (hητ : ∀ i < N, (s i).η ≤ (s i).τ)
    (hnextA : ∀ i < N, (s (i + 1)).A = (accept (s i)).A)
    (hnextη : ∀ i < N, (s (i + 1)).η = (accept (s i)).η)
    (hend : ∀ i < N, (s i).A ≤ (s N).A)
    (henergy : (∑ i ∈ Finset.range N,
      if (s i).τ = (s i).η then 0 else (s i).A * (s i).η ^ 3) ≤ D ^ 2) :
    (N : ℝ) * Real.log 2 ≤
      2 * Real.log 2 * (3 * PointwiseHessianCounting.level D (s N).A *
        (Real.log (s N).A - Real.log (s 0).A) + 8 * PointwiseHessianCounting.level D (s N).A) +
      |Real.log (s 0).η - Real.log (PointwiseHessianCounting.threshold D (s 0).A)| +
      Real.log (PointwiseHessianCounting.threshold D (s 0).A) -
      Real.log (PointwiseHessianCounting.threshold D (s N).A) := by
  classical
  let F := PointwiseHessianCounting.level D (s N).A
  let L := Real.log (s N).A - Real.log (s 0).A
  let Gf := (Finset.range N).filter (fun i => (s i).τ = (s i).η ∧
    (s i).η ≤ 2 * PointwiseHessianCounting.threshold D (s i).A)
  let Gr := (Finset.range N).filter (fun i => (s i).τ ≠ (s i).η ∧
    PointwiseHessianCounting.threshold D (s i).A / 2 ≤ (s i).η)
  let good : ℕ → Bool := fun i => decide (((s i).τ = (s i).η ∧
    (s i).η ≤ 2 * PointwiseHessianCounting.threshold D (s i).A) ∨
    ((s i).τ ≠ (s i).η ∧ PointwiseHessianCounting.threshold D (s i).A / 2 ≤ (s i).η))
  have hmono (i : ℕ) (hi : i < N) : (s i).A ≤ (s (i + 1)).A := by
    rw [hnextA i hi]
    exact (accepted_weight_bounds (s i) (hA i hi.le) (hη i hi.le) (hητ i hi) (hq i hi)).1.le
  have hGf : (Gf.card : ℝ) ≤ 3 * F * L := by
    apply good_full_card s Gf N hD.le (Finset.filter_subset _ _) hA
      (fun i hi => hη i hi.le) hq hmono hend
    · intro i hi
      exact hnextA i (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)
    · intro i hi
      exact (Finset.mem_filter.mp hi).2.1
    · intro i hi
      exact (Finset.mem_filter.mp hi).2.2
  have hGr : (Gr.card : ℝ) ≤ 8 * F := by
    apply good_damped_card (fun i => (s i).A) (fun i => (s i).η) Gr hD
    · intro i hi
      exact hA i (Finset.mem_range.mp (Finset.mem_filter.mp hi).1).le
    · intro i hi
      have hin := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
      exact PointwiseHessianCounting.level_mono hD.le (hA i hin.le).le (hend i hin)
    · intro i hi
      exact (Finset.mem_filter.mp hi).2.2
    · apply le_trans _ henergy
      change (∑ i ∈ (Finset.range N).filter _, _) ≤ _
      rw [Finset.sum_filter]
      apply Finset.sum_le_sum
      intro i hi
      have hin := Finset.mem_range.mp hi
      have hAp := hA i hin.le
      have hηp := hη i hin.le
      split_ifs <;> simp_all
      positivity
    · exact (PointwiseHessianCounting.level_pos D (s N).A).le
  have hgood : (∑ i ∈ Finset.range N, if good i then (1 : ℝ) else 0) =
      (Gf.card : ℝ) + (Gr.card : ℝ) := by
    have hf : (Gf.card : ℝ) = ∑ i ∈ Finset.range N,
        if (s i).τ = (s i).η ∧ (s i).η ≤ 2 * PointwiseHessianCounting.threshold D (s i).A
        then (1 : ℝ) else 0 := by simp [Gf]
    have hr : (Gr.card : ℝ) = ∑ i ∈ Finset.range N,
        if (s i).τ ≠ (s i).η ∧ PointwiseHessianCounting.threshold D (s i).A / 2 ≤ (s i).η
        then (1 : ℝ) else 0 := by simp [Gr]
    rw [hf, hr, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases ht : (s i).τ = (s i).η <;> simp [good, ht]
  let P := fun i => |Real.log (s i).η - Real.log (PointwiseHessianCounting.threshold D (s i).A)|
  let V := fun i => Real.log (PointwiseHessianCounting.threshold D (s i).A)
  have hpot (i : ℕ) (hi : i < N) : P (i + 1) - P i ≤
      (if good i then Real.log 2 else -Real.log 2) + (V i - V (i + 1)) := by
    dsimp only [P, V]
    rw [hnextη i hi, (accept_fields (s i)).2.2.2]
    by_cases ht : (s i).τ = (s i).η
    · simpa [good, ht] using PointwiseHessianCounting.full_log_potential hD.le
        (hA i hi.le) (hmono i hi) (hη i hi.le)
    · simpa [good, ht] using PointwiseHessianCounting.damped_log_potential hD.le
        (hA i hi.le) (hmono i hi) (hη i hi.le)
  have hh := PointwiseHessianCounting.potential_count P V good N (abs_nonneg _) hpot
  rw [hgood] at hh
  have hc : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hg := mul_le_mul_of_nonneg_left (add_le_add hGf hGr) (show 0 ≤ 2 * Real.log 2 by positivity)
  dsimp only [P, V, F, L] at hh hg
  linarith

lemma damped_charge {A a η M r : ℝ} (hA : 0 ≤ A) (ha : 0 ≤ a)
    (hη : 0 ≤ η) (hbound : η ≤ 1024 * M * r) :
    A * η ^ 3 ≤ (1024 * M) ^ 2 * ((A + a) * η * r ^ 2) := by
  have hs := pow_le_pow_left₀ hη hbound 2
  have hm := mul_le_mul_of_nonneg_left hs (mul_nonneg hA hη)
  have hh := mul_le_mul_of_nonneg_right (show A * η ≤ (A + a) * η by nlinarith)
    (sq_nonneg (1024 * M * r))
  nlinarith only [hm, hh]

lemma damped_energy_sum (S : Finset ℕ) (A a η r : ℕ → ℝ) {M R : ℝ}
    (hA : ∀ i ∈ S, 0 ≤ A i) (ha : ∀ i ∈ S, 0 ≤ a i) (hη : ∀ i ∈ S, 0 ≤ η i)
    (hbound : ∀ i ∈ S, η i ≤ 1024 * M * r i)
    (henergy : ∑ i ∈ S, (A i + a i) * η i * r i ^ 2 ≤ (8 / 3 : ℝ) * R ^ 2) :
    (∑ i ∈ S, A i * η i ^ 3) ≤ (2048 * M * R) ^ 2 := by
  have hh : (∑ i ∈ S, A i * η i ^ 3) ≤
      (1024 * M) ^ 2 * (∑ i ∈ S, (A i + a i) * η i * r i ^ 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i hi => damped_charge (hA i hi) (ha i hi) (hη i hi) (hbound i hi))
  have hm := mul_le_mul_of_nonneg_left henergy (sq_nonneg (1024 * M))
  nlinarith [sq_nonneg (M * R)]

end LongTails.Proofs.PointwiseHessianOuter
