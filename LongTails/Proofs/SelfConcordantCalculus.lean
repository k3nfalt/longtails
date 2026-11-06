import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.IntermediateValue

namespace LongTails.Proofs.SelfConcordantCalculus

open Set Real

lemma le_of_deriv_nonpos {F F' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ x ∈ Icc a b, HasDerivAt F (F' x) x) (h : ∀ x ∈ Icc a b, F' x ≤ 0) : F b ≤ F a :=
  image_le_of_deriv_right_le_deriv_boundary (f := F) (B := fun _ => F a) (B' := fun _ => 0)
    (fun x hx => (hF x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hF x (Ico_subset_Icc_self hx)).hasDerivWithinAt)
    le_rfl continuousOn_const (fun _ _ => hasDerivWithinAt_const _ _ _)
    (fun x hx => h x (Ico_subset_Icc_self hx)) ⟨hab, le_rfl⟩

lemma le_of_deriv_nonneg {F F' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ x ∈ Icc a b, HasDerivAt F (F' x) x) (h : ∀ x ∈ Icc a b, 0 ≤ F' x) : F a ≤ F b := by
  have := le_of_deriv_nonpos (F := fun x => -F x) (F' := fun x => -F' x) hab
    (fun x hx => (hF x hx).neg) (fun x hx => by linarith [h x hx])
  linarith

structure SC1 (φ φ1 ψ ψ1 : ℝ → ℝ) (a b : ℝ) : Prop where
  hφ : ∀ u ∈ Icc a b, HasDerivAt φ (φ1 u) u
  hφ1 : ∀ u ∈ Icc a b, HasDerivAt φ1 (ψ u) u
  hψ : ∀ u ∈ Icc a b, HasDerivAt ψ (ψ1 u) u
  pos : ∀ u ∈ Icc a b, 0 < ψ u
  sc : ∀ u ∈ Icc a b, |ψ1 u| ≤ 2 * √(ψ u) * ψ u

structure Comp (ψ χ χ1 : ℝ → ℝ) (a b : ℝ) : Prop where
  hχ : ∀ u ∈ Icc a b, HasDerivAt χ (χ1 u) u
  pos : ∀ u ∈ Icc a b, 0 < χ u
  bd : ∀ u ∈ Icc a b, |χ1 u| ≤ 2 * √(ψ u) * χ u

noncomputable def hinv (ψ : ℝ → ℝ) (u : ℝ) : ℝ := 1 / √(ψ u)

section Lip

variable {φ φ1 ψ ψ1 : ℝ → ℝ} {a b : ℝ}

lemma hinv_pos (S : SC1 φ φ1 ψ ψ1 a b) {u : ℝ} (hu : u ∈ Icc a b) : 0 < hinv ψ u := by
  have := S.pos u hu
  unfold hinv; positivity

lemma hinv_deriv (S : SC1 φ φ1 ψ ψ1 a b) {u : ℝ} (hu : u ∈ Icc a b) :
    HasDerivAt (hinv ψ) (-(ψ1 u / (2 * √(ψ u))) / (√(ψ u)) ^ 2) u := by
  have hp := S.pos u hu
  have hs : √(ψ u) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  have h1 := (S.hψ u hu).sqrt hp.ne'
  have h2 := h1.inv hs
  have : hinv ψ = fun y => (√(ψ y))⁻¹ := by funext y; simp [hinv]
  rw [this]
  exact h2

lemma hinv_deriv_abs (S : SC1 φ φ1 ψ ψ1 a b) {u : ℝ} (hu : u ∈ Icc a b) :
    |(-(ψ1 u / (2 * √(ψ u))) / (√(ψ u)) ^ 2)| ≤ 1 := by
  have hp := S.pos u hu
  have hsp : 0 < √(ψ u) := Real.sqrt_pos.mpr hp
  have hsq : (√(ψ u)) ^ 2 = ψ u := Real.sq_sqrt hp.le
  rw [abs_div, abs_neg, abs_div, hsq, abs_of_pos hp,
    abs_of_pos (by positivity : (0:ℝ) < 2 * √(ψ u))]
  rw [div_div, div_le_one (by positivity)]
  have := S.sc u hu
  linarith

lemma hinv_lip_up (S : SC1 φ φ1 ψ ψ1 a b) {u w : ℝ} (hu : u ∈ Icc a b) (hw : w ∈ Icc a b)
    (huw : u ≤ w) : hinv ψ w ≤ hinv ψ u + (w - u) := by
  have hsub : Icc u w ⊆ Icc a b := Icc_subset_Icc hu.1 hw.2
  have := le_of_deriv_nonpos (F := fun x => hinv ψ x - x)
    (F' := fun x => -(ψ1 x / (2 * √(ψ x))) / (√(ψ x)) ^ 2 - 1) huw
    (fun x hx => (hinv_deriv S (hsub hx)).sub (hasDerivAt_id' x))
    (fun x hx => by
      have := hinv_deriv_abs S (hsub hx)
      have := le_abs_self (-(ψ1 x / (2 * √(ψ x))) / (√(ψ x)) ^ 2)
      linarith)
  linarith

lemma hinv_lip_down (S : SC1 φ φ1 ψ ψ1 a b) {u w : ℝ} (hu : u ∈ Icc a b) (hw : w ∈ Icc a b)
    (huw : u ≤ w) : hinv ψ u - (w - u) ≤ hinv ψ w := by
  have hsub : Icc u w ⊆ Icc a b := Icc_subset_Icc hu.1 hw.2
  have := le_of_deriv_nonneg (F := fun x => hinv ψ x + x)
    (F' := fun x => -(ψ1 x / (2 * √(ψ x))) / (√(ψ x)) ^ 2 + 1) huw
    (fun x hx => (hinv_deriv S (hsub hx)).add (hasDerivAt_id' x))
    (fun x hx => by
      have := hinv_deriv_abs S (hsub hx)
      have := neg_abs_le (-(ψ1 x / (2 * √(ψ x))) / (√(ψ x)) ^ 2)
      linarith)
  linarith

lemma sqrt_eq_inv_hinv (S : SC1 φ φ1 ψ ψ1 a b) {u : ℝ} (hu : u ∈ Icc a b) :
    √(ψ u) = 1 / hinv ψ u := by
  have := S.pos u hu
  unfold hinv; field_simp

lemma psi_eq (S : SC1 φ φ1 ψ ψ1 a b) {u : ℝ} (hu : u ∈ Icc a b) :
    ψ u = 1 / hinv ψ u ^ 2 := by
  have hp := S.pos u hu
  unfold hinv
  rw [div_pow, Real.sq_sqrt hp.le]; field_simp

lemma psi_le_of_hinv (S : SC1 φ φ1 ψ ψ1 a b) {u c : ℝ} (hu : u ∈ Icc a b) (hc : 0 < c)
    (h : c ≤ hinv ψ u) : ψ u ≤ 1 / c ^ 2 := by
  rw [psi_eq S hu]
  apply one_div_le_one_div_of_le (by positivity)
  exact pow_le_pow_left₀ hc.le h 2

lemma psi_ge_of_hinv (S : SC1 φ φ1 ψ ψ1 a b) {u c : ℝ} (hu : u ∈ Icc a b)
    (h : hinv ψ u ≤ c) : 1 / c ^ 2 ≤ ψ u := by
  rw [psi_eq S hu]
  have := hinv_pos S hu
  apply one_div_le_one_div_of_le (by positivity)
  exact pow_le_pow_left₀ this.le h 2

lemma sqrt_le_of_hinv (S : SC1 φ φ1 ψ ψ1 a b) {u c : ℝ} (hu : u ∈ Icc a b) (hc : 0 < c)
    (h : c ≤ hinv ψ u) : √(ψ u) ≤ 1 / c := by
  rw [sqrt_eq_inv_hinv S hu]
  exact one_div_le_one_div_of_le hc h

end Lip

section Short

variable {φ φ1 ψ ψ1 χ χ1 : ℝ → ℝ} {a b : ℝ}

lemma comp_short_up (S : SC1 φ φ1 ψ ψ1 a b) (C : Comp ψ χ χ1 a b) {u : ℝ} (hu : u ∈ Icc a b)
    (hlt : u - a < hinv ψ a) :
    χ u * (hinv ψ a - (u - a)) ^ 2 ≤ χ a * hinv ψ a ^ 2 := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hu.1.trans hu.2⟩
  have hsub : Icc a u ⊆ Icc a b := Icc_subset_Icc le_rfl hu.2
  have := le_of_deriv_nonpos (F := fun x => χ x * (hinv ψ a - (x - a)) ^ 2)
    (F' := fun x => χ1 x * (hinv ψ a - (x - a)) ^ 2 +
      χ x * (2 * (hinv ψ a - (x - a)) * (-1))) hu.1
    (fun x hx => by
      have h1 := C.hχ x (hsub hx)
      have h2 : HasDerivAt (fun x => (hinv ψ a - (x - a)) ^ 2)
          (2 * (hinv ψ a - (x - a)) * (-1)) x := by
        have h := (((hasDerivAt_id' x).sub_const a).const_sub (hinv ψ a)).pow 2
        convert h using 1
        norm_num
      exact h1.mul h2)
    (fun x hx => by
      have hxab := hsub hx
      have hc : 0 < hinv ψ a - (x - a) := by linarith [hx.2]
      have hle : hinv ψ a - (x - a) ≤ hinv ψ x := hinv_lip_down S ha hxab hx.1
      have hsq := sqrt_le_of_hinv S hxab hc hle
      have hχ := C.pos x hxab
      have hb := C.bd x hxab
      have : χ1 x ≤ 2 * χ x / (hinv ψ a - (x - a)) := by
        have := le_abs_self (χ1 x)
        calc χ1 x ≤ 2 * √(ψ x) * χ x := by linarith
          _ ≤ 2 * (1 / (hinv ψ a - (x - a))) * χ x := by
            apply mul_le_mul_of_nonneg_right _ hχ.le; linarith
          _ = 2 * χ x / (hinv ψ a - (x - a)) := by ring
      have hmul : χ1 x * (hinv ψ a - (x - a)) ≤ 2 * χ x := by
        calc χ1 x * (hinv ψ a - (x - a)) ≤ 2 * χ x / (hinv ψ a - (x - a)) *
              (hinv ψ a - (x - a)) := mul_le_mul_of_nonneg_right this hc.le
          _ = 2 * χ x := by field_simp
      nlinarith)
  simpa using this

lemma comp_short_down (S : SC1 φ φ1 ψ ψ1 a b) (C : Comp ψ χ χ1 a b) {u : ℝ} (hu : u ∈ Icc a b)
    (hlt : u - a < hinv ψ a) :
    χ a * (hinv ψ a - (u - a)) ^ 2 ≤ χ u * hinv ψ a ^ 2 := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hu.1.trans hu.2⟩
  have hsub : Icc a u ⊆ Icc a b := Icc_subset_Icc le_rfl hu.2
  have hpos : ∀ x ∈ Icc a u, 0 < hinv ψ a - (x - a) := fun x hx => by linarith [hx.2]
  have := le_of_deriv_nonneg (F := fun x => χ x / (hinv ψ a - (x - a)) ^ 2)
    (F' := fun x => (χ1 x * (hinv ψ a - (x - a)) ^ 2 -
      χ x * (2 * (hinv ψ a - (x - a)) * (-1))) / ((hinv ψ a - (x - a)) ^ 2) ^ 2) hu.1
    (fun x hx => by
      have h1 := C.hχ x (hsub hx)
      have h2 : HasDerivAt (fun x => (hinv ψ a - (x - a)) ^ 2)
          (2 * (hinv ψ a - (x - a)) * (-1)) x := by
        have h := (((hasDerivAt_id' x).sub_const a).const_sub (hinv ψ a)).pow 2
        convert h using 1
        norm_num
      exact h1.div h2 (by have := hpos x hx; positivity))
    (fun x hx => by
      have hxab := hsub hx
      have hc := hpos x hx
      have hle : hinv ψ a - (x - a) ≤ hinv ψ x := hinv_lip_down S ha hxab hx.1
      have hsq := sqrt_le_of_hinv S hxab hc hle
      have hχ := C.pos x hxab
      have hb := C.bd x hxab
      have : -(2 * χ x / (hinv ψ a - (x - a))) ≤ χ1 x := by
        have := neg_abs_le (χ1 x)
        have : 2 * √(ψ x) * χ x ≤ 2 * (1 / (hinv ψ a - (x - a))) * χ x := by
          apply mul_le_mul_of_nonneg_right _ hχ.le; linarith
        have e : 2 * (1 / (hinv ψ a - (x - a))) * χ x = 2 * χ x / (hinv ψ a - (x - a)) := by ring
        linarith
      have hmul : -(2 * χ x) ≤ χ1 x * (hinv ψ a - (x - a)) := by
        have := mul_le_mul_of_nonneg_right this hc.le
        have e : -(2 * χ x / (hinv ψ a - (x - a))) * (hinv ψ a - (x - a)) = -(2 * χ x) := by
          field_simp
        linarith
      apply div_nonneg _ (by positivity)
      nlinarith)
  have hc0 := hpos u ⟨hu.1, le_rfl⟩
  have hapos := hinv_pos S ha
  rw [sub_self, sub_zero, div_le_div_iff₀ (by positivity) (by positivity)] at this
  nlinarith [C.pos a ha, C.pos u hu, sq_nonneg (hinv ψ a - (u - a))]

end Short

section Osc

variable {φ φ1 ψ ψ1 χ χ1 : ℝ → ℝ} {m e Δ : ℝ}

lemma amgm_aux (c r : ℝ) (hc : 0 < c) : 2 * r ≤ c * r ^ 2 + 1 / c := by
  have : c * r ^ 2 + 1 / c - 2 * r = (c * r - 1) ^ 2 / c := by field_simp; ring
  have : 0 ≤ (c * r - 1) ^ 2 / c := by positivity
  linarith

lemma phi1_mono (S : SC1 φ φ1 ψ ψ1 m e) {u w : ℝ} (hu : u ∈ Icc m e) (hw : w ∈ Icc m e)
    (huw : u ≤ w) : φ1 u ≤ φ1 w :=
  le_of_deriv_nonneg huw (fun x hx => S.hφ1 x (Icc_subset_Icc hu.1 hw.2 hx))
    (fun x hx => (S.pos x (Icc_subset_Icc hu.1 hw.2 hx)).le)

lemma phi_mono_right (S : SC1 φ φ1 ψ ψ1 m e) (h0 : 0 ≤ φ1 m) {u w : ℝ} (hu : u ∈ Icc m e)
    (hw : w ∈ Icc m e) (huw : u ≤ w) : φ u ≤ φ w :=
  le_of_deriv_nonneg huw (fun x hx => S.hφ x (Icc_subset_Icc hu.1 hw.2 hx))
    (fun _ hx => h0.trans (phi1_mono S ⟨le_rfl, hu.1.trans hu.2⟩
      (Icc_subset_Icc hu.1 hw.2 hx) (hu.1.trans hx.1)))

lemma convex_tangent (S : SC1 φ φ1 ψ ψ1 m e) {u w : ℝ} (hu : u ∈ Icc m e) (hw : w ∈ Icc m e)
    (huw : u ≤ w) : φ u + φ1 u * (w - u) ≤ φ w := by
  have := le_of_deriv_nonneg (F := fun x => φ x - φ1 u * (x - u)) (F' := fun x => φ1 x - φ1 u)
    huw
    (fun x hx => by
      have h2 : HasDerivAt (fun x => φ1 u * (x - u)) (φ1 u) x := by
        simpa using ((hasDerivAt_id' x).sub_const u).const_mul (φ1 u)
      exact (S.hφ x (Icc_subset_Icc hu.1 hw.2 hx)).sub h2)
    (fun x hx => by
      have := phi1_mono S hu (Icc_subset_Icc hu.1 hw.2 hx) hx.1
      linarith)
  simp only [sub_self, mul_zero, sub_zero] at this
  linarith

lemma phi1_increment (S : SC1 φ φ1 ψ ψ1 m e) {u w K : ℝ} (hu : u ∈ Icc m e) (hw : w ∈ Icc m e)
    (huw : u ≤ w) (hK : ∀ x ∈ Icc u w, ψ x ≤ K) : φ1 w ≤ φ1 u + K * (w - u) := by
  have := le_of_deriv_nonpos (F := fun x => φ1 x - K * x) (F' := fun x => ψ x - K) huw
    (fun x hx => (S.hφ1 x (Icc_subset_Icc hu.1 hw.2 hx)).sub ((hasDerivAt_id' x).const_mul K)
      |>.congr_deriv (by simp))
    (fun x hx => by linarith [hK x hx])
  linarith

lemma log_ratio_bound (S : SC1 φ φ1 ψ ψ1 m e) (hme : m ≤ e) (h0 : 0 ≤ φ1 m)
    (hΔ : φ e - φ m ≤ Δ) :
    Real.log (1 + (e - m) / hinv ψ e) ≤ Δ + 1 := by
  have he : e ∈ Icc m e := ⟨hme, le_rfl⟩
  have hm : m ∈ Icc m e := ⟨le_rfl, hme⟩
  set A := hinv ψ e with hA
  have hApos : 0 < A := hinv_pos S he
  have hposx : ∀ x ∈ Icc m e, 0 < A + (e - x) := fun x hx => by linarith [hx.2]
  have := le_of_deriv_nonneg
    (F := fun x => (e - x) * φ1 x + φ x + Real.log (A + (e - x)) + A / (A + (e - x)))
    (F' := fun x => ((-1) * φ1 x + (e - x) * ψ x) + φ1 x + (-1) / (A + (e - x)) +
      -(A * (-1)) / (A + (e - x)) ^ 2) hme
    (fun x hx => by
      have hp := hposx x hx
      have h1 : HasDerivAt (fun x => e - x) (-1) x := by
        simpa using (hasDerivAt_id' x).const_sub e
      have h2 : HasDerivAt (fun x => A + (e - x)) (-1) x := by
        simpa using h1.const_add A
      have h3 := (h2.log hp.ne')
      have h4 := (hasDerivAt_const x A).div h2 hp.ne'
      have h5 := (h1.mul (S.hφ1 x hx)).add (S.hφ x hx)
      convert (h5.add h3).add h4 using 1
      simp)
    (fun x hx => by
      have hp := hposx x hx
      have hle : hinv ψ x ≤ A + (e - x) := by
        have := hinv_lip_down S hx he hx.2; linarith [hA]
      have hψ := psi_ge_of_hinv S hx hle
      have hex : 0 ≤ e - x := by linarith [hx.2]
      have : (e - x) * (1 / (A + (e - x)) ^ 2) ≤ (e - x) * ψ x :=
        mul_le_mul_of_nonneg_left hψ hex
      have e1 : ((-1) * φ1 x + (e - x) * ψ x) + φ1 x + (-1) / (A + (e - x)) +
          -(A * (-1)) / (A + (e - x)) ^ 2 =
          (e - x) * ψ x - (e - x) * (1 / (A + (e - x)) ^ 2) := by
        field_simp; ring
      rw [e1]; linarith)
  simp only [sub_self, zero_mul, zero_add, add_zero] at this
  have hAD : 0 < A + (e - m) := hposx m hm
  have hfrac : 0 ≤ A / (A + (e - m)) := by positivity
  rw [div_self hApos.ne'] at this
  have hφ1 : 0 ≤ (e - m) * φ1 m := mul_nonneg (by linarith) h0
  have hlog : Real.log (1 + (e - m) / A) = Real.log (A + (e - m)) - Real.log A := by
    rw [← Real.log_div hAD.ne' hApos.ne']
    congr 1; field_simp
  rw [hlog]
  linarith

lemma endpoint_term (S : SC1 φ φ1 ψ ψ1 m e) (hme : m ≤ e) (h0 : 0 ≤ φ1 m)
    (hΔ : φ e - φ m ≤ Δ) (hΔ0 : 0 ≤ Δ) :
    hinv ψ e / 2 * φ1 e - ((e - m) + hinv ψ e / 2) * φ1 m ≤ Δ + 1 := by
  have he : e ∈ Icc m e := ⟨hme, le_rfl⟩
  have hm : m ∈ Icc m e := ⟨le_rfl, hme⟩
  set A := hinv ψ e with hA
  have hApos : 0 < A := hinv_pos S he
  have hlow : ∀ x ∈ Icc m e, A - (e - x) ≤ hinv ψ x := fun x hx => by
    have := hinv_lip_up S hx he hx.2; linarith [hA]
  have hDφ : 0 ≤ (e - m) * φ1 m := mul_nonneg (by linarith) h0
  by_cases hcase : m ≤ e - A / 2
  · obtain ⟨u1, hu1def⟩ : ∃ u1 : ℝ, u1 = e - A / 2 := ⟨_, rfl⟩
    rw [← hu1def] at hcase
    have hu1 : u1 ∈ Icc m e := ⟨hcase, by linarith⟩
    have ht := convex_tangent S hu1 he hu1.2
    have hmono := phi_mono_right S h0 hm hu1 hcase
    have hK : ∀ x ∈ Icc u1 e, ψ x ≤ 1 / (A / 2) ^ 2 := fun x hx => by
      have hx' : x ∈ Icc m e := ⟨hcase.trans hx.1, hx.2⟩
      apply psi_le_of_hinv S hx' (by positivity)
      have := hlow x hx'; linarith [hx.1]
    have hinc := phi1_increment S hu1 he hu1.2 hK
    have e1 : 1 / (A / 2) ^ 2 * (e - u1) = 2 / A := by
      rw [hu1def]; field_simp; ring
    have e2 : φ1 u1 * (e - u1) = A / 2 * φ1 u1 := by rw [hu1def]; ring
    have h1 : A / 2 * φ1 u1 ≤ Δ := by linarith
    have h2 : A / 2 * φ1 e ≤ A / 2 * φ1 u1 + 1 := by
      have := mul_le_mul_of_nonneg_left hinc (by linarith : (0:ℝ) ≤ A / 2)
      rw [e1] at this
      have e3 : A / 2 * (φ1 u1 + 2 / A) = A / 2 * φ1 u1 + 1 := by
        field_simp
      linarith
    have h3 : 0 ≤ (A / 2) * φ1 m := mul_nonneg (by linarith) h0
    nlinarith
  · push Not at hcase
    have hK : ∀ x ∈ Icc m e, ψ x ≤ 1 / (A / 2) ^ 2 := fun x hx => by
      apply psi_le_of_hinv S hx (by positivity)
      have := hlow x hx; linarith [hx.1]
    have hinc := phi1_increment S hm he hme hK
    have h2 : A / 2 * φ1 e ≤ A / 2 * φ1 m + 1 := by
      have := mul_le_mul_of_nonneg_left hinc (by linarith : (0:ℝ) ≤ A / 2)
      have e3 : A / 2 * (φ1 m + 1 / (A / 2) ^ 2 * (e - m)) = A / 2 * φ1 m + 2 * (e - m) / A := by
        field_simp
      have e4 : 2 * (e - m) / A ≤ 1 := by
        rw [div_le_one hApos]; linarith
      linarith
    nlinarith

lemma osc_right (S : SC1 φ φ1 ψ ψ1 m e) (C : Comp ψ χ χ1 m e) (hme : m ≤ e) (h0 : 0 ≤ φ1 m)
    (hΔ : φ e - φ m ≤ Δ) (hΔ0 : 0 ≤ Δ) :
    Real.log (χ e) - Real.log (χ m) ≤ 3 * Δ + 3 ∧
      Real.log (χ m) - Real.log (χ e) ≤ 3 * Δ + 3 := by
  have he : e ∈ Icc m e := ⟨hme, le_rfl⟩
  have hm : m ∈ Icc m e := ⟨le_rfl, hme⟩
  set A := hinv ψ e with hA
  have hApos : 0 < A := hinv_pos S he
  set η := A / 2 with hη
  have hηpos : 0 < η := by positivity
  have hend := endpoint_term S hme h0 hΔ hΔ0
  rw [← hA, ← hη] at hend
  have hlr := log_ratio_bound S hme h0 hΔ
  rw [← hA] at hlr
  have hDA : 0 ≤ (e - m) / A := div_nonneg (by linarith) hApos.le
  have hlogη : Real.log ((e - m) + η) - Real.log η ≤ Real.log 2 + (Δ + 1) := by
    rw [← Real.log_div (by linarith) hηpos.ne']
    have heq : ((e - m) + η) / η = 1 + 2 * ((e - m) / A) := by
      rw [hη]; field_simp; ring
    have hle : ((e - m) + η) / η ≤ 2 * (1 + (e - m) / A) := by rw [heq]; linarith
    have hpos : 0 < ((e - m) + η) / η := by rw [heq]; linarith
    calc Real.log (((e - m) + η) / η) ≤ Real.log (2 * (1 + (e - m) / A)) :=
          Real.log_le_log hpos hle
      _ = Real.log 2 + Real.log (1 + (e - m) / A) := by
          rw [Real.log_mul (by norm_num) (by linarith)]
      _ ≤ Real.log 2 + (Δ + 1) := by linarith
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num); linarith
  have hposx : ∀ x ∈ Icc m e, 0 < e - x + η := fun x hx => by linarith [hx.2]
  have hderivs : ∀ x ∈ Icc m e,
      HasDerivAt (fun x => (e - x + η) * φ1 x + φ x)
        (((-1) * φ1 x + (e - x + η) * ψ x) + φ1 x) x ∧
      HasDerivAt (fun x => Real.log (e - x + η)) ((-1) / (e - x + η)) x ∧
      HasDerivAt (fun x => Real.log (χ x)) (χ1 x / χ x) x := fun x hx => by
    have h1 : HasDerivAt (fun x => e - x + η) (-1) x := by
      exact ((hasDerivAt_id' x).const_sub e).add_const η
    refine ⟨(h1.mul (S.hφ1 x hx)).add (S.hφ x hx), h1.log (hposx x hx).ne',
      (C.hχ x hx).log (C.pos x hx).ne'⟩
  have hamgm : ∀ x ∈ Icc m e, |χ1 x / χ x| ≤ (e - x + η) * ψ x + 1 / (e - x + η) := fun x hx => by
    have hχ := C.pos x hx
    have hp := S.pos x hx
    rw [abs_div, abs_of_pos hχ, div_le_iff₀ hχ]
    have h1 := C.bd x hx
    have h2 := amgm_aux (e - x + η) (√(ψ x)) (hposx x hx)
    rw [Real.sq_sqrt hp.le] at h2
    nlinarith
  constructor
  · have := le_of_deriv_nonpos
      (F := fun x => Real.log (χ x) - ((e - x + η) * φ1 x + φ x) + Real.log (e - x + η))
      (F' := fun x => χ1 x / χ x - (((-1) * φ1 x + (e - x + η) * ψ x) + φ1 x) +
        (-1) / (e - x + η)) hme
      (fun x hx => by
        obtain ⟨h1, h2, h3⟩ := hderivs x hx
        exact (h3.sub h1).add h2)
      (fun x hx => by
        have := hamgm x hx
        have := le_abs_self (χ1 x / χ x)
        have e1 : (-1) / (e - x + η) = -(1 / (e - x + η)) := by ring
        rw [e1]; linarith)
    simp only [sub_self, zero_add] at this
    linarith
  · have := le_of_deriv_nonneg
      (F := fun x => Real.log (χ x) + ((e - x + η) * φ1 x + φ x) - Real.log (e - x + η))
      (F' := fun x => χ1 x / χ x + (((-1) * φ1 x + (e - x + η) * ψ x) + φ1 x) -
        (-1) / (e - x + η)) hme
      (fun x hx => by
        obtain ⟨h1, h2, h3⟩ := hderivs x hx
        exact (h3.add h1).sub h2)
      (fun x hx => by
        have := hamgm x hx
        have := neg_abs_le (χ1 x / χ x)
        have e1 : (-1) / (e - x + η) = -(1 / (e - x + η)) := by ring
        rw [e1]; linarith)
    simp only [sub_self, zero_add] at this
    linarith

end Osc

section Full

variable {φ φ1 ψ ψ1 χ χ1 : ℝ → ℝ} {a b Δ : ℝ}

lemma SC1.mono (S : SC1 φ φ1 ψ ψ1 a b) {a' b' : ℝ} (h : Icc a' b' ⊆ Icc a b) :
    SC1 φ φ1 ψ ψ1 a' b' :=
  ⟨fun u hu => S.hφ u (h hu), fun u hu => S.hφ1 u (h hu), fun u hu => S.hψ u (h hu),
    fun u hu => S.pos u (h hu), fun u hu => S.sc u (h hu)⟩

lemma Comp.mono (C : Comp ψ χ χ1 a b) {a' b' : ℝ} (h : Icc a' b' ⊆ Icc a b) :
    Comp ψ χ χ1 a' b' :=
  ⟨fun u hu => C.hχ u (h hu), fun u hu => C.pos u (h hu), fun u hu => C.bd u (h hu)⟩

lemma neg_mem_Icc {u : ℝ} (hu : u ∈ Icc (-b) (-a)) : -u ∈ Icc a b :=
  ⟨by linarith [hu.2], by linarith [hu.1]⟩

lemma SC1.reflect (S : SC1 φ φ1 ψ ψ1 a b) :
    SC1 (fun u => φ (-u)) (fun u => -φ1 (-u)) (fun u => ψ (-u)) (fun u => -ψ1 (-u)) (-b) (-a) where
  hφ u hu := by
    have := (S.hφ (-u) (neg_mem_Icc hu)).comp u (hasDerivAt_neg u)
    exact this.congr_deriv (by ring)
  hφ1 u hu := by
    have := ((S.hφ1 (-u) (neg_mem_Icc hu)).comp u (hasDerivAt_neg u)).neg
    exact this.congr_deriv (by ring)
  hψ u hu := by
    have := (S.hψ (-u) (neg_mem_Icc hu)).comp u (hasDerivAt_neg u)
    exact this.congr_deriv (by ring)
  pos u hu := S.pos (-u) (neg_mem_Icc hu)
  sc u hu := by simpa [abs_neg] using S.sc (-u) (neg_mem_Icc hu)

lemma Comp.reflect (C : Comp ψ χ χ1 a b) :
    Comp (fun u => ψ (-u)) (fun u => χ (-u)) (fun u => -χ1 (-u)) (-b) (-a) where
  hχ u hu := by
    have := (C.hχ (-u) (neg_mem_Icc hu)).comp u (hasDerivAt_neg u)
    exact this.congr_deriv (by ring)
  pos u hu := C.pos (-u) (neg_mem_Icc hu)
  bd u hu := by simpa [abs_neg] using C.bd (-u) (neg_mem_Icc hu)

lemma osc_left (S : SC1 φ φ1 ψ ψ1 a b) (C : Comp ψ χ χ1 a b) (hab : a ≤ b) (h0 : φ1 b ≤ 0)
    (hΔ : φ a - φ b ≤ Δ) (hΔ0 : 0 ≤ Δ) :
    |Real.log (χ b) - Real.log (χ a)| ≤ 3 * Δ + 3 := by
  have h := osc_right S.reflect C.reflect (by linarith) (by simpa using h0)
    (by simpa using hΔ) hΔ0
  simp only [neg_neg] at h
  rw [abs_le]
  constructor <;> linarith [h.1, h.2]

lemma osc_right' (S : SC1 φ φ1 ψ ψ1 a b) (C : Comp ψ χ χ1 a b) (hab : a ≤ b) (h0 : 0 ≤ φ1 a)
    (hΔ : φ b - φ a ≤ Δ) (hΔ0 : 0 ≤ Δ) :
    |Real.log (χ b) - Real.log (χ a)| ≤ 3 * Δ + 3 := by
  have h := osc_right S C hab h0 hΔ hΔ0
  rw [abs_le]
  constructor <;> linarith [h.1, h.2]

lemma osc_full (S : SC1 φ φ1 ψ ψ1 a b) (C : Comp ψ χ χ1 a b) (hab : a ≤ b)
    (hosc : ∀ u ∈ Icc a b, ∀ w ∈ Icc a b, φ u - φ w ≤ Δ) (hΔ0 : 0 ≤ Δ) :
    |Real.log (χ b) - Real.log (χ a)| ≤ 6 * Δ + 6 := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  by_cases hpa : 0 ≤ φ1 a
  · have := osc_right' S C hab hpa (hosc b hb a ha) hΔ0
    linarith
  by_cases hpb : φ1 b ≤ 0
  · have := osc_left S C hab hpb (hosc a ha b hb) hΔ0
    linarith
  push Not at hpa hpb
  have hcont : ContinuousOn φ1 (Icc a b) := fun u hu => (S.hφ1 u hu).continuousAt.continuousWithinAt
  obtain ⟨m, hm, hm0⟩ := intermediate_value_Icc hab hcont ⟨hpa.le, hpb.le⟩
  have h1 := osc_right' (S.mono (Icc_subset_Icc hm.1 le_rfl)) (C.mono (Icc_subset_Icc hm.1 le_rfl))
    hm.2 hm0.ge (hosc b hb m hm) hΔ0
  have h2 := osc_left (S.mono (Icc_subset_Icc le_rfl hm.2)) (C.mono (Icc_subset_Icc le_rfl hm.2))
    hm.1 hm0.le (hosc a ha m hm) hΔ0
  calc |Real.log (χ b) - Real.log (χ a)|
      = |(Real.log (χ b) - Real.log (χ m)) + (Real.log (χ m) - Real.log (χ a))| := by
        congr 1; ring
    _ ≤ |Real.log (χ b) - Real.log (χ m)| + |Real.log (χ m) - Real.log (χ a)| := abs_add_le _ _
    _ ≤ 6 * Δ + 6 := by linarith

lemma second_order_lower (S : SC1 φ φ1 ψ ψ1 a b) (hab : a ≤ b) {m : ℝ}
    (hm : ∀ u ∈ Icc a b, m ≤ ψ u) :
    φ a + φ1 a * (b - a) + m / 2 * (b - a) ^ 2 ≤ φ b := by
  have hd : ∀ u ∈ Icc a b, 0 ≤ φ1 u - φ1 a - m * (u - a) := fun u hu => by
    have := le_of_deriv_nonneg (F := fun x => φ1 x - m * x) (F' := fun x => ψ x - m) hu.1
      (fun x hx => ((S.hφ1 x ⟨hx.1, hx.2.trans hu.2⟩).sub
        ((hasDerivAt_id' x).const_mul m)).congr_deriv
        (by simp))
      (fun x hx => by linarith [hm x ⟨hx.1, hx.2.trans hu.2⟩])
    linarith
  have := le_of_deriv_nonneg (F := fun x => φ x - φ1 a * (x - a) - m / 2 * (x - a) ^ 2)
    (F' := fun x => φ1 x - φ1 a - m * (x - a)) hab
    (fun x hx => by
      have h1 := S.hφ x hx
      have h2 : HasDerivAt (fun x => φ1 a * (x - a)) (φ1 a) x := by
        simpa using ((hasDerivAt_id' x).sub_const a).const_mul (φ1 a)
      have h3 : HasDerivAt (fun x => m / 2 * (x - a) ^ 2) (m * (x - a)) x := by
        have := (((hasDerivAt_id' x).sub_const a).pow 2).const_mul (m / 2)
        convert this using 1; simp; ring
      convert (h1.sub h2).sub h3 using 1)
    hd
  simp only [sub_self, mul_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow] at this
  linarith

end Full

section Wolfe1D

variable {φ φ1 ψ ψ1 : ℝ → ℝ} {a b : ℝ}

lemma tangent_left (S : SC1 φ φ1 ψ ψ1 a b) {u w : ℝ} (hu : u ∈ Icc a b) (hw : w ∈ Icc a b)
    (huw : u ≤ w) : φ w - φ1 w * (w - u) ≤ φ u := by
  have := le_of_deriv_nonpos (F := fun x => φ x - φ1 w * (x - w)) (F' := fun x => φ1 x - φ1 w)
    huw
    (fun x hx => by
      have h2 : HasDerivAt (fun x => φ1 w * (x - w)) (φ1 w) x := by
        simpa using ((hasDerivAt_id' x).sub_const w).const_mul (φ1 w)
      exact (S.hφ x (Icc_subset_Icc hu.1 hw.2 hx)).sub h2)
    (fun x hx => by
      have := phi1_mono S (Icc_subset_Icc hu.1 hw.2 hx) hw hx.2
      linarith)
  simp only [sub_self, mul_zero, sub_zero] at this
  linarith

lemma chord (S : SC1 φ φ1 ψ ψ1 0 1) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) :
    φ τ ≤ (1 - τ) * φ 0 + τ * φ 1 := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have t1 := convex_tangent S hτ h1 hτ.2
  have t2 := tangent_left S h0 hτ hτ.1
  have hτ0 := hτ.1
  have hτ1 : 0 ≤ 1 - τ := by linarith [hτ.2]
  nlinarith [mul_le_mul_of_nonneg_left t1 hτ0, mul_le_mul_of_nonneg_left t2 hτ1]

lemma wolfe_decrease (S : SC1 φ φ1 ψ ψ1 0 1) {m α : ℝ} (hm0 : 0 ≤ m)
    (hm : ∀ u ∈ Icc (0 : ℝ) 1, m ≤ ψ u)
    (hα : 0 < α) (hα1 : α < 1) (harm : φ 1 ≤ φ 0 + α * φ1 0) :
    m / 2 ≤ (1 - α) * (-φ1 0) ∧ α * m / 2 ≤ φ 0 - φ 1 := by
  have h := second_order_lower S zero_le_one hm
  simp only [sub_zero, one_pow, mul_one] at h
  have h1 : m / 2 ≤ (1 - α) * (-φ1 0) := by linarith
  refine ⟨h1, ?_⟩
  have h2 : α * (m / 2) ≤ α * ((1 - α) * (-φ1 0)) := mul_le_mul_of_nonneg_left h1 hα.le
  have h3 : 0 ≤ -φ1 0 := by nlinarith
  have h4 : α * ((1 - α) * (-φ1 0)) ≤ α * (-φ1 0) := by
    have := mul_nonneg hα.le (mul_nonneg hα.le h3)
    nlinarith
  linarith

lemma wolfe_theta_upper (S : SC1 φ φ1 ψ ψ1 0 1) {m M α : ℝ} (hm0 : 0 < m)
    (hm : ∀ u ∈ Icc (0 : ℝ) 1, m ≤ ψ u) (hM : ∀ u ∈ Icc (0 : ℝ) 1, ψ u ≤ M)
    (hα : 0 < α) (hα1 : α < 1) (harm : φ 1 ≤ φ 0 + α * φ1 0) (hdesc : φ1 0 < 0) :
    (φ1 1 - φ1 0) / (-φ1 0) ≤ 2 * (1 - α) * M / m := by
  have hdec := (wolfe_decrease S hm0.le hm hα hα1 harm).1
  have hinc := phi1_increment S ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one hM
  simp only [sub_zero, mul_one] at hinc
  have hpos : 0 < -φ1 0 := by linarith
  rw [div_le_div_iff₀ hpos hm0]
  have hM0 : 0 ≤ M := (hm0.le.trans (hm 0 ⟨le_rfl, zero_le_one⟩)).trans (hM 0 ⟨le_rfl, zero_le_one⟩)
  have : (φ1 1 - φ1 0) * m ≤ M * m := mul_le_mul_of_nonneg_right (by linarith) hm0.le
  nlinarith

lemma wolfe_theta_lower {φ1 : ℝ → ℝ} {β : ℝ} (hcurv : β * φ1 0 ≤ φ1 1) (hdesc : φ1 0 < 0) :
    1 - β ≤ (φ1 1 - φ1 0) / (-φ1 0) := by
  have hpos : 0 < -φ1 0 := by linarith
  rw [le_div_iff₀ hpos]
  linarith

lemma second_order_upper {φ φ1 ψ ψ1 : ℝ → ℝ} {a b : ℝ} (S : SC1 φ φ1 ψ ψ1 a b) (hab : a ≤ b)
    {M : ℝ} (hM : ∀ u ∈ Icc a b, ψ u ≤ M) :
    φ b ≤ φ a + φ1 a * (b - a) + M / 2 * (b - a) ^ 2 := by
  have hd : ∀ u ∈ Icc a b, φ1 u - φ1 a - M * (u - a) ≤ 0 := fun u hu => by
    have := le_of_deriv_nonpos (F := fun x => φ1 x - M * x) (F' := fun x => ψ x - M) hu.1
      (fun x hx => ((S.hφ1 x ⟨hx.1, hx.2.trans hu.2⟩).sub
        ((hasDerivAt_id' x).const_mul M)).congr_deriv
        (by simp))
      (fun x hx => by linarith [hM x ⟨hx.1, hx.2.trans hu.2⟩])
    linarith
  have := le_of_deriv_nonpos (F := fun x => φ x - φ1 a * (x - a) - M / 2 * (x - a) ^ 2)
    (F' := fun x => φ1 x - φ1 a - M * (x - a)) hab
    (fun x hx => by
      have h1 := S.hφ x hx
      have h2 : HasDerivAt (fun x => φ1 a * (x - a)) (φ1 a) x := by
        simpa using ((hasDerivAt_id' x).sub_const a).const_mul (φ1 a)
      have h3 : HasDerivAt (fun x => M / 2 * (x - a) ^ 2) (M * (x - a)) x := by
        have := (((hasDerivAt_id' x).sub_const a).pow 2).const_mul (M / 2)
        convert this using 1; simp; ring
      convert (h1.sub h2).sub h3 using 1)
    hd
  simp only [sub_self, mul_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow] at this
  linarith

end Wolfe1D

end LongTails.Proofs.SelfConcordantCalculus
