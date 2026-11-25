import LongTails.Proofs.RhoSmoothParams

open scoped RealInnerProductSpace

namespace LongTails.Proofs.RhoSmoothPhaseOne

open LongTails.Setups.RhoSmoothRadiusConvex LongTails.Algorithms.RhoSmoothThreePhase
open LongTails.Proofs.RhoSmoothLocal LongTails.Proofs.RhoSmoothParams

noncomputable def trans (p : Params) (g : p.E → p.E) (s : State p.E) : State p.E :=
  step p s (g (point s))

noncomputable def gdSeq (p : Params) (g : p.E → p.E) (x : p.E) (k : ℕ) : p.E :=
  (fun z => gdPoint p z (g z))^[k] x

lemma trans_cut_far (p : Params) (g : p.E → p.E) (x : p.E) (hx : threshold p ≤ ‖g x‖) :
    trans p g (.cut x) = .cut (x - (depth p / ‖g x‖) • g x) := by
  simp only [trans, step, point, hx, ↓reduceIte]

lemma trans_cut_near (p : Params) (g : p.E → p.E) (x : p.E) (hx : ‖g x‖ < threshold p) :
    trans p g (.cut x) = .descend x 0 := by
  have hn : ¬ threshold p ≤ ‖g x‖ := not_le.mpr hx
  simp only [trans, step, point, hn, ↓reduceIte]

lemma trans_descend_cont (p : Params) (g : p.E → p.E) (x : p.E) (j : ℕ)
    (hj : j + 1 < descentSteps p) :
    trans p g (.descend x j) = .descend (gdPoint p x (g x)) (j + 1) := by
  simp only [trans, step, point, hj, ↓reduceIte]

lemma trans_descend_exit (p : Params) (g : p.E → p.E) (x : p.E) (j : ℕ)
    (hj : ¬ j + 1 < descentSteps p) :
    trans p g (.descend x j) =
      .accel (gdPoint p x (g x)) (gdPoint p x (g x)) (initialWeight p) false := by
  simp only [trans, step, point, hj, ↓reduceIte]

lemma descentSteps_pos (p : Params) : 0 < descentSteps p := by
  unfold descentSteps; omega

lemma descend_iter (p : Params) (g : p.E → p.E) (x : p.E) :
    ∀ i, i < descentSteps p → (trans p g)^[i] (.descend x 0) = .descend (gdSeq p g x i) i := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
      intro hi
      rw [Function.iterate_succ_apply', ih (by omega),
        trans_descend_cont p g _ i (by omega)]
      congr 1
      unfold gdSeq
      rw [Function.iterate_succ_apply']

lemma descend_exit (p : Params) (g : p.E → p.E) (x : p.E) :
    (trans p g)^[descentSteps p] (.descend x 0) =
      .accel (gdSeq p g x (descentSteps p)) (gdSeq p g x (descentSteps p)) (initialWeight p)
        false := by
  obtain ⟨n, hn⟩ : ∃ n, descentSteps p = n + 1 :=
    ⟨descentSteps p - 1, by have := descentSteps_pos p; omega⟩
  rw [hn, Function.iterate_succ_apply', descend_iter p g x n (by omega),
    trans_descend_exit p g _ n (by omega)]
  have e : gdSeq p g x (n + 1) = gdPoint p (gdSeq p g x n) (g (gdSeq p g x n)) := by
    unfold gdSeq
    rw [Function.iterate_succ_apply']
  rw [e]

section
variable (p : Params) (hp : spec.valid p) {f : p.E → ℝ} {g : p.E → p.E}
  (H : Hyp f g p.L0 p.L1 p.ρ) {u : p.E} (hu : IsMinOn f Set.univ u)
include hp H hu

lemma cut_step_dist (x : p.E) (hx : threshold p ≤ ‖g x‖) :
    ‖(x - (depth p / ‖g x‖) • g x) - u‖ ^ 2 ≤ ‖x - u‖ ^ 2 - depth p ^ 2 :=
  deep_cut_step H hu x (threshold_pos p hp) hx

lemma cut_phase (N : ℕ) : ∀ x : p.E, ‖x - u‖ ^ 2 ≤ N * depth p ^ 2 →
    ∃ m ≤ N, ∃ z, (trans p g)^[m + 1] (.cut x) = .descend z 0 ∧ ‖g z‖ < threshold p ∧
      ‖z - u‖ ≤ ‖x - u‖ := by
  induction N with
  | zero =>
      intro x hx
      have hx0 : ‖x - u‖ = 0 := by
        have : ‖x - u‖ ^ 2 ≤ 0 := by simpa using hx
        nlinarith [norm_nonneg (x - u)]
      have hxu : x = u := by
        have := norm_eq_zero.mp hx0
        exact sub_eq_zero.mp this
      have hg : g x = 0 := by rw [hxu]; exact gradient_zero H hu
      have hlt : ‖g x‖ < threshold p := by rw [hg, norm_zero]; exact threshold_pos p hp
      exact ⟨0, le_rfl, x, by rw [zero_add, Function.iterate_one, trans_cut_near p g x hlt],
        hlt, le_rfl⟩
  | succ N ih =>
      intro x hx
      by_cases hfar : threshold p ≤ ‖g x‖
      · set x' := x - (depth p / ‖g x‖) • g x
        have hd := cut_step_dist p hp H hu x hfar
        have hx' : ‖x' - u‖ ^ 2 ≤ N * depth p ^ 2 := by
          push_cast at hx
          linarith
        obtain ⟨m, hm, z, hz, hgz, hdz⟩ := ih x' hx'
        refine ⟨m + 1, by omega, z, ?_, hgz, ?_⟩
        · rw [Function.iterate_succ_apply, trans_cut_far p g x hfar]
          exact hz
        · have h1 : ‖x' - u‖ ≤ ‖x - u‖ := by
            have : ‖x' - u‖ ^ 2 ≤ ‖x - u‖ ^ 2 := by
              have := sq_nonneg (depth p)
              linarith
            exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this
          exact hdz.trans h1
      · have hlt : ‖g x‖ < threshold p := not_le.mp hfar
        exact ⟨0, by omega, x, by rw [zero_add, Function.iterate_one, trans_cut_near p g x hlt],
          hlt, le_rfl⟩

omit hu in
lemma gd_decrease (x : p.E) :
    f (gdPoint p x (g x)) ≤ f x - 3 * ‖g x‖ ^ 2 / (16 * curvature p (2 * ‖g x‖)) := by
  by_cases hg0 : g x = 0
  · simp [gdPoint, hg0]
  set a := ‖g x‖ with ha
  have hapos : 0 < a := norm_pos_iff.mpr hg0
  set K := curvature p (2 * a)
  have hK : 0 < K := curvature_pos p hp (by linarith)
  set v : p.E := -(1 / (4 * K)) • g x with hvdef
  have hvn : ‖v‖ = a / (4 * K) := by
    rw [hvdef, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity), ← ha]
    field_simp
  have hv : 2 * curv p.L0 p.L1 p.ρ (2 * a) * ‖v‖ ≤ a := by
    rw [← curvature_eq, hvn]
    have : 2 * K * (a / (4 * K)) = a / 2 := by field_simp; ring
    linarith
  have hup := upper H x v hapos le_rfl hv
  have hinner : ⟪g x, v⟫ = -(a ^ 2 / (4 * K)) := by
    rw [hvdef, real_inner_smul_right, real_inner_self_eq_norm_sq]
    ring
  have hpt : gdPoint p x (g x) = x + v := by
    show x - (1 / (4 * curvature p (2 * ‖g x‖))) • g x = x + -(1 / (4 * K)) • g x
    rw [neg_smul, ← sub_eq_add_neg]
  rw [hpt]
  rw [hinner, hvn, ← curvature_eq] at hup
  have e : K * (a / (4 * K)) ^ 2 = a ^ 2 / (16 * K) := by field_simp; ring
  rw [e] at hup
  have e2 : 3 * a ^ 2 / (16 * K) = a ^ 2 / (4 * K) - a ^ 2 / (16 * K) := by field_simp; ring
  rw [e2]
  linarith

lemma gd_dist (x : p.E) : ‖gdPoint p x (g x) - u‖ ≤ ‖x - u‖ := by
  set K := curvature p (2 * ‖g x‖)
  have hK : 0 < K := curvature_pos p hp (by positivity)
  set η := 1 / (4 * K)
  have hη : 0 < η := by positivity
  have hdec := gd_decrease p hp H x
  have hconv := convex_lower H x u
  have hmin : f u ≤ f (gdPoint p x (g x)) := hu (Set.mem_univ _)
  have hpt : gdPoint p x (g x) - u = (x - u) - η • g x := by
    simp only [gdPoint]; abel
  have hsq : ‖gdPoint p x (g x) - u‖ ^ 2 ≤ ‖x - u‖ ^ 2 := by
    rw [hpt, norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_of_nonneg hη.le]
    have hin : ⟪x - u, g x⟫ ≥ 3 * ‖g x‖ ^ 2 / (16 * K) := by
      have h1 : ⟪g x, u - x⟫ = -⟪x - u, g x⟫ := by
        rw [real_inner_comm, ← inner_neg_left, neg_sub]
      linarith
    have e : 3 * ‖g x‖ ^ 2 / (16 * K) = 3 / 4 * η * ‖g x‖ ^ 2 := by
      simp only [η]; field_simp; ring
    rw [e] at hin
    nlinarith [sq_nonneg ‖g x‖, sq_nonneg η]
  nlinarith [norm_nonneg (gdPoint p x (g x) - u), norm_nonneg (x - u)]

lemma gdSeq_props (x : p.E) (k : ℕ) :
    ‖gdSeq p g x k - u‖ ≤ ‖x - u‖ ∧ f (gdSeq p g x k) ≤ f x := by
  induction k with
  | zero => exact ⟨le_rfl, le_rfl⟩
  | succ k ih =>
      have e : gdSeq p g x (k + 1) = gdPoint p (gdSeq p g x k) (g (gdSeq p g x k)) := by
        unfold gdSeq
        rw [Function.iterate_succ_apply']
      rw [e]
      refine ⟨(gd_dist p hp H hu _).trans ih.1, ?_⟩
      have h := gd_decrease p hp H (gdSeq p g x k)
      have hK := curvature_pos p hp (show (0 : ℝ) ≤ 2 * ‖g (gdSeq p g x k)‖ by positivity)
      have : 0 ≤ 3 * ‖g (gdSeq p g x k)‖ ^ 2 /
          (16 * curvature p (2 * ‖g (gdSeq p g x k)‖)) := by positivity
      linarith [ih.2]

omit hp hu in
lemma gap_le_grad (z : p.E) (hz : ‖z - u‖ ≤ p.R) : f z - f u ≤ ‖g z‖ * p.R := by
  have hconv := convex_lower H z u
  have h1 : ⟪g z, u - z⟫ = -⟪g z, z - u⟫ := by rw [← inner_neg_right, neg_sub]
  have h2 : ⟪g z, z - u⟫ ≤ ‖g z‖ * ‖z - u‖ := real_inner_le_norm _ _
  have h3 : ‖g z‖ * ‖z - u‖ ≤ ‖g z‖ * p.R := mul_le_mul_of_nonneg_left hz (norm_nonneg _)
  linarith

omit hu in
lemma gd_step_bound (z : p.E) (hz : ‖z - u‖ ≤ p.R)
    (hpos : 0 < f (gdPoint p z (g z)) - f u) :
    ((f z - f u) - (f (gdPoint p z (g z)) - f u)) / (3 * threshold p ^ 2 / (128 * p.L0)) +
      (1 / (f (gdPoint p z (g z)) - f u) - 1 / (f z - f u)) /
        (3 / (32 * p.L0 * p.R ^ 2)) ≥ 1 := by
  have hG := threshold_pos p hp
  have hL := L0_pos p hp
  have hR := R_pos p hp
  set G := threshold p
  set d0 := f z - f u
  set d1 := f (gdPoint p z (g z)) - f u
  have hdec := gd_decrease p hp H z
  have hK := curvature_pos p hp (show (0 : ℝ) ≤ 2 * ‖g z‖ by positivity)
  have hdec' : d0 - d1 ≥ 3 * ‖g z‖ ^ 2 / (16 * curvature p (2 * ‖g z‖)) := by
    simp only [d0, d1]; linarith
  have hnn : 0 ≤ 3 * ‖g z‖ ^ 2 / (16 * curvature p (2 * ‖g z‖)) := by positivity
  have hd01 : d1 ≤ d0 := by linarith
  have hd0pos : 0 < d0 := lt_of_lt_of_le hpos hd01
  have hcA : 0 < 3 * G ^ 2 / (128 * p.L0) := by positivity
  have hcB : 0 < 3 / (32 * p.L0 * p.R ^ 2) := by positivity
  have hsecond : 0 ≤ (1 / d1 - 1 / d0) / (3 / (32 * p.L0 * p.R ^ 2)) := by
    apply div_nonneg _ hcB.le
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le hpos hd01
  have hfirst : 0 ≤ (d0 - d1) / (3 * G ^ 2 / (128 * p.L0)) := div_nonneg (by linarith) hcA.le
  by_cases hbig : G / 2 ≤ ‖g z‖
  · have hmono := sq_curv_mono p hp (s := G / 2) (t := ‖g z‖) (by positivity) hbig
    have hcG : curvature p (2 * (G / 2)) = 2 * p.L0 := by
      rw [show 2 * (G / 2) = G by ring]; exact curvature_threshold p hp
    rw [hcG] at hmono
    have hA : 3 * G ^ 2 / (128 * p.L0) ≤ 3 * ‖g z‖ ^ 2 / (16 * curvature p (2 * ‖g z‖)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have : 1 ≤ (d0 - d1) / (3 * G ^ 2 / (128 * p.L0)) := by
      rw [le_div_iff₀ hcA]; linarith
    linarith
  · have hsmall : ‖g z‖ < G / 2 := not_le.mp hbig
    have hcle : curvature p (2 * ‖g z‖) ≤ 2 * p.L0 :=
      curvature_le_of_le p hp (by positivity) (by linarith)
    have hgap := gap_le_grad p H z hz
    have hgR : d0 ≤ ‖g z‖ * p.R := hgap
    have hB : 3 / (32 * p.L0 * p.R ^ 2) * d0 ^ 2 ≤ d0 - d1 := by
      have h1 : 3 * ‖g z‖ ^ 2 / (32 * p.L0) ≤ 3 * ‖g z‖ ^ 2 / (16 * curvature p (2 * ‖g z‖)) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        linarith
      have h2 : 3 / (32 * p.L0 * p.R ^ 2) * d0 ^ 2 ≤ 3 * ‖g z‖ ^ 2 / (32 * p.L0) := by
        have hsq : d0 ^ 2 ≤ (‖g z‖ * p.R) ^ 2 := by
          exact pow_le_pow_left₀ hd0pos.le hgR 2
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
        have : 3 * d0 ^ 2 * (32 * p.L0) ≤ 3 * (‖g z‖ * p.R) ^ 2 * (32 * p.L0) := by
          nlinarith
        nlinarith
      linarith
    have hinv : 1 / d1 - 1 / d0 ≥ 3 / (32 * p.L0 * p.R ^ 2) := by
      rw [div_sub_div _ _ hpos.ne' hd0pos.ne', ge_iff_le, le_div_iff₀ (by positivity)]
      have : 3 / (32 * p.L0 * p.R ^ 2) * (d1 * d0) ≤ 3 / (32 * p.L0 * p.R ^ 2) * d0 ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hcB.le
        nlinarith
      nlinarith
    have : 1 ≤ (1 / d1 - 1 / d0) / (3 / (32 * p.L0 * p.R ^ 2)) := by
      rw [le_div_iff₀ hcB]; linarith
    linarith

lemma gd_rate (x : p.E) (hx : ‖x - u‖ ≤ p.R) (hgap : f x - f u ≤ threshold p * p.R) :
    f (gdSeq p g x (descentSteps p)) - f u ≤ threshold p ^ 2 / (16384 * p.L0) := by
  have hG := threshold_pos p hp
  have hL := L0_pos p hp
  have hR := R_pos p hp
  set G := threshold p
  set τ := G ^ 2 / (16384 * p.L0)
  have hτ : 0 < τ := by positivity
  by_contra hcon
  rw [not_le] at hcon
  set cA := 3 * G ^ 2 / (128 * p.L0)
  set cB := 3 / (32 * p.L0 * p.R ^ 2)
  have hcA : 0 < cA := by positivity
  have hcB : 0 < cB := by positivity
  let δ : ℕ → ℝ := fun k => f (gdSeq p g x k) - f u
  have hmono : ∀ k, δ (k + 1) ≤ δ k := by
    intro k
    have e : gdSeq p g x (k + 1) = gdPoint p (gdSeq p g x k) (g (gdSeq p g x k)) := by
      unfold gdSeq
      rw [Function.iterate_succ_apply']
    simp only [δ, e]
    have h := gd_decrease p hp H (gdSeq p g x k)
    have hK := curvature_pos p hp (show (0 : ℝ) ≤ 2 * ‖g (gdSeq p g x k)‖ by positivity)
    have : 0 ≤ 3 * ‖g (gdSeq p g x k)‖ ^ 2 /
        (16 * curvature p (2 * ‖g (gdSeq p g x k)‖)) := by positivity
    linarith
  have hanti : ∀ i j, i ≤ j → δ j ≤ δ i := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ j _ ih => exact (hmono j).trans ih
  have hlow : ∀ k, k ≤ descentSteps p → τ < δ k := fun k hk =>
    lt_of_lt_of_le hcon (hanti k _ hk)
  have hsum : ∀ k, k ≤ descentSteps p →
      (k : ℝ) ≤ (δ 0 - δ k) / cA + (1 / δ k - 1 / δ 0) / cB := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
        intro hk
        have ihk := ih (by omega)
        have hz := (gdSeq_props p hp H hu x k).1.trans hx
        have hpos : 0 < δ (k + 1) := lt_trans hτ (hlow (k + 1) hk)
        have e : gdSeq p g x (k + 1) = gdPoint p (gdSeq p g x k) (g (gdSeq p g x k)) := by
          unfold gdSeq
          rw [Function.iterate_succ_apply']
        have hstep := gd_step_bound p hp H (gdSeq p g x k) hz (by
          have : δ (k + 1) = f (gdPoint p (gdSeq p g x k) (g (gdSeq p g x k))) - f u := by
            simp only [δ, e]
          rw [← this]; exact hpos)
        have e2 : δ (k + 1) = f (gdPoint p (gdSeq p g x k) (g (gdSeq p g x k))) - f u := by
          simp only [δ, e]
        rw [← e2] at hstep
        have hdk : δ k = f (gdSeq p g x k) - f u := rfl
        rw [← hdk] at hstep
        have hstep' : (δ k - δ (k + 1)) / cA + (1 / δ (k + 1) - 1 / δ k) / cB ≥ 1 := hstep
        push_cast
        have split1 : (δ 0 - δ (k + 1)) / cA = (δ 0 - δ k) / cA + (δ k - δ (k + 1)) / cA := by
          field_simp; ring
        have split2 : (1 / δ (k + 1) - 1 / δ 0) / cB =
            (1 / δ k - 1 / δ 0) / cB + (1 / δ (k + 1) - 1 / δ k) / cB := by
          field_simp; ring
        rw [split1, split2]
        linarith
  have hK := hsum (descentSteps p) le_rfl
  have h0 : δ 0 ≤ G * p.R := by simpa [δ, gdSeq] using hgap
  have hfirst : (δ 0 - δ (descentSteps p)) / cA ≤ 128 / 3 * ratio p := by
    have hdK : 0 ≤ δ (descentSteps p) := hτ.le.trans (hlow _ le_rfl).le
    rw [div_le_iff₀ hcA]
    unfold ratio
    simp only [cA, G]
    field_simp
    nlinarith
  have hsecond : (1 / δ (descentSteps p) - 1 / δ 0) / cB ≤ 524288 / 3 * ratio p ^ 2 := by
    have hd0 : 0 < δ 0 := lt_trans hτ (hlow 0 (Nat.zero_le _))
    have hdK := hlow (descentSteps p) le_rfl
    have h1 : 1 / δ (descentSteps p) ≤ 1 / τ := one_div_le_one_div_of_le hτ hdK.le
    have h2 : 0 ≤ 1 / δ 0 := by positivity
    rw [div_le_iff₀ hcB, ratio_sq p hp]
    have e : 1 / τ = 16384 * p.L0 / G ^ 2 := by simp only [τ]; field_simp
    have e2 : 524288 / 3 * (p.L0 ^ 2 * p.R ^ 2 / G ^ 2) * cB = 16384 * p.L0 / G ^ 2 := by
      simp only [cB]; field_simp; ring
    rw [e2]
    linarith
  have hsteps : (descentSteps p : ℝ) ≥ 43 * ratio p + 174763 * ratio p ^ 2 + 1 := by
    unfold descentSteps
    push_cast
    have := Nat.le_ceil (43 * ratio p + 174763 * ratio p ^ 2)
    linarith
  have hr := ratio_nonneg p hp
  nlinarith [sq_nonneg (ratio p)]

end

end LongTails.Proofs.RhoSmoothPhaseOne
