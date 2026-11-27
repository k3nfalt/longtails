import LongTails.Setups.SpectralTwoTapLogistic
import LongTails.Proofs.LogisticSpectralWork

open scoped RealInnerProductSpace
open LongTails.Setups.SpectralTwoTapLogistic
open LongTails.Proofs.LogisticSpectralWork

namespace LongTails.Proofs.SpectralTwoTapResponse

variable {u : Input} {X : Images u}

private lemma coord (s : Spectrum X) (v : State u.d) (i : Modes u) :
    s.basis.repr (s.move v) i = s.multiplier i*s.basis.repr v i := by
  simp [Spectrum.move]

lemma move_add (s : Spectrum X) (v w : State u.d) : s.move (v+w) = s.move v+s.move w := by
  apply s.basis.repr.injective
  ext i
  simp [coord,mul_add]

lemma move_sub (s : Spectrum X) (v w : State u.d) : s.move (v-w) = s.move v-s.move w := by
  apply eq_sub_iff_add_eq.mpr
  rw [← move_add,sub_add_cancel]

lemma move_bound (s : Spectrum X) (κ : ℝ) (hk : ∀ i, |s.multiplier i| ≤ κ)
    (v : State u.d) : ‖s.move v‖ ≤ κ*‖v‖ := by
  have hκ : 0 ≤ κ := (abs_nonneg _).trans (hk (0 : Modes u))
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hκ (norm_nonneg _))).mp
  rw [mul_pow,← s.basis.repr.norm_map (s.move v),← s.basis.repr.norm_map v,
    EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [coord,norm_mul,mul_pow]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (abs_nonneg _) (hk i) _) (sq_nonneg _)

lemma affine_coord (s : Spectrum X) (j : Modes u) (t : ℕ) :
    s.basis.repr (s.affine t) j =
      (s.basis.repr (u.η • descent X s.center) j) *
      ∑ k ∈ Finset.range t, (s.multiplier j)^k := by
  induction t with
  | zero => simp [Spectrum.affine]
  | succ t ih =>
    simp only [Spectrum.affine,map_add,PiLp.add_apply,coord,ih]
    rw [Finset.sum_range_succ']
    simp only [pow_zero,pow_succ,← Finset.sum_mul]
    ring

lemma affine_work (s : Spectrum X) (i : Fin u.n) (N : ℕ) :
    ⟪action (X i) s.center,s.affine (2*N)⟫ =
      ∑ k ∈ Finset.range N, ∑ j, s.work i j*((s.multiplier j)^2)^k := by
  let b := s.basis.repr (u.η • descent X s.center)
  let a := s.basis.repr (action (X i) s.center)
  have obs (t : ℕ) : ⟪action (X i) s.center,s.affine t⟫ =
      ∑ j, a j*(b j * ∑ k ∈ Finset.range t, (s.multiplier j)^k) := by
    rw [← s.basis.repr.inner_map_map,PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro j _
    simp [a,b,affine_coord,RCLike.inner_apply,mul_comm]
  rw [obs]
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.mul_succ,Finset.sum_range_succ]
    simp only [show 2*N+2=2*N+1+1 by omega,Finset.sum_range_succ]
    simp only [mul_add,Finset.sum_add_distrib]
    rw [ih]
    rw [add_assoc,← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    dsimp [a,b,Spectrum.work]
    rw [← pow_mul,pow_succ]
    ring

lemma allowance_floor (s : Spectrum X) (i : Fin u.n) {d W R σ : ℝ}
    (hd : 0 < d) (hW : 0 < W) (hu : W ≤ 4*d) (hR : 1-W/(4*d) ≤ R)
    (hμ : ∀ j, (s.multiplier j)^2 ≤ R)
    (hm : 4*W/5 ≤ σ + ∑ j, s.work i j)
    (hc : ∀ t ∈ Set.Icc 0 R, (4*W/5)*max (1-W/(4*d)-t) 0 ≤
      σ*max (R-t) 0 + ∑ j, s.work i j*max ((s.multiplier j)^2-t) 0)
    (N : ℕ) (hN : 2*d ≤ N*W) :
    5*d/4 < σ*(∑ j ∈ Finset.range N,R^j) + ⟪action (X i) s.center,s.affine (2*N)⟫ := by
  let w : Option (Modes u) → ℝ := Option.elim' σ (s.work i)
  let x : Option (Modes u) → ℝ := Option.elim' R (fun j => (s.multiplier j)^2)
  have hpos : 0 ≤ R := (sq_nonneg _).trans (hμ (0 : Modes u))
  have h := signed_budget_floor w x hd hW hu (fun j => by
    cases j with
    | none => exact ⟨hpos,le_rfl⟩
    | some k => exact ⟨sq_nonneg _,hμ k⟩) hR
    (by simpa [w,Fintype.sum_option] using hm)
    (fun t ht => by simpa [x,w,Fintype.sum_option] using hc t ht) N hN
  rw [affine_work]
  simpa [w,x,Fintype.sum_option,Finset.sum_add_distrib,Finset.mul_sum] using h

end LongTails.Proofs.SpectralTwoTapResponse
