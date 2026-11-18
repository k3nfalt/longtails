import LongTails.Proofs.SampleLossRegularity

open scoped RealInnerProductSpace BigOperators
open LongTails.Proofs.SampleLossRadial LongTails.Proofs.SampleLossCalculus
open LongTails.Proofs.SampleLossChain LongTails.Proofs.SampleLossRegularity
open LongTails.Proofs.SoftRadialProjection

namespace LongTails.Proofs.SampleLossGradient

variable {E B : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]

private lemma sum_single_nat (j n : ℕ) (a : ℝ) :
    (∑ t ∈ Finset.range n, if t = j then a else 0) = if j < n then a else 0 := by
  simp

omit [CompleteSpace E] in
lemma link_direction (P : ℕ → E →L[ℝ] B) (u : ℕ → B) (j : ℕ) (x v : E) :
    fderiv ℝ (link P u j) x v =
      fderiv ℝ (incoming P u j) x v * (1 + signal P u j x) +
      incoming P u j x * fderiv ℝ (signal P u j) x v := by
  have hd := (derivative_line x v (incoming_differentiable P u j x)).mul
    ((hasDerivAt_const 0 (1 : ℝ)).add (derivative_line x v (signal_differentiable P u j x)))
  simp only [zero_smul, add_zero, zero_add] at hd
  simpa [mul_comm, add_comm] using (derivative_line x v (link_differentiable P u j x)).unique hd

lemma base_block_barrier (P : ℕ → E →L[ℝ] B) (u : ℕ → B) (n : ℕ) (x : E)
    (hu : ∀ j < n, ‖u j‖ = 1) (exists_small : ∃ j < n, signal P u j x < 1/64)
    (injectBlock : ∀ k < n, ∀ v : B, ∃ h : E, ‖h‖ = ‖v‖ ∧ ⟪x,h⟫ = ⟪P k x,v⟫ ∧
      ∀ j < n, P j h = if j=k then v else 0) :
    1/8 < ‖gradient (base P u n) x‖ := by
  classical
  let k := Nat.find exists_small
  obtain ⟨hk,hq⟩ := Nat.find_spec exists_small
  change k < n at hk
  change signal P u k x < 1/64 at hq
  have ha : incoming P u k x = 1 := by
    cases he : k with
    | zero => rfl
    | succ j =>
      apply (gate_flat_above _).1
      by_contra! h
      exact Nat.find_min exists_small (by change j < k; omega) ⟨by omega,h⟩
  let extra := if k+1 < n then gateSlope (signal P u k x) * (1+signal P u (k+1) x) else 0
  let c := 1+extra
  have hc : 1 ≤ c ∧ c ≤ 513 := by
    unfold c extra
    split_ifs with hn
    · have h := (alignment_abs (u (k+1)) (P (k+1) x)).trans (hu _ hn).le
      change |signal P u (k+1) x| ≤ 1 at h
      obtain ⟨hs,ht⟩ := gateSlope_mem (signal P u k x)
      obtain ⟨hl,hr⟩ := abs_le.mp h
      constructor <;> nlinarith [mul_nonneg hs (by linarith : 0 ≤ 1+signal P u (k+1) x),
        mul_le_mul ht (by linarith : 1+signal P u (k+1) x ≤ 2) (by linarith) (by norm_num : (0:ℝ) ≤ 256)]
    · norm_num
  let v := (2:ℝ) • P k x - c • derivative 1 (P k x) (u k)
  have hv : 1/8 < ‖v‖ := radial_barrier _ _ (hu k hk) hq.le hc.1 hc.2
  obtain ⟨h,hn,hi,hcoord⟩ := injectBlock k hk v
  let z := ⟪derivative 1 (P k x) (u k),v⟫
  have ds (j : ℕ) (hj : j<n) :
      fderiv ℝ (signal P u j) x h = if j=k then z else 0 := by
    rw [signal_fderiv, hcoord j hj]
    split_ifs with he
    · subst j; rfl
    · simp
  have da (j : ℕ) (hj : j<n) : fderiv ℝ (incoming P u j) x h =
      if j=k+1 then gateSlope (signal P u k x)*z else 0 := by
    cases j with
    | zero => simp [incoming]
    | succ j =>
      rw [incoming_fderiv, ← signal_fderiv, ds j (by omega)]
      by_cases he : j=k
      · subst j; simp
      · simp [he]
  have dl (j : ℕ) (hj : j<n) : fderiv ℝ (link P u j) x h =
      (if j=k then z else 0) + (if j=k+1 then gateSlope (signal P u k x)*z*(1+signal P u (k+1) x) else 0) := by
    rw [link_direction, ds j hj, da j hj]
    by_cases he : j=k
    · subst j; simp [ha]
    · by_cases he' : j=k+1
      · subst j; simp
      · simp [he,he']
  have hd := base_direction (u:=u) P n x h
  rw [Finset.sum_congr rfl (fun j hj => dl j (Finset.mem_range.mp hj)), Finset.sum_add_distrib,
    sum_single_nat, sum_single_nat, ite_eq_left hk, hi] at hd
  have hd' : fderiv ℝ (base P u n) x h = ⟪v,v⟫ := by
    conv_rhs => lhs; unfold v
    rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left]
    dsimp only [c, extra]
    split_ifs at hd ⊢ <;> dsimp only [z] at hd <;> linarith
  have hgrad := (base_differentiable P u n x).hasGradientAt.hasFDerivAt.fderiv
  rw [hgrad, InnerProductSpace.toDual_apply_apply, real_inner_self_eq_norm_sq] at hd'
  have hnle := real_inner_le_norm (gradient (base P u n) x) h
  rw [hd',hn] at hnle
  by_contra! hsmall
  nlinarith [mul_pos (show 0 < ‖v‖ by linarith) (show 0 < ‖v‖ - ‖gradient (base P u n) x‖ by linarith)]

end LongTails.Proofs.SampleLossGradient
