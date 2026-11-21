import LongTails.Proofs.EllSmoothProfiles
import LongTails.Proofs.AbcChain
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Gradient.Basic

open scoped BigOperators RealInnerProductSpace Topology

namespace LongTails.Proofs.EllSmoothChain

open LongTails.Proofs.EllSmoothProfiles
open LongTails.Proofs.AbcChainProfiles (pos rr abs_sub_le_sum pos_nonneg pos_of_nonneg pos_of_nonpos)

variable (S : Shape)

noncomputable def link (a b : ℝ) : ℝ := psi (-a) * phi S (-b) - psi a * phi S b

noncomputable def linkA (a b : ℝ) : ℝ := -(dpsi (-a) * phi S (-b)) - dpsi a * phi S b

noncomputable def linkB (a b : ℝ) : ℝ := -(psi (-a) * dphi S (-b)) - psi a * dphi S b

noncomputable def linkAA (a b : ℝ) : ℝ := ddpsi (-a) * phi S (-b) - ddpsi a * phi S b

noncomputable def linkAB (a b : ℝ) : ℝ := dpsi (-a) * dphi S (-b) - dpsi a * dphi S b

noncomputable def linkBB (a b : ℝ) : ℝ := psi (-a) * ddphi S (-b) - psi a * ddphi S b

lemma small_le {a : ℝ} (ha : |a| ≤ 1 / 4) : a ≤ 1 / 2 ∧ -a ≤ 1 / 2 := by
  have h1 := neg_abs_le a
  have h2 := le_abs_self a
  constructor <;> linarith

lemma link_of_small {a : ℝ} (b : ℝ) (ha : |a| ≤ 1 / 4) : link S a b = 0 := by
  unfold link
  rw [psi_of_le (small_le ha).2, psi_of_le (small_le ha).1]
  ring

lemma linkA_of_small {a : ℝ} (b : ℝ) (ha : |a| ≤ 1 / 4) : linkA S a b = 0 := by
  unfold linkA
  rw [dpsi_of_le (small_le ha).2, dpsi_of_le (small_le ha).1]
  ring

lemma linkB_of_small {a : ℝ} (b : ℝ) (ha : |a| ≤ 1 / 4) : linkB S a b = 0 := by
  unfold linkB
  rw [psi_of_le (small_le ha).2, psi_of_le (small_le ha).1]
  ring

lemma large_cases {a : ℝ} (ha : 1 ≤ |a|) :
    (1 ≤ a ∧ -a ≤ 1 / 2) ∨ (1 ≤ -a ∧ a ≤ 1 / 2) := by
  rcases le_abs.mp ha with h | h
  · exact Or.inl ⟨h, by linarith⟩
  · exact Or.inr ⟨h, by linarith⟩

lemma linkA_of_large {a : ℝ} (b : ℝ) (ha : 1 ≤ |a|) : linkA S a b = 0 := by
  unfold linkA
  rcases large_cases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [dpsi_of_ge h1, dpsi_of_le h2]; ring
  · rw [dpsi_of_ge h1, dpsi_of_le h2]; ring

lemma linkAA_of_large {a : ℝ} (b : ℝ) (ha : 1 ≤ |a|) : linkAA S a b = 0 := by
  unfold linkAA
  rcases large_cases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [ddpsi_of_ge h1, ddpsi_of_le h2]; ring
  · rw [ddpsi_of_ge h1, ddpsi_of_le h2]; ring

lemma linkAB_of_large {a : ℝ} (b : ℝ) (ha : 1 ≤ |a|) : linkAB S a b = 0 := by
  unfold linkAB
  rcases large_cases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [dpsi_of_ge h1, dpsi_of_le h2]; ring
  · rw [dpsi_of_ge h1, dpsi_of_le h2]; ring

lemma linkA_nonpos (a b : ℝ) : linkA S a b ≤ 0 := by
  unfold linkA
  nlinarith [mul_nonneg (dpsi_nonneg (-a)) (phi_nonneg S (-b)),
    mul_nonneg (dpsi_nonneg a) (phi_nonneg S b)]

lemma linkB_nonpos (a b : ℝ) : linkB S a b ≤ 0 := by
  unfold linkB
  nlinarith [mul_nonneg (psi_nonneg (-a)) (dphi_nonneg S (-b)),
    mul_nonneg (psi_nonneg a) (dphi_nonneg S b)]

lemma link_abs (a b : ℝ) : |link S a b| ≤ 20 := by
  unfold link
  have h1 : |psi (-a) * phi S (-b)| ≤ 10 := by
    rw [abs_of_nonneg (mul_nonneg (psi_nonneg _) (phi_nonneg S _))]
    nlinarith [psi_le_one (-a), psi_nonneg (-a), phi_le S (-b), phi_nonneg S (-b)]
  have h2 : |psi a * phi S b| ≤ 10 := by
    rw [abs_of_nonneg (mul_nonneg (psi_nonneg _) (phi_nonneg S _))]
    nlinarith [psi_le_one a, psi_nonneg a, phi_le S b, phi_nonneg S b]
  calc _ ≤ |psi (-a) * phi S (-b)| + |psi a * phi S b| := abs_sub_le_sum _ _
    _ ≤ 20 := by linarith

lemma linkA_abs (a b : ℝ) : |linkA S a b| ≤ 100 := by
  rw [abs_of_nonpos (linkA_nonpos S a b)]
  unfold linkA
  nlinarith [mul_le_mul (dpsi_le (-a)) (phi_le S (-b)) (phi_nonneg S (-b)) (by norm_num),
    mul_le_mul (dpsi_le a) (phi_le S b) (phi_nonneg S b) (by norm_num)]

lemma linkB_abs (a b : ℝ) : |linkB S a b| ≤ 2 := by
  rw [abs_of_nonpos (linkB_nonpos S a b)]
  unfold linkB
  nlinarith [mul_le_mul (psi_le_one (-a)) (dphi_le_one S (-b)) (dphi_nonneg S (-b)) zero_le_one,
    mul_le_mul (psi_le_one a) (dphi_le_one S b) (dphi_nonneg S b) zero_le_one]

lemma linkAA_abs (a b : ℝ) : |linkAA S a b| ≤ 720 := by
  unfold linkAA
  have h1 : |ddpsi (-a) * phi S (-b)| ≤ 360 := by
    rw [abs_mul, abs_of_nonneg (phi_nonneg S _)]
    nlinarith [ddpsi_abs (-a), abs_nonneg (ddpsi (-a)), phi_le S (-b), phi_nonneg S (-b)]
  have h2 : |ddpsi a * phi S b| ≤ 360 := by
    rw [abs_mul, abs_of_nonneg (phi_nonneg S _)]
    nlinarith [ddpsi_abs a, abs_nonneg (ddpsi a), phi_le S b, phi_nonneg S b]
  calc _ ≤ |ddpsi (-a) * phi S (-b)| + |ddpsi a * phi S b| := abs_sub_le_sum _ _
    _ ≤ 720 := by linarith

lemma linkAB_abs (a b : ℝ) : |linkAB S a b| ≤ 10 := by
  unfold linkAB
  have h1 : |dpsi (-a) * dphi S (-b)| ≤ 5 := by
    rw [abs_of_nonneg (mul_nonneg (dpsi_nonneg _) (dphi_nonneg S _))]
    nlinarith [dpsi_le (-a), dpsi_nonneg (-a), dphi_le_one S (-b), dphi_nonneg S (-b)]
  have h2 : |dpsi a * dphi S b| ≤ 5 := by
    rw [abs_of_nonneg (mul_nonneg (dpsi_nonneg _) (dphi_nonneg S _))]
    nlinarith [dpsi_le a, dpsi_nonneg a, dphi_le_one S b, dphi_nonneg S b]
  calc _ ≤ |dpsi (-a) * dphi S (-b)| + |dpsi a * dphi S b| := abs_sub_le_sum _ _
    _ ≤ 10 := by linarith

lemma linkBB_abs (a b : ℝ) : |linkBB S a b| ≤ 8 / S.th := by
  unfold linkBB
  have hth := S.hth
  have h0 : (0 : ℝ) ≤ 4 / S.th := by positivity
  have h1 : |psi (-a) * ddphi S (-b)| ≤ 4 / S.th := by
    rw [abs_mul, abs_of_nonneg (psi_nonneg _)]
    calc psi (-a) * |ddphi S (-b)| ≤ 1 * (4 / S.th) :=
          mul_le_mul (psi_le_one _) (ddphi_abs_le S _) (abs_nonneg _) zero_le_one
      _ = 4 / S.th := one_mul _
  have h2 : |psi a * ddphi S b| ≤ 4 / S.th := by
    rw [abs_mul, abs_of_nonneg (psi_nonneg _)]
    calc psi a * |ddphi S b| ≤ 1 * (4 / S.th) :=
          mul_le_mul (psi_le_one _) (ddphi_abs_le S _) (abs_nonneg _) zero_le_one
      _ = 4 / S.th := one_mul _
  calc _ ≤ |psi (-a) * ddphi S (-b)| + |psi a * ddphi S b| := abs_sub_le_sum _ _
    _ ≤ 8 / S.th := by
      have : 8 / S.th = 4 / S.th + 4 / S.th := by ring
      linarith

lemma linkBB_relative {a : ℝ} (b : ℝ) (ha : 1 ≤ |a|) :
    |linkBB S a b| ≤ 36 / S.th * |linkB S a b| ^ (2 - S.th) + S.mu := by
  unfold linkBB linkB
  rcases large_cases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [psi_of_ge h1, psi_of_le h2]
    simp only [zero_mul, neg_zero, zero_sub, one_mul, abs_neg]
    rw [abs_of_nonneg (dphi_nonneg S b)]
    exact ddphi_relative S b
  · rw [psi_of_ge h1, psi_of_le h2]
    simp only [zero_mul, sub_zero, one_mul, abs_neg]
    rw [abs_of_nonneg (dphi_nonneg S (-b))]
    exact ddphi_relative S (-b)

lemma linkB_le_of_large {a b : ℝ} (ha : 1 ≤ |a|) (hb : |b| ≤ 1) : linkB S a b ≤ -1 := by
  unfold linkB
  rw [dphi_of_abs_le S hb, dphi_of_abs_le S (by rwa [abs_neg])]
  rcases large_cases ha with ⟨h1, _⟩ | ⟨h1, _⟩
  · rw [psi_of_ge h1]
    linarith [psi_nonneg (-a)]
  · rw [psi_of_ge h1]
    linarith [psi_nonneg a]

section Vector

variable {n : ℕ}

abbrev Chain (n : ℕ) := EuclideanSpace ℝ (Fin (n + 1))

noncomputable def prj (k : Fin (n + 1)) : Chain n →L[ℝ] ℝ := EuclideanSpace.proj k

lemma prj_apply (k : Fin (n + 1)) (u : Chain n) : prj k u = u k := rfl

lemma coord_hasFDerivAt (k : Fin (n + 1)) (u : Chain n) :
    HasFDerivAt (fun x : Chain n => x k) (prj k) u := (prj k).hasFDerivAt

lemma comp_coord_hasFDerivAt {g : ℝ → ℝ} {g' : ℝ} (k : Fin (n + 1)) (u : Chain n)
    (hg : HasDerivAt g g' (u k)) : HasFDerivAt (fun x : Chain n => g (x k)) (g' • prj k) u :=
  hg.comp_hasFDerivAt u (coord_hasFDerivAt k u)

lemma comp_neg_coord_hasFDerivAt {g : ℝ → ℝ} {g' : ℝ} (k : Fin (n + 1)) (u : Chain n)
    (hg : HasDerivAt g g' (-u k)) :
    HasFDerivAt (fun x : Chain n => g (-x k)) ((-g') • prj k) u := by
  have h := hg.comp_hasFDerivAt u (coord_hasFDerivAt k u).neg
  refine h.congr_fderiv ?_
  ext v
  simp

noncomputable def chain (u : Chain n) : ℝ :=
  -phi S (u 0) + ∑ i : Fin n, link S (u i.castSucc) (u i.succ)

noncomputable def fieldFirst (u : Chain n) : Fin (n + 1) → ℝ :=
  Fin.cases (-dphi S (u 0)) (fun _ => 0)

noncomputable def fieldA (u : Chain n) : Fin (n + 1) → ℝ :=
  Fin.lastCases 0 (fun i : Fin n => linkA S (u i.castSucc) (u i.succ))

noncomputable def fieldB (u : Chain n) : Fin (n + 1) → ℝ :=
  Fin.cases 0 (fun i : Fin n => linkB S (u i.castSucc) (u i.succ))

noncomputable def field (u : Chain n) : Chain n :=
  WithLp.toLp 2 (fun k => fieldFirst S u k + fieldA S u k + fieldB S u k)

lemma field_apply (u : Chain n) (k : Fin (n + 1)) :
    field S u k = fieldFirst S u k + fieldA S u k + fieldB S u k := rfl

lemma sum_fieldFirst (u : Chain n) (h : Fin (n + 1) → ℝ) :
    ∑ k, fieldFirst S u k * h k = -dphi S (u 0) * h 0 := by
  rw [Fin.sum_univ_succ]; simp [fieldFirst]

lemma sum_fieldA (u : Chain n) (h : Fin (n + 1) → ℝ) :
    ∑ k, fieldA S u k * h k =
      ∑ i : Fin n, linkA S (u i.castSucc) (u i.succ) * h i.castSucc := by
  rw [Fin.sum_univ_castSucc]; simp [fieldA]

lemma sum_fieldB (u : Chain n) (h : Fin (n + 1) → ℝ) :
    ∑ k, fieldB S u k * h k = ∑ i : Fin n, linkB S (u i.castSucc) (u i.succ) * h i.succ := by
  rw [Fin.sum_univ_succ]; simp [fieldB]

lemma inner_field (u v : Chain n) :
    ⟪field S u, v⟫ = -dphi S (u 0) * v 0 +
      ∑ i : Fin n, (linkA S (u i.castSucc) (u i.succ) * v i.castSucc +
        linkB S (u i.castSucc) (u i.succ) * v i.succ) := by
  have h : ⟪field S u, v⟫ = ∑ k, (fieldFirst S u k + fieldA S u k + fieldB S u k) * v k := by
    simp [PiLp.inner_apply, RCLike.inner_apply, field, mul_comm]
  rw [h]
  simp only [add_mul, Finset.sum_add_distrib, sum_fieldFirst, sum_fieldA, sum_fieldB]
  ring

lemma link_hasFDerivAt (i j : Fin (n + 1)) (u : Chain n) :
    HasFDerivAt (fun x : Chain n => link S (x i) (x j))
      (linkA S (u i) (u j) • prj i + linkB S (u i) (u j) • prj j) u := by
  have h1 := comp_neg_coord_hasFDerivAt i u (psi_hasDerivAt (-u i))
  have h2 := comp_neg_coord_hasFDerivAt j u (phi_hasDerivAt S (-u j))
  have h3 := comp_coord_hasFDerivAt i u (psi_hasDerivAt (u i))
  have h4 := comp_coord_hasFDerivAt j u (phi_hasDerivAt S (u j))
  have h := (h1.mul h2).sub (h3.mul h4)
  refine h.congr_fderiv ?_
  ext v
  simp only [linkA, linkB, add_apply, smul_apply,
    sub_apply, smul_eq_mul, prj_apply]
  ring

lemma chain_hasGradientAt (u : Chain n) : HasGradientAt (chain S) (field S u) u := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h0 := (comp_coord_hasFDerivAt (0 : Fin (n + 1)) u (phi_hasDerivAt S (u 0))).neg
  have hs : HasFDerivAt (fun x : Chain n => ∑ i : Fin n, link S (x i.castSucc) (x i.succ))
      (∑ i : Fin n, (linkA S (u i.castSucc) (u i.succ) • prj i.castSucc +
        linkB S (u i.castSucc) (u i.succ) • prj i.succ)) u :=
    HasFDerivAt.fun_sum (fun i _ => link_hasFDerivAt S i.castSucc i.succ u)
  have h := h0.add hs
  refine h.congr_fderiv ?_
  ext v
  simp only [InnerProductSpace.toDual_apply_apply, inner_field, add_apply,
    neg_apply, smul_apply, sum_apply,
    smul_eq_mul, prj_apply]
  ring

lemma coord_sq_le (x : Chain n) (k : Fin (n + 1)) : x k ^ 2 ≤ ‖x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  exact Finset.single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg (x j))
    (Finset.mem_univ k)

lemma abs_coord_le (x : Chain n) (k : Fin (n + 1)) : |x k| ≤ ‖x‖ := by
  have h := coord_sq_le x k
  rw [← sq_abs] at h
  nlinarith [abs_nonneg (x k), norm_nonneg x]

lemma fieldFirst_nonpos (u : Chain n) (k : Fin (n + 1)) : fieldFirst S u k ≤ 0 := by
  induction k using Fin.cases with
  | zero => simp only [fieldFirst, Fin.cases_zero]; linarith [dphi_nonneg S (u 0)]
  | succ i => simp [fieldFirst]

lemma fieldA_nonpos (u : Chain n) (k : Fin (n + 1)) : fieldA S u k ≤ 0 := by
  induction k using Fin.lastCases with
  | last => simp [fieldA]
  | cast i => simp only [fieldA, Fin.lastCases_castSucc]; exact linkA_nonpos S _ _

lemma fieldB_nonpos (u : Chain n) (k : Fin (n + 1)) : fieldB S u k ≤ 0 := by
  induction k using Fin.cases with
  | zero => simp [fieldB]
  | succ i => simp only [fieldB, Fin.cases_succ]; exact linkB_nonpos S _ _

lemma fieldFirst_abs (u : Chain n) (k : Fin (n + 1)) : |fieldFirst S u k| ≤ 1 := by
  induction k using Fin.cases with
  | zero =>
    simp only [fieldFirst, Fin.cases_zero, abs_neg, abs_of_nonneg (dphi_nonneg S _)]
    exact dphi_le_one S _
  | succ i => simp [fieldFirst]

lemma fieldA_abs (u : Chain n) (k : Fin (n + 1)) : |fieldA S u k| ≤ 100 := by
  induction k using Fin.lastCases with
  | last => simp [fieldA]
  | cast i => simp only [fieldA, Fin.lastCases_castSucc]; exact linkA_abs S _ _

lemma fieldB_abs (u : Chain n) (k : Fin (n + 1)) : |fieldB S u k| ≤ 2 := by
  induction k using Fin.cases with
  | zero => simp [fieldB]
  | succ i => simp only [fieldB, Fin.cases_succ]; exact linkB_abs S _ _

lemma field_abs (u : Chain n) (k : Fin (n + 1)) : |field S u k| ≤ 103 := by
  rw [field_apply]
  calc _ ≤ |fieldFirst S u k| + |fieldA S u k| + |fieldB S u k| := abs_add_three _ _ _
    _ ≤ 103 := by linarith [fieldFirst_abs S u k, fieldA_abs S u k, fieldB_abs S u k]

lemma field_norm_le (u : Chain n) : ‖field S u‖ ≤ 103 * ((n : ℝ) + 1) := by
  have hsq : ‖field S u‖ ^ 2 ≤ (103 * ((n : ℝ) + 1)) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc _ ≤ ∑ _k : Fin (n + 1), (103 : ℝ) ^ 2 := by
          apply Finset.sum_le_sum
          intro k _
          have h := field_abs S u k
          nlinarith [sq_abs (field S u k), abs_nonneg (field S u k)]
      _ = 103 ^ 2 * ((n : ℝ) + 1) := by simp; ring
      _ ≤ _ := by
          have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by
            have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
            linarith
          nlinarith
  have hn : (0 : ℝ) ≤ 103 * ((n : ℝ) + 1) := by positivity
  exact le_of_sq_le_sq hsq hn

lemma chain_abs (u : Chain n) : |chain S u| ≤ 20 * ((n : ℝ) + 1) := by
  unfold chain
  have h1 : |-phi S (u 0)| ≤ 10 := by
    rw [abs_neg, abs_of_nonneg (phi_nonneg S _)]
    exact phi_le S _
  have h2 : |∑ i : Fin n, link S (u i.castSucc) (u i.succ)| ≤ ∑ _i : Fin n, (20 : ℝ) :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => link_abs S _ _))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
  calc _ ≤ |-phi S (u 0)| + |∑ i : Fin n, link S (u i.castSucc) (u i.succ)| := abs_add_le _ _
    _ ≤ _ := by linarith

lemma chain_zero_le : chain S (0 : Chain n) ≤ 0 := by
  have h : chain S (0 : Chain n) = -phi S 0 := by
    simp only [chain, PiLp.zero_apply, link_of_small S _ (by norm_num : |(0 : ℝ)| ≤ 1 / 4)]
    simp
  rw [h]
  linarith [phi_nonneg S 0]

lemma field_of_large (u : Chain n) (k : Fin (n + 1)) (hk : S.tEnd ≤ |u k|) :
    field S u k = 0 := by
  have h13 := S.tEnd_ge
  have hneg : S.tEnd ≤ |-u k| := by rwa [abs_neg]
  have hone : 1 ≤ |u k| := by linarith
  have h0 : fieldFirst S u k = 0 := by
    induction k using Fin.cases with
    | zero => simp [fieldFirst, dphi_of_ge S hk]
    | succ i => simp [fieldFirst]
  have hA : fieldA S u k = 0 := by
    induction k using Fin.lastCases with
    | last => simp [fieldA]
    | cast i =>
      simp only [fieldA, Fin.lastCases_castSucc]
      exact linkA_of_large S _ hone
  have hB : fieldB S u k = 0 := by
    induction k using Fin.cases with
    | zero => simp [fieldB]
    | succ i =>
      simp only [fieldB, Fin.cases_succ, linkB, dphi_of_ge S hk, dphi_of_ge S hneg]
      ring
  rw [field_apply, h0, hA, hB]
  ring

lemma exists_first_small (u : Chain n) (h : ∃ k : Fin (n + 1), |u k| < 1) :
    ∃ j : Fin (n + 1), |u j| < 1 ∧ ∀ i : Fin (n + 1), i < j → 1 ≤ |u i| := by
  classical
  obtain ⟨k, hk⟩ := h
  let s := Finset.univ.filter (fun j : Fin (n + 1) => |u j| < 1)
  have hs : s.Nonempty := ⟨k, by simp [s, hk]⟩
  refine ⟨s.min' hs, (Finset.mem_filter.mp (s.min'_mem hs)).2, ?_⟩
  intro i hi
  by_contra hc
  push Not at hc
  exact absurd (s.min'_le i (by simp [s, hc])) (not_le.mpr hi)

lemma field_large_coordinate (u : Chain n) (h : ∃ k : Fin (n + 1), |u k| < 1) :
    ∃ k : Fin (n + 1), field S u k ≤ -1 := by
  obtain ⟨j, hj, hmin⟩ := exists_first_small u h
  refine ⟨j, ?_⟩
  induction j using Fin.cases with
  | zero =>
    rw [field_apply]
    have h0 : fieldFirst S u 0 = -dphi S (u 0) := by simp [fieldFirst]
    have hB : fieldB S u 0 = 0 := by simp [fieldB]
    rw [h0, hB, dphi_of_abs_le S hj.le]
    linarith [fieldA_nonpos S u 0]
  | succ i =>
    have hprev := hmin i.castSucc Fin.castSucc_lt_succ
    rw [field_apply]
    have h0 : fieldFirst S u i.succ = 0 := by simp [fieldFirst]
    have hB : fieldB S u i.succ = linkB S (u i.castSucc) (u i.succ) := by simp [fieldB]
    rw [h0, hB]
    have hl := linkB_le_of_large S hprev hj.le
    linarith [fieldA_nonpos S u i.succ]

lemma field_norm_ge_one (u : Chain n) (h : ∃ k : Fin (n + 1), |u k| < 1) :
    1 ≤ ‖field S u‖ := by
  obtain ⟨k, hk⟩ := field_large_coordinate S u h
  have h1 := abs_coord_le (field S u) k
  have h2 : 1 ≤ |field S u k| := by
    rw [abs_of_nonpos (by linarith)]
    linarith
  linarith

noncomputable def trunc (m : ℕ) (u : Chain n) : Chain n :=
  WithLp.toLp 2 (fun i => if i.val < m then u i else 0)

lemma trunc_apply (m : ℕ) (u : Chain n) (i : Fin (n + 1)) :
    trunc m u i = if i.val < m then u i else 0 := rfl

lemma trunc_congr (m : ℕ) (u v : Chain n) (h : ∀ i : Fin (n + 1), i.val < m → u i = v i) :
    trunc m u = trunc m v := by
  ext i
  rw [trunc_apply, trunc_apply]
  split_ifs with hi
  · exact h i hi
  · rfl

lemma field_congr (u v : Chain n) (k : Fin (n + 1))
    (h : ∀ j : Fin (n + 1), j.val ≤ k.val + 1 → u j = v j) : field S u k = field S v k := by
  rw [field_apply, field_apply]
  have h0 : u 0 = v 0 := h 0 (by simp)
  have hF : fieldFirst S u k = fieldFirst S v k := by simp only [fieldFirst, h0]
  have hA : fieldA S u k = fieldA S v k := by
    induction k using Fin.lastCases with
    | last => simp [fieldA]
    | cast i =>
      simp only [fieldA, Fin.lastCases_castSucc]
      rw [h i.castSucc (by simp), h i.succ (by simp)]
  have hB : fieldB S u k = fieldB S v k := by
    induction k using Fin.cases with
    | zero => simp [fieldB]
    | succ i =>
      simp only [fieldB, Fin.cases_succ]
      rw [h i.castSucc (by simp; omega), h i.succ (by simp)]
  rw [hF, hA, hB]

noncomputable def visibleField (r : ℕ) (u : Chain n) : Chain n :=
  WithLp.toLp 2 (fun k => if k.val < r then field S (trunc r u) k else 0)

lemma visibleField_congr (r : ℕ) (u v : Chain n)
    (h : ∀ i : Fin (n + 1), i.val < r → u i = v i) :
    visibleField S r u = visibleField S r v := by
  simp only [visibleField, trunc_congr r u v h]

lemma chain_trunc_succ (m : ℕ) (u : Chain n)
    (hs : ∀ i : Fin (n + 1), m ≤ i.val → |u i| ≤ 1 / 4) :
    chain S (trunc (m + 1) u) = chain S u := by
  unfold chain
  have h0 : trunc (m + 1) u 0 = u 0 := by rw [trunc_apply, ite_eq_left (by simp)]
  rw [h0]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [trunc_apply, trunc_apply]
  by_cases h1 : i.val + 1 < m + 1
  · rw [ite_eq_left (by simp; omega), ite_eq_left (by simp; omega)]
  · rw [link_of_small S _ (hs i.castSucc (by simp; omega))]
    by_cases h2 : i.val < m + 1
    · rw [ite_eq_left (by simp; omega), link_of_small S _ (hs i.castSucc (by simp; omega))]
    · rw [ite_eq_right (by simp; omega), link_of_small S _ (by norm_num : |(0 : ℝ)| ≤ 1 / 4)]

lemma field_zero_beyond (m : ℕ) (u : Chain n)
    (hs : ∀ i : Fin (n + 1), m ≤ i.val → |u i| ≤ 1 / 4) (k : Fin (n + 1)) (hk : m + 1 ≤ k.val) :
    field S u k = 0 := by
  have hkm := hs k (by omega)
  have hA : fieldA S u k = 0 := by
    induction k using Fin.lastCases with
    | last => simp [fieldA]
    | cast i => simp only [fieldA, Fin.lastCases_castSucc]; exact linkA_of_small S _ hkm
  have hF : fieldFirst S u k = 0 := by
    induction k using Fin.cases with
    | zero => simp at hk
    | succ i => simp [fieldFirst]
  have hB : fieldB S u k = 0 := by
    induction k using Fin.cases with
    | zero => simp [fieldB]
    | succ i =>
      simp only [fieldB, Fin.cases_succ]
      exact linkB_of_small S _ (hs i.castSucc (by simp at hk ⊢; omega))
  rw [field_apply, hF, hA, hB]
  ring

lemma fieldA_of_small (u : Chain n) (k : Fin (n + 1)) (h : |u k| ≤ 1 / 4) :
    fieldA S u k = 0 := by
  induction k using Fin.lastCases with
  | last => simp [fieldA]
  | cast i => simp only [fieldA, Fin.lastCases_castSucc]; exact linkA_of_small S _ h

lemma fieldB_congr (u v : Chain n) (k : Fin (n + 1))
    (h : ∀ j : Fin (n + 1), j.val + 1 = k.val ∨ j = k → u j = v j) :
    fieldB S u k = fieldB S v k := by
  induction k using Fin.cases with
  | zero => simp [fieldB]
  | succ i =>
    simp only [fieldB, Fin.cases_succ]
    rw [h i.castSucc (Or.inl (by simp)), h i.succ (Or.inr rfl)]

lemma visibleField_eq (m : ℕ) (u : Chain n)
    (hs : ∀ i : Fin (n + 1), m ≤ i.val → |u i| ≤ 1 / 4) :
    visibleField S (m + 1) u = field S u := by
  ext k
  simp only [visibleField]
  by_cases hk : k.val < m
  · rw [ite_eq_left (by omega)]
    apply field_congr
    intro j hj
    rw [trunc_apply, ite_eq_left (by omega)]
  · by_cases hkm : k.val = m
    · rw [ite_eq_left (by omega), field_apply, field_apply]
      have hsm := hs k (by omega)
      have htk : trunc (m + 1) u k = u k := by rw [trunc_apply, ite_eq_left (by omega)]
      have hF : fieldFirst S (trunc (m + 1) u) k = fieldFirst S u k := by
        simp only [fieldFirst]
        rw [trunc_apply, ite_eq_left (by simp)]
      have hA : fieldA S (trunc (m + 1) u) k = fieldA S u k := by
        rw [fieldA_of_small S _ k (by rw [htk]; exact hsm), fieldA_of_small S _ k hsm]
      have hB : fieldB S (trunc (m + 1) u) k = fieldB S u k := by
        apply fieldB_congr
        intro j hj
        rw [trunc_apply, ite_eq_left]
        rcases hj with hj | hj
        · omega
        · rw [hj]; omega
      rw [hF, hA, hB]
    · rw [ite_eq_right (by omega), field_zero_beyond S m u hs k (by omega)]

noncomputable def clip (u : Chain n) : Chain n :=
  WithLp.toLp 2 (fun k => if |u k| < S.tEnd then u k else 0)

lemma clip_norm_le (u : Chain n) : ‖clip S u‖ ≤ S.tEnd * ((n : ℝ) + 1) := by
  have ht := S.tEnd_pos
  have hsq : ‖clip S u‖ ^ 2 ≤ (S.tEnd * ((n : ℝ) + 1)) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc _ ≤ ∑ _k : Fin (n + 1), S.tEnd ^ 2 := by
          apply Finset.sum_le_sum
          intro k _
          simp only [clip]
          split_ifs with hk
          · nlinarith [sq_abs (u k), abs_nonneg (u k)]
          · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]; positivity
      _ = S.tEnd ^ 2 * ((n : ℝ) + 1) := by simp; ring
      _ ≤ _ := by
          have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by
            have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
            linarith
          nlinarith [sq_nonneg S.tEnd]
  exact le_of_sq_le_sq hsq (by positivity)

lemma field_add_smul_ge (u : Chain n) (γ : ℝ) :
    ‖field S u‖ - |γ| * (S.tEnd * ((n : ℝ) + 1)) ≤ ‖field S u + γ • u‖ := by
  have h1 : ‖field S u + γ • clip S u‖ ≤ ‖field S u + γ • u‖ := by
    have hsq : ‖field S u + γ • clip S u‖ ^ 2 ≤ ‖field S u + γ • u‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
      apply Finset.sum_le_sum
      intro k _
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, clip]
      split_ifs with hk
      · exact le_rfl
      · rw [field_of_large S u k (not_lt.mp hk)]
        simp only [mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
          zero_add]
        positivity
    exact le_of_sq_le_sq hsq (norm_nonneg _)
  have h2 : ‖field S u‖ - ‖γ • clip S u‖ ≤ ‖field S u + γ • clip S u‖ := by
    have := norm_sub_norm_le (field S u) (-(γ • clip S u))
    rwa [norm_neg, sub_neg_eq_add] at this
  have h3 : ‖γ • clip S u‖ ≤ |γ| * (S.tEnd * ((n : ℝ) + 1)) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (clip_norm_le S u) (abs_nonneg γ)
  linarith

end Vector

end LongTails.Proofs.EllSmoothChain
