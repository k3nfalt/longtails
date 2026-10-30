import LongTails.Proofs.AdaptiveSilverSplit

namespace LongTails.Proofs.AdaptiveSilverDynamics

open scoped RealInnerProductSpace
open LongTails.Algorithms.SilverSchedule
open LongTails.Proofs.AdaptiveSilverScalar
open LongTails.Proofs.AdaptiveSilverSplit

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def esum (g : E → E) (R : E → ℝ) : List ℝ → E → ℝ
  | [], _ => 0
  | h :: hs, x => h * R x + esum g R hs (x - h • g x)

lemma esum_le (g : E → E) (R : E → ℝ) {c : ℝ} :
    ∀ (hs : List ℝ) (x : E), (∀ h ∈ hs, 0 ≤ h) →
      (∀ t < hs.length, R (run g (hs.take t) x) ≤ c) → esum g R hs x ≤ hs.sum * c
  | [], _, _, _ => by simp [esum]
  | h :: hs, x, hpos, hR => by
    simp only [esum, List.sum_cons]
    have h0 := hR 0 (by simp)
    simp only [List.take_zero, run] at h0
    have ih := esum_le g R hs (x - h • g x) (fun h' hh => hpos h' (List.mem_cons_of_mem _ hh))
      (fun t ht => by
        have := hR (t + 1) (by simp; omega)
        simpa [List.take_succ_cons, run] using this)
    have hh := hpos h (by simp)
    nlinarith [mul_le_mul_of_nonneg_left h0 hh]

lemma travel_le (g : E → E) {c : ℝ} :
    ∀ (hs : List ℝ) (x : E), (∀ h ∈ hs, 0 ≤ h) →
      (∀ t < hs.length, ‖g (run g (hs.take t) x)‖ ≤ c) → ‖run g hs x - x‖ ≤ hs.sum * c
  | [], _, _, _ => by simp [run]
  | h :: hs, x, hpos, hR => by
    simp only [run, List.sum_cons]
    have h0 := hR 0 (by simp)
    simp only [List.take_zero, run] at h0
    have ih := travel_le g hs (x - h • g x) (fun h' hh => hpos h' (List.mem_cons_of_mem _ hh))
      (fun t ht => by
        have := hR (t + 1) (by simp; omega)
        simpa [List.take_succ_cons, run] using this)
    have hh := hpos h (by simp)
    have he : run g hs (x - h • g x) - x = (run g hs (x - h • g x) - (x - h • g x)) - h • g x := by
      abel
    rw [he]
    calc ‖(run g hs (x - h • g x) - (x - h • g x)) - h • g x‖
        ≤ ‖run g hs (x - h • g x) - (x - h • g x)‖ + ‖h • g x‖ := norm_sub_le _ _
      _ ≤ hs.sum * c + h * c := by
          rw [norm_smul, Real.norm_of_nonneg hh]
          exact add_le_add ih (mul_le_mul_of_nonneg_left h0 hh)
      _ = (h + hs.sum) * c := by ring

lemma run_take_succ (g : E → E) (hs : List ℝ) (x : E) (t : ℕ) (ht : t < hs.length) :
    run g (hs.take (t + 1)) x =
      run g (hs.take t) x - hs[t] • g (run g (hs.take t) x) := by
  induction hs generalizing x t with
  | nil => simp at ht
  | cons h r ih =>
    cases t with
    | zero => simp [run]
    | succ t =>
      simp only [List.take_succ_cons, run, List.getElem_cons_succ]
      exact ih _ t (by simpa using ht)

lemma travel_prefix (g : E → E) {c : ℝ} (hs : List ℝ) (x : E) (hpos : ∀ h ∈ hs, 0 ≤ h)
    (hR : ∀ t < hs.length, ‖g (run g (hs.take t) x)‖ ≤ c) (t : ℕ) (ht : t ≤ hs.length) :
    ‖run g (hs.take t) x - x‖ ≤ hs.sum * c := by
  have hc : 0 ≤ c ∨ hs = [] := by
    rcases hs with _ | ⟨h, r⟩
    · exact Or.inr rfl
    · left
      have := hR 0 (by simp)
      exact (norm_nonneg _).trans this
  have h1 := travel_le g (hs.take t) x (fun h hh => hpos h (List.mem_of_mem_take hh))
    (fun s hs' => by
      have hlen : s < hs.length := by
        have := List.length_take_le t hs; omega
      have := hR s hlen
      rwa [List.take_take, min_eq_left (by have := List.length_take_le t hs; omega)])
  have h2 : (hs.take t).sum ≤ hs.sum := by
    have := List.sum_take_add_sum_drop hs t
    have : 0 ≤ (hs.drop t).sum := List.sum_nonneg (fun h hh => hpos h (List.mem_of_mem_drop hh))
    linarith
  rcases hc with hc | hc
  · exact h1.trans (mul_le_mul_of_nonneg_right h2 hc)
  · subst hc; simp [run]

section Spectral

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ) (H : E →L[ℝ] E)
  (hc : ∀ j v, ⟪b j, H v⟫ = eig j * ⟪b j, v⟫)

include hc

lemma duhamel (L : ℝ) (gn gl : E → E) (hgl : ∀ y y', gl y - gl y' = (1 / L) • H (y - y'))
    {W : ℝ} (hW : 0 ≤ W) :
    ∀ (hs : List ℝ), (∀ h ∈ hs, 0 ≤ h) →
      (∀ s, s <:+ hs → ∀ u, ‖lin H L s (P b eig u)‖ ≤ W * ‖P b eig u‖) →
      ∀ x x', ‖P b eig (run gn hs x - run gl hs x') - lin H L hs (P b eig (x - x'))‖ ≤
        W * esum gn (fun y => ‖P b eig (gn y - gl y)‖) hs x
  | [], _, _, x, x' => by simp [run, lin, esum]
  | h :: t, hpos, hsuf, x, x' => by
    have hh := hpos h (by simp)
    have ih := duhamel L gn gl hgl hW t (fun h' hh' => hpos h' (List.mem_cons_of_mem _ hh'))
      (fun s hs u => hsuf s (hs.trans (List.suffix_cons h t)) u) (x - h • gn x) (x' - h • gl x')
    have hdiff : (x - h • gn x) - (x' - h • gl x') =
        ((x - x') - (h * (1 / L)) • H (x - x')) - h • (gn x - gl x) := by
      have := hgl x x'
      have e1 : gn x = gl x + (gn x - gl x) := by abel
      rw [e1, smul_add, show gl x = gl x' + (gl x - gl x') by abel, this]
      simp only [smul_add, smul_smul]
      abel_nf
    have harg : P b eig ((x - h • gn x) - (x' - h • gl x')) =
        (P b eig (x - x') - h • ((1 / L) • H (P b eig (x - x')))) - h • P b eig (gn x - gl x) := by
      rw [hdiff, P_comm b eig H hc]
      simp only [map_sub, map_smul, smul_smul]
    have hstep : lin H L (h :: t) (P b eig (x - x')) =
        lin H L t (P b eig (x - x') - h • ((1 / L) • H (P b eig (x - x')))) := rfl
    have hV : lin H L t (P b eig ((x - h • gn x) - (x' - h • gl x'))) =
        lin H L (h :: t) (P b eig (x - x')) - h • lin H L t (P b eig (gn x - gl x)) := by
      rw [harg, lin_sub b eig H hc, lin_smul b eig H hc, hstep]
    rw [hV] at ih
    have hb := hsuf t (List.suffix_cons h t) (gn x - gl x)
    have hrun1 : run gn (h :: t) x = run gn t (x - h • gn x) := rfl
    have hrun2 : run gl (h :: t) x' = run gl t (x' - h • gl x') := rfl
    have hes : esum gn (fun y => ‖P b eig (gn y - gl y)‖) (h :: t) x =
        h * ‖P b eig (gn x - gl x)‖ + esum gn (fun y => ‖P b eig (gn y - gl y)‖) t (x - h • gn x) :=
      rfl
    rw [hrun1, hrun2, hes]
    obtain ⟨A, hA⟩ : ∃ A, A = P b eig (run gn t (x - h • gn x) - run gl t (x' - h • gl x')) :=
      ⟨_, rfl⟩
    obtain ⟨V0, hV0⟩ : ∃ V0, V0 = lin H L (h :: t) (P b eig (x - x')) := ⟨_, rfl⟩
    obtain ⟨Z, hZ⟩ : ∃ Z, Z = lin H L t (P b eig (gn x - gl x)) := ⟨_, rfl⟩
    rw [← hA, ← hV0, ← hZ] at ih
    rw [← hA, ← hV0]
    rw [← hZ] at hb
    have h1 : A - V0 = (A - (V0 - h • Z)) - h • Z := by abel
    rw [h1]
    calc ‖(A - (V0 - h • Z)) - h • Z‖ ≤ ‖A - (V0 - h • Z)‖ + ‖h • Z‖ := norm_sub_le _ _
      _ ≤ W * esum gn (fun y => ‖P b eig (gn y - gl y)‖) t (x - h • gn x) +
          h * (W * ‖P b eig (gn x - gl x)‖) := by
            apply add_le_add ih
            rw [norm_smul, Real.norm_of_nonneg hh]
            exact mul_le_mul_of_nonneg_left hb hh
      _ = W * (h * ‖P b eig (gn x - gl x)‖ +
            esum gn (fun y => ‖P b eig (gn y - gl y)‖) t (x - h • gn x)) := by ring

noncomputable def phiPart (g0 d : E) : ℝ :=
  ⟪g0, P b eig d⟫ + ⟪P b eig d, H (P b eig d)⟫ / 2

noncomputable def psiPart (g0 d : E) : ℝ :=
  ⟪g0, d - P b eig d⟫ + ⟪d - P b eig d, H (d - P b eig d)⟫ / 2

lemma model_split (g0 d : E) :
    ⟪g0, d⟫ + ⟪d, H d⟫ / 2 = phiPart b eig H g0 d + psiPart b eig H g0 d := by
  have hQ : P b eig (d - P b eig d) = 0 := by rw [map_sub, P_idem, sub_self]
  have h0 := cross_zero b eig H hc d (d - P b eig d) hQ
  have h1 : ⟪d - P b eig d, H (P b eig d)⟫ = 0 := by
    rw [P_comm b eig H hc, ← P_symm, hQ, inner_zero_left]
  have hd : d = P b eig d + (d - P b eig d) := by abel
  unfold phiPart psiPart
  conv_lhs => rw [hd]
  rw [inner_add_right, map_add, inner_add_left, inner_add_right, inner_add_right, h0, h1]
  ring

omit hc in
lemma Q_range (v : E) : P b eig (v - P b eig v) = 0 := by
  rw [map_sub, P_idem, sub_self]

omit hc in
lemma inner_Q_left (z v : E) (hz : P b eig z = 0) : ⟪z, v⟫ = ⟪z, v - P b eig v⟫ := by
  rw [inner_sub_right, ← P_symm, hz, inner_zero_left, sub_zero]

lemma Q_shift (g0 d : E) :
    (g0 + H (d - P b eig d)) - P b eig (g0 + H (d - P b eig d)) =
      (g0 + H d) - P b eig (g0 + H d) := by
  simp only [map_sub, map_add, P_comm b eig H hc, P_idem]
  abel

lemma psi_step (hsym : ∀ u v, ⟪H u, v⟫ = ⟪u, H v⟫) (g0 d e : E) {α : ℝ} (hα : 0 ≤ α) :
    psiPart b eig H g0 (d - α • (g0 + H d + e)) ≤
      psiPart b eig H g0 d - α / 2 * ‖(g0 + H d) - P b eig (g0 + H d)‖ ^ 2 + α / 2 * ‖e‖ ^ 2 := by
  obtain ⟨u, hu⟩ : ∃ u, u = (g0 + H d) - P b eig (g0 + H d) := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, w = d - P b eig d := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = e - P b eig e := ⟨_, rfl⟩
  rw [← hu]
  have hzP : P b eig (u + q) = 0 := by
    rw [map_add, hu, hq, Q_range b eig, Q_range b eig, add_zero]
  have hd' : (d - α • (g0 + H d + e)) - P b eig (d - α • (g0 + H d + e)) = w - α • (u + q) := by
    rw [hu, hw, hq]
    simp only [map_sub, map_add, map_smul]
    module
  have hpsi' : psiPart b eig H g0 (d - α • (g0 + H d + e)) =
      ⟪g0, w - α • (u + q)⟫ + ⟪w - α • (u + q), H (w - α • (u + q))⟫ / 2 := by
    unfold psiPart; rw [hd']
  have hpsi : psiPart b eig H g0 d = ⟪g0, w⟫ + ⟪w, H w⟫ / 2 := by
    unfold psiPart; rw [hw]
  rw [hpsi', hpsi]
  obtain ⟨z, hz⟩ : ∃ z, z = u + q := ⟨_, rfl⟩
  rw [← hz] at hzP ⊢
  have hkey : ⟪g0, z⟫ + ⟪z, H w⟫ = ⟪z, u⟫ := by
    have h1 : ⟪g0, z⟫ + ⟪z, H w⟫ = ⟪z, g0 + H w⟫ := by
      rw [inner_add_right, real_inner_comm z g0]
    rw [h1, inner_Q_left b eig z _ hzP, hw, Q_shift b eig H hc, ← hu]
  have hs1 : ⟪w, H z⟫ = ⟪z, H w⟫ := by
    rw [← hsym w z]; exact real_inner_comm _ _
  have e1 : ⟪g0, w - α • z⟫ = ⟪g0, w⟫ - α * ⟪g0, z⟫ := by
    rw [inner_sub_right, real_inner_smul_right]
  have e2 : ⟪w - α • z, H (w - α • z)⟫ =
      ⟪w, H w⟫ - 2 * α * ⟪z, H w⟫ + α ^ 2 * ⟪z, H z⟫ := by
    simp only [map_sub, map_smul, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right]
    rw [hs1]
    ring
  rw [e1, e2]
  have hneg := neg_part b eig H hc z hzP
  have hzu : ⟪z, u⟫ = ‖u‖ ^ 2 + ⟪q, u⟫ := by
    rw [hz, inner_add_left, real_inner_self_eq_norm_sq]
  have hqe : ‖q‖ ≤ ‖e‖ := by rw [hq]; exact Q_norm_le b eig e
  have hcs : |⟪q, u⟫| ≤ ‖q‖ * ‖u‖ := abs_real_inner_le_norm _ _
  have h1 : α ^ 2 / 2 * ⟪z, H z⟫ ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg
  have hqu : ‖q‖ * ‖u‖ ≤ ‖u‖ ^ 2 / 2 + ‖e‖ ^ 2 / 2 := by
    nlinarith [sq_nonneg (‖q‖ - ‖u‖), norm_nonneg q, norm_nonneg e, norm_nonneg u]
  have h2 : -(α * ⟪q, u⟫) ≤ α / 2 * ‖u‖ ^ 2 + α / 2 * ‖e‖ ^ 2 := by
    have := (abs_le.mp hcs).1
    nlinarith
  have hsum : ⟪g0, w⟫ - α * ⟪g0, z⟫ + (⟪w, H w⟫ - 2 * α * ⟪z, H w⟫ + α ^ 2 * ⟪z, H z⟫) / 2 =
      ⟪g0, w⟫ + ⟪w, H w⟫ / 2 - α * (⟪g0, z⟫ + ⟪z, H w⟫) + α ^ 2 / 2 * ⟪z, H z⟫ := by ring
  rw [hsum, hkey, hzu]
  nlinarith

lemma grad_step (g0 d e : E) {α : ℝ} (hα : 0 ≤ α) :
    ‖(g0 + H d) - P b eig (g0 + H d)‖ - α * ‖H‖ * ‖e‖ ≤
      ‖(g0 + H (d - α • (g0 + H d + e))) - P b eig (g0 + H (d - α • (g0 + H d + e)))‖ := by
  obtain ⟨u, hu⟩ : ∃ u, u = (g0 + H d) - P b eig (g0 + H d) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = e - P b eig e := ⟨_, rfl⟩
  rw [← hu]
  have huP : P b eig u = 0 := by rw [hu]; exact Q_range b eig _
  have hnew : (g0 + H (d - α • (g0 + H d + e))) - P b eig (g0 + H (d - α • (g0 + H d + e))) =
      (u - α • H u) - α • H q := by
    rw [hu, hq]
    simp only [map_sub, map_add, map_smul, P_comm b eig H hc]
    module
  rw [hnew]
  have hgrow : ‖u‖ ≤ ‖u - α • H u‖ := by
    have hneg := neg_part b eig H hc u huP
    have hsq : ‖u‖ ^ 2 ≤ ‖u - α • H u‖ ^ 2 := by
      rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_of_nonneg hα]
      nlinarith [sq_nonneg (α * ‖H u‖), mul_nonpos_of_nonneg_of_nonpos hα hneg]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  have herr : ‖α • H q‖ ≤ α * ‖H‖ * ‖e‖ := by
    rw [norm_smul, Real.norm_of_nonneg hα, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hα
    calc ‖H q‖ ≤ ‖H‖ * ‖q‖ := H.le_opNorm _
      _ ≤ ‖H‖ * ‖e‖ := mul_le_mul_of_nonneg_left (by rw [hq]; exact Q_norm_le b eig e)
          (norm_nonneg _)
  have h3 : ‖u - α • H u‖ - ‖α • H q‖ ≤ ‖u - α • H u - α • H q‖ := by
    have := norm_sub_le (u - α • H u - α • H q) (-(α • H q))
    rw [sub_neg_eq_add, sub_add_cancel, norm_neg] at this
    linarith
  linarith

lemma phi_dev (hsym : ∀ u v, ⟪H u, v⟫ = ⟪u, H v⟫) {L : ℝ} (hH : ‖H‖ ≤ L) (g0 d d' : E) :
    phiPart b eig H g0 d ≤ phiPart b eig H g0 d' +
      ‖P b eig (g0 + H d')‖ * ‖P b eig (d - d')‖ + L / 2 * ‖P b eig (d - d')‖ ^ 2 := by
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = P b eig (d - d') := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = P b eig d' := ⟨_, rfl⟩
  rw [← hδ]
  have hPd : P b eig d = v + δ := by rw [hδ, hv, map_sub]; abel
  have hδP : P b eig δ = δ := by rw [hδ, P_idem]
  have hvP : P b eig v = v := by rw [hv, P_idem]
  have hphi : ∀ x : E, phiPart b eig H g0 x = ⟪g0, P b eig x⟫ +
      ⟪P b eig x, H (P b eig x)⟫ / 2 := fun x => rfl
  rw [hphi, hphi, hPd, ← hv]
  have hgrad : P b eig (g0 + H d') = P b eig g0 + H v := by
    rw [map_add, ← P_comm b eig H hc, hv]
  have hlin : ⟪g0, δ⟫ + ⟪δ, H v⟫ = ⟪δ, P b eig (g0 + H d')⟫ := by
    rw [hgrad, inner_add_right, ← P_symm, hδP, real_inner_comm δ g0]
  have hs1 : ⟪v, H δ⟫ = ⟪δ, H v⟫ := by
    rw [← hsym v δ]; exact real_inner_comm _ _
  have hexp : ⟪g0, v + δ⟫ + ⟪v + δ, H (v + δ)⟫ / 2 =
      ⟪g0, v⟫ + ⟪v, H v⟫ / 2 + (⟪g0, δ⟫ + ⟪δ, H v⟫) + ⟪δ, H δ⟫ / 2 := by
    simp only [map_add, inner_add_left, inner_add_right]
    rw [hs1]
    ring
  rw [hexp, hlin]
  have hq : ⟪δ, H δ⟫ ≤ L * ‖δ‖ ^ 2 := by
    calc ⟪δ, H δ⟫ ≤ ‖δ‖ * ‖H δ‖ := real_inner_le_norm _ _
      _ ≤ ‖δ‖ * (‖H‖ * ‖δ‖) := mul_le_mul_of_nonneg_left (H.le_opNorm _) (norm_nonneg _)
      _ ≤ ‖δ‖ * (L * ‖δ‖) := by gcongr
      _ = L * ‖δ‖ ^ 2 := by ring
  have hcs : ⟪δ, P b eig (g0 + H d')⟫ ≤ ‖P b eig (g0 + H d')‖ * ‖δ‖ := by
    have := real_inner_le_norm δ (P b eig (g0 + H d'))
    linarith [mul_comm ‖δ‖ ‖P b eig (g0 + H d')‖]
  linarith

end Spectral

end LongTails.Proofs.AdaptiveSilverDynamics
