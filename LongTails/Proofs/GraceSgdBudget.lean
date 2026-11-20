import LongTails.Proofs.GraceCommunicationTime
import LongTails.Proofs.GraceSgdGuarantee
import LongTails.Proofs.DistributedBatchedBudget

namespace LongTails.Proofs.GraceSgdBudget

open DistributedTemplate
open LongTails.Setups.GraphBandwidthSmoothNonconvex
open LongTails.Algorithms
open GraceGraph GraceRouting GraceBatch GraceTree
open GraceSampleSchedule (time)

noncomputable def width (p : Params) := 32 + 4 * Nat.log2
  (2 + p.d + ⌈2 * p.L * p.Δ / p.ε⌉₊ + ⌈p.σ^2 / p.ε⌉₊)

noncomputable def cost (p : Params) (S : Finset (Fin p.n)) : Time :=
  let t := GracePacket.limbWidth (B p)
  batchTime p S + if S.card ≤ 1 then 0 else
    16 * (p.d * (width p + t) + t * (Fintype.card (Link p) + 1) * p.n : ℕ) / α p S

def solo (p : Params) (r : Fin p.n) : Routes p {r} r where
  P := 1
  tree _ := {
    nodes := {r}
    terminals := fun _ h => h
    parent := fun _ => r
    depth := fun _ => 0
    root_mem := Finset.mem_singleton_self _
    depth_root := rfl
    parent_root := rfl
    parent_mem := by simp
    parent_edge := by simp
    parent_depth := by simp }

lemma solo_time (p : Params) (r : Fin p.n) : time (solo p r) = batchTime p {r} := by
  have hf (q : ℕ) : (solo p r).frameTime q = 0 := by
    apply le_antisymm _ zero_le
    apply Finset.sup_le
    intro e _
    have h : (solo p r).linkLanes e.val.1 e.val.2 = ∅ := by
      ext a
      by_cases hi : e.val.1 = r <;> by_cases hj : e.val.2 = r <;> simp [solo,Routes.linkLanes,hi,hj]
    simp [h]
  simp [time,GraceRoundSchedule.halfTime,hf]

lemma subset_routes (p : Params) (hp : spec.valid p) (S : Finset (Fin p.n)) (hS : S.Nonempty) :
    ∃ (r : Fin p.n) (A : Routes p S r), r ∈ S ∧ time A ≤ cost p S := by
  classical
  obtain ⟨hG,hb,hh,hL,hΔ,_,hε⟩ := hp
  by_cases h1 : S.card ≤ 1
  · obtain ⟨r,hr⟩ := Finset.card_eq_one.mp (le_antisymm h1 (Finset.card_pos.mpr hS))
    subst S
    exact ⟨r,solo p r,by simp,by simp [solo_time,cost]⟩
  · obtain ⟨r,hr⟩ := hS
    have ha := GraceGraphPacking.alpha_pos p (lt_of_not_ge h1) hG (fun i j he => (hb i j he).1)
    obtain ⟨m,A,hm,hl,hc⟩ := GraceGraphPacking.integral_routes p hr ha
    refine ⟨r,A,hr,?_⟩
    have hnet := GraceCommunicationTime.two_phase_budget A m (B p) (tuning p S).width hl ha hc
      (fun e => (hb _ _ e.property.2).1)
    have hw : ((tuning p S).width : ℕ) ≤ width p :=
      DistributedBatchedBudget.width_le (p := statistical p) (mul_pos two_pos hL) hΔ hε
    have hh' := GraceRouting.height_lt_workers A
    have hbound : p.d * (((tuning p S).width : ℕ) + GraceRoundSchedule.t p) +
        GraceRoundSchedule.t p * (m : ℕ) * (A.height+1) ≤
      p.d * (width p + GraceRoundSchedule.t p) +
        GraceRoundSchedule.t p * (Fintype.card (Link p)+1) * (p.n : ℕ) := by
      gcongr
      omega
    have hhalf : GraceRoundSchedule.halfTime A + GraceRoundSchedule.halfTime A ≤
        16 * ((p.d * (width p + GraceRoundSchedule.t p) +
          GraceRoundSchedule.t p * (Fintype.card (Link p)+1) * (p.n : ℕ) : ℕ) : Time) / α p S := by
      rw [← two_mul,GraceRoundSchedule.halfTime,← mul_assoc]
      refine hnet.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by norm_num)) zero_le)
      exact_mod_cast hbound
    simpa only [cost,h1,ite_false,time,add_assoc] using add_le_add_right hhalf (batchTime p S)

abbrev Workers (p : Params) := {S : Finset (Fin p.n) // S.Nonempty}

lemma select_routes (p : Params) (hp : spec.valid p) :
    ∃ (S : Workers p) (r : Fin p.n) (A : Routes p S.val r),
      r ∈ S.val ∧ time A ≤ ⨅ U : Workers p, cost p U.val := by
  classical
  let _ : Nonempty (Workers p) := ⟨⟨{0},by simp⟩⟩
  obtain ⟨S,_,hmin⟩ := Finset.univ.exists_min_image (fun U : Workers p => cost p U.val) Finset.univ_nonempty
  obtain ⟨r,A,hr,ht⟩ := subset_routes p hp S.val S.property
  exact ⟨S,r,A,hr,ht.trans (le_ciInf fun U => hmin U (Finset.mem_univ _))⟩

lemma iterations_sub_one (p : Params) (S : Finset (Fin p.n)) :
    ((tuning p S).iterations : ℕ) - 1 = ⌈32 * p.L * p.Δ / p.ε⌉₊ - 1 := by
  change max 1 ⌈16 * (2*p.L) * p.Δ / p.ε⌉₊ - 1 = _
  rw [show (16 : ℝ) * (2*p.L) = 32*p.L by ring]
  omega

lemma cut_formula (p : Params) (S : Finset (Fin p.n)) (hs : 1 < S.card) :
    α p S = ⨅ C : {C : Finset (Fin p.n) // (S ∩ C).Nonempty ∧ (S \ C).Nonempty},
      cut p C.val := by
  classical
  obtain ⟨i,hi⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  obtain ⟨j,hj,hji⟩ := Finset.exists_mem_ne hs i
  have hcut : {i} ∈ cuts p S := by
    simp only [cuts, Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨⟨i,by simp [hi]⟩,⟨j,by simp [hj,hji]⟩⟩
  let _ : Nonempty {C : Finset (Fin p.n) // (S ∩ C).Nonempty ∧ (S \ C).Nonempty} :=
    ⟨⟨{i},(Finset.mem_filter.mp hcut).2⟩⟩
  let vals := (cuts p S).image (cut p)
  have hv : vals.Nonempty := ⟨_,Finset.mem_image_of_mem _ hcut⟩
  have hα : α p S = vals.min' hv := dite_eq_left hv
  apply le_antisymm
  · apply le_ciInf
    intro C
    exact GraceGraphPacking.alpha_le p S C.val ((GraceGraphPacking.cuts_iff ..).mp
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,C.property⟩))
  · obtain ⟨C,hC,he⟩ := Finset.mem_image.mp (vals.min'_mem hv)
    rw [hα,← he]
    exact ciInf_le_of_le (OrderBot.bddBelow _) ⟨C,(Finset.mem_filter.mp hC).2⟩ le_rfl

end LongTails.Proofs.GraceSgdBudget
