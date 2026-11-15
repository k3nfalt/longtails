import LongTails.Proofs.InterpolatedFiniteSumLinkGeometry
import LongTails.Proofs.InterpolatedFiniteSumLinkPlacement
import LongTails.Proofs.InterpolatedFiniteSumLinkOracle
import LongTails.Proofs.InterpolatedFiniteSumExponentialOracle

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators RealInnerProductSpace
open Classical

namespace LongTails.Proofs.InterpolatedFiniteSumLinkReplies

open InterpolatedFiniteSumLinkGeometry
open InterpolatedFiniteSumPairs InterpolatedFiniteSumExponentialFamily

noncomputable def latent {d T : ℕ} (π : Fin T → Fin d) (η a L r G W : ℝ) (j : Fin T) :=
  InterpolatedFiniteSumLinks.shielded (vector π a L j) (offset j) (coefficient η j) r G W

noncomputable def latentField {d T : ℕ} (π : Fin T → Fin d) (η a L r G W : ℝ) (j : Fin T) :=
  InterpolatedFiniteSumLinks.shieldedField (vector π a L j) (offset j) (coefficient η j) r G W

noncomputable def empty {d : ℕ} (r G W : ℝ) : EuclideanSpace ℝ (Fin d) → ℝ :=
  InterpolatedFiniteSumLinks.shielded 0 0 0 r G W

noncomputable def emptyField {d : ℕ} (r G W : ℝ) : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
  InterpolatedFiniteSumLinks.shieldedField 0 0 0 r G W

noncomputable def emptyReply {d : ℕ} (r G W B : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    ℝ × EuclideanSpace ℝ (Fin d) :=
  if ‖x‖ ≤ B then (empty r G W x, emptyField r G W x)
  else (InterpolatedFiniteSumShield.radialWall r G 0 W x, InterpolatedFiniteSumShield.radialField r G x)

noncomputable def latentReply {d T : ℕ} (π : Fin T → Fin d) (η a L r G W B : ℝ)
    (j : ℕ) (x : EuclideanSpace ℝ (Fin d)) : ℝ × EuclideanSpace ℝ (Fin d) :=
  if h : j < T then
    if ‖x‖ ≤ B then (latent π η a L r G W ⟨j, h⟩ x, latentField π η a L r G W ⟨j, h⟩ x)
    else (InterpolatedFiniteSumShield.radialWall r G 0 W x, InterpolatedFiniteSumShield.radialField r G x)
  else emptyReply r G W B x

lemma latentReply_local {d T : ℕ} (π ρ : Fin T → Fin d) (η a L r G W B : ℝ)
    (j : ℕ) (x : EuclideanSpace ℝ (Fin d)) (h : ∀ i : Fin T, i.val ≤ j → π i = ρ i) :
    latentReply π η a L r G W B j x = latentReply ρ η a L r G W B j x := by
  by_cases hj : j < T
  · have hv := vector_prefix π ρ a L ⟨j, hj⟩ h
    simp only [latentReply, dite_eq_left hj, latent, latentField, hv]
  · simp only [latentReply, dite_eq_right hj]

lemma latentReply_future {d T : ℕ} (π : Fin T → Fin d) (η a L r G W B θ : ℝ)
    (hL : 0 ≤ L) (hθL : L * θ ≤ 1 / 4) (ℓ j : ℕ) (hj : ℓ < j) (x : EuclideanSpace ℝ (Fin d))
    (hx : ‖x‖ ≤ B → ∀ i : Fin T, ℓ ≤ i.val → |x (π i)| ≤ θ) :
    latentReply π η a L r G W B j x = emptyReply r G W B x := by
  by_cases hjT : j < T
  · by_cases hnear : ‖x‖ ≤ B
    · have hj0 : j ≠ 0 := by omega
      have hv : |⟪vector π a L ⟨j, hjT⟩, x⟫ - offset ⟨j, hjT⟩| ≤ 1 / 4 := by
        rw [vector_inner, ite_eq_right hj0, offset, ite_eq_right hj0, sub_zero, abs_mul,
          abs_of_nonneg (by positivity : 0 ≤ L / 2)]
        have hp := hx hnear (previous ⟨j, hjT⟩) (by dsimp [previous]; omega)
        have hc := hx hnear ⟨j, hjT⟩ (by change ℓ ≤ j; omega)
        have hh := abs_sub (x (π (previous ⟨j, hjT⟩))) (x (π ⟨j, hjT⟩))
        have hm := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ L / 2)
        have hs := mul_le_mul_of_nonneg_left (add_le_add hp hc) (by positivity : 0 ≤ L / 2)
        nlinarith only [hm, hs, hθL]
      have he := InterpolatedFiniteSumLinks.shielded_flat (vector π a L ⟨j, hjT⟩)
        (offset ⟨j, hjT⟩) (coefficient η ⟨j, hjT⟩) r G W x hv
      simp only [latentReply, dite_eq_left hjT, emptyReply, ite_eq_left hnear, latent, latentField,
        empty, emptyField, he.1, he.2]
    · simp only [latentReply, dite_eq_left hjT, emptyReply, ite_eq_right hnear]
  · simp only [latentReply, dite_eq_right hjT]

lemma emptyReply_full {d : ℕ} (r G W B η : ℝ) (hG : 0 < G) (hW : 0 < W) (hη : 0 ≤ η)
    (hB : 4 * r + (η + W) / G ≤ B) (x : EuclideanSpace ℝ (Fin d)) :
    emptyReply r G W B x = (empty r G W x, emptyField r G W x) := by
  by_cases hx : ‖x‖ ≤ B
  · simp only [emptyReply, ite_eq_left hx]
  · have he := InterpolatedFiniteSumLinks.shielded_far (0 : EuclideanSpace ℝ (Fin d)) 0 0 r G W η B
      (by norm_num) hG hW (by simpa using hG.le)
      (by simpa [InterpolatedFiniteSumLinks.potential] using hη) hB x (lt_of_not_ge hx).le
    simp only [emptyReply, ite_eq_right hx, empty, emptyField, he.1, he.2]

lemma latentReply_full {d T : ℕ} (π : Fin T → Fin d) (η a L r G W B : ℝ)
    (hη : 0 ≤ η) (hG : 0 < G) (hW : 0 < W)
    (hgrad : ∀ j : Fin T, coefficient η j * ‖vector π a L j‖ ≤ G)
    (hB : 4 * r + (η + W) / G ≤ B) (j : Fin T) (x : EuclideanSpace ℝ (Fin d)) :
    latentReply π η a L r G W B j.val x = (latent π η a L r G W j x, latentField π η a L r G W j x) := by
  by_cases hx : ‖x‖ ≤ B
  · simp only [latentReply, dite_eq_left j.isLt, ite_eq_left hx]
  · have hinit : InterpolatedFiniteSumLinks.potential (vector π a L j) (offset j) (coefficient η j) 0 ≤ η := by
      change raw π η a L j 0 ≤ η
      rw [raw_zero]
      split_ifs <;> linarith
    have he := InterpolatedFiniteSumLinks.shielded_far (vector π a L j) (offset j) (coefficient η j) r G W η B
      (coefficient_nonnegative η hη j) hG hW (hgrad j) hinit hB x (lt_of_not_ge hx).le
    simp only [latentReply, dite_eq_left j.isLt, ite_eq_right hx, latent, latentField, he.1, he.2]

noncomputable def transformQuery {d n g : ℕ} (h : 2 * g ≤ n) (v : EuclideanSpace ℝ (Fin d)) (C : ℝ)
    (q : Fin n × EuclideanSpace ℝ (Fin d)) (z : ℝ × EuclideanSpace ℝ (Fin d)) : ℝ × EuclideanSpace ℝ (Fin d) :=
  paired h (fun a => InterpolatedFiniteSumExponentialOracle.transform (signed v a.2) C q.2 z) q.1

noncomputable def inactive {d n g : ℕ} (h : 2 * g ≤ n) (v : EuclideanSpace ℝ (Fin d)) (C r G W B : ℝ)
    (q : Fin n × EuclideanSpace ℝ (Fin d)) : ℝ × EuclideanSpace ℝ (Fin d) :=
  transformQuery h v C q (emptyReply r G W B q.2)

noncomputable def reply {d n g T : ℕ} (h : 2 * g ≤ n) (v : EuclideanSpace ℝ (Fin d)) (C η a L r G W B : ℝ)
    (π : Fin T → Fin d) (j : ℕ) (q : Fin n × EuclideanSpace ℝ (Fin d)) : ℝ × EuclideanSpace ℝ (Fin d) :=
  transformQuery h v C q (latentReply π η a L r G W B j q.2)

lemma reply_local {d n g T : ℕ} (h : 2 * g ≤ n) (v : EuclideanSpace ℝ (Fin d)) (C η a L r G W B : ℝ)
    (π ρ : Fin T → Fin d) (j : ℕ) (q : Fin n × EuclideanSpace ℝ (Fin d))
    (hp : ∀ i : Fin T, i.val ≤ j → π i = ρ i) :
    reply h v C η a L r G W B π j q = reply h v C η a L r G W B ρ j q := by
  rw [reply, reply, latentReply_local π ρ η a L r G W B j q.2 hp]

lemma reply_future {d n g T : ℕ} (h : 2 * g ≤ n) (v : EuclideanSpace ℝ (Fin d)) (C η a L r G W B θ : ℝ)
    (hL : 0 ≤ L) (hθL : L * θ ≤ 1 / 4) (π : Fin T → Fin d) (ℓ j : ℕ) (hj : ℓ < j)
    (q : Fin n × EuclideanSpace ℝ (Fin d))
    (hx : ‖q.2‖ ≤ B → ∀ i : Fin T, ℓ ≤ i.val → |q.2 (π i)| ≤ θ) :
    reply h v C η a L r G W B π j q = inactive h v C r G W B q := by
  rw [reply, latentReply_future π η a L r G W B θ hL hθL ℓ j hj q.2 hx]
  rfl

noncomputable def family {d g T : ℕ} (θ : Fin T ↪ Fin g) (π : Fin T → Fin d) (η a L r G W : ℝ) :
    Fin g → EuclideanSpace ℝ (Fin d) → ℝ :=
  InterpolatedFiniteSumLinkPlacement.assigned θ (latent π η a L r G W) (empty r G W)

noncomputable def familyField {d g T : ℕ} (θ : Fin T ↪ Fin g) (π : Fin T → Fin d) (η a L r G W : ℝ) :
    Fin g → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
  InterpolatedFiniteSumLinkPlacement.assigned θ (latentField π η a L r G W) (emptyField r G W)

noncomputable def fullReply {d n g T : ℕ} (h : 2 * g ≤ n) (θ : Fin T ↪ Fin g) (π : Fin T → Fin d)
    (v : EuclideanSpace ℝ (Fin d)) (C η a L r G W : ℝ) (q : Fin n × EuclideanSpace ℝ (Fin d)) :
    ℝ × EuclideanSpace ℝ (Fin d) :=
  (components h (family θ π η a L r G W) v C q.1 q.2,
    fields h (family θ π η a L r G W) (familyField θ π η a L r G W) v C q.1 q.2)

lemma fullReply_lookup {d n g T : ℕ} (h : 2 * g ≤ n)
    (w : InterpolatedFiniteSumDistinctSearch.OwnerWords g T) (π : Fin T → Fin d)
    (v : EuclideanSpace ℝ (Fin d)) (C η a L r G W B : ℝ)
    (hη : 0 ≤ η) (hG : 0 < G) (hW : 0 < W)
    (hgrad : ∀ j : Fin T, coefficient η j * ‖vector π a L j‖ ≤ G)
    (hB : 4 * r + (η + W) / G ≤ B) (q : Fin n × EuclideanSpace ℝ (Fin d)) :
    fullReply h (InterpolatedFiniteSumDistinctSearch.owner w) π v C η a L r G W q =
      InterpolatedFiniteSumLinkOracle.lookup (fun q => ownerQuery g q.1)
        (reply h v C η a L r G W B) (inactive h v C r G W B) π w.val q := by
  rcases q with ⟨i, x⟩
  rcases index_or_outside h i with ⟨b, rfl⟩ | hi
  · by_cases hb : ∃ j, InterpolatedFiniteSumDistinctSearch.owner w j = b.1
    · obtain ⟨j, hj⟩ := hb
      have hmem : b.1.castSucc ∈ w.val := (InterpolatedFiniteSumDistinctSearch.owner_mem_iff w b.1).mpr ⟨j, hj⟩
      have hidx : w.val.idxOf b.1.castSucc = j.val := by
        rw [← hj]
        exact InterpolatedFiniteSumDistinctSearch.owner_idxOf w j
      have hf : family (InterpolatedFiniteSumDistinctSearch.owner w) π η a L r G W b.1 = latent π η a L r G W j := by
        unfold family
        rw [← hj, InterpolatedFiniteSumLinkPlacement.assigned_at]
      have hdf : familyField (InterpolatedFiniteSumDistinctSearch.owner w) π η a L r G W b.1 = latentField π η a L r G W j := by
        unfold familyField
        rw [← hj, InterpolatedFiniteSumLinkPlacement.assigned_at]
      simp only [fullReply, components, fields, paired_at_index, hf, hdf,
        InterpolatedFiniteSumLinkOracle.lookup, ownerQuery_index, ite_eq_left hmem, hidx,
        reply, transformQuery, paired_at_index]
      rw [latentReply_full π η a L r G W B hη hG hW hgrad hB j x,
        InterpolatedFiniteSumExponentialOracle.transform_full]
    · have hmem : b.1.castSucc ∉ w.val := by
        simpa only [InterpolatedFiniteSumDistinctSearch.owner_mem_iff] using hb
      have hf : family (InterpolatedFiniteSumDistinctSearch.owner w) π η a L r G W b.1 = empty r G W :=
        InterpolatedFiniteSumLinkPlacement.assigned_outside _ _ _ _ hb
      have hdf : familyField (InterpolatedFiniteSumDistinctSearch.owner w) π η a L r G W b.1 = emptyField r G W :=
        InterpolatedFiniteSumLinkPlacement.assigned_outside _ _ _ _ hb
      simp only [fullReply, components, fields, paired_at_index, hf, hdf,
        InterpolatedFiniteSumLinkOracle.lookup, ownerQuery_index, ite_eq_right hmem,
        inactive, transformQuery, paired_at_index]
      rw [emptyReply_full r G W B η hG hW hη hB x,
        InterpolatedFiniteSumExponentialOracle.transform_full]
  · have hmem : Fin.last g ∉ w.val := by
      intro hh
      have he := InterpolatedFiniteSumDistinctSearch.ownerWord_mem w (Fin.last g) hh
      simp at he
    simp only [fullReply, components, fields,
      InterpolatedFiniteSumLinkOracle.lookup, ownerQuery_outside i hi, ite_eq_right hmem,
      inactive, transformQuery, paired_outside h _ i hi]
    rfl

lemma latent_gradient {d T : ℕ} (π : Fin T → Fin d) (η a L r G W : ℝ)
    (hr : 0 < r) (hW : 0 < W) (j : Fin T) (x : EuclideanSpace ℝ (Fin d)) :
    HasGradientAt (latent π η a L r G W j) (latentField π η a L r G W j x) x :=
  InterpolatedFiniteSumLinks.shielded_gradient _ _ _ _ _ _ hr hW x

lemma latent_zero {d T : ℕ} (π : Fin T → Fin d) (η a L r G W : ℝ)
    (hη : 0 ≤ η) (hr : 0 < r) (hG : 0 ≤ G) (hW : 0 < W) (j : Fin T) :
    latent π η a L r G W j 0 = if j.val = 0 then η else 0 := by
  rw [latent, InterpolatedFiniteSumLinks.shielded,
    InterpolatedFiniteSumShield.envelope_radial_interior _ r G 0 W hr hG hW
      (InterpolatedFiniteSumLinks.potential_nonnegative _ _ _ (coefficient_nonnegative η hη j))
      0 (by simpa using hr.le)]
  exact raw_zero π η a L j

lemma empty_zero {d : ℕ} (r G W : ℝ) (hr : 0 < r) (hG : 0 ≤ G) (hW : 0 < W) :
    empty (d := d) r G W 0 = 0 :=
  InterpolatedFiniteSumLinks.shielded_minimizer_value _ _ _ _ _ _ (by norm_num) hr hG hW 0
    (by simpa using hr.le) (by simp)

lemma family_gradient {d g T : ℕ} (θ : Fin T ↪ Fin g) (π : Fin T → Fin d) (η a L r G W : ℝ)
    (hr : 0 < r) (hW : 0 < W) (i : Fin g) (x : EuclideanSpace ℝ (Fin d)) :
    HasGradientAt (family θ π η a L r G W i) (familyField θ π η a L r G W i x) x :=
  InterpolatedFiniteSumLinkPlacement.assigned_gradient θ _ _ _ _
    (latent_gradient π η a L r G W hr hW)
    (InterpolatedFiniteSumLinks.shielded_gradient _ _ _ _ _ _ hr hW) i x

lemma initial_sum {d g k : ℕ} (θ : Fin (k + 1) ↪ Fin g) (π : Fin (k + 1) → Fin d) (η a L r G W : ℝ)
    (hη : 0 ≤ η) (hr : 0 < r) (hG : 0 ≤ G) (hW : 0 < W) :
    (∑ i : Fin g, (Real.exp (family θ π η a L r G W i 0) - 1)) = Real.exp η - 1 := by
  have he := InterpolatedFiniteSumLinkPlacement.sum_assigned_eq θ (latent π η a L r G W) (empty r G W)
    (fun f => Real.exp (f 0) - 1) (by rw [empty_zero r G W hr hG hW]; simp)
  change (∑ i : Fin g, (Real.exp (family θ π η a L r G W i 0) - 1)) = _ at he
  rw [he]
  have hf (j : Fin (k + 1)) : Real.exp (latent π η a L r G W j 0) - 1 =
      if j = 0 then Real.exp η - 1 else 0 := by
    rw [latent_zero π η a L r G W hη hr hG hW]
    by_cases hj : j = 0
    · simp [hj]
    · have hv : j.val ≠ 0 := by intro hh; exact hj (Fin.ext hh)
      simp only [ite_eq_right hv, ite_eq_right hj, Real.exp_zero, sub_self]
  simp_rw [hf]
  simp

noncomputable def fullOracle {d n g T : ℕ} (h : 2 * g ≤ n) (θ : Fin T ↪ Fin g) (π : Fin T → Fin d)
    (v : EuclideanSpace ℝ (Fin d)) (C η a L r G W : ℝ) :
    OracleTemplate.Oracle (Fin n × EuclideanSpace ℝ (Fin d)) (ℝ × EuclideanSpace ℝ (Fin d)) where
  answer _ q _ := fullReply h θ π v C η a L r G W q.2

lemma coupled_execution {d n g T : ℕ} (h : 2 * g ≤ n)
    (w : InterpolatedFiniteSumDistinctSearch.OwnerWords g T) (π : Fin T → Fin d)
    (v : EuclideanSpace ℝ (Fin d)) (C η a L r G W B θ : ℝ)
    (hη : 0 ≤ η) (hL : 0 ≤ L) (hG : 0 < G) (hW : 0 < W)
    (hgrad : ∀ j : Fin T, coefficient η j * ‖vector π a L j‖ ≤ G)
    (hB : 4 * r + (η + W) / G ≤ B) (hθL : L * θ ≤ 1 / 4)
    (A : OracleTemplate.Algorithm (Fin n × EuclideanSpace ℝ (Fin d)) (ℝ × EuclideanSpace ℝ (Fin d))
      (EuclideanSpace ℝ (Fin d))) (b : ℕ) (seed : A.Seed) (ξ : ℕ → Unit) (carrier : Fin d)
    (hgood : ¬InterpolatedFiniteSumLinkOracle.Bad A (fun q => ownerQuery g q.1)
      (reply h v C η a L r G W B) (inactive h v C r G W B)
      Prod.snd id (A.initial seed) w.val b B θ carrier π) :
    OracleTemplate.execute (fullOracle h (InterpolatedFiniteSumDistinctSearch.owner w) π v C η a L r G W)
      A (fun _ => b) seed ξ =
      A.output (InterpolatedFiniteSumLinkOracle.process A (fun q => ownerQuery g q.1)
        (reply h v C η a L r G W B) (inactive h v C r G W B) (A.initial seed) w.val π b).1.1.1 := by
  rw [OracleTemplate.execute_eq_of_answer_eq
    (fullOracle h (InterpolatedFiniteSumDistinctSearch.owner w) π v C η a L r G W)
    (fullReply h (InterpolatedFiniteSumDistinctSearch.owner w) π v C η a L r G W) (by intros; rfl),
    OracleTemplate.execute_iterate _ A b seed]
  apply congrArg A.output
  apply InterpolatedFiniteSumLinkOracle.process_coupling
  intro t ht
  let s := (InterpolatedFiniteSumLinkOracle.process A (fun q => ownerQuery g q.1)
    (reply h v C η a L r G W B) (inactive h v C r G W B) (A.initial seed) w.val π t).1
  let q := (A.query s.1.1).2
  have hp := InterpolatedFiniteSumLinkOracle.process_prefix A (fun q => ownerQuery g q.1)
    (reply h v C η a L r G W B) (inactive h v C r G W B) (A.initial seed) w.val π t
  change s.1.2 ++ s.2.1 = w.val at hp
  dsimp only
  rw [fullReply_lookup h w π v C η a L r G W B hη hG hW hgrad hB]
  change InterpolatedFiniteSumLinkOracle.lookup (fun q => ownerQuery g q.1)
    (reply h v C η a L r G W B) (inactive h v C r G W B) π w.val q =
      InterpolatedFiniteSumLinkOracle.decoded (fun q => ownerQuery g q.1)
        (reply h v C η a L r G W B) (inactive h v C r G W B) π s.1.2
        (InterpolatedFiniteSumLinkOracle.hit A (fun q => ownerQuery g q.1) s) q
  rw [← hp]
  change InterpolatedFiniteSumLinkOracle.lookup (fun q => ownerQuery g q.1)
    (reply h v C η a L r G W B) (inactive h v C r G W B) π (s.1.2 ++ s.2.1) q =
      InterpolatedFiniteSumLinkOracle.decoded (fun q => ownerQuery g q.1)
        (reply h v C η a L r G W B) (inactive h v C r G W B) π s.1.2
        (InterpolatedFiniteSumLinkOracle.test (fun q => ownerQuery g q.1) q s.2.1) q
  apply (InterpolatedFiniteSumLinkOracle.decoded_lookup _ _ _ π s.1.2 s.2.1 q _).symm
  intro j hj
  apply reply_future h v C η a L r G W B θ hL hθL π s.1.2.length j hj q
  intro hnear i hi
  have hh := InterpolatedFiniteSumLinkOracle.good_coordinate A (fun q => ownerQuery g q.1)
    (reply h v C η a L r G W B) (inactive h v C r G W B) Prod.snd id (A.initial seed) w.val
    b B θ carrier π hgood ⟨t, by omega⟩ i hi
    (by simpa only [InterpolatedFiniteSumLinkOracle.observation, ite_eq_right (ne_of_lt ht)] using hnear)
  simpa only [InterpolatedFiniteSumLinkOracle.observation, ite_eq_right (ne_of_lt ht)] using hh

end LongTails.Proofs.InterpolatedFiniteSumLinkReplies
