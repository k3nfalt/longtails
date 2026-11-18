import LongTails.Proofs.PolynomialMixingBurst
import LongTails.Proofs.PolynomialMixingBlocks

open MeasureTheory ProbabilityTheory

namespace LongTails.Proofs.PolynomialMixingBurst

open LongTails.Setups.PolynomialMixingSubgradient
open LongTails.Proofs.PolynomialMixingBlocks

def overlap (n t m : ℕ) : Set Bits :=
  ⋃ i : Fin (m - t), {b | b (n + t + i.val) = true}

lemma overlap_probability (n t m : ℕ) (a : unitInterval) :
    (bitsLaw a).real (overlap n t m) ≤ (m - t : ℕ) * (a : ℝ) := by
  have hsingle (k : ℕ) : (bitsLaw a).real {b | b k = true} = (a : ℝ) := by
    have hm := (OracleTemplate.StochasticGeneralized.infinitePi_iid (bitLaw a)).marginal k
    have he := congrArg (fun μ : Measure Bool => μ.real {true}) hm
    rw [map_measureReal_apply (measurable_pi_apply k) (measurableSet_singleton _)] at he
    exact he.trans (by simp [bitLaw, bernoulliMeasure_real_apply a (measurableSet_singleton true)])
  unfold overlap
  simpa only [hsingle, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
    (measureReal_iUnion_fintype_le (μ := bitsLaw a)
      (fun i : Fin (m - t) => {b : Bits | b (n + t + i.val) = true}))

def stopBits (j : ℕ) (u : Fin j → Bool) (k : ℕ) : Bool :=
  if hk : k < j then u ⟨k, hk⟩ else false

lemma measurable_stopBits (j : ℕ) : Measurable (stopBits j) := by
  apply Measurable.of_eval
  intro k
  by_cases hk : k < j
  · simpa only [stopBits, dite_eq_left hk] using (show Measurable (fun u : Fin j → Bool => u ⟨k, hk⟩) from measurable_pi_apply _)
  · simpa only [stopBits, dite_eq_right hk] using (measurable_const : Measurable (fun _ : Fin j → Bool => false))

lemma blocked_past_eq (n t m : ℕ) (b : Bits) (hb : b ∉ overlap n t m) :
    past (n + 1) (burst m b) =
      past (n + 1) (burst m (stopBits (n + t) (fun i => b i.val))) := by
  funext i
  unfold past burst
  congr 1
  apply propext
  constructor
  · rintro ⟨j, hj⟩
    by_cases h : i.val + j.val < n + t
    · exact ⟨j, by simpa only [stopBits, dite_eq_left h] using hj⟩
    · exfalso
      apply hb
      apply Set.mem_iUnion.mpr
      have hi := i.isLt
      have hj' := j.isLt
      refine ⟨⟨i.val + j.val - (n + t), by omega⟩, ?_⟩
      change b (n + t + (i.val + j.val - (n + t))) = true
      rwa [Nat.add_sub_of_le (by omega : n + t ≤ i.val + j.val)]
  · rintro ⟨j, hj⟩
    by_cases h : i.val + j.val < n + t
    · exact ⟨j, by simpa only [stopBits, dite_eq_left h] using hj⟩
    · simp [stopBits, h] at hj

lemma burst_block_error (m n t : ℕ) (a : unitInterval) :
    let P := (burstLaw m a : Measure Path)
    SetError (P.map (fun z => (past (n + 1) z, future (n + t) z)))
      ((P.map (past (n + 1))).prod P) (2 * ((m - t : ℕ) : ℝ) * a) := by
  let U := bitsLaw a
  let F := past (n + 1) ∘ burst m
  let cut := n + t
  let pre := fun (b : Bits) (j : Fin cut) => b j.val
  let post := fun (b : Bits) (j : ℕ) => b (cut + j)
  let D := past (n + 1) ∘ burst m ∘ stopBits cut
  let H := D ∘ pre
  let V := burst m ∘ post
  have hp : Measurable (past (n + 1)) := by unfold past; fun_prop
  have hF := hp.comp (measurable_burst m)
  have hD := hF.comp (measurable_stopBits cut)
  have hpre : Measurable pre := by unfold pre; fun_prop
  have hpost : Measurable post := by unfold post; fun_prop
  have hH := hD.comp hpre
  have hV := (measurable_burst m).comp hpost
  have hh : ∀ b ∉ overlap n t m, F b = H b := fun b hb => blocked_past_eq n t m b hb
  have hj := setError_coupling U (hF.prodMk hV) (hH.prodMk hV) (overlap n t m)
    (fun b hb => Prod.ext (hh b hb) rfl)
  have hind := ((OracleTemplate.StochasticGeneralized.infinitePi_iid (bitLaw a)).prefix_tail_independent cut).comp hD (measurable_burst m)
  have he : U.map (fun b => (H b, V b)) = (U.map H).prod (U.map V) :=
    hind.map_prod_eq_prod_map_map hH.aemeasurable hV.aemeasurable
  change SetError (U.map (fun b => (F b, V b))) (U.map (fun b => (H b, V b))) _ at hj
  rw [he] at hj
  let : IsProbabilityMeasure (U.map F) := (Measure.isProbabilityMeasure_map_iff hF.aemeasurable).mpr inferInstance
  let : IsProbabilityMeasure (U.map H) := (Measure.isProbabilityMeasure_map_iff hH.aemeasurable).mpr inferInstance
  let : IsProbabilityMeasure (U.map V) := (Measure.isProbabilityMeasure_map_iff hV.aemeasurable).mpr inferInstance
  have hc := setError_prod_right (U.map V) (setError_symm (setError_coupling U hF hH (overlap n t m) hh))
  have hfull := setError_trans hj hc
  have hshift : U.map V = (burstLaw m a : Measure Path) := by
    dsimp only [V]
    rw [← Measure.map_map (measurable_burst m) hpost]
    change ((bitsLaw a).map (fun b k => b (cut + k))).map _ = _
    rw [bits_shift]
    rfl
  rw [hshift] at hfull
  have hjoint : ((burstLaw m a : Measure Path).map (fun z => (past (n + 1) z, future cut z))) =
      U.map (fun b => (F b, V b)) := by
    change (U.map (burst m)).map _ = _
    rw [Measure.map_map (hp.prodMk (show Measurable (future cut) by unfold future; fun_prop)) (measurable_burst m)]
    congr 1
    funext b
    exact Prod.ext rfl (burst_shift m cut b)
  have hmarg : (burstLaw m a : Measure Path).map (past (n + 1)) = U.map F :=
    Measure.map_map hp (measurable_burst m)
  dsimp only
  rw [hjoint, hmarg]
  intro B hB
  apply (hfull B hB).trans
  have h := overlap_probability n t m a
  change (bitsLaw a).real _ + (bitsLaw a).real _ ≤ _
  linarith

end LongTails.Proofs.PolynomialMixingBurst
