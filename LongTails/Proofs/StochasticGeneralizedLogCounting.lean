import LongTails.Proofs.StochasticGeneralizedRateTuning
import LongTails.Proofs.GeneralizedSelfNormalizedConvergence

open scoped BigOperators

namespace OracleTemplate.StochasticGeneralized

open LongTails.Setups.StochasticGeneralizedSmoothAndConvex

open GeneralizedAccelerated (Iterate coupling chargingSet chargeValue)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma run_count_self_normalized {L0 L1 R : ℝ} (hL0 : 0 < L0) (hL1 : 0 < L1) (hR : 0 ≤ R)
    (v h : ℕ → E → E) (s : Iterate E) (hA : 0 < s.A) (hG : 0 < s.guess)
    (hfirst : 16*(L0+L1*‖v 0 (coupling s)‖) ≤ s.guess) (n : ℕ)
    (hD : (∑ i ∈ Finset.range (n+1), dissipation L0 L1 (v i) (run L0 L1 v h s i)) ≤ 3*R^2) :
    (n : ℝ) ≤ 2*Real.log (1+32*Real.sqrt (s.guess*(run L0 L1 v h s (n+1)).A))+
      96*Real.sqrt (4*L0*(run L0 L1 v h s (n+1)).A)+
      4*Real.log (2*(run L0 L1 v h s (n+1)).A/s.A)+
      2048*(L1*R*Real.log (2*(run L0 L1 v h s (n+1)).A/s.A))^(2/3 : ℝ) := by
  classical
  let Q := chargingSet (runUp L0 L1 v h s) n
  let B := fun b : ℕ × ℕ => (run L0 L1 v h s (b.1+1)).A
  let G := fun b : ℕ × ℕ => (run L0 L1 v h s b.1).guess
  let M := fun b : ℕ × ℕ => 16*(L0+L1*‖v b.1 (coupling (run L0 L1 v h s b.1))‖)
  let rest := Q.filter (fun b => b.1 ≠ 0)
  let low := rest.filter (fun b => M b ≤ 32*L0)
  let high := rest.filter (fun b => ¬M b ≤ 32*L0)
  let Afinal := (run L0 L1 v h s (n+1)).A
  have hv (i : ℕ) := run_valid hL0 hL1.le v h s hA.le hG i
  have hbase (i : ℕ) : s.A ≤ (run L0 L1 v h s i).A :=
    run_weight_mono hL0 hL1.le v h s hA.le hG (Nat.zero_le i)
  have hAF : s.A ≤ Afinal := hbase _
  have hcharge := run_charging_bound hL0 hL1.le v h s hA.le hG hfirst n
  have hweights : (∑ b ∈ Q, (2 : ℝ)^b.2/Real.sqrt (G b)) ≤ 32*Real.sqrt Afinal := by
    simpa only [chargeValue, mul_one_div] using hcharge.1
  have hsubset (T : Finset (ℕ × ℕ)) (hT : T ⊆ Q) :
      (∑ b ∈ T, (2 : ℝ)^b.2/Real.sqrt (G b)) ≤ 32*Real.sqrt Afinal := by
    exact (Finset.sum_le_sum_of_subset_of_nonneg hT (fun b _ _ => by positivity)).trans hweights
  have hlQ : low ⊆ Q := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hhQ : high ⊆ Q := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hinj : Set.InjOn Prod.fst (Q : Set (ℕ × ℕ)) := by
    intro a ha b hb hab
    exact GeneralizedAccelerated.charging_unique_index _ n (List.mem_toFinset.mp ha)
      (List.mem_toFinset.mp hb) hab
  have hexception := exceptional_count_bound Q G hG hinj
    (fun b _ hb => by dsimp [G]; rw [hb]; rfl) hweights
  have hlow := GeneralizedAccelerated.low_count_sqrt_bound low G Prod.snd
    (show 0 ≤ 4*L0 by positivity) (fun b _ => (hv b.1).2)
    (fun b hb => by
      have hs := charging_selected_curvature L0 L1 v h s n b (hlQ hb)
        (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).2
      have hm := (Finset.mem_filter.mp hb).2
      change G b ≤ M b at hs
      linarith) (hsubset low hlQ)
  have henergy : (∑ b ∈ high, B b*G b) ≤ (512/3)*(8*(L1*R))^2 := by
    have he := charged_high_energy hL0 hL1 v h s hA.le hG n hD high hhQ
      (fun b hb => (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).2)
      (fun b hb => lt_of_not_ge (Finset.mem_filter.mp hb).2)
    change (∑ b ∈ high, B b*G b) ≤ _ at he
    nlinarith [sq_nonneg (L1*R)]
  have hprefix : ∀ b ∈ high,
      (∑ a ∈ high.filter (fun a => a.1 < b.1), (2 : ℝ)^a.2/Real.sqrt (G a)) ≤ 32*Real.sqrt (B b) := by
    intro b hb
    have hsub : high.filter (fun a => a.1 < b.1) ⊆ Q.filter (fun a => a.1 < b.1) := by
      intro a ha
      exact Finset.mem_filter.mpr ⟨hhQ (Finset.mem_filter.mp ha).1, (Finset.mem_filter.mp ha).2⟩
    have hs := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun a => (2 : ℝ)^a.2/Real.sqrt (G a)) hsub (fun a _ _ => by positivity)
    have hp := hcharge.2 b (hhQ hb)
    simp only [chargeValue, mul_one_div] at hp
    exact hs.trans hp
  let D := Real.log (2*Afinal/s.A)
  have hDpos : 0 ≤ D := by
    apply Real.log_nonneg
    apply (le_div_iff₀ hA).mpr
    linarith
  have hh := GeneralizedAccelerated.high_count_self_normalized high Prod.fst B G Prod.snd hA hAF
    (fun b _ => hbase _) (fun b _ => (hv b.1).2) (by positivity)
    (hinj.mono hhQ) henergy (hsubset high hhQ) hprefix
  have hr := GeneralizedAccelerated.high_root_simplify (show 0 ≤ 8*(L1*R) by positivity) hDpos
  change (∑ b ∈ high, (b.2 : ℝ)) ≤ 4*D+64*(((512/3)*(8*(L1*R))^2)*D^2)^(1/3 : ℝ) at hh
  have he : (8*(L1*R)*D)^(2/3 : ℝ) = 4*(L1*R*D)^(2/3 : ℝ) := by
    rw [mul_assoc, eight_power_two_thirds (by positivity)]
  change 64*(((512/3)*(8*(L1*R))^2)*D^2)^(1/3 : ℝ) ≤ 512*(8*(L1*R)*D)^(2/3 : ℝ) at hr
  rw [he] at hr
  have hhigh : (∑ b ∈ high, (b.2 : ℝ)) ≤ 4*D+2048*(L1*R*D)^(2/3 : ℝ) := by linarith
  have hcount : (∑ b ∈ Q, (b.2 : ℝ)) = n := by
    exact_mod_cast GeneralizedAccelerated.charging_sum_count (runUp L0 L1 v h s) n
  have hsplit : (∑ b ∈ low, (b.2 : ℝ))+(∑ b ∈ high, (b.2 : ℝ)) = ∑ b ∈ rest, (b.2 : ℝ) :=
    Finset.sum_filter_add_sum_filter_not rest _ _
  have hsplit0 : (∑ b ∈ Q.filter (fun b => b.1=0), (b.2 : ℝ))+(∑ b ∈ rest, (b.2 : ℝ)) = n := by
    rw [← hcount]
    exact Finset.sum_filter_add_sum_filter_not Q _ _
  change (n : ℝ) ≤ 2*Real.log (1+32*Real.sqrt (s.guess*Afinal))+
    96*Real.sqrt (4*L0*Afinal)+4*D+2048*(L1*R*D)^(2/3 : ℝ)
  linarith

lemma high_self_normalized_simplify {a r A0 A : ℝ} (ha : 0 < a) (hr : 1 ≤ r)
    (hA0 : 0 < A0) (hA : A0 ≤ A) (hbound : 2*A/A0 ≤ 64*r) :
    4*Real.log (2*A/A0)+2048*(a*Real.log (2*A/A0))^(2/3 : ℝ) ≤
      12*Real.log (4+4*r)+6144*(a*Real.log (4+4*r))^(2/3 : ℝ) := by
  have ht := ratio_tuning ha hr
  have hlog := Real.log_le_log (show 0 < 2*A/A0 by have := hA0.trans_le hA; positivity) hbound
  have hrp : 0 < r := by linarith
  rw [Real.log_mul (by norm_num) hrp.ne', show (64 : ℝ)=2^6 by norm_num, Real.log_pow] at hlog
  have h8 := Real.log_le_log (by norm_num : (0 : ℝ)<8) (show 8 ≤ 4+4*r by linarith)
  rw [show (8 : ℝ)=2^3 by norm_num, Real.log_pow] at h8
  norm_num only [Nat.cast_ofNat] at h8 hlog
  have hlog' : Real.log (2*A/A0) ≤ 3*Real.log (4+4*r) := by linarith [ht.2.2.2]
  have hD : 0 ≤ Real.log (2*A/A0) := Real.log_nonneg ((le_div_iff₀ hA0).mpr (by linarith))
  have hL : 0 ≤ Real.log (4+4*r) := by linarith [ht.2.2.1]
  have hm : a*Real.log (2*A/A0) ≤ 3*(a*Real.log (4+4*r)) := by nlinarith only [hlog', ha]
  have hp := Real.rpow_le_rpow (mul_nonneg ha.le hD) hm (by norm_num : (0 : ℝ) ≤ 2/3)
  rw [Real.mul_rpow (by norm_num) (mul_nonneg ha.le hL)] at hp
  have hc := Real.rpow_le_self_of_one_le (by norm_num : (1 : ℝ) ≤ 3) (by norm_num : (2/3 : ℝ) ≤ 1)
  have hh := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (mul_nonneg ha.le hL) (2/3 : ℝ))
  nlinarith only [hlog', hp, hh]

end OracleTemplate.StochasticGeneralized
