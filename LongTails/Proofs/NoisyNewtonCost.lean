import LongTails.Proofs.NoisyNewtonCounting

namespace LongTails.Proofs.NoisyNewtonCost

open LongTails.Setups.StochasticLocalHessianConvex
open LongTails.Algorithms.NoisyDampedNewton
open LongTails.Proofs.NoisyNewtonProcess
open LongTails.Proofs.NoisyNewtonCounting
open LongTails.Proofs.NoisyNewtonTuning
open LongTails.Proofs.NoisyMsAccounting
open OracleTemplate.GeneralizedAccelerated (Iterate tentativeWeight tentativeWeight_pos)

def ModelState {E : Type*} : State E → Prop
  | .model _ _ _ => True
  | _ => False

noncomputable def cycleIncrement (p : Params) (S : ℕ → State (Point p.d)) (i : ℕ) : ℝ := by
  classical
  exact if ModelState (S (3 * i)) then actualWeight (cycleTrial S i) else 0

noncomputable def cycleProposed (p : Params) (S : ℕ → State (Point p.d)) (i : ℕ) : ℝ := by
  classical
  exact if ModelState (S (3 * i)) then tentativeWeight (cycleIterate S i) else 0

lemma cycle_ledger (p : Params) (hp : spec.valid p)
    (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (S : ℕ → State (Point p.d))
    (N : ℕ) (hstep : ∀ i < 3 * N, PhaseStep p g H (S i) (S (i + 1)))
    (h₀ : (∃ it, S 0 = .model it 0 (fun _ => 0)) ∨ ∃ it, S 0 = .done it)
    (hbounds : ∀ i ≤ 3 * N, StateBounds p (S i)) (i : ℕ) (hi : i < N) :
    (cycleIterate S (i + 1)).A = (cycleIterate S i).A + cycleIncrement p S i ∧
      0 ≤ cycleIncrement p S i ∧
      cycleProposed p S i ≤ 4 * (tentativeWeight (cycleIterate S i) -
        tentativeWeight (cycleIterate S (i + 1))) + 13 * cycleIncrement p S i := by
  classical
  rcases phasePath_cycle_boundary p g H S N hstep h₀ i hi.le with ⟨it, hit⟩ | ⟨it, hit⟩
  · have h₁ := hstep (3 * i) (by omega)
    rw [hit] at h₁
    obtain ⟨v, w, t, _, _, hprev, hcorr, hout⟩ := phaseStep_cycle p g H it _ _ _ h₁
      (hstep (3 * i + 1) (by omega)) (hstep (3 * i + 2) (by omega))
    have hit₀ : cycleIterate S i = it := by simp only [cycleIterate, hit, baseIterate]
    have ht : cycleTrial S i = t := by simp only [cycleTrial, hcorr, stateTrial]
    have hit₁ : cycleIterate S (i + 1) = finish (curvatureFloor p) t w := by
      unfold cycleIterate
      rw [show 3 * (i + 1) = 3 * i + 3 by omega, hout, baseIterate_resume]
    have hb := hbounds (3 * i + 2) (by omega)
    rw [hcorr] at hb
    have hW := target_pos p hp
    have hf : 0 < curvatureFloor p := by unfold curvatureFloor; positivity
    have hη : 0 < t.previous.guess := hf.trans_le hb.1.2.2
    have ha := (actualWeight_bounds t hη hb.2.2).1.le
    have hcases := finish_weight_cases t hb.1.1.le hη hb.2.2 (curvatureFloor p) w
    have hc := proposal_charge _ _ _ ha hcases
    simp only [cycleIncrement, cycleProposed, hit, ModelState, ite_true, hit₀, hit₁, ht]
    refine ⟨?_, ha, ?_⟩
    · change t.previous.A + actualWeight t = it.A + actualWeight t
      rw [hprev]
    · simpa only [hprev] using hc
  · have hnext : S (3 * (i + 1)) = .done it :=
      phasePath_done p g H S (3 * (i + 1)) (3 * i)
        (fun j hj => hstep j (by omega)) (by omega) it hit
    simp only [cycleIncrement, cycleProposed, hit, ModelState, ite_false,
      cycleIterate, hnext, baseIterate, add_zero, sub_self, mul_zero, le_refl, and_self]

lemma cycle_sums (p : Params) (hp : spec.valid p)
    (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (S : ℕ → State (Point p.d))
    (N : ℕ) (hstep : ∀ i < 3 * N, PhaseStep p g H (S i) (S (i + 1)))
    (h₀ : (∃ it, S 0 = .model it 0 (fun _ => 0)) ∨ ∃ it, S 0 = .done it)
    (hbounds : ∀ i ≤ 3 * N, StateBounds p (S i)) :
    (∑ i ∈ Finset.range N, cycleIncrement p S i) = (cycleIterate S N).A - (cycleIterate S 0).A ∧
      (∑ i ∈ Finset.range N, cycleProposed p S i) ≤
        4 * tentativeWeight (cycleIterate S 0) + 13 * ((cycleIterate S N).A - (cycleIterate S 0).A) := by
  have hledger := cycle_ledger p hp g H S N hstep h₀ hbounds
  have hs : ∀ k ≤ N, (∑ i ∈ Finset.range k, cycleIncrement p S i) =
      (cycleIterate S k).A - (cycleIterate S 0).A := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih (by omega), (hledger k (by omega)).1]
      ring
  have hb := (hbounds (3 * N) le_rfl).1
  have hW := target_pos p hp
  have hf : 0 < curvatureFloor p := by unfold curvatureFloor; positivity
  have hη : 0 < (cycleIterate S N).guess := hf.trans_le hb.2.2
  have hh := total_charges (fun i => tentativeWeight (cycleIterate S i))
    (cycleProposed p S) (cycleIncrement p S) N (tentativeWeight_pos _ hη).le
    (fun i hi => (hledger i hi).2.2)
  rw [hs N le_rfl] at hh
  exact ⟨hs N le_rfl, hh⟩

lemma cycle_sum_bounds (p : Params) (hp : spec.valid p)
    (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (S : ℕ → State (Point p.d))
    (N : ℕ) (hstep : ∀ i < 3 * N, PhaseStep p g H (S i) (S (i + 1)))
    (h₀ : (∃ it, S 0 = .model it 0 (fun _ => 0)) ∨ ∃ it, S 0 = .done it)
    (hinit : cycleIterate S 0 = initialIterate p)
    (hbounds : ∀ i ≤ 3 * N, StateBounds p (S i)) :
    (∑ i ∈ Finset.range N, cycleIncrement p S i) ≤ 48 * p.R ^ 2 / p.ε ∧
      (∑ i ∈ Finset.range N, cycleProposed p S i) ≤ 752 * p.R ^ 2 / p.ε := by
  have hs := cycle_sums p hp g H S N hstep h₀ hbounds
  have hb := (hbounds (3 * N) le_rfl).1
  have hcap : (cycleIterate S N).A ≤ 3 * target p / 2 := hb.2.1
  have hinitpos : 0 < (cycleIterate S 0).A := by rw [hinit]; exact (initial_properties p hp).1
  have hproposal : tentativeWeight (cycleIterate S 0) ≤ target p := by
    rw [hinit]
    have hi := initial_properties p hp
    have hW := target_pos p hp
    apply tentativeWeight_cap (initialIterate p) (target p) hW hi.1.le
    · linarith [hi.2.1]
    · exact le_rfl
  have ha : (∑ i ∈ Finset.range N, cycleIncrement p S i) ≤ 3 * target p / 2 := by
    linarith [hs.1]
  have hm : (∑ i ∈ Finset.range N, cycleProposed p S i) ≤ 47 * target p / 2 := by
    linarith [hs.2]
  constructor
  · convert ha using 1
    unfold target
    ring
  · convert hm using 1
    unfold target
    ring

lemma max_one_ceil_bound (x : ℝ) (hx : 0 ≤ x) : ((max 1 ⌈x⌉₊ : ℕ) : ℝ) ≤ x + 1 := by
  rw [Nat.cast_max, Nat.cast_one]
  exact max_le (by linarith) (Nat.ceil_lt_add_one hx).le

lemma modelGroups_bound (p : Params) (hp : spec.valid p) :
    (modelGroups p : ℝ) ≤ 17 * confidence p := by
  have hl := confidence_lower p hp
  have hh := max_one_ceil_bound (16 * confidence p) (by positivity)
  change ((max 1 ⌈16 * confidence p⌉₊ : ℕ) : ℝ) ≤ _
  linarith

lemma modelSize_bound (p : Params) (hp : spec.valid p) (a : ℝ) (ha : 0 < a) :
    (modelSize p a : ℝ) ≤ 1 + 154618822656 * p.σ ^ 2 * confidence p ^ 2 * a / p.ε := by
  have hl := confidence_lower p hp
  have hε := hp.2.2.2.2.2.2.2.1
  have hB := modelRadius_pos p hp a ha
  have hs := modelRadius_half_square p hp a ha
  have hs' : modelRadius p a ^ 2 = 4 * (p.ε / (1073741824 * confidence p ^ 2 * a)) := by
    nlinarith only [hs]
  have he : 576 * p.σ ^ 2 / modelRadius p a ^ 2 =
      154618822656 * p.σ ^ 2 * confidence p ^ 2 * a / p.ε := by
    rw [hs']
    field_simp
    ring
  have hh := max_one_ceil_bound (576 * p.σ ^ 2 / modelRadius p a ^ 2) (by positivity)
  change ((max 1 ⌈576 * p.σ ^ 2 / modelRadius p a ^ 2⌉₊ : ℕ) : ℝ) ≤ _
  rw [he] at hh ⊢
  linarith

lemma modelCost_bound (p : Params) (hp : spec.valid p) (a : ℝ) (ha : 0 < a) :
    (modelCost p a : ℝ) ≤ 17 * confidence p +
      4398046511104 * p.σ ^ 2 * confidence p ^ 3 * a / p.ε := by
  have hl := confidence_lower p hp
  have hε := hp.2.2.2.2.2.2.2.1
  have hg := modelGroups_bound p hp
  have hs := modelSize_bound p hp a ha
  have hm := mul_le_mul hg hs (Nat.cast_nonneg (modelSize p a)) (by positivity : 0 ≤ 17 * confidence p)
  have hx : 0 ≤ p.σ ^ 2 * confidence p ^ 3 * a / p.ε := by positivity
  change ((modelGroups p * modelSize p a : ℕ) : ℝ) ≤ _
  rw [Nat.cast_mul]
  have he : 17 * confidence p * (1 + 154618822656 * p.σ ^ 2 * confidence p ^ 2 * a / p.ε) =
      17 * confidence p + 2628519985152 * (p.σ ^ 2 * confidence p ^ 3 * a / p.ε) := by ring
  rw [he] at hm
  have hm₂ := mul_le_mul_of_nonneg_right
    (show (2628519985152 : ℝ) ≤ 4398046511104 by norm_num) hx
  calc
    _ ≤ 17 * confidence p + 2628519985152 * (p.σ ^ 2 * confidence p ^ 3 * a / p.ε) := hm
    _ ≤ 17 * confidence p + 4398046511104 * (p.σ ^ 2 * confidence p ^ 3 * a / p.ε) :=
      add_le_add (le_refl _) hm₂
    _ = _ := by ring

lemma updateSize_bound (p : Params) (hp : spec.valid p) (a : ℝ) (ha : 0 ≤ a) :
    (updateSize p a : ℝ) ≤ 1 + 16777216 * p.σ ^ 2 * a * confidence p ^ 2 / p.ε := by
  have hε := hp.2.2.2.2.2.2.2.1
  have hh := max_one_ceil_bound (16777216 * p.σ ^ 2 * a * confidence p ^ 2 / p.ε) (by positivity)
  change ((max 1 ⌈16777216 * p.σ ^ 2 * a * confidence p ^ 2 / p.ε⌉₊ : ℕ) : ℝ) ≤ _
  linarith

noncomputable def phaseChannelCost (p : Params) (ch : Fin 2) (s : State (Point p.d)) : ℕ :=
  if ((algorithm p).query s).1 = ch then phaseCost p s else 0

noncomputable def cycleChannelCost (p : Params) (ch : Fin 2) (S : ℕ → State (Point p.d)) (i : ℕ) : ℕ := by
  classical
  exact if ModelState (S (3 * i)) then
    if ch = 0 then modelCost p (tentativeWeight (cycleIterate S i)) + updateSize p (actualWeight (cycleTrial S i))
    else 1
  else 0

lemma phaseTriple_cost (p : Params) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (S : ℕ → State (Point p.d))
    (N : ℕ) (hstep : ∀ i < 3 * N, PhaseStep p g H (S i) (S (i + 1)))
    (h₀ : (∃ it, S 0 = .model it 0 (fun _ => 0)) ∨ ∃ it, S 0 = .done it)
    (ch : Fin 2) (i : ℕ) (hi : i < N) :
    phaseChannelCost p ch (S (3 * i)) + phaseChannelCost p ch (S (3 * i + 1)) +
      phaseChannelCost p ch (S (3 * i + 2)) = cycleChannelCost p ch S i := by
  classical
  rcases phasePath_cycle_boundary p g H S N hstep h₀ i hi.le with ⟨it, hit⟩ | ⟨it, hit⟩
  · have h₁ := hstep (3 * i) (by omega)
    rw [hit] at h₁
    obtain ⟨v, w, t, hhess, _, _, hcorr, _⟩ := phaseStep_cycle p g H it _ _ _ h₁
      (hstep (3 * i + 1) (by omega)) (hstep (3 * i + 2) (by omega))
    fin_cases ch <;> simp [phaseChannelCost, cycleChannelCost, hit, hhess, hcorr,
      ModelState, phaseCost, algorithm, cycleIterate, cycleTrial, stateTrial, baseIterate]
  · have h₁ : S (3 * i + 1) = .done it := phasePath_done p g H S (3 * i + 1) (3 * i)
      (fun j hj => hstep j (by omega)) (by omega) it hit
    have h₂ : S (3 * i + 2) = .done it := phasePath_done p g H S (3 * i + 2) (3 * i)
      (fun j hj => hstep j (by omega)) (by omega) it hit
    simp [phaseChannelCost, cycleChannelCost, hit, h₁, h₂, ModelState, phaseCost]

lemma sum_triples (c : ℕ → ℕ) (N : ℕ) :
    ∑ j ∈ Finset.range (3 * N), c j =
      ∑ i ∈ Finset.range N, (c (3 * i) + c (3 * i + 1) + c (3 * i + 2)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.mul_succ]
    simp only [Finset.sum_range_succ]
    rw [ih]
    omega

lemma phase_channel_sum (p : Params) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (S : ℕ → State (Point p.d))
    (N : ℕ) (hstep : ∀ i < 3 * N, PhaseStep p g H (S i) (S (i + 1)))
    (h₀ : (∃ it, S 0 = .model it 0 (fun _ => 0)) ∨ ∃ it, S 0 = .done it)
    (ch : Fin 2) :
    ∑ j ∈ Finset.range (3 * N), phaseChannelCost p ch (S j) =
      ∑ i ∈ Finset.range N, cycleChannelCost p ch S i := by
  rw [sum_triples]
  apply Finset.sum_congr rfl
  intro i hi
  exact phaseTriple_cost p g H S N hstep h₀ ch i (Finset.mem_range.mp hi)

lemma cycle_hessian_cost_le (p : Params) (S : ℕ → State (Point p.d)) (i : ℕ) :
    cycleChannelCost p 1 S i ≤ 1 := by
  unfold cycleChannelCost
  split_ifs <;> norm_num at *

lemma phase_hessian_cost_le (p : Params) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (S : ℕ → State (Point p.d))
    (N : ℕ) (hstep : ∀ i < 3 * N, PhaseStep p g H (S i) (S (i + 1)))
    (h₀ : (∃ it, S 0 = .model it 0 (fun _ => 0)) ∨ ∃ it, S 0 = .done it) :
    ∑ j ∈ Finset.range (3 * N), phaseChannelCost p 1 (S j) ≤ N := by
  rw [phase_channel_sum p g H S N hstep h₀ 1]
  calc
    _ ≤ ∑ i ∈ Finset.range N, 1 := Finset.sum_le_sum (fun i _ => cycle_hessian_cost_le p S i)
    _ = _ := by simp

lemma cycle_gradient_cost_bound (p : Params) (hp : spec.valid p)
    (S : ℕ → State (Point p.d)) (i : ℕ)
    (hb : IterateBounds p (cycleIterate S i)) (ha : 0 ≤ cycleIncrement p S i) :
    (cycleChannelCost p 0 S i : ℝ) ≤ 17 * confidence p + 1 +
      (4398046511104 * p.σ ^ 2 * confidence p ^ 3 / p.ε) * cycleProposed p S i +
      (16777216 * p.σ ^ 2 * confidence p ^ 2 / p.ε) * cycleIncrement p S i := by
  classical
  have hl := confidence_lower p hp
  by_cases hm : ModelState (S (3 * i))
  · have hW := target_pos p hp
    have hf : 0 < curvatureFloor p := by unfold curvatureFloor; positivity
    have hη := hf.trans_le hb.2.2
    have hq := tentativeWeight_pos (cycleIterate S i) hη
    have ha' : 0 ≤ actualWeight (cycleTrial S i) := by
      simpa only [cycleIncrement, ite_eq_left hm] using ha
    have hb₁ := modelCost_bound p hp _ hq
    have hb₂ := updateSize_bound p hp _ ha'
    simp only [cycleChannelCost, cycleProposed, cycleIncrement, ite_eq_left hm,
      ite_true, Nat.cast_add]
    convert add_le_add hb₁ hb₂ using 1
    ring
  · simp only [cycleChannelCost, cycleProposed, cycleIncrement, ite_eq_right hm,
      Nat.cast_zero, mul_zero, add_zero]
    linarith

lemma phase_gradient_cost_bound (p : Params) (hp : spec.valid p)
    (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (S : ℕ → State (Point p.d))
    (N : ℕ) (hstep : ∀ i < 3 * N, PhaseStep p g H (S i) (S (i + 1)))
    (h₀ : (∃ it, S 0 = .model it 0 (fun _ => 0)) ∨ ∃ it, S 0 = .done it)
    (hinit : cycleIterate S 0 = initialIterate p)
    (hbounds : ∀ i ≤ 3 * N, StateBounds p (S i)) :
    (∑ j ∈ Finset.range (3 * N), phaseChannelCost p 0 (S j) : ℕ) ≤
      (N : ℝ) * (17 * confidence p + 1) +
        4398046511104 * p.σ ^ 2 * confidence p ^ 3 / p.ε * (752 * p.R ^ 2 / p.ε) +
        16777216 * p.σ ^ 2 * confidence p ^ 2 / p.ε * (48 * p.R ^ 2 / p.ε) := by
  have hl := confidence_lower p hp
  have hε := hp.2.2.2.2.2.2.2.1
  have hs := cycle_sum_bounds p hp g H S N hstep h₀ hinit hbounds
  have hledger := cycle_ledger p hp g H S N hstep h₀ hbounds
  have hh := Finset.sum_le_sum (fun i (hi : i ∈ Finset.range N) =>
    cycle_gradient_cost_bound p hp S i (hbounds (3 * i) (by have := Finset.mem_range.mp hi; omega)).1
      (hledger i (Finset.mem_range.mp hi)).2.1)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    ← Finset.mul_sum] at hh
  have hm₁ := mul_le_mul_of_nonneg_left hs.2
    (show 0 ≤ 4398046511104 * p.σ ^ 2 * confidence p ^ 3 / p.ε by positivity)
  have hm₂ := mul_le_mul_of_nonneg_left hs.1
    (show 0 ≤ 16777216 * p.σ ^ 2 * confidence p ^ 2 / p.ε by positivity)
  rw [phase_channel_sum p g H S N hstep h₀ 0, Nat.cast_sum]
  linarith

lemma horizon_upper (p : Params) (hp : spec.valid p) :
    (horizon p : ℝ) ≤ 2147483648 * shape p * confidence p ^ 2 := by
  have hs := (shape_bounds p hp).1
  have hl := confidence_lower p hp
  have hℓ : 1 ≤ confidence p ^ 2 := by nlinarith only [hl, sq_nonneg (confidence p - 1)]
  have hprod : 1 ≤ shape p * confidence p ^ 2 := by
    nlinarith only [hs, hℓ, mul_nonneg (by linarith : 0 ≤ shape p - 1)
      (by linarith : 0 ≤ confidence p ^ 2 - 1)]
  have hh := (Nat.ceil_lt_add_one (by positivity : 0 ≤ 1073741824 * shape p * confidence p ^ 2)).le
  change (⌈1073741824 * shape p * confidence p ^ 2⌉₊ : ℝ) ≤ _
  linarith

lemma gradient_scalar_bound (p : Params) (hp : spec.valid p) (n : ℝ)
    (hn : n ≤ 2147483648 * shape p * confidence p ^ 2) :
    n * (17 * confidence p + 1) +
      4398046511104 * p.σ ^ 2 * confidence p ^ 3 / p.ε * (752 * p.R ^ 2 / p.ε) +
      16777216 * p.σ ^ 2 * confidence p ^ 2 / p.ε * (48 * p.R ^ 2 / p.ε) ≤
        36028797018963968 * (shape p + p.σ ^ 2 * p.R ^ 2 / p.ε ^ 2) * confidence p ^ 3 := by
  have hs : 0 ≤ shape p := le_trans (by norm_num) (shape_bounds p hp).1
  have hl := confidence_lower p hp
  have hε := hp.2.2.2.2.2.2.2.1
  have hy : 0 ≤ p.σ ^ 2 * p.R ^ 2 / p.ε ^ 2 := by positivity
  have hℓ : confidence p ^ 2 ≤ confidence p ^ 3 := by
    nlinarith only [mul_nonneg (sq_nonneg (confidence p))
      (by linarith : 0 ≤ confidence p - 1)]
  have hinit : n * (17 * confidence p + 1) ≤ 68719476736 * shape p * confidence p ^ 3 := by
    have h₁ := mul_le_mul_of_nonneg_right hn (by positivity : 0 ≤ 17 * confidence p + 1)
    have h₂ := mul_le_mul_of_nonneg_left
      (show 17 * confidence p + 1 ≤ 32 * confidence p by linarith)
      (show 0 ≤ 2147483648 * shape p * confidence p ^ 2 by positivity)
    nlinarith only [h₁, h₂]
  have hnoise := mul_le_mul_of_nonneg_left hℓ hy
  have hshape : 0 ≤ shape p * confidence p ^ 3 := by positivity
  have hnoise₃ : 0 ≤ (p.σ ^ 2 * p.R ^ 2 / p.ε ^ 2) * confidence p ^ 3 := by positivity
  have he₁ : 4398046511104 * p.σ ^ 2 * confidence p ^ 3 / p.ε * (752 * p.R ^ 2 / p.ε) =
      (4398046511104 * 752) * ((p.σ ^ 2 * p.R ^ 2 / p.ε ^ 2) * confidence p ^ 3) := by ring
  have he₂ : 16777216 * p.σ ^ 2 * confidence p ^ 2 / p.ε * (48 * p.R ^ 2 / p.ε) =
      805306368 * ((p.σ ^ 2 * p.R ^ 2 / p.ε ^ 2) * confidence p ^ 2) := by ring
  rw [he₁, he₂]
  nlinarith only [hinit, hnoise, hshape, hnoise₃]

open LongTails.Proofs.NoisyNewtonExecution
open OracleTemplate.StochasticGeneralized (blockTrace blockCalls blockCalls_succ)

lemma oracleCount_add (p : Params) (S : ℕ → State (Point p.d)) (ch : Fin 2) (n m : ℕ) :
    oracleCount p S ch (n + m) = oracleCount p S ch n + oracleCount p (fun i => S (n + i)) ch m := by
  classical
  exact Finset.sum_range_add _ _ _

lemma rawAdvance_phase_channel (p : Params) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (ξ : ℕ → p.Ω)
    (s : State (Point p.d)) (hs : PhaseStart s) (call j : ℕ) (hj : j < phaseCost p s) :
    ((algorithm p).query (rawAdvance p g H ξ j call s)).1 = ((algorithm p).query s).1 := by
  cases s with
  | model it n v =>
    obtain ⟨rfl, rfl⟩ := hs
    rw [rawAdvance_model_prefix p g H ξ it call j hj]
    rfl
  | hessian it v =>
    have hz : j = 0 := by change j < 1 at hj; omega
    subst j
    rfl
  | correction t n v =>
    obtain ⟨rfl, rfl⟩ := hs
    rw [rawAdvance_correction_prefix p g H ξ t call j hj]
    rfl
  | done it => change j < 0 at hj; omega

lemma rawAdvance_phase_count (p : Params) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (ξ : ℕ → p.Ω)
    (s : State (Point p.d)) (hs : PhaseStart s) (call : ℕ) (ch : Fin 2) :
    oracleCount p (fun j => rawAdvance p g H ξ j call s) ch (phaseCost p s) = phaseChannelCost p ch s := by
  classical
  unfold oracleCount
  calc
    _ = ∑ j ∈ Finset.range (phaseCost p s), (if ((algorithm p).query s).1 = ch then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [rawAdvance_phase_channel p g H ξ s hs call j (Finset.mem_range.mp hj)]
    _ = _ := by by_cases h : ((algorithm p).query s).1 = ch <;> simp [phaseChannelCost, h]

lemma blockTrace_oracleCount (p : Params) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (ξ : ℕ → p.Ω)
    (s : State (Point p.d)) (hs : PhaseStart s) (n : ℕ) (ch : Fin 2) :
    oracleCount p (fun j => rawAdvance p g H ξ j 0 s) ch
      (blockCalls (phaseCost p) (phaseNext p g H) s ξ n) =
      ∑ i ∈ Finset.range n, phaseChannelCost p ch (blockTrace (phaseCost p) (phaseNext p g H) s ξ i).1 := by
  induction n with
  | zero => simp [oracleCount, blockCalls]
  | succ n ih =>
    rw [blockCalls_succ, oracleCount_add, ih, Finset.sum_range_succ]
    congr 1
    have he : (fun j => rawAdvance p g H ξ
        (blockCalls (phaseCost p) (phaseNext p g H) s ξ n + j) 0 s) =
        (fun j => rawAdvance p g H ξ j (blockCalls (phaseCost p) (phaseNext p g H) s ξ n)
          (blockTrace (phaseCost p) (phaseNext p g H) s ξ n).1) := by
      funext j
      rw [rawAdvance_add, Nat.zero_add, ← blockTrace_eq_rawAdvance p g H ξ s hs n]
    rw [he]
    exact rawAdvance_phase_count p g H ξ _ (blockTrace_start p g H ξ s hs n) _ ch

lemma phase_oracle_rate (p : Params) (hp : spec.valid p)
    (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (S : ℕ → State (Point p.d))
    (hstep : ∀ i < 3 * horizon p, PhaseStep p g H (S i) (S (i + 1)))
    (h₀ : (∃ it, S 0 = .model it 0 (fun _ => 0)) ∨ ∃ it, S 0 = .done it)
    (hinit : cycleIterate S 0 = initialIterate p)
    (hbounds : ∀ i ≤ 3 * horizon p, StateBounds p (S i)) (ch : Fin 2) :
    (∑ j ∈ Finset.range (3 * horizon p), phaseChannelCost p ch (S j) : ℕ) ≤
      36028797018963968 * (shape p + if ch = 0 then p.σ ^ 2 * p.R ^ 2 / p.ε ^ 2 else 0) *
        confidence p ^ 3 := by
  fin_cases ch
  · have hh := (phase_gradient_cost_bound p hp g H S (horizon p) hstep h₀ hinit hbounds).trans
      (gradient_scalar_bound p hp _ (horizon_upper p hp))
    simpa using hh
  · have hh : ((∑ j ∈ Finset.range (3 * horizon p), phaseChannelCost p 1 (S j) : ℕ) : ℝ) ≤
        (horizon p : ℝ) := by
      exact_mod_cast phase_hessian_cost_le p g H S (horizon p) hstep h₀
    have hN := horizon_upper p hp
    have hs : 0 ≤ shape p := le_trans (by norm_num) (shape_bounds p hp).1
    have hl := confidence_lower p hp
    have hℓ : confidence p ^ 2 ≤ confidence p ^ 3 := by
      nlinarith only [mul_nonneg (sq_nonneg (confidence p))
        (by linarith : 0 ≤ confidence p - 1)]
    have hm := mul_le_mul_of_nonneg_left hℓ hs
    have hn : 0 ≤ shape p * confidence p ^ 3 := by positivity
    norm_num
    rw [Nat.cast_sum] at hh
    nlinarith only [hh, hN, hm, hn]

lemma oracle_rate_log_bound (p : Params) (hp : spec.valid p) (ch : Fin 2) :
    36028797018963968 * (shape p + if ch = 0 then p.σ ^ 2 * p.R ^ 2 / p.ε ^ 2 else 0) *
      confidence p ^ 3 ≤
    1208925819614629174706176 * (shape p + if ch = 0 then p.σ ^ 2 * p.R ^ 2 / p.ε ^ 2 else 0) *
      Real.log (scaleBase p) ^ 3 := by
  have hs : 0 ≤ shape p := le_trans (by norm_num) (shape_bounds p hp).1
  have hX : 1 ≤ scaleBase p := le_trans (by norm_num) (scaleBase_bounds p hp).1
  have hl := Real.log_nonneg hX
  have hy : 0 ≤ (if ch = 0 then p.σ ^ 2 * p.R ^ 2 / p.ε ^ 2 else 0 : ℝ) := by
    split_ifs <;> positivity
  have hh := mul_nonneg (add_nonneg hs hy) (pow_nonneg hl 3)
  unfold confidence
  nlinarith only [hh]

end LongTails.Proofs.NoisyNewtonCost
