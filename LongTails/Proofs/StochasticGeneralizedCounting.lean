import LongTails.Proofs.StochasticGeneralizedDynamics
import LongTails.Proofs.GeneralizedConvergence

open scoped BigOperators

namespace OracleTemplate.StochasticGeneralized

open LongTails.Setups.StochasticGeneralizedSmoothAndConvex

open GeneralizedAccelerated (Iterate tentativeWeight coupling chargingSet chargeValue downMass
  chargeTotal charging charging_total_le charging_prefix_bound charging_sum charging_sum_prefix)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma step_guess (L0 L1 : ℝ) (v h : E → E) (s : Iterate E) :
    (step L0 L1 v h s).guess =
      if 16*(L0+L1*‖v (coupling s)‖) ≤ s.guess then s.guess/16 else 16*s.guess := by
  simp only [step, finish, prepare, max_le_iff, le_refl, true_and]

omit [CompleteSpace E] in
lemma step_inverse_sqrt_guess (L0 L1 : ℝ) (v h : E → E) (s : Iterate E) (hG : 0 < s.guess) :
    1/Real.sqrt (step L0 L1 v h s).guess =
      if 16*(L0+L1*‖v (coupling s)‖) ≤ s.guess then 4*(1/Real.sqrt s.guess)
      else (1/Real.sqrt s.guess)/4 := by
  rw [step_guess]
  split_ifs <;> simp [Real.sqrt_div, Real.sqrt_mul, hG.le]
  <;> norm_num <;> ring

omit [CompleteSpace E] in
lemma step_down_growth (L0 L1 : ℝ) (v h : E → E) (s : Iterate E)
    (hA : 0 ≤ s.A) (hG : 0 < s.guess) (hd : 16*(L0+L1*‖v (coupling s)‖) ≤ s.guess) :
    1/(2*Real.sqrt s.guess) ≤ Real.sqrt (step L0 L1 v h s).A-Real.sqrt s.A := by
  have he : (step L0 L1 v h s).A = s.A+tentativeWeight s := by
    simp [step, finish, prepare, max_eq_left hd, hG.ne']
  rw [he]
  exact GeneralizedAccelerated.down_growth hG hA
    (GeneralizedAccelerated.tentativeWeight_pos s hG)
    (GeneralizedAccelerated.tentativeWeight_equation s hA hG)

omit [CompleteSpace E] in
lemma down_sum_le_sqrt {L0 L1 : ℝ} (hL0 : 0 < L0) (hL1 : 0 ≤ L1)
    (v h : ℕ → E → E) (s : Iterate E) (hA : 0 ≤ s.A) (hG : 0 < s.guess) (N : ℕ) :
    (∑ i ∈ Finset.range N,
      if 16*(L0+L1*‖v i (coupling (run L0 L1 v h s i))‖) ≤ (run L0 L1 v h s i).guess
      then 1/Real.sqrt (run L0 L1 v h s i).guess else 0) ≤ 2*Real.sqrt (run L0 L1 v h s N).A := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hv := run_valid hL0 hL1 v h s hA hG n
    split_ifs with hd
    · have hs := step_down_growth L0 L1 (v n) (h n) (run L0 L1 v h s n) hv.1 hv.2 hd
      have he : 1/(2*Real.sqrt (run L0 L1 v h s n).guess) =
          (1/Real.sqrt (run L0 L1 v h s n).guess)/2 := by ring
      rw [he] at hs
      change _ ≤ 2*Real.sqrt (step L0 L1 (v n) (h n) (run L0 L1 v h s n)).A
      linarith
    · have hs := Real.sqrt_le_sqrt (step_weights hL0 hL1 (v n) (h n) (run L0 L1 v h s n) hv.2).1.le
      change _ ≤ 2*Real.sqrt (step L0 L1 (v n) (h n) (run L0 L1 v h s n)).A
      linarith

noncomputable def runUp (L0 L1 : ℝ) (v h : ℕ → E → E) (s : Iterate E) (n : ℕ) : Bool := by
  classical
  exact decide ((run L0 L1 v h s n).guess < 16*(L0+L1*‖v n (coupling (run L0 L1 v h s n))‖))

omit [CompleteSpace E] in
lemma run_charging_bound {L0 L1 : ℝ} (hL0 : 0 < L0) (hL1 : 0 ≤ L1)
    (v h : ℕ → E → E) (s : Iterate E) (hA : 0 ≤ s.A) (hG : 0 < s.guess)
    (hfirst : 16*(L0+L1*‖v 0 (coupling s)‖) ≤ s.guess) (n : ℕ) :
    let w := fun i => 1/Real.sqrt (run L0 L1 v h s i).guess
    let up := runUp L0 L1 v h s
    (∑ b ∈ chargingSet up n, chargeValue w b) ≤ 32*Real.sqrt (run L0 L1 v h s (n+1)).A ∧
    ∀ b ∈ chargingSet up n,
      (∑ a ∈ (chargingSet up n).filter (fun a => a.1 < b.1), chargeValue w a) ≤
        32*Real.sqrt (run L0 L1 v h s (b.1+1)).A := by
  let w := fun i => 1/Real.sqrt (run L0 L1 v h s i).guess
  let up := runUp L0 L1 v h s
  have hzero : up 0 = false := by simp [up, runUp, run, not_lt_of_ge hfirst]
  have hw : ∀ i, 0 ≤ w i := fun i => one_div_nonneg.mpr (Real.sqrt_nonneg _)
  have hnext : ∀ i, w (i+1) = if up i then w i/4 else 4*w i := by
    intro i
    have hv := run_valid hL0 hL1 v h s hA hG i
    have hs := step_inverse_sqrt_guess L0 L1 (v i) (h i) (run L0 L1 v h s i) hv.2
    dsimp [w, up, runUp]
    simp only [decide_eq_true_eq, ← not_le, ite_not]
    exact hs
  have hmass (i : ℕ) : downMass up w i ≤ 2*Real.sqrt (run L0 L1 v h s (i+1)).A := by
    have hs := down_sum_le_sqrt hL0 hL1 v h s hA hG (i+1)
    simpa only [downMass, up, runUp, w, decide_eq_true_eq, ← not_le, ite_not] using hs
  have htotal (i : ℕ) : chargeTotal w (charging up i) ≤ 32*Real.sqrt (run L0 L1 v h s (i+1)).A := by
    have hs := charging_total_le hzero hw hnext i
    linarith [hmass i]
  have hmono : Monotone (fun i => 32*Real.sqrt (run L0 L1 v h s (i+1)).A) := by
    intro i j hij
    have h := Real.sqrt_le_sqrt (run_weight_mono hL0 hL1 v h s hA hG (Nat.add_le_add_right hij 1))
    linarith
  have hprefix := charging_prefix_bound
    (show 0 ≤ 32*Real.sqrt (run L0 L1 v h s (0+1)).A by positivity) hmono htotal n
  dsimp only
  constructor
  · rw [charging_sum]
    exact htotal n
  · intro b hb
    rw [charging_sum_prefix]
    exact hprefix b (List.mem_toFinset.mp hb)

omit [CompleteSpace E] in
lemma step_high_dissipation {L0 L1 : ℝ} (hL0 : 0 < L0) (hL1 : 0 < L1)
    (v h : E → E) (s : Iterate E) (hA : 0 ≤ s.A) (hG : 0 < s.guess)
    (hup : s.guess ≤ 16*(L0+L1*‖v (coupling s)‖))
    (hhigh : 32*L0 < 16*(L0+L1*‖v (coupling s)‖)) :
    (step L0 L1 v h s).A*s.guess ≤ (8192/3)*L1^2*dissipation L0 L1 v s := by
  let M := 16*(L0+L1*‖v (coupling s)‖)
  let d := ‖coupling s-(1/M) • v (coupling s)-coupling s‖
  have hM : 0 < M := by dsimp [M]; positivity
  have hcurv : (prepare L0 L1 s (v (coupling s))).curvature = M := max_eq_right hup
  have hmove : 1/(32*L1) ≤ d := by
    rw [show d = ‖v (coupling s)‖/M from local_step_norm hM _ _]
    apply (div_le_div_iff₀ (by positivity) hM).mpr
    dsimp [M] at *
    linarith
  have hm : 1 ≤ 32*L1*d := by
    have ht := (div_le_iff₀ (show 0 < 32*L1 by positivity)).mp hmove
    nlinarith only [ht]
  have hs : 1 ≤ 1024*L1^2*d^2 := by nlinarith [sq_nonneg (32*L1*d-1)]
  have ha := GeneralizedAccelerated.tentativeWeight_pos s hG
  have hd : dissipation L0 L1 v s = (3/8)*s.guess*(s.A+tentativeWeight s)*d^2 := by
    simp only [dissipation, prepare, max_eq_right hup]
    change (s.guess/M)*(s.A+tentativeWeight s)*(3*M/8)*d^2 = _
    field_simp

  have hmul := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ s.guess*(s.A+tentativeWeight s) by positivity)
  have hw := mul_le_mul_of_nonneg_right (step_weights hL0 hL1.le v h s hG).2.1 hG.le
  rw [hd]
  nlinarith only [hmul, hw]

omit [CompleteSpace E] in
lemma run_shift (L0 L1 : ℝ) (v h : ℕ → E → E) (s : Iterate E) (m n : ℕ) :
    run L0 L1 v h s (m+n) =
      run L0 L1 (fun i => v (m+i)) (fun i => h (m+i)) (run L0 L1 v h s m) n := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    change step L0 L1 (v (m+n)) (h (m+n)) (run L0 L1 v h s (m+n)) = _
    rw [ih]
    rfl

omit [CompleteSpace E] in
lemma run_high_sum_le {L0 L1 D : ℝ} (hL0 : 0 < L0) (hL1 : 0 < L1)
    (v h : ℕ → E → E) (s : Iterate E) (hA : 0 ≤ s.A) (hG : 0 < s.guess) (N : ℕ)
    (hD : (∑ i ∈ Finset.range N, dissipation L0 L1 (v i) (run L0 L1 v h s i)) ≤ D)
    (Q : Finset ℕ) (hQ : Q ⊆ Finset.range N)
    (hup : ∀ i ∈ Q, (run L0 L1 v h s i).guess ≤ 16*(L0+L1*‖v i (coupling (run L0 L1 v h s i))‖))
    (hhigh : ∀ i ∈ Q, 32*L0 < 16*(L0+L1*‖v i (coupling (run L0 L1 v h s i))‖)) :
    (∑ i ∈ Q, (run L0 L1 v h s (i+1)).A*(run L0 L1 v h s i).guess) ≤ (8192/3)*L1^2*D := by
  have hsub := Finset.sum_le_sum_of_subset_of_nonneg hQ
    (fun i _ _ => dissipation_nonneg hL0 hL1.le (v i) (run L0 L1 v h s i)
      (run_valid hL0 hL1.le v h s hA hG i).1 (run_valid hL0 hL1.le v h s hA hG i).2)
  calc
    _ ≤ ∑ i ∈ Q, (8192/3)*L1^2*dissipation L0 L1 (v i) (run L0 L1 v h s i) := by
      apply Finset.sum_le_sum
      intro i hi
      have hv := run_valid hL0 hL1.le v h s hA hG i
      exact step_high_dissipation hL0 hL1 (v i) (h i) _ hv.1 hv.2 (hup i hi) (hhigh i hi)
    _ = (8192/3)*L1^2*(∑ i ∈ Q, dissipation L0 L1 (v i) (run L0 L1 v h s i)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (8192/3)*L1^2*D := mul_le_mul_of_nonneg_left (hsub.trans hD) (by positivity)

omit [CompleteSpace E] in
lemma charging_selected_curvature (L0 L1 : ℝ) (v h : ℕ → E → E) (s : Iterate E)
    (n : ℕ) (b : ℕ × ℕ) (hb : b ∈ chargingSet (runUp L0 L1 v h s) n) (hne : b.1 ≠ 0) :
    (run L0 L1 v h s b.1).guess ≤ 16*(L0+L1*‖v b.1 (coupling (run L0 L1 v h s b.1))‖) := by
  have hi := (GeneralizedAccelerated.charging_indices (runUp L0 L1 v h s) n).2.2.2 b
    (List.mem_toFinset.mp hb)
  have hu := hi.resolve_left hne
  exact (of_decide_eq_true hu).le

omit [CompleteSpace E] in
lemma charged_high_energy {L0 L1 D : ℝ} (hL0 : 0 < L0) (hL1 : 0 < L1)
    (v h : ℕ → E → E) (s : Iterate E) (hA : 0 ≤ s.A) (hG : 0 < s.guess) (n : ℕ)
    (hD : (∑ i ∈ Finset.range (n+1), dissipation L0 L1 (v i) (run L0 L1 v h s i)) ≤ D)
    (Q : Finset (ℕ × ℕ)) (hQ : Q ⊆ chargingSet (runUp L0 L1 v h s) n)
    (hne : ∀ b ∈ Q, b.1 ≠ 0)
    (hhigh : ∀ b ∈ Q, 32*L0 < 16*(L0+L1*‖v b.1 (coupling (run L0 L1 v h s b.1))‖)) :
    (∑ b ∈ Q, (run L0 L1 v h s (b.1+1)).A*(run L0 L1 v h s b.1).guess) ≤ (8192/3)*L1^2*D := by
  classical
  have hindex : Q.image Prod.fst ⊆ Finset.range (n+1) := by
    intro i hi
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le
      (GeneralizedAccelerated.charging_index_le _ n b (List.mem_toFinset.mp (hQ hb))))
  have hup : ∀ i ∈ Q.image Prod.fst, (run L0 L1 v h s i).guess ≤
      16*(L0+L1*‖v i (coupling (run L0 L1 v h s i))‖) := by
    intro i hi
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hi
    exact charging_selected_curvature L0 L1 v h s n b (hQ hb) (hne b hb)
  have hhigh' : ∀ i ∈ Q.image Prod.fst, 32*L0 < 16*(L0+L1*‖v i (coupling (run L0 L1 v h s i))‖) := by
    intro i hi
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hi
    exact hhigh b hb
  have he := run_high_sum_le hL0 hL1 v h s hA hG (n+1) hD (Q.image Prod.fst) hindex hup hhigh'
  have hinj : ∀ a ∈ Q, ∀ b ∈ Q, a.1 = b.1 → a = b := by
    intro a ha b hb hab
    exact GeneralizedAccelerated.charging_unique_index _ n (List.mem_toFinset.mp (hQ ha))
      (List.mem_toFinset.mp (hQ hb)) hab
  rw [Finset.sum_image hinj] at he
  exact he

lemma exceptional_count_bound (Q : Finset (ℕ × ℕ)) (G : (ℕ × ℕ) → ℝ) {G0 A : ℝ}
    (hG0 : 0 < G0) (hinj : Set.InjOn Prod.fst (Q : Set (ℕ × ℕ)))
    (hzero : ∀ b ∈ Q, b.1 = 0 → G b = G0)
    (hw : (∑ b ∈ Q, (2 : ℝ)^b.2/Real.sqrt (G b)) ≤ 32*Real.sqrt A) :
    (∑ b ∈ Q.filter (fun b => b.1 = 0), (b.2 : ℝ)) ≤ 2*Real.log (1+32*Real.sqrt (G0*A)) := by
  classical
  let Z := Q.filter (fun b => b.1 = 0)
  have hlog : 0 ≤ Real.log (1+32*Real.sqrt (G0*A)) :=
    Real.log_nonneg (by nlinarith [Real.sqrt_nonneg (G0*A)])
  by_cases hz : Z.Nonempty
  · obtain ⟨b, hb⟩ := hz
    have hbQ : b ∈ Q := (Finset.mem_filter.mp hb).1
    have hb0 : b.1 = 0 := (Finset.mem_filter.mp hb).2
    have heZ : Z = {b} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hb, ?_⟩
      intro a ha
      have haQ := (Finset.mem_filter.mp ha).1
      have ha0 := (Finset.mem_filter.mp ha).2
      exact hinj haQ hbQ (ha0.trans hb0.symm)
    change (∑ b ∈ Z, (b.2 : ℝ)) ≤ _
    rw [heZ, Finset.sum_singleton]
    have hs := (Finset.single_le_sum (f := fun b => (2 : ℝ)^b.2/Real.sqrt (G b))
      (fun b _ => by positivity) hbQ).trans hw
    rw [hzero b hbQ hb0] at hs
    have hp := (div_le_iff₀ (Real.sqrt_pos.mpr hG0)).mp hs
    have he : 32*Real.sqrt A*Real.sqrt G0 = 32*Real.sqrt (G0*A) := by
      rw [Real.sqrt_mul hG0.le]
      ring
    rw [he] at hp
    have hl := Real.log_le_log (show 0 < (2 : ℝ)^b.2 by positivity)
      (show (2 : ℝ)^b.2 ≤ 1+32*Real.sqrt (G0*A) by linarith)
    rw [Real.log_pow] at hl
    have hlog2 := GeneralizedAccelerated.count_exponent_lower
    have hn : 0 ≤ (b.2 : ℝ) := Nat.cast_nonneg _
    have hm := mul_le_mul_of_nonneg_left (show (1/2 : ℝ) ≤ Real.log 2 by linarith) hn
    linarith
  · have heZ : Z = ∅ := Finset.not_nonempty_iff_eq_empty.mp hz
    change (∑ b ∈ Z, (b.2 : ℝ)) ≤ _
    rw [heZ, Finset.sum_empty]
    positivity

omit [CompleteSpace E] in
lemma run_count_positive {L0 L1 R : ℝ} (hL0 : 0 < L0) (hL1 : 0 < L1) (hR : 0 ≤ R)
    (v h : ℕ → E → E) (s : Iterate E) (hA : 0 < s.A) (hG : 0 < s.guess)
    (hfirst : 16*(L0+L1*‖v 0 (coupling s)‖) ≤ s.guess) (n : ℕ)
    (hD : (∑ i ∈ Finset.range (n+1), dissipation L0 L1 (v i) (run L0 L1 v h s i)) ≤ 3*R^2) :
    (n : ℝ) ≤ 2*Real.log (1+32*Real.sqrt (s.guess*(run L0 L1 v h s (n+1)).A))+
      96*Real.sqrt (4*L0*(run L0 L1 v h s (n+1)).A)+
      384*(1+(8*(L1*R))^(2/3 : ℝ))*Real.log (2*(run L0 L1 v h s (n+1)).A/s.A) := by
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
  have htune := GeneralizedAccelerated.mixed_tuning (show 0 ≤ 8*(L1*R) by positivity)
  have hh := GeneralizedAccelerated.high_count_log_bound high Prod.fst B G Prod.snd hA hAF
    (fun b _ => hbase _) (fun b _ => (hv b.1).2) (by positivity) htune.1 htune.2.1
    (hinj.mono hhQ) henergy (hsubset high hhQ) hprefix htune.2.2
  have hhigh := hh.trans (GeneralizedAccelerated.high_log_simplify hA hAF
    (show 0 ≤ 8*(L1*R) by positivity))
  have hcount : (∑ b ∈ Q, (b.2 : ℝ)) = n := by
    exact_mod_cast GeneralizedAccelerated.charging_sum_count (runUp L0 L1 v h s) n
  have hsplit : (∑ b ∈ low, (b.2 : ℝ))+(∑ b ∈ high, (b.2 : ℝ)) = ∑ b ∈ rest, (b.2 : ℝ) :=
    Finset.sum_filter_add_sum_filter_not rest _ _
  have hsplit0 : (∑ b ∈ Q.filter (fun b => b.1=0), (b.2 : ℝ))+(∑ b ∈ rest, (b.2 : ℝ)) = n := by
    rw [← hcount]
    exact Finset.sum_filter_add_sum_filter_not Q _ _
  change (n : ℝ) ≤ 2*Real.log (1+32*Real.sqrt (s.guess*Afinal))+
    96*Real.sqrt (4*L0*Afinal)+384*(1+(8*(L1*R))^(2/3 : ℝ))*Real.log (2*Afinal/s.A)
  linarith

omit [CompleteSpace E] in
lemma run_up_guess (L0 L1 : ℝ) (v h : ℕ → E → E) (s : Iterate E) (n : ℕ)
    (hu : ∀ i < n, runUp L0 L1 v h s i = true) :
    (run L0 L1 v h s n).guess = 16^n*s.guess := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    have hn : (run L0 L1 v h s n).guess < 16*(L0+L1*‖v n (coupling (run L0 L1 v h s n))‖) :=
      of_decide_eq_true (hu n (by omega))
    change (step L0 L1 (v n) (h n) (run L0 L1 v h s n)).guess = _
    rw [step_guess, ite_eq_right (not_le.mpr hn), ih (fun i hi => hu i (by omega)), pow_succ]
    ring

omit [CompleteSpace E] in
lemma run_high_point_le {L0 L1 R : ℝ} (hL0 : 0 < L0) (hL1 : 0 < L1)
    (v h : ℕ → E → E) (s : Iterate E) (hA : 0 ≤ s.A) (hG : 0 < s.guess) (N i : ℕ)
    (hi : i < N)
    (hD : (∑ k ∈ Finset.range N, dissipation L0 L1 (v k) (run L0 L1 v h s k)) ≤ 3*R^2)
    (hup : (run L0 L1 v h s i).guess ≤ 16*(L0+L1*‖v i (coupling (run L0 L1 v h s i))‖))
    (hhigh : 32*L0 < 16*(L0+L1*‖v i (coupling (run L0 L1 v h s i))‖)) :
    s.A*(run L0 L1 v h s i).guess ≤ 8192*(L1*R)^2 := by
  have hv := run_valid hL0 hL1.le v h s hA hG i
  have hd := (Finset.single_le_sum (f := fun k => dissipation L0 L1 (v k) (run L0 L1 v h s k))
    (fun k _ => dissipation_nonneg hL0 hL1.le (v k) _
      (run_valid hL0 hL1.le v h s hA hG k).1 (run_valid hL0 hL1.le v h s hA hG k).2)
    (Finset.mem_range.mpr hi)).trans hD
  have he := step_high_dissipation hL0 hL1 (v i) (h i) _ hv.1 hv.2 hup hhigh
  have hb : s.A ≤ (run L0 L1 v h s (i+1)).A := run_weight_mono hL0 hL1.le v h s hA hG (Nat.zero_le _)
  have hm := mul_le_mul_of_nonneg_right hb hv.2.le
  have hd' := mul_le_mul_of_nonneg_left hd (show 0 ≤ (8192/3)*L1^2 by positivity)
  change (run L0 L1 v h s (i+1)).A*(run L0 L1 v h s i).guess ≤ _ at he
  nlinarith only [hm, he, hd']

omit [CompleteSpace E] in
lemma run_dissipation_shift_le {L0 L1 D : ℝ} (hL0 : 0 < L0) (hL1 : 0 ≤ L1)
    (v h : ℕ → E → E) (s : Iterate E) (hA : 0 ≤ s.A) (hG : 0 < s.guess) (m n : ℕ)
    (hD : (∑ i ∈ Finset.range (m+n), dissipation L0 L1 (v i) (run L0 L1 v h s i)) ≤ D) :
    (∑ i ∈ Finset.range n, dissipation L0 L1 (v (m+i))
      (run L0 L1 (fun j => v (m+j)) (fun j => h (m+j)) (run L0 L1 v h s m) i)) ≤ D := by
  rw [Finset.sum_range_add] at hD
  simp_rw [run_shift] at hD
  have hn : 0 ≤ ∑ i ∈ Finset.range m, dissipation L0 L1 (v i) (run L0 L1 v h s i) :=
    Finset.sum_nonneg (fun i _ => dissipation_nonneg hL0 hL1 (v i) _
      (run_valid hL0 hL1 v h s hA hG i).1 (run_valid hL0 hL1 v h s hA hG i).2)
  linarith

omit [CompleteSpace E] in
lemma run_count_smooth {L0 K : ℝ} (hL0 : 0 < L0) (v h : ℕ → E → E)
    (s : Iterate E) (hA : 0 ≤ s.A) (hG : 0 < s.guess)
    (hfirst : 16*L0 ≤ s.guess) (hK : 16*L0 ≤ K) (hKG : s.guess ≤ K) (n : ℕ) :
    (n : ℝ) ≤ Real.sqrt K*(32*Real.sqrt (run L0 0 v h s (n+1)).A) := by
  let Q := chargingSet (runUp L0 0 v h s) n
  let G := fun b : ℕ × ℕ => (run L0 0 v h s b.1).guess
  have hcharge := run_charging_bound hL0 (le_refl 0) v h s hA hG
    (by simpa only [zero_mul, add_zero] using hfirst) n
  have hbound : ∀ b ∈ Q, G b ≤ K := by
    intro b hb
    by_cases hz : b.1=0
    · simpa only [G, hz, run] using hKG
    · have hs := charging_selected_curvature L0 0 v h s n b hb hz
      simp only [zero_mul, add_zero] at hs
      exact hs.trans hK
  have hweights : (∑ b ∈ Q, (2 : ℝ)^b.2/Real.sqrt (G b)) ≤
      32*Real.sqrt (run L0 0 v h s (n+1)).A := by
    simpa only [chargeValue, mul_one_div] using hcharge.1
  have hh := GeneralizedAccelerated.low_count_bound Q G Prod.snd
    (fun b _ => (run_valid hL0 (le_refl 0) v h s hA hG b.1).2) hbound hweights
  have hcount : (∑ b ∈ Q, (b.2 : ℝ)) = n := by
    exact_mod_cast GeneralizedAccelerated.charging_sum_count (runUp L0 0 v h s) n
  rwa [hcount] at hh

end OracleTemplate.StochasticGeneralized
