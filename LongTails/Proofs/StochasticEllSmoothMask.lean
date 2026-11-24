import LongTails.Proofs.EllSmoothSimulation
import LongTails.Proofs.AbcHardExecution

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.StochasticEllSmoothMask

open LongTails.Proofs.EllSmoothProfiles LongTails.Proofs.EllSmoothChain
open LongTails.Proofs.EllSmoothHard LongTails.Proofs.EllSmoothHardBounds
open LongTails.Proofs.EllSmoothSimulation
open LongTails.Proofs.AbcHardFunction (sel sel_apply sel_norm adjoint_norm)
open LongTails.Proofs.AbcHardOracle (Scale toUnit stage stageUpTo small_of_stage stage_le
  stageUpTo_le stageUpTo_eq stageUpTo_congr coin unif unif_real_le setOf_le_measurable
  coin_measurable coin_integral coin_integrable)
open LongTails.Proofs.AbcHardExecution (coinCount level coinCount_mono level_mono level_le
  level_succ_of_gt)

variable (S : Shape) {d n : ℕ}

lemma field_sub_visible_zero (u : Chain n) (s : ℕ)
    (hs : ∀ i : Fin (n + 1), s ≤ i.val → |u i| ≤ 1 / 4) (k : Fin (n + 1))
    (hk : k.val + 1 < s ∨ s < k.val) : field S u k - visibleField S s u k = 0 := by
  rcases hk with hk | hk
  · have hv : visibleField S s u k = field S (trunc s u) k := by
      simp only [visibleField]; rw [ite_eq_left (by omega)]
    rw [hv, field_congr S (trunc s u) u k (fun j hj => by
      rw [trunc_apply, ite_eq_left (by omega)])]
    ring
  · have hv : visibleField S s u k = 0 := by
      simp only [visibleField]; rw [ite_eq_right (by omega)]
    rw [hv, field_zero_beyond S s u hs k (by omega)]
    ring

lemma field_sub_visible_abs (u : Chain n) (s : ℕ) (k : Fin (n + 1)) :
    |field S u k - visibleField S s u k| ≤ 206 := by
  have h1 := field_abs S u k
  have h2 : |visibleField S s u k| ≤ 103 := by
    simp only [visibleField]
    split_ifs
    · exact field_abs S _ k
    · simp
  have := abs_sub (field S u k) (visibleField S s u k)
  linarith

lemma card_val_eq_le_one (c : ℕ) :
    (Finset.univ.filter (fun k : Fin (n + 1) => k.val = c)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  simp only [Finset.mem_filter] at ha hb
  exact Fin.ext (ha.2.trans hb.2.symm)

lemma sum_val_eq_le (c : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    (∑ k : Fin (n + 1), if k.val = c then a else 0) ≤ a := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have := card_val_eq_le_one (n := n) c
  have h1 : ((Finset.univ.filter (fun k : Fin (n + 1) => k.val = c)).card : ℝ) ≤ 1 := by
    exact_mod_cast this
  nlinarith

lemma field_sub_visible_norm (u : Chain n) (s : ℕ)
    (hs : ∀ i : Fin (n + 1), s ≤ i.val → |u i| ≤ 1 / 4) :
    ‖field S u - visibleField S s u‖ ≤ 300 := by
  have hsq : ‖field S u - visibleField S s u‖ ^ 2 ≤ 300 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    have hpt (k : Fin (n + 1)) : ((field S u - visibleField S s u) k) ^ 2 ≤
        (if k.val = s - 1 then (206 : ℝ) ^ 2 else 0) + (if k.val = s then (206 : ℝ) ^ 2 else 0) := by
      have he : (field S u - visibleField S s u) k = field S u k - visibleField S s u k := rfl
      rw [he]
      by_cases h1 : k.val = s - 1
      · rw [ite_eq_left h1]
        have := field_sub_visible_abs S u s k
        have h0 : (0 : ℝ) ≤ if k.val = s then (206 : ℝ) ^ 2 else 0 := by split_ifs <;> positivity
        nlinarith [sq_abs (field S u k - visibleField S s u k), abs_nonneg (field S u k - visibleField S s u k)]
      · by_cases h2 : k.val = s
        · rw [ite_eq_right h1, ite_eq_left h2]
          have := field_sub_visible_abs S u s k
          nlinarith [sq_abs (field S u k - visibleField S s u k), abs_nonneg (field S u k - visibleField S s u k)]
        · rw [ite_eq_right h1, ite_eq_right h2, field_sub_visible_zero S u s hs k (by omega)]
          norm_num
    have hsum := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin (n + 1)))) => hpt k)
    rw [Finset.sum_add_distrib] at hsum
    have h1 := sum_val_eq_le (n := n) (s - 1) ((206 : ℝ) ^ 2) (by positivity)
    have h2 := sum_val_eq_le (n := n) s ((206 : ℝ) ^ 2) (by positivity)
    nlinarith
  exact norm_le_of_sq_le (by norm_num) hsq

lemma secret_bound (π : Fin (n + 1) ↪ Fin d) (w : Space d) :
    ‖hgrad S π w - pgrad S π (stage (sel π w)) w‖ ≤ 512 := by
  by_cases hw : ‖w‖ ≤ 4 * rad S n
  · have hs : ∀ i : Fin (n + 1), stage (sel π w) ≤ i.val → |sel π w i| ≤ 1 / 4 :=
      fun i hi => small_of_stage (sel π w) i hi
    have he : hgrad S π w - pgrad S π (stage (sel π w)) w =
        cut S n (‖w‖ ^ 2) • (sel π).adjoint (field S (sel π w) -
          visibleField S (stage (sel π w)) (sel π w)) +
          (2 * dcut S n (‖w‖ ^ 2) * (chain S (sel π w) -
            chain S (trunc (stage (sel π w)) (sel π w)))) • w := by
      simp only [hgrad, pgrad, vfield, bco, map_sub]
      module
    rw [he]
    have hr := rad_pos S n
    have hrg := rad_ge' S n
    have hn := n1_pos n
    have h1 : ‖cut S n (‖w‖ ^ 2) • (sel π).adjoint (field S (sel π w) -
        visibleField S (stage (sel π w)) (sel π w))‖ ≤ 300 := by
      rw [norm_smul, Real.norm_of_nonneg (cut_nonneg S n _)]
      calc cut S n (‖w‖ ^ 2) * ‖(sel π).adjoint (field S (sel π w) -
            visibleField S (stage (sel π w)) (sel π w))‖
          ≤ 1 * ‖field S (sel π w) - visibleField S (stage (sel π w)) (sel π w)‖ :=
            mul_le_mul (cut_le_one S n _) (adjoint_norm π _) (norm_nonneg _) zero_le_one
        _ ≤ 300 := by rw [one_mul]; exact field_sub_visible_norm S (sel π w) _ hs
    have hc := chain_abs S (sel π w)
    have hct := chain_abs S (trunc (stage (sel π w)) (sel π w))
    have hdc := dcut_abs S n (‖w‖ ^ 2)
    have h2 : ‖(2 * dcut S n (‖w‖ ^ 2) * (chain S (sel π w) -
        chain S (trunc (stage (sel π w)) (sel π w)))) • w‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_mul, abs_two]
      have hdiff : |chain S (sel π w) - chain S (trunc (stage (sel π w)) (sel π w))| ≤
          40 * ((n : ℝ) + 1) := by
        have := abs_sub (chain S (sel π w)) (chain S (trunc (stage (sel π w)) (sel π w)))
        linarith
      have h3 : 2 * |dcut S n (‖w‖ ^ 2)| *
          |chain S (sel π w) - chain S (trunc (stage (sel π w)) (sel π w))| * ‖w‖ ≤
          2 * (5 / (24 * rad S n ^ 2)) * (40 * ((n : ℝ) + 1)) * (4 * rad S n) := by
        gcongr
      refine h3.trans ?_
      have e : 2 * (5 / (24 * rad S n ^ 2)) * (40 * ((n : ℝ) + 1)) * (4 * rad S n) =
          200 / 3 * ((n : ℝ) + 1) / rad S n := by field_simp; ring
      rw [e, div_le_iff₀ hr]
      nlinarith
    calc _ ≤ ‖cut S n (‖w‖ ^ 2) • (sel π).adjoint (field S (sel π w) -
            visibleField S (stage (sel π w)) (sel π w))‖ +
          ‖(2 * dcut S n (‖w‖ ^ 2) * (chain S (sel π w) -
            chain S (trunc (stage (sel π w)) (sel π w)))) • w‖ := norm_add_le _ _
      _ ≤ 512 := by linarith
  · have hfar := far_sq S hw
    have he : hgrad S π w - pgrad S π (stage (sel π w)) w = 0 := by
      simp only [hgrad, pgrad, vfield, bco, cut_of_ge S n hfar, dcut_of_ge S n hfar]
      simp
    rw [he, norm_zero]
    norm_num

noncomputable def knownPart (Sc : Scale) (π : Fin (n + 1) ↪ Fin d) (m : ℕ) (x0 x : Space d) :
    Space d :=
  (Sc.a / Sc.lam) • pgrad S π m (toUnit Sc x0 x)

noncomputable def reply (Sc : Scale) (q : ℝ) (π : Fin (n + 1) ↪ Fin d) (x0 x : Space d) (ω : ℝ) :
    Space d :=
  knownPart S Sc π (stage (sel π (toUnit Sc x0 x))) x0 x +
    coin q ω • (objGrad S Sc π x0 x - knownPart S Sc π (stage (sel π (toUnit Sc x0 x))) x0 x)

lemma secret_norm (Sc : Scale) (π : Fin (n + 1) ↪ Fin d) (x0 x : Space d) :
    ‖objGrad S Sc π x0 x - knownPart S Sc π (stage (sel π (toUnit Sc x0 x))) x0 x‖ ≤
      512 * (Sc.a / Sc.lam) := by
  rw [objGrad, knownPart, ← smul_sub, norm_smul,
    Real.norm_of_nonneg (by have := Sc.ha; have := Sc.hlam; positivity), mul_comm]
  exact mul_le_mul_of_nonneg_right (secret_bound S π _)
    (by have := Sc.ha; have := Sc.hlam; positivity)

lemma reply_integral (Sc : Scale) {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1)
    (π : Fin (n + 1) ↪ Fin d) (x0 x : Space d) :
    ∫ ω, reply S Sc q π x0 x ω ∂unif = objGrad S Sc π x0 x := by
  unfold reply
  rw [integral_add (integrable_const _) ((coin_integrable _).smul_const _), integral_const,
    probReal_univ, one_smul, integral_smul_const, coin_integral _ hq0 hq1, one_smul]
  abel

lemma reply_integrable (Sc : Scale) (q : ℝ) (π : Fin (n + 1) ↪ Fin d) (x0 x : Space d) :
    Integrable (reply S Sc q π x0 x) unif := by
  unfold reply
  exact (integrable_const _).add ((coin_integrable _).smul_const _)

lemma coin_sub_rpow_eq {p q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) (ω : ℝ) :
    |coin q ω - 1| ^ p = {ω' : ℝ | ω' ≤ q}.indicator (fun _ => (1 / q - 1) ^ p - 1) ω + 1 := by
  by_cases h : ω ≤ q
  · rw [Set.indicator_of_mem (show ω ∈ {ω' : ℝ | ω' ≤ q} from h)]
    simp only [coin, h, ↓reduceIte]
    have h1 : 0 ≤ 1 / q - 1 := by
      rw [sub_nonneg, le_div_iff₀ hq0]; linarith
    rw [abs_of_nonneg h1]; ring
  · rw [Set.indicator_of_notMem (show ω ∉ {ω' : ℝ | ω' ≤ q} from h)]
    simp only [coin, h, ↓reduceIte, zero_sub, abs_neg, abs_one, Real.one_rpow]
    ring

lemma coin_moment {p q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) :
    Integrable (fun ω => |coin q ω - 1| ^ p) unif ∧
      ∫ ω, |coin q ω - 1| ^ p ∂unif = q * (1 / q - 1) ^ p + (1 - q) := by
  have he : (fun ω => |coin q ω - 1| ^ p) =
      fun ω => {ω' : ℝ | ω' ≤ q}.indicator (fun _ => (1 / q - 1) ^ p - 1) ω + 1 := by
    funext ω; exact coin_sub_rpow_eq hq0 hq1 ω
  have hi : Integrable (fun ω => {ω' : ℝ | ω' ≤ q}.indicator (fun _ => (1 / q - 1) ^ p - 1) ω)
      unif := (integrable_const _).indicator (setOf_le_measurable q)
  rw [he]
  refine ⟨hi.add (integrable_const _), ?_⟩
  rw [integral_add hi (integrable_const _), integral_indicator (setOf_le_measurable q),
    setIntegral_const, unif_real_le q hq0.le hq1, integral_const, probReal_univ, smul_eq_mul,
    smul_eq_mul]
  ring

lemma coin_moment_le {p q : ℝ} (hp : 1 ≤ p) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    q * (1 / q - 1) ^ p + (1 - q) ≤ 2 * q ^ (1 - p) := by
  have h0 : 0 ≤ 1 / q - 1 := by
    rw [sub_nonneg, le_div_iff₀ hq0]; linarith
  have h1 : (1 / q - 1) ^ p ≤ (1 / q) ^ p :=
    Real.rpow_le_rpow h0 (by linarith) (by linarith)
  have h2 : q * (1 / q) ^ p = q ^ (1 - p) := by
    rw [Real.div_rpow zero_le_one hq0.le, Real.one_rpow, Real.rpow_sub hq0, Real.rpow_one]
    field_simp
  have h3 : 1 ≤ q ^ (1 - p) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hq0 hq1 (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left h1 hq0.le]

lemma trunc_full' (m : ℕ) (u : Chain n) (hm : n + 1 ≤ m) : trunc m u = u := by
  ext i
  rw [trunc_apply, ite_eq_left (by have := i.isLt; omega)]

lemma pgrad_full (π : Fin (n + 1) ↪ Fin d) (m : ℕ) (w : Space d) (hm : n + 1 ≤ m) :
    pgrad S π m w = hgrad S π w := by
  have hv : visibleField S m (sel π w) = field S (sel π w) := by
    ext k
    simp only [visibleField]
    rw [ite_eq_left (by have := k.isLt; omega), trunc_full' m _ hm]
  simp only [pgrad, hgrad, vfield, bco, hv, trunc_full' m _ hm]

lemma pgrad_far (π : Fin (n + 1) ↪ Fin d) (m : ℕ) (w : Space d) (hw : ¬ ‖w‖ ≤ 4 * rad S n) :
    pgrad S π m w = hgrad S π w := by
  have hfar := far_sq S hw
  simp only [pgrad, hgrad, vfield, bco, cut_of_ge S n hfar, dcut_of_ge S n hfar]
  simp

variable {St : Type*}

noncomputable def simReply (Sc : Scale) (q : ℝ) (π : Fin (n + 1) ↪ Fin d) (r : ℕ)
    (x0 x : Space d) (ω : ℝ) : Space d :=
  knownPart S Sc π (stageUpTo r (sel π (toUnit Sc x0 x))) x0 x +
    if stageUpTo r (sel π (toUnit Sc x0 x)) < r then
      coin q ω • (knownPart S Sc π (stageUpTo r (sel π (toUnit Sc x0 x)) + 1) x0 x -
        knownPart S Sc π (stageUpTo r (sel π (toUnit Sc x0 x))) x0 x)
    else 0

lemma knownPart_prefix (Sc : Scale) (π ρ : Fin (n + 1) ↪ Fin d) (m : ℕ) (x0 x : Space d)
    (h : ∀ k : Fin (n + 1), k.val < m → π k = ρ k) :
    knownPart S Sc π m x0 x = knownPart S Sc ρ m x0 x := by
  simp only [knownPart, pgrad_prefix S π ρ m _ h]

lemma simReply_prefix (Sc : Scale) (q : ℝ) (π ρ : Fin (n + 1) ↪ Fin d) (r : ℕ)
    (x0 x : Space d) (ω : ℝ) (h : ∀ k : Fin (n + 1), k.val < r → π k = ρ k) :
    simReply S Sc q π r x0 x ω = simReply S Sc q ρ r x0 x ω := by
  have hs : ∀ i : Fin (n + 1), i.val < r →
      sel π (toUnit Sc x0 x) i = sel ρ (toUnit Sc x0 x) i := by
    intro i hi; rw [sel_apply, sel_apply, h i hi]
  have hst := stageUpTo_congr r _ _ hs
  have hle := stageUpTo_le r (sel ρ (toUnit Sc x0 x))
  unfold simReply
  rw [hst, knownPart_prefix S Sc π ρ _ x0 x (fun k hk => h k (by omega))]
  split_ifs with hlt
  · rw [knownPart_prefix S Sc π ρ _ x0 x (fun k hk => h k (by omega))]
  · rfl

noncomputable def simState (Sc : Scale) (q : ℝ) (π : Fin (n + 1) ↪ Fin d) (x0 : Space d)
    (query : St → Space d) (update : St → Space d → St) (initial : St) (ω : ℕ → ℝ) : ℕ → St
  | 0 => initial
  | t + 1 =>
    let s := simState Sc q π x0 query update initial ω t
    update s (simReply S Sc q π (level n q ω (t + 1)) x0 (query s) (ω t))

noncomputable def trueState (Sc : Scale) (q : ℝ) (π : Fin (n + 1) ↪ Fin d) (x0 : Space d)
    (query : St → Space d) (update : St → Space d → St) (initial : St) (ω : ℕ → ℝ) : ℕ → St
  | 0 => initial
  | t + 1 =>
    let s := trueState Sc q π x0 query update initial ω t
    update s (reply S Sc q π x0 (query s) (ω t))

lemma simState_prefix (Sc : Scale) (q : ℝ) (π ρ : Fin (n + 1) ↪ Fin d) (x0 : Space d)
    (query : St → Space d) (update : St → Space d → St) (initial : St) (ω : ℕ → ℝ) (t : ℕ)
    (h : ∀ k : Fin (n + 1), k.val < level n q ω t → π k = ρ k) :
    simState S Sc q π x0 query update initial ω t =
      simState S Sc q ρ x0 query update initial ω t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hm := level_mono n q ω (Nat.le_add_right t 1)
    have he := ih (fun k hk => h k (by omega))
    simp only [simState]
    rw [he, simReply_prefix S Sc q π ρ _ x0 _ _ h]

lemma reply_far (Sc : Scale) (q : ℝ) (π : Fin (n + 1) ↪ Fin d) (x0 x : Space d) (ω : ℝ)
    (hw : ¬ ‖toUnit Sc x0 x‖ ≤ 4 * rad S n) : reply S Sc q π x0 x ω = objGrad S Sc π x0 x := by
  simp only [reply, knownPart, objGrad, pgrad_far S π _ _ hw, sub_self, smul_zero, add_zero]

lemma simReply_far (Sc : Scale) (q : ℝ) (π : Fin (n + 1) ↪ Fin d) (r : ℕ) (x0 x : Space d)
    (ω : ℝ) (hw : ¬ ‖toUnit Sc x0 x‖ ≤ 4 * rad S n) :
    simReply S Sc q π r x0 x ω = objGrad S Sc π x0 x := by
  simp only [simReply, knownPart, objGrad, pgrad_far S π _ _ hw, sub_self, smul_zero, ite_self,
    add_zero]

lemma reply_eq_simReply (Sc : Scale) (q : ℝ) (π : Fin (n + 1) ↪ Fin d) (x0 x : Space d)
    (ω : ℕ → ℝ) (t : ℕ)
    (hhit : ‖toUnit Sc x0 x‖ ≤ 4 * rad S n →
      ∀ i : Fin (n + 1), level n q ω t ≤ i.val → |sel π (toUnit Sc x0 x) i| ≤ 1 / 4) :
    reply S Sc q π x0 x (ω t) = simReply S Sc q π (level n q ω (t + 1)) x0 x (ω t) := by
  set w := toUnit Sc x0 x
  by_cases hw : ‖w‖ ≤ 4 * rad S n
  · have hsm := hhit hw
    have hmono := level_mono n q ω (Nat.le_add_right t 1)
    have hsm' : ∀ i : Fin (n + 1), level n q ω (t + 1) ≤ i.val → |sel π w i| ≤ 1 / 4 :=
      fun i hi => hsm i (by omega)
    have hst : stageUpTo (level n q ω (t + 1)) (sel π w) = stage (sel π w) :=
      stageUpTo_eq _ _ hsm'
    have hstage : stage (sel π w) ≤ level n q ω t := by
      rw [← stageUpTo_eq _ _ hsm]; exact stageUpTo_le _ _
    unfold simReply reply
    rw [hst]
    by_cases hlt : stage (sel π w) < level n q ω (t + 1)
    · rw [ite_eq_left hlt]
      have hex : knownPart S Sc π (stage (sel π w) + 1) x0 x = objGrad S Sc π x0 x := by
        simp only [knownPart, objGrad]
        rw [pgrad_exact S π _ _ (fun _ i hi => small_of_stage _ i hi)]
      rw [hex]
    · rw [ite_eq_right hlt, add_zero]
      have heq : stage (sel π w) = level n q ω t := by omega
      by_cases hfull : n + 1 ≤ stage (sel π w)
      · have hpf : pgrad S π (stage (sel π (toUnit Sc x0 x))) (toUnit Sc x0 x) =
            hgrad S π (toUnit Sc x0 x) := pgrad_full S π _ _ hfull
        simp only [knownPart, objGrad, hpf, sub_self, smul_zero, add_zero]
        exact congrArg (fun v => (Sc.a / Sc.lam) • v) hpf.symm
      · have hcount : ¬ ω t ≤ q := by
          intro hc
          have h1 : level n q ω (t + 1) = min (n + 1) (coinCount q ω t + 1) := by
            simp [level, coinCount, hc]
          have h2 : level n q ω t = min (n + 1) (coinCount q ω t) := rfl
          omega
        have hc0 : coin q (ω t) = 0 := by
          unfold coin
          rw [ite_eq_right]
          intro hle
          exact hcount hle
        rw [hc0, zero_smul, add_zero]
  · rw [reply_far S Sc q π x0 x _ hw, simReply_far S Sc q π _ x0 x _ hw]

lemma coupling (Sc : Scale) (q : ℝ) (π : Fin (n + 1) ↪ Fin d) (x0 : Space d)
    (query : St → Space d) (update : St → Space d → St) (initial : St) (ω : ℕ → ℝ) (N : ℕ)
    (hhit : ∀ t < N,
      let x := query (simState S Sc q π x0 query update initial ω t)
      ‖toUnit Sc x0 x‖ ≤ 4 * rad S n →
        ∀ i : Fin (n + 1), level n q ω t ≤ i.val → |sel π (toUnit Sc x0 x) i| ≤ 1 / 4) :
    simState S Sc q π x0 query update initial ω N =
      trueState S Sc q π x0 query update initial ω N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have he := ih (fun t ht => hhit t (by omega))
    simp only [simState, trueState]
    rw [← he, reply_eq_simReply S Sc q π x0 _ ω N (hhit N (by omega))]

end LongTails.Proofs.StochasticEllSmoothMask
