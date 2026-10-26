import LongTails.Proofs.GeneralizedFiniteSumContainment
import LongTails.Proofs.GeneralizedFiniteSumStopping
import LongTails.Proofs.VradaConvex

open Set
open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.GeneralizedFiniteSum

open LongTails.Setups.GeneralizedSmoothFiniteSum
open LongTails.Setups.FiniteSumSmoothAndConvex (objective)

noncomputable def coreEnergy (p : Params) (f : Fin p.n → p.E → ℝ) (u : p.E)
    (s : LocalCore p) : ℝ :=
  (epochWeight p s.epoch + epochIncrement p (epochWeight p s.epoch)) *
    (s.outputs.map (fun x => objective f x - objective f u)).sum +
  ((p.n : ℝ) - s.index) * epochWeight p s.epoch * (objective f s.snapshot - objective f u) +
  (p.n : ℝ) / 2 * ‖s.dual - u‖ ^ 2

def CoreValid (p : Params) (s : LocalCore p) : Prop :=
  s.index < p.n ∧ s.outputs.length = s.index

lemma coreStep_valid (p : Params) (g : Fin p.n → p.E → p.E) (s : LocalCore p)
    (hs : CoreValid p s) (ξ : Fin ((2 * p.n).factorial)) : CoreValid p (coreStep p g s ξ) := by
  unfold coreStep
  split_ifs with h
  · exact ⟨h, by simpa using congrArg Nat.succ hs.2⟩
  · exact ⟨NeZero.pos p.n, rfl⟩

lemma coreEnergy_dual_le (p : Params) (f : Fin p.n → p.E → ℝ) (u : p.E)
    (hmin : IsMinOn (objective f) univ u) (s : LocalCore p) (hs : CoreValid p s)
    (hA : 0 ≤ epochWeight p s.epoch) (ha : 0 ≤ epochIncrement p (epochWeight p s.epoch)) :
    (p.n : ℝ) / 2 * ‖s.dual - u‖ ^ 2 ≤ coreEnergy p f u s := by
  have hg (x : p.E) : 0 ≤ objective f x - objective f u := sub_nonneg.mpr (hmin (mem_univ x))
  have hsum : 0 ≤ (s.outputs.map (fun x => objective f x - objective f u)).sum := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    exact hg y
  have hi : (s.index : ℝ) ≤ p.n := by exact_mod_cast hs.1.le
  unfold coreEnergy
  have hfirst := mul_nonneg (add_nonneg hA ha) hsum
  have hsecond := mul_nonneg (mul_nonneg (sub_nonneg.mpr hi) hA) (hg s.snapshot)
  linarith

lemma coreEnergy_nonneg (p : Params) (f : Fin p.n → p.E → ℝ) (u : p.E)
    (hmin : IsMinOn (objective f) univ u) (s : LocalCore p) (hs : CoreValid p s)
    (hA : 0 ≤ epochWeight p s.epoch) (ha : 0 ≤ epochIncrement p (epochWeight p s.epoch)) :
    0 ≤ coreEnergy p f u s :=
  (by positivity : 0 ≤ (p.n : ℝ) / 2 * ‖s.dual - u‖ ^ 2).trans
    (coreEnergy_dual_le p f u hmin s hs hA ha)

lemma coreEnergy_dual_radius (p : Params) (f : Fin p.n → p.E → ℝ) (u : p.E)
    (hmin : IsMinOn (objective f) univ u) (s : LocalCore p) (hs : CoreValid p s)
    (hA : 0 ≤ epochWeight p s.epoch) (ha : 0 ≤ epochIncrement p (epochWeight p s.epoch))
    (hR : 0 ≤ p.R) (henergy : coreEnergy p f u s ≤ 6 * p.n * p.R ^ 2) :
    ‖s.dual - u‖ ≤ 4 * p.R := by
  have hn : (0 : ℝ) < p.n := by exact_mod_cast NeZero.pos p.n
  have hd := (coreEnergy_dual_le p f u hmin s hs hA ha).trans henergy
  have hsq : ‖s.dual - u‖ ^ 2 ≤ 12 * p.R ^ 2 := by
    apply (mul_le_mul_iff_left₀ hn).mp
    nlinarith only [hd]
  nlinarith [norm_nonneg (s.dual - u)]

lemma list_average_radius {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (xs : List E) (u : E) (R : ℝ) (hne : xs.length ≠ 0)
    (hx : ∀ x ∈ xs, ‖x - u‖ ≤ R) : ‖(xs.length : ℝ)⁻¹ • xs.sum - u‖ ≤ R := by
  have hh : ‖xs.sum - (xs.length : ℝ) • u‖ ≤ (xs.length : ℝ) * R := by
    clear hne
    induction xs with
    | nil => simp
    | cons x tail ih =>
      have ht := ih (fun y hy => hx y (List.mem_cons_of_mem x hy))
      have hxx := hx x (List.mem_cons_self)
      have he : x + tail.sum - ((tail.length : ℝ) + 1) • u =
          (x - u) + (tail.sum - (tail.length : ℝ) • u) := by module
      simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one, he]
      exact (norm_add_le _ _).trans (by nlinarith only [ht, hxx])
  have hn : (0 : ℝ) < xs.length := by exact_mod_cast Nat.pos_of_ne_zero hne
  have he : (xs.length : ℝ)⁻¹ • xs.sum - u =
      (xs.length : ℝ)⁻¹ • (xs.sum - (xs.length : ℝ) • u) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hn.ne', one_smul]
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hn.le)]
  have hv := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hn.le)
  simpa only [← mul_assoc, inv_mul_cancel₀ hn.ne', one_mul] using hv

lemma coreEnergy_snapshot_gap (p : Params) (f : Fin p.n → p.E → ℝ) (u : p.E)
    (s : LocalCore p) (hs : CoreValid p s) (hi : s.index = 0)
    (hA : 0 < epochWeight p s.epoch)
    (henergy : coreEnergy p f u s ≤ 6 * p.n * p.R ^ 2) :
    objective f s.snapshot - objective f u ≤ 6 * p.R ^ 2 / epochWeight p s.epoch := by
  have ho : s.outputs = [] := List.length_eq_zero_iff.mp (hs.2.trans hi)
  have hn : (0 : ℝ) < p.n := by exact_mod_cast NeZero.pos p.n
  simp only [coreEnergy, ho, List.map_nil, List.sum_nil, mul_zero, hi, Nat.cast_zero,
    sub_zero, zero_add] at henergy
  apply (le_div_iff₀ hA).mpr
  apply (mul_le_mul_iff_left₀ hn).mp
  nlinarith only [henergy, mul_nonneg (div_nonneg hn.le (by norm_num : (0 : ℝ) ≤ 2))
    (sq_nonneg ‖s.dual - u‖)]

structure Hyp (p : Params) (f : Fin p.n → p.E → ℝ) (g : Fin p.n → p.E → p.E)
    (u : p.E) : Prop where
  positive_L0 : 0 < p.L0
  nonnegative_L1 : 0 ≤ p.L1
  nonnegative_G : 0 ≤ p.G
  positive_R : 0 < p.R
  positive_gap : 0 < p.Δ
  positive_accuracy : 0 < p.ε
  convex : ∀ i, ConvexOn ℝ univ (f i)
  gradient : ∀ i x, HasGradientAt (f i) (g i x) x
  continuous : ∀ i, Continuous (g i)
  smooth : ∀ i, CompositeGeneralized.SymmetricSmooth (g i) p.L0 p.L1
  minimizer : IsMinOn (objective f) univ u
  distance : ‖p.x0 - u‖ ≤ p.R
  gap : objective f p.x0 - objective f u ≤ p.Δ
  heterogeneity : (p.n : ℝ)⁻¹ * ∑ i, ‖g i u‖ ≤ p.G

def CoreInvariant (p : Params) (f : Fin p.n → p.E → ℝ) (u : p.E) (s : LocalCore p) : Prop :=
  CoreValid p s ∧ (coreEnergy p f u s ≤ 6 * p.n * p.R ^ 2 →
    ‖s.snapshot - u‖ ≤ 4 * p.R ∧
    objective f s.snapshot - objective f u ≤ 6 * p.R ^ 2 / epochWeight p s.epoch ∧
    ∀ x ∈ s.outputs, ‖x - u‖ ≤ 4 * p.R)

lemma coreStep_invariant (p : Params) (f : Fin p.n → p.E → ℝ) (g : Fin p.n → p.E → p.E)
    (u : p.E) (h : Hyp p f g u) (s : LocalCore p) (hs : CoreInvariant p f u s)
    (hsafe : coreEnergy p f u s ≤ 6 * p.n * p.R ^ 2) (ξ : Fin ((2 * p.n).factorial)) :
    CoreInvariant p f u (coreStep p g s ξ) := by
  have hvalid := coreStep_valid p g s hs.1 ξ
  refine ⟨hvalid, ?_⟩
  intro hnew
  have hA (k : ℕ) := epochWeight_pos p h.positive_L0 h.nonnegative_L1 h.nonnegative_G
    h.positive_R h.positive_gap k
  have ha (k : ℕ) := epochIncrement_pos p h.positive_L0 h.nonnegative_L1 h.nonnegative_G
    h.positive_R.le (hA k)
  have hz := coreEnergy_dual_radius p f u h.minimizer (coreStep p g s ξ) hvalid
    (hA _).le (ha _).le h.positive_R.le hnew
  obtain ⟨hsrad, hsgap, houts⟩ := hs.2 hsafe
  let A := epochWeight p s.epoch
  let a := epochIncrement p A
  let cache := fun i => g i s.snapshot
  let w := snapshotWeights p.L0 p.L1 cache
  let i := drawIndex w ξ
  let y := mix A a s.snapshot s.dual
  let z := s.dual - (a / p.n) • direction w cache i (g i y)
  let out := mix A a s.snapshot z
  have hz' : ‖z - u‖ ≤ 4 * p.R := by
    simpa only [coreStep, z, y, i, w, cache, A, a, apply_ite, LocalCore.dual, ite_self] using hz
  have hout : ‖out - u‖ ≤ 4 * p.R :=
    mix_radius (hA _).le (ha _).le (add_pos (hA _) (ha _)) s.snapshot z u hsrad hz'
  have hlist : ∀ x ∈ out :: s.outputs, ‖x - u‖ ≤ 4 * p.R := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hout
    · exact houts x hx
  by_cases hi : s.index + 1 < p.n
  · simp only [coreStep, ite_eq_left hi]
    exact ⟨hsrad, hsgap, hlist⟩
  · have hlen : (out :: s.outputs).length = p.n := by
      simp only [List.length_cons, hs.1.2]
      have hi0 := hs.1.1
      omega
    have hav := list_average_radius (out :: s.outputs) u (4 * p.R) (by rw [hlen]; exact NeZero.ne p.n) hlist
    rw [hlen] at hav
    have hgap := coreEnergy_snapshot_gap p f u (coreStep p g s ξ) hvalid
      (by simp only [coreStep, ite_eq_right hi]) (hA _) hnew
    simp only [coreStep, ite_eq_right hi] at hgap ⊢
    exact ⟨hav, hgap, by simp⟩

lemma coreStep_energy_bound (p : Params) (f : Fin p.n → p.E → ℝ) (g : Fin p.n → p.E → p.E)
    (u : p.E) (h : Hyp p f g u) (s : LocalCore p) (hs : CoreValid p s)
    (ξ : Fin ((2 * p.n).factorial)) :
    let A := epochWeight p s.epoch
    let a := epochIncrement p A
    let w := snapshotWeights p.L0 p.L1 (fun i => g i s.snapshot)
    let y := mix A a s.snapshot s.dual
    let i := drawIndex w ξ
    let z := s.dual - (a / p.n) • direction w (fun i => g i s.snapshot) i (g i y)
    let out := mix A a s.snapshot z
    coreEnergy p f u (coreStep p g s ξ) ≤
      (A + a) * (s.outputs.map (fun x => objective f x - objective f u)).sum +
      ((p.n : ℝ) - s.index - 1) * A * (objective f s.snapshot - objective f u) +
      ((A + a) * (objective f out - objective f u) + (p.n : ℝ) / 2 * ‖z - u‖ ^ 2) := by
  let A := epochWeight p s.epoch
  let a := epochIncrement p A
  let w := snapshotWeights p.L0 p.L1 (fun i => g i s.snapshot)
  let y := mix A a s.snapshot s.dual
  let i := drawIndex w ξ
  let z := s.dual - (a / p.n) • direction w (fun i => g i s.snapshot) i (g i y)
  let out := mix A a s.snapshot z
  have hA := epochWeight_pos p h.positive_L0 h.nonnegative_L1 h.nonnegative_G
    h.positive_R h.positive_gap s.epoch
  have ha := epochIncrement_pos p h.positive_L0 h.nonnegative_L1 h.nonnegative_G h.positive_R.le hA
  by_cases hi : s.index + 1 < p.n
  · simp only [coreStep, ite_eq_left hi, coreEnergy, List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_one]
    ring_nf
    exact le_rfl
  · have hlen : (out :: s.outputs).length = p.n := by
      simp only [List.length_cons, hs.2]
      have hi0 := hs.1
      omega
    have hh := FiniteSum.objective_list_average (oracle := fun ix => g ix.1 ix.2)
      h.convex h.gradient u (out :: s.outputs) (by rw [hlen]; exact NeZero.ne p.n)
    rw [hlen, List.map_cons, List.sum_cons] at hh
    have hb := mul_le_mul_of_nonneg_left hh (add_pos hA ha).le
    have hidx : (p.n : ℝ) - s.index - 1 = 0 := by
      have hi0 := hs.1
      have heq : s.index + 1 = p.n := by omega
      have heqR : (s.index : ℝ) + 1 = p.n := by exact_mod_cast heq
      linarith
    simp only [coreStep, ite_eq_right hi, coreEnergy, List.map_nil, List.sum_nil, mul_zero,
      Nat.cast_zero, sub_zero, zero_add, epochWeight]
    change (p.n : ℝ) * (A + a) * (objective f ((p.n : ℝ)⁻¹ • (out :: s.outputs).sum) - objective f u) +
      (p.n : ℝ) / 2 * ‖z - u‖ ^ 2 ≤ _
    change _ ≤ (A + a) * (s.outputs.map (fun x => objective f x - objective f u)).sum +
      ((p.n : ℝ) - s.index - 1) * A * (objective f s.snapshot - objective f u) +
      ((A + a) * (objective f out - objective f u) + (p.n : ℝ) / 2 * ‖z - u‖ ^ 2)
    rw [hidx]
    simp only [List.sum_cons]
    dsimp [A, a] at hb ⊢
    nlinarith only [hb]

lemma coreStep_mean (p : Params) (f : Fin p.n → p.E → ℝ) (g : Fin p.n → p.E → p.E)
    (u : p.E) (h : Hyp p f g u) (s : LocalCore p) (hs : CoreInvariant p f u s)
    (hsafe : coreEnergy p f u s ≤ 6 * p.n * p.R ^ 2) :
    (𝔼 ξ : Fin ((2 * p.n).factorial), coreEnergy p f u (coreStep p g s ξ)) ≤ coreEnergy p f u s := by
  classical
  let : NeZero (2 * p.n).factorial := ⟨Nat.factorial_ne_zero _⟩
  let A := epochWeight p s.epoch
  let a := epochIncrement p A
  let w := snapshotWeights p.L0 p.L1 (fun i => g i s.snapshot)
  let M := (∑ i, w i) / p.n
  have hA := epochWeight_pos p h.positive_L0 h.nonnegative_L1 h.nonnegative_G
    h.positive_R h.positive_gap s.epoch
  have ha := epochIncrement_pos p h.positive_L0 h.nonnegative_L1 h.nonnegative_G h.positive_R.le hA
  obtain ⟨hsrad, hsgap, _⟩ := hs.2 hsafe
  have hz := coreEnergy_dual_radius p f u h.minimizer s hs.1 hA.le ha.le h.positive_R.le hsafe
  have hd : ‖s.dual - s.snapshot‖ ≤ 8 * p.R := by
    have hh := norm_sub_le (s.dual - u) (s.snapshot - u)
    rw [show (s.dual - u) - (s.snapshot - u) = s.dual - s.snapshot by module] at hh
    linarith
  have hG : Finset.univ.expect (fun i => ‖g i u‖) ≤ p.G := by
    simpa only [Fintype.expect_eq_sum_div_card, Fintype.card_fin, div_eq_inv_mul] using h.heterogeneity
  have hcurv := average_curvature (g := fun ix => g ix.1 ix.2) h.positive_L0 h.nonnegative_L1
    h.convex h.gradient h.continuous h.smooth h.minimizer hG s.snapshot
  have hm : M ≤ 3 * (p.L0 + p.L1 * p.G) + 204 * (p.L1 * p.R) ^ 2 / A := by
    have hh := mul_le_mul_of_nonneg_left hsgap (show 0 ≤ 34 * p.L1 ^ 2 by positivity)
    have he : 34 * p.L1 ^ 2 * (6 * p.R ^ 2 / A) = 204 * (p.L1 * p.R) ^ 2 / A := by ring
    change 34 * p.L1 ^ 2 * (objective f s.snapshot - objective f u) ≤ _ at hh
    rw [he] at hh
    simp only [Fintype.expect_eq_sum_div_card, Fintype.card_fin] at hcurv
    change M ≤ 3 * (p.L0 + p.L1 * p.G) + 34 * p.L1 ^ 2 *
      (objective f s.snapshot - objective f u) at hcurv
    linarith
  have hn : (1 : ℝ) ≤ p.n := by exact_mod_cast NeZero.pos p.n
  have hL : 0 < p.L0 + p.L1 * p.G := by
    have := h.positive_L0
    have := h.nonnegative_L1
    have := h.nonnegative_G
    positivity
  have hq : 0 ≤ p.L1 * p.R := mul_nonneg h.nonnegative_L1 h.positive_R.le
  have controls := increment_controls hA hL hq hn hm
  change 0 < a ∧ a ≤ A / (1024 * (1 + p.L1 * p.R)) ∧
    a ^ 2 ≤ (p.n : ℝ) * A / (1048576 * (p.L0 + p.L1 * p.G)) ∧
    a * (p.L1 * p.R) ≤ A / 1024 ∧ a ^ 2 * M ≤ (207 / 1048576) * p.n * A at controls
  have hcap : a * p.L1 * p.R ≤ A / 1024 := by nlinarith only [controls.2.2.2.1]
  have hloc := localized_step h.positive_L0 h.nonnegative_L1 hA ha h.convex h.gradient
    h.continuous h.smooth s.snapshot s.dual u hd hcap controls.2.2.2.2
  have hh := Finset.expect_le_expect (s := Finset.univ) (fun ξ _ => coreStep_energy_bound p f g u h s hs.1 ξ)
  simp only [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const] at hh hloc
  dsimp [coreEnergy, A, a, w, mix] at hh hloc ⊢
  nlinarith only [hh, hloc]

lemma initialCore_valid (p : Params) : CoreValid p (initialCore p) :=
  ⟨NeZero.pos p.n, rfl⟩

lemma initialCore_energy (p : Params) (f : Fin p.n → p.E → ℝ) (g : Fin p.n → p.E → p.E)
    (u : p.E) (h : Hyp p f g u) :
    coreEnergy p f u (initialCore p) ≤ (3 / 2) * p.n * p.R ^ 2 := by
  have hΔ := h.positive_gap
  have hg := mul_le_mul_of_nonneg_left h.gap (show 0 ≤ p.R ^ 2 / p.Δ by positivity)
  rw [div_mul_cancel₀ _ hΔ.ne'] at hg
  have hd := pow_le_pow_left₀ (norm_nonneg _) h.distance 2
  have hn : (0 : ℝ) ≤ p.n := Nat.cast_nonneg _
  have hg' := mul_le_mul_of_nonneg_left hg hn
  have hd' := mul_le_mul_of_nonneg_left hd hn
  simp only [coreEnergy, initialCore, epochWeight, List.map_nil, List.sum_nil, mul_zero,
    Nat.cast_zero, sub_zero, zero_add]
  nlinarith only [hg', hd']

lemma initialCore_invariant (p : Params) (f : Fin p.n → p.E → ℝ) (g : Fin p.n → p.E → p.E)
    (u : p.E) (h : Hyp p f g u) : CoreInvariant p f u (initialCore p) := by
  refine ⟨initialCore_valid p, fun _ => ?_⟩
  have hR := h.positive_R
  have hΔ := h.positive_gap
  have he : 6 * p.R ^ 2 / (p.R ^ 2 / p.Δ) = 6 * p.Δ := by field_simp
  simp only [initialCore, epochWeight]
  refine ⟨by nlinarith [h.distance], ?_, by simp⟩
  rw [he]
  nlinarith [h.gap]

lemma coreRun_eq_plainRun (p : Params) (g : Fin p.n → p.E → p.E)
    (k : ℕ) (s : LocalCore p) (ξ : Fin k → Fin ((2 * p.n).factorial)) :
    coreRun p g k s ξ = plainRun (coreStep p g) k s ξ := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => exact ih _ _

lemma coreRun_valid (p : Params) (g : Fin p.n → p.E → p.E)
    (k : ℕ) (s : LocalCore p) (hs : CoreValid p s) (ξ : Fin k → Fin ((2 * p.n).factorial)) :
    CoreValid p (coreRun p g k s ξ) := by
  induction k generalizing s with
  | zero => exact hs
  | succ k ih => exact ih _ (coreStep_valid p g s hs _) _

lemma coreStep_clock (p : Params) (g : Fin p.n → p.E → p.E) (s : LocalCore p)
    (hs : CoreValid p s) (ξ : Fin ((2 * p.n).factorial)) :
    (coreStep p g s ξ).epoch * p.n + (coreStep p g s ξ).index = s.epoch * p.n + s.index + 1 := by
  have hi0 := hs.1
  unfold coreStep
  split_ifs with hi
  · simp only
    omega
  · simp only
    rw [Nat.add_mul]
    omega

lemma coreRun_clock (p : Params) (g : Fin p.n → p.E → p.E)
    (k : ℕ) (s : LocalCore p) (hs : CoreValid p s) (ξ : Fin k → Fin ((2 * p.n).factorial)) :
    (coreRun p g k s ξ).epoch * p.n + (coreRun p g k s ξ).index = s.epoch * p.n + s.index + k := by
  induction k generalizing s with
  | zero => simp [coreRun]
  | succ k ih =>
    rw [coreRun, ih _ (coreStep_valid p g s hs _) _, coreStep_clock p g s hs]
    omega

lemma coreRun_terminal (p : Params) (g : Fin p.n → p.E → p.E)
    (N : ℕ) (ξ : Fin (N * p.n) → Fin ((2 * p.n).factorial)) :
    (coreRun p g (N * p.n) (initialCore p) ξ).epoch = N ∧
      (coreRun p g (N * p.n) (initialCore p) ξ).index = 0 := by
  let s := coreRun p g (N * p.n) (initialCore p) ξ
  have hv := coreRun_valid p g (N * p.n) (initialCore p) (initialCore_valid p) ξ
  have hc := coreRun_clock p g (N * p.n) (initialCore p) (initialCore_valid p) ξ
  change s.epoch * p.n + s.index = 0 * p.n + 0 + N * p.n at hc
  simp only [zero_mul, zero_add] at hc
  have hindex : s.index < p.n := hv.1
  have hi : s.index = 0 := by
    have hh := congrArg (fun k => k % p.n) hc
    simpa only [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_eq_of_lt hindex,
      Nat.mod_mod] using hh
  refine ⟨?_, hi⟩
  rw [hi, add_zero] at hc
  exact mul_right_cancel₀ (NeZero.ne p.n) hc

end OracleTemplate.GeneralizedFiniteSum
