import LongTails.Proofs.NcConcaveChainGrad
import LongTails.Proofs.NcConcavePartThree
import LongTails.Proofs.NcConcaveConcavity

open scoped BigOperators Topology RealInnerProductSpace

namespace LongTails.Proofs.NcConcaveEmbed

open LongTails.Proofs.NcConcaveScalars LongTails.Proofs.NcConcaveTransitions
open LongTails.Proofs.NcConcaveTransitionBounds LongTails.Proofs.NcConcaveInstance
open LongTails.Proofs.NcConcaveModel LongTails.Proofs.NcConcaveLocality
open LongTails.Proofs.NcConcaveAnalysis LongTails.Proofs.NcConcaveChainGrad
open LongTails.Proofs.NcConcavePartThree LongTails.Proofs.NcConcaveConcavity
open LongTails.Setups.StochasticNonconvexConcaveMinimax

variable {d n m : ℕ}

def K (n m : ℕ) : ℕ := n * (m + 4) + 1

lemma pU_lt (j : Fin (n + 1)) : pU m j < K n m := by
  have : (j : ℕ) * (m + 4) ≤ n * (m + 4) := Nat.mul_le_mul_right _ (Nat.lt_succ_iff.mp j.isLt)
  unfold pU K; omega

lemma blk_le (i : Fin n) : (i : ℕ) * (m + 4) + (m + 4) ≤ n * (m + 4) := by
  have : ((i : ℕ) + 1) * (m + 4) ≤ n * (m + 4) := Nat.mul_le_mul_right _ i.isLt
  rw [Nat.add_mul, one_mul] at this; exact this

lemma pA_lt (i : Fin n) : pA m i < K n m := by
  have := blk_le (m := m) i; unfold pA K; omega

lemma pB_lt (i : Fin n) : pB m i < K n m := by
  have := blk_le (m := m) i; unfold pB K; omega

lemma pY_lt (i : Fin n) (k : Fin (m + 1)) : pY m i k < K n m := by
  have := blk_le (m := m) i; have := k.isLt; unfold pY K; omega

def posU (j : Fin (n + 1)) : Fin (K n m) := ⟨pU m j, pU_lt j⟩
def posA (i : Fin n) : Fin (K n m) := ⟨pA m i, pA_lt i⟩
def posB (i : Fin n) : Fin (K n m) := ⟨pB m i, pB_lt i⟩
def posY (i : Fin n) (k : Fin (m + 1)) : Fin (K n m) := ⟨pY m i k, pY_lt i k⟩

lemma pos_mod_div (i r : ℕ) (hr : r < m + 4) :
    (i * (m + 4) + r) % (m + 4) = r ∧ (i * (m + 4) + r) / (m + 4) = i := by
  constructor
  · rw [Nat.mul_add_mod', Nat.mod_eq_of_lt hr]
  · rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hr, add_zero]

lemma pos_inj {i i' r r' : ℕ} (hr : r < m + 4) (hr' : r' < m + 4)
    (h : i * (m + 4) + r = i' * (m + 4) + r') : i = i' ∧ r = r' := by
  have h1 := pos_mod_div (m := m) i r hr
  have h2 := pos_mod_div (m := m) i' r' hr'
  rw [h] at h1
  exact ⟨h1.2.symm.trans h2.2, h1.1.symm.trans h2.1⟩

lemma posU_inj : Function.Injective (posU (n := n) (m := m)) := by
  intro j j' h
  have h' : (j : ℕ) * (m + 4) + 0 = (j' : ℕ) * (m + 4) + 0 := by
    have := congrArg Fin.val h; simpa [posU, pU] using this
  exact Fin.ext (pos_inj (m := m) (by omega) (by omega) h').1

lemma posA_inj : Function.Injective (posA (n := n) (m := m)) := by
  intro j j' h
  have h' : (j : ℕ) * (m + 4) + 1 = (j' : ℕ) * (m + 4) + 1 := by
    have := congrArg Fin.val h; simpa [posA, pA] using this
  exact Fin.ext (pos_inj (m := m) (by omega) (by omega) h').1

lemma posB_inj : Function.Injective (posB (n := n) (m := m)) := by
  intro j j' h
  have h' : (j : ℕ) * (m + 4) + (m + 3) = (j' : ℕ) * (m + 4) + (m + 3) := by
    have := congrArg Fin.val h; simp only [posB, pB] at this; omega
  exact Fin.ext (pos_inj (m := m) (by omega) (by omega) h').1

lemma posA_ne_posB (i j : Fin n) : posA (m := m) i ≠ posB j := by
  intro h
  have h' : (i : ℕ) * (m + 4) + 1 = (j : ℕ) * (m + 4) + (m + 3) := by
    have := congrArg Fin.val h; simp only [posA, posB, pA, pB] at this; omega
  have := (pos_inj (m := m) (by omega) (by omega) h').2
  omega

lemma posY_inj : Function.Injective (fun p : Fin n × Fin (m + 1) => posY (m := m) p.1 p.2) := by
  intro p p' h
  have h' : (p.1 : ℕ) * (m + 4) + (2 + p.2) = (p'.1 : ℕ) * (m + 4) + (2 + p'.2) := by
    have := congrArg Fin.val h; simp only [posY, pY] at this; omega
  have hk := p.2.isLt
  have hk' := p'.2.isLt
  obtain ⟨h1, h2⟩ := pos_inj (m := m) (by omega) (by omega) h'
  exact Prod.ext (Fin.ext h1) (Fin.ext (by omega))

structure Word (d n m : ℕ) where
  w : Fin (K n m) ↪ Fin d

def Word.πU (W : Word d n m) (j : Fin (n + 1)) : Fin d := W.w (posU j)
def Word.πA (W : Word d n m) (i : Fin n) : Fin d := W.w (posA i)
def Word.πB (W : Word d n m) (i : Fin n) : Fin d := W.w (posB i)
def Word.πY (W : Word d n m) (i : Fin n) (k : Fin (m + 1)) : Fin d := W.w (posY i k)

def Word.coords (W : Word d n m) : Coords d n where
  πU := W.πU
  πA := W.πA
  πB := W.πB
  hU := W.w.injective.comp posU_inj
  hA := W.w.injective.comp posA_inj
  hB := W.w.injective.comp posB_inj
  hAB i j h := posA_ne_posB i j (W.w.injective h)

lemma Word.πY_inj (W : Word d n m) :
    Function.Injective (fun p : Fin n × Fin (m + 1) => W.πY p.1 p.2) :=
  W.w.injective.comp posY_inj

noncomputable def selC (W : Word d n m) (s : ℝ) (x : Prim d) (y : Dual d) : CS n m :=
  (fun j => x (0, W.πU j) / s, fun i => x (1, W.πA i) / s, fun i => x (1, W.πB i) / s,
    fun i k => y (W.πY i k) / s)

lemma selC_sub (W : Word d n m) (s : ℝ) (x x' : Prim d) (y y' : Dual d) :
    selC W s x' y' - selC W s x y = selC W s (x' - x) (y' - y) := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · funext j; simp only [selC, Prod.fst_sub, Pi.sub_apply, PiLp.sub_apply]; ring
  · funext j; simp only [selC, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply, PiLp.sub_apply]; ring
  · funext j; simp only [selC, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply, PiLp.sub_apply]; ring
  · funext j k; simp only [selC, Prod.snd_sub, Pi.sub_apply, PiLp.sub_apply]; ring

lemma real_inner_eq_sum {ι : Type*} [Fintype ι] (x y : EuclideanSpace ℝ ι) :
    ⟪x, y⟫ = ∑ i, x i * y i := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma nsq_selC (W : Word d n m) {s : ℝ} (hs : 0 < s) (x : Prim d) (y : Dual d) :
    nsq (selC W s x y).1 (selC W s x y).2.1 (selC W s x y).2.2.1 (selC W s x y).2.2.2 ≤
      (‖x‖ ^ 2 + ‖y‖ ^ 2) / s ^ 2 := by
  have h1 : sq1 (selC W s x y).1 ≤ blockSq x 0 / s ^ 2 := by
    simp only [selC, sq1, div_pow, ← Finset.sum_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact sum_comp_le W.πU W.coords.hU (fun i => x (0, i) ^ 2) (fun _ => sq_nonneg _)
  have h2 : sq2 (selC W s x y).2.1 + sq2 (selC W s x y).2.2.1 ≤ blockSq x 1 / s ^ 2 := by
    simp only [selC, sq2, div_pow, ← Finset.sum_div, ← add_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [blockSq_eq, split_sum2 W.πA W.πB W.coords.hA W.coords.hB W.coords.hAB (fun i => x (1, i) ^ 2)]
    have : 0 ≤ ∑ i ∈ (Finset.univ.map ⟨W.πA, W.coords.hA⟩ ∪ Finset.univ.map ⟨W.πB, W.coords.hB⟩)ᶜ,
        x (1, i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  have h3 : sqY (selC W s x y).2.2.2 ≤ ‖y‖ ^ 2 / s ^ 2 := by
    simp only [selC, sqY, div_pow, ← Finset.sum_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [EuclideanSpace.real_norm_sq_eq, ← Fintype.sum_prod_type']
    exact sum_comp_le (fun p : Fin n × Fin (m + 1) => W.πY p.1 p.2) W.πY_inj (fun i => y i ^ 2)
      (fun _ => sq_nonneg _)
  have hn := norm_sq_prim x
  unfold nsq
  rw [show (‖x‖ ^ 2 + ‖y‖ ^ 2) / s ^ 2 = blockSq x 0 / s ^ 2 + blockSq x 1 / s ^ 2 + ‖y‖ ^ 2 / s ^ 2 by
    rw [hn]; ring]
  linarith

noncomputable def fhat (θ τ : ℝ) (W : Word d n m) (s ℓ : ℝ) (x : Prim d) (y : Dual d) : ℝ :=
  ℓ * s ^ 2 * Fc θ τ (selC W s x y)

def eU (j : Fin (n + 1)) : CS n m := (Pi.single j 1, 0, 0, 0)
def eA (i : Fin n) : CS n m := (0, Pi.single i 1, 0, 0)
def eB (i : Fin n) : CS n m := (0, 0, Pi.single i 1, 0)
def eY (i : Fin n) (k : Fin (m + 1)) : CS n m := (0, 0, 0, Pi.single i (Pi.single k 1))

noncomputable def gradC (θ τ : ℝ) (c : CS n m) : CS n m :=
  (fun j => DFc θ τ c (eU j), fun i => DFc θ τ c (eA i), fun i => DFc θ τ c (eB i),
    fun i k => DFc θ τ c (eY i k))

lemma cs_decomp (v : CS n m) :
    v = ∑ j, v.1 j • eU (m := m) j + ∑ i, v.2.1 i • eA (m := m) i + ∑ i, v.2.2.1 i • eB (m := m) i +
      ∑ i, ∑ k, v.2.2.2 i k • eY i k := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · simp only [Prod.fst_add, Prod.fst_sum, Prod.smul_fst, eU, eA, eB, eY, smul_zero,
      Finset.sum_const_zero, add_zero]
    funext j; simp [Finset.sum_apply, Pi.single_apply]
  · simp only [Prod.snd_add, Prod.fst_add, Prod.snd_sum, Prod.fst_sum, Prod.smul_snd, Prod.smul_fst,
      eU, eA, eB, eY, smul_zero, Finset.sum_const_zero, add_zero, zero_add]
    funext j; simp [Finset.sum_apply, Pi.single_apply]
  · simp only [Prod.snd_add, Prod.fst_add, Prod.snd_sum, Prod.fst_sum, Prod.smul_snd, Prod.smul_fst,
      eU, eA, eB, eY, smul_zero, Finset.sum_const_zero, add_zero, zero_add]
    funext j; simp [Finset.sum_apply, Pi.single_apply]
  · simp only [Prod.snd_add, Prod.snd_sum, Prod.smul_snd, eU, eA, eB, eY, smul_zero,
      Finset.sum_const_zero, zero_add]
    funext i k
    simp [Finset.sum_apply, Pi.single_apply, ite_apply]

lemma DFc_expand (θ τ : ℝ) (c v : CS n m) :
    DFc θ τ c v = ∑ j, (gradC θ τ c).1 j * v.1 j + ∑ i, (gradC θ τ c).2.1 i * v.2.1 i +
      ∑ i, (gradC θ τ c).2.2.1 i * v.2.2.1 i + ∑ i, ∑ k, (gradC θ τ c).2.2.2 i k * v.2.2.2 i k := by
  conv_lhs => rw [cs_decomp v]
  simp only [map_add, map_sum, map_smul, smul_eq_mul, gradC]
  congr 1; congr 1; congr 1
  all_goals first
    | exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    | exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => mul_comm _ _

noncomputable def embX (W : Word d n m) (g : CS n m) : Prim d :=
  WithLp.toLp 2 (fun c => if c.1 = 0 then emb W.πU g.1 c.2 else emb W.πA g.2.1 c.2 + emb W.πB g.2.2.1 c.2)

noncomputable def embY (W : Word d n m) (g : CS n m) : Dual d :=
  WithLp.toLp 2 (fun i => ∑ a, ∑ k, if W.πY a k = i then g.2.2.2 a k else 0)

lemma inner_embX (W : Word d n m) (g : CS n m) (h : Prim d) :
    ⟪embX W g, h⟫ = ∑ j, g.1 j * h (0, W.πU j) + ∑ i, g.2.1 i * h (1, W.πA i) +
      ∑ i, g.2.2.1 i * h (1, W.πB i) := by
  rw [real_inner_eq_sum, Fintype.sum_prod_type, Fin.sum_univ_two]
  have h0 : ∀ i, (embX W g) (0, i) = emb W.πU g.1 i := fun i => by simp [embX]
  have h1 : ∀ i, (embX W g) (1, i) = emb W.πA g.2.1 i + emb W.πB g.2.2.1 i := fun i => by
    simp [embX]
  simp only [h0, h1, add_mul, Finset.sum_add_distrib]
  rw [emb_sum W.πU g.1 (fun i => h (0, i)), emb_sum W.πA g.2.1 (fun i => h (1, i)),
    emb_sum W.πB g.2.2.1 (fun i => h (1, i))]
  ring

lemma inner_embY (W : Word d n m) (g : CS n m) (h : Dual d) :
    ⟪embY W g, h⟫ = ∑ i, ∑ k, g.2.2.2 i k * h (W.πY i k) := by
  rw [real_inner_eq_sum]
  simp only [embY, PiLp.toLp_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]; simp

noncomputable def gxh (θ τ : ℝ) (W : Word d n m) (s ℓ : ℝ) (x : Prim d) (y : Dual d) : Prim d :=
  (ℓ * s) • embX W (gradC θ τ (selC W s x y))

noncomputable def gyh (θ τ : ℝ) (W : Word d n m) (s ℓ : ℝ) (x : Prim d) (y : Dual d) : Dual d :=
  (ℓ * s) • embY W (gradC θ τ (selC W s x y))

lemma DFc_selC (θ τ : ℝ) (W : Word d n m) {s ℓ : ℝ} (hs : 0 < s) (x : Prim d) (y : Dual d)
    (h : Prim d) (k : Dual d) :
    ℓ * s ^ 2 * DFc θ τ (selC W s x y) (selC W s h k) =
      ⟪gxh θ τ W s ℓ x y, h⟫ + ⟪gyh θ τ W s ℓ x y, k⟫ := by
  rw [DFc_expand, gxh, gyh, inner_smul_left, inner_smul_left, inner_embX, inner_embY]
  generalize gradC θ τ (selC W s x y) = G
  simp only [selC, conj_trivial, mul_div_assoc', ← Finset.sum_div]
  have hs0 : s ≠ 0 := hs.ne'
  field_simp

theorem fhat_model {θ τ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hτ : 0 < τ) (W : Word d n m) {s ℓ : ℝ}
    (hs : 0 < s) (hℓ : 0 ≤ ℓ) (B : ℝ) (hB : 0 ≤ B) (x : Prim d) (y : Dual d)
    (ha : sq2 (selC W s x y).2.1 ≤ B ^ 2) (hb : ∀ i, |(selC W s x y).2.2.1 i| ≤ B)
    (x' : Prim d) (y' : Dual d) :
    |fhat θ τ W s ℓ x' y' - fhat θ τ W s ℓ x y - ⟪gxh θ τ W s ℓ x y, x' - x⟫ -
      ⟪gyh θ τ W s ℓ x y, y' - y⟫| ≤ ℓ * cF B * (‖x' - x‖ ^ 2 + ‖y' - y‖ ^ 2) := by
  have hm := Fc_model hθ hθ1 hτ B hB (selC W s x y) (selC W s x' y') ha hb
  rw [selC_sub] at hm
  have hn := nsq_selC W hs (x' - x) (y' - y)
  have e : fhat θ τ W s ℓ x' y' - fhat θ τ W s ℓ x y - ⟪gxh θ τ W s ℓ x y, x' - x⟫ -
      ⟪gyh θ τ W s ℓ x y, y' - y⟫ = ℓ * s ^ 2 * (Fc θ τ (selC W s x' y') - Fc θ τ (selC W s x y) -
        DFc θ τ (selC W s x y) (selC W s (x' - x) (y' - y))) := by
    rw [mul_sub, DFc_selC θ τ W hs x y]
    simp only [fhat]; ring
  rw [e, abs_mul, abs_of_nonneg (by positivity)]
  have hc : 0 ≤ cF B := by unfold cF cP; linarith
  calc ℓ * s ^ 2 * _ ≤ ℓ * s ^ 2 * (cF B * ((‖x' - x‖ ^ 2 + ‖y' - y‖ ^ 2) / s ^ 2)) :=
        mul_le_mul_of_nonneg_left (hm.trans (mul_le_mul_of_nonneg_left hn hc)) (by positivity)
    _ = _ := by field_simp

lemma selC_bounds (W : Word d n m) {s : ℝ} (hs : 0 < s) (x : Prim d) (y : Dual d) :
    sq2 (selC W s x y).2.1 ≤ (‖x‖ / s) ^ 2 ∧ ∀ i, |(selC W s x y).2.2.1 i| ≤ ‖x‖ / s := by
  have hn := nsq_selC W hs x 0
  have e : selC W s x y = ((selC W s x 0).1, (selC W s x 0).2.1, (selC W s x 0).2.2.1,
      (selC W s x y).2.2.2) := rfl
  constructor
  · have h1 := sq1_nonneg (selC W s x 0).1
    have h2 := sq2_nonneg (selC W s x 0).2.2.1
    have h3 := sqY_nonneg (selC W s x 0).2.2.2
    unfold nsq at hn
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at hn
    have : sq2 (selC W s x y).2.1 = sq2 (selC W s x 0).2.1 := rfl
    rw [this, div_pow]; linarith
  · intro i
    have hb : (x (1, W.πB i)) ^ 2 ≤ ‖x‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      exact Finset.single_le_sum (f := fun c => x c ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ _)
    have : |x (1, W.πB i)| ≤ ‖x‖ := by
      rw [← Real.sqrt_sq (abs_nonneg _), sq_abs, ← Real.sqrt_sq (norm_nonneg x)]
      exact Real.sqrt_le_sqrt hb
    simp only [selC, abs_div, abs_of_pos hs]
    exact div_le_div_of_nonneg_right this hs.le

theorem fhat_hasGradientAt_x {θ τ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hτ : 0 < τ) (W : Word d n m)
    {s ℓ : ℝ} (hs : 0 < s) (hℓ : 0 ≤ ℓ) (x : Prim d) (y : Dual d) :
    HasGradientAt (fun x' => fhat θ τ W s ℓ x' y) (gxh θ τ W s ℓ x y) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  apply hasFDerivAt_of_model (C := ℓ * cF (‖x‖ / s))
  intro x'
  obtain ⟨ha, hb⟩ := selC_bounds W hs x y
  have h := fhat_model hθ hθ1 hτ W hs hℓ (‖x‖ / s) (by positivity) x y ha hb x' y
  simp only [sub_self, inner_zero_right, sub_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, add_zero] at h
  simpa only [InnerProductSpace.toDual_apply_apply] using h

theorem fhat_hasGradientAt_y {θ τ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hτ : 0 < τ) (W : Word d n m)
    {s ℓ : ℝ} (hs : 0 < s) (hℓ : 0 ≤ ℓ) (x : Prim d) (y : Dual d) :
    HasGradientAt (fhat θ τ W s ℓ x) (gyh θ τ W s ℓ x y) y := by
  rw [hasGradientAt_iff_hasFDerivAt]
  apply hasFDerivAt_of_model (C := ℓ * cF (‖x‖ / s))
  intro y'
  obtain ⟨ha, hb⟩ := selC_bounds W hs x y
  have h := fhat_model hθ hθ1 hτ W hs hℓ (‖x‖ / s) (by positivity) x y ha hb x y'
  simp only [sub_self, inner_zero_right, sub_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, zero_add] at h
  simpa only [InnerProductSpace.toDual_apply_apply] using h

lemma selC_bounds_feasible (W : Word d n m) {s : ℝ} (hs : 0 < s) (x : Prim d) (y : Dual d)
    (hx : blockSq x 1 ≤ (2 * s) ^ 2) :
    sq2 (selC W s x y).2.1 ≤ 2 ^ 2 ∧ ∀ i, |(selC W s x y).2.2.1 i| ≤ 2 := by
  have h2 : sq2 (selC W s x y).2.1 + sq2 (selC W s x y).2.2.1 ≤ blockSq x 1 / s ^ 2 := by
    simp only [selC, sq2, div_pow, ← Finset.sum_div, ← add_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [blockSq_eq, split_sum2 W.πA W.πB W.coords.hA W.coords.hB W.coords.hAB (fun i => x (1, i) ^ 2)]
    have : 0 ≤ ∑ i ∈ (Finset.univ.map ⟨W.πA, W.coords.hA⟩ ∪ Finset.univ.map ⟨W.πB, W.coords.hB⟩)ᶜ,
        x (1, i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  have h4 : blockSq x 1 / s ^ 2 ≤ 2 ^ 2 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hA := sq2_nonneg (selC W s x y).2.1
  have hB := sq2_nonneg (selC W s x y).2.2.1
  refine ⟨by linarith, fun i => ?_⟩
  have h5 : (selC W s x y).2.2.1 i ^ 2 ≤ sq2 (selC W s x y).2.2.1 :=
    Finset.single_le_sum (f := fun j => (selC W s x y).2.2.1 j ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ i)
  have : (selC W s x y).2.2.1 i ^ 2 ≤ 2 ^ 2 := by linarith
  exact abs_le.mpr (abs_le_of_sq_le_sq' this (by norm_num))

theorem fhat_lipschitz {θ τ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hτ : 0 < τ) (W : Word d n m)
    {s ℓ : ℝ} (hs : 0 < s) (hℓ : 0 ≤ ℓ) (x x' : Prim d) (y y' : Dual d)
    (hx : blockSq x 1 ≤ (2 * s) ^ 2) (hx' : blockSq x' 1 ≤ (2 * s) ^ 2) :
    ‖gxh θ τ W s ℓ x y - gxh θ τ W s ℓ x' y'‖ ^ 2 + ‖gyh θ τ W s ℓ x y - gyh θ τ W s ℓ x' y'‖ ^ 2 ≤
      (6 * (ℓ * cF 2)) ^ 2 * (‖x - x'‖ ^ 2 + ‖y - y'‖ ^ 2) := by
  have hK : 0 ≤ ℓ * cF 2 := mul_nonneg hℓ (by unfold cF cP; norm_num)
  exact pair_lipschitz (fhat θ τ W s ℓ) (gxh θ τ W s ℓ) (gyh θ τ W s ℓ)
    {z | blockSq z.1 1 ≤ (2 * s) ^ 2} (ℓ * cF 2) hK
    (fun z hz x'' y'' => by
      obtain ⟨ha, hb⟩ := selC_bounds_feasible W hs z.1 z.2 hz
      exact fhat_model hθ hθ1 hτ W hs hℓ 2 (by norm_num) z.1 z.2 ha hb x'' y'')
    (x, y) (x', y') hx hx'

theorem fhat_concave {θ τ : ℝ} (hθ : 0 < θ) (hτ : 0 < τ) (W : Word d n m) {s ℓ : ℝ}
    (hs : 0 < s) (hℓ : 0 ≤ ℓ) (x : Prim d) (S : Set (Dual d)) (hS : Convex ℝ S) :
    ConcaveOn ℝ S (fhat θ τ W s ℓ x) := by
  have hblk : ∀ i : Fin n, ConcaveOn ℝ Set.univ (fun y : Dual d =>
      robB θ τ (x (1, W.πA i) / s) (x (1, W.πB i) / s) (fun k => y (W.πY i k) / s)) := by
    intro i
    let g : Dual d →ₗ[ℝ] (Fin (m + 1) → ℝ) :=
      { toFun := fun y k => y (W.πY i k) / s
        map_add' := fun y y' => by funext k; simp only [PiLp.add_apply, Pi.add_apply]; ring
        map_smul' := fun c y => by
          funext k; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, Pi.smul_apply]; ring }
    have := (robB_concave (m := m) hθ hτ (x (1, W.πA i) / s) (x (1, W.πB i) / s)).comp_linearMap g
    exact this
  have hsum : ConcaveOn ℝ Set.univ (fun y : Dual d => ∑ i, robB θ τ (x (1, W.πA i) / s)
      (x (1, W.πB i) / s) (fun k => y (W.πY i k) / s)) := by
    have h := convexOn_finset_sum (Finset.univ : Finset (Fin n))
      (fun i (y : Dual d) => -robB θ τ (x (1, W.πA i) / s) (x (1, W.πB i) / s)
        (fun k => y (W.πY i k) / s)) (fun i _ => (hblk i).neg)
    have h2 := h.neg
    convert h2 using 1
    funext y
    simp [Finset.sum_neg_distrib]
  have hc : ConcaveOn ℝ Set.univ (fhat θ τ W s ℓ x) := by
    have h1 := (hsum.add (concaveOn_const (robP θ (selC W s x 0).1 (selC W s x 0).2.1
      (selC W s x 0).2.2.1) convex_univ)).smul (by positivity : (0 : ℝ) ≤ ℓ * s ^ 2)
    convert h1 using 1
    funext y
    simp only [fhat, Fc, robF, selC, Pi.add_apply, smul_eq_mul]
    ring
  exact hc.subset (Set.subset_univ _) hS

end LongTails.Proofs.NcConcaveEmbed
