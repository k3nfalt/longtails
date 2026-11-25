import LongTails.Proofs.NcConcaveEmbed

open scoped BigOperators Topology RealInnerProductSpace

namespace LongTails.Proofs.NcConcaveValue

open LongTails.Proofs.NcConcaveScalars LongTails.Proofs.NcConcaveTransitions
open LongTails.Proofs.NcConcaveTransitionBounds LongTails.Proofs.NcConcavePsi
open LongTails.Proofs.NcConcaveInstance LongTails.Proofs.NcConcaveBlock
open LongTails.Proofs.NcConcaveModel LongTails.Proofs.NcConcaveLocality
open LongTails.Proofs.NcConcaveAnalysis LongTails.Proofs.NcConcaveChainGrad
open LongTails.Proofs.NcConcavePartThree LongTails.Proofs.NcConcaveEmbed
open LongTails.Proofs.NcConcaveProx
open LongTails.Setups.StochasticNonconvexConcaveMinimax

variable {d n m : ℕ}

noncomputable def fsg (τ : ℝ) (W : Word d n m) (s ℓ : ℝ) (x : Prim d) (y : Dual d) : ℝ :=
  ℓ * s ^ 2 * baseF τ (selC W s x y).1 (selC W s x y).2.1 (selC W s x y).2.2.1 (selC W s x y).2.2.2

noncomputable def emb2 {ι : Type*} [Fintype ι] (π : ι → Fin d) (g : ι → ℝ) (i : Fin d) : ℝ :=
  ∑ p, if π p = i then g p else 0

lemma emb2_apply {ι : Type*} [Fintype ι] {π : ι → Fin d} (hπ : Function.Injective π) (g : ι → ℝ)
    (p : ι) : emb2 π g (π p) = g p := by
  simp only [emb2]
  rw [Finset.sum_eq_single p]
  · simp
  · intro p' _ hp'; rw [ite_eq_right (fun h => hp' (hπ h))]
  · simp

lemma emb2_sq {ι : Type*} [Fintype ι] {π : ι → Fin d} (hπ : Function.Injective π) (g : ι → ℝ) :
    ∑ i, emb2 π g i ^ 2 = ∑ p, g p ^ 2 := by
  classical
  rw [← Finset.sum_add_sum_compl (Finset.univ.map ⟨π, hπ⟩), Finset.sum_map]
  have h0 : ∑ i ∈ (Finset.univ.map ⟨π, hπ⟩)ᶜ, emb2 π g i ^ 2 = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have : emb2 π g i = 0 := by
      simp only [emb2]
      apply Finset.sum_eq_zero; intro p _
      rw [ite_eq_right]; intro h; apply Finset.mem_compl.mp hi
      simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
      exact ⟨p, h⟩
    rw [this]; ring
  rw [h0, add_zero]
  exact Finset.sum_congr rfl fun p _ => by simp only [Function.Embedding.coeFn_mk, emb2_apply hπ]

noncomputable def ystarY (W : Word d n m) (s : ℝ) (x : Prim d) : Dual d :=
  WithLp.toLp 2 (emb2 (fun p : Fin n × Fin (m + 1) => W.πY p.1 p.2)
    (fun p => s * ystar (m := m) (x (1, W.πA p.1) / s) (x (1, W.πB p.1) / s) p.2))

lemma selC_ystar (W : Word d n m) {s : ℝ} (hs : 0 < s) (x : Prim d) (y : Dual d) :
    (selC W s x (ystarY W s x)).2.2.2 =
      fun a k => ystar (m := m) ((selC W s x y).2.1 a) ((selC W s x y).2.2.1 a) k := by
  funext a k
  simp only [selC, ystarY, PiLp.toLp_apply]
  rw [emb2_apply (π := fun p : Fin n × Fin (m + 1) => W.πY p.1 p.2) W.πY_inj _ (a, k)]
  field_simp

lemma ystarY_norm (W : Word d n m) {s : ℝ} (hs : 0 < s) (x : Prim d)
    (hx : blockSq x 1 ≤ (2 * s) ^ 2) : ‖ystarY W s x‖ ^ 2 ≤ 8 * (s * (m + 1)) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [ystarY, PiLp.toLp_apply]
  rw [emb2_sq W.πY_inj, Fintype.sum_prod_type]
  obtain ⟨ha, hb⟩ := selC_bounds_feasible W hs x 0 hx
  have h2 : sq2 (selC W s x 0).2.1 + sq2 (selC W s x 0).2.2.1 ≤ 4 := by
    have h2 : sq2 (selC W s x 0).2.1 + sq2 (selC W s x 0).2.2.1 ≤ blockSq x 1 / s ^ 2 := by
      simp only [selC, sq2, div_pow, ← Finset.sum_div, ← add_div]
      apply div_le_div_of_nonneg_right _ (by positivity)
      rw [blockSq_eq, split_sum2 W.πA W.πB W.coords.hA W.coords.hB W.coords.hAB (fun i => x (1, i) ^ 2)]
      have : 0 ≤ ∑ i ∈ (Finset.univ.map ⟨W.πA, W.coords.hA⟩ ∪ Finset.univ.map ⟨W.πB, W.coords.hB⟩)ᶜ,
          x (1, i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      linarith
    have h4 : blockSq x 1 / s ^ 2 ≤ 4 := by rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have hpt : ∀ a : Fin n, ∑ k : Fin (m + 1), (s * ystar (m := m) (x (1, W.πA a) / s)
      (x (1, W.πB a) / s) k) ^ 2 ≤ s ^ 2 * (2 * (m + 1) ^ 2 *
        ((x (1, W.πA a) / s) ^ 2 + (x (1, W.πB a) / s) ^ 2)) := by
    intro a
    simp only [mul_pow, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (ystar_sq_le _ _) (sq_nonneg _)
  calc _ ≤ ∑ a : Fin n, s ^ 2 * (2 * (m + 1) ^ 2 *
        ((x (1, W.πA a) / s) ^ 2 + (x (1, W.πB a) / s) ^ 2)) := Finset.sum_le_sum fun a _ => hpt a
    _ = s ^ 2 * (2 * (m + 1) ^ 2) * (sq2 (selC W s x 0).2.1 + sq2 (selC W s x 0).2.2.1) := by
        simp only [← Finset.mul_sum, sq2, selC, Finset.sum_add_distrib]; ring
    _ ≤ s ^ 2 * (2 * (m + 1) ^ 2) * 4 := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

lemma phiW_selC (W : Word d n m) (s ℓ : ℝ) (x : Prim d) (y : Dual d) :
    phiW W.coords s ℓ x = ℓ * s ^ 2 * psi (selC W s x y).1 (selC W s x y).2.1 (selC W s x y).2.2.1 :=
  rfl

theorem fsg_le (W : Word d n m) {s ℓ τ : ℝ} (hs : 0 < s) (hℓ : 0 ≤ ℓ) (hτ : alpha m ≤ τ)
    (x : Prim d) (hx : blockSq x 1 ≤ (2 * s) ^ 2) (y : Dual d) :
    fsg τ W s ℓ x y ≤ phiW W.coords s ℓ x := by
  obtain ⟨-, hb⟩ := selC_bounds_feasible W hs x y hx
  have hα := alpha_pos m
  have hτ0 : 0 < τ := lt_of_lt_of_le hα hτ
  have hb' : ∀ i, |alpha m * (selC W s x y).2.2.1 i / 2| ≤ τ := by
    intro i
    rw [abs_div, abs_mul, abs_of_pos hα, abs_two]
    have := hb i
    nlinarith
  rw [fsg, phiW_selC W s ℓ x y]
  exact mul_le_mul_of_nonneg_left (baseF_le τ hτ0 _ _ _ hb' _) (by positivity)

theorem fsg_star (W : Word d n m) {s ℓ τ : ℝ} (hs : 0 < s) (hτ : alpha m ≤ τ)
    (x : Prim d) (hx : blockSq x 1 ≤ (2 * s) ^ 2) :
    fsg τ W s ℓ x (ystarY W s x) = phiW W.coords s ℓ x := by
  obtain ⟨-, hb⟩ := selC_bounds_feasible W hs x 0 hx
  have hα := alpha_pos m
  have hτ0 : 0 < τ := lt_of_lt_of_le hα hτ
  have hb' : ∀ i, |alpha m * (selC W s x 0).2.2.1 i / 2| ≤ τ := by
    intro i
    rw [abs_div, abs_mul, abs_of_pos hα, abs_two]
    have := hb i
    nlinarith
  rw [fsg, phiW_selC W s ℓ x 0, selC_ystar W hs x 0]
  have := baseF_star (m := m) τ hτ0 (selC W s x 0).1 (selC W s x 0).2.1 (selC W s x 0).2.2.1 hb'
  rw [← this]
  rfl

theorem fhat_close (W : Word d n m) {s ℓ θ τ RU D : ℝ} (hs : 0 < s) (hℓ : 0 ≤ ℓ) (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) (hτ : 0 < τ) (hτ2 : τ ≤ 2) (x : Prim d) (hx : x ∈ primBall RU (2 * s))
    (hRU : 0 ≤ RU) (y : Dual d) (hy : ‖y‖ ≤ D / 2) :
    |fhat θ τ W s ℓ x y - fsg τ W s ℓ x y| ≤
      ℓ * s ^ 2 * (θ * closeBound n m (RU / s) (D / 2 / s)) := by
  obtain ⟨ha, hb⟩ := selC_bounds_feasible W hs x y hx.2
  have hcoord : ∀ (t B : ℝ), t ^ 2 ≤ B ^ 2 → 0 ≤ B → |t| ≤ B := fun t B h hB =>
    abs_le.mpr (abs_le_of_sq_le_sq' h hB)
  have hU : ∀ j, |(selC W s x y).1 j| ≤ RU / s := by
    intro j
    have h1 : x (0, W.πU j) ^ 2 ≤ blockSq x 0 :=
      Finset.single_le_sum (f := fun i => x (0, i) ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ _)
    simp only [selC, abs_div, abs_of_pos hs]
    exact div_le_div_of_nonneg_right (hcoord _ _ (h1.trans hx.1) hRU) hs.le
  have hA : ∀ i, |(selC W s x y).2.1 i| ≤ 2 := by
    intro i
    have h1 : (selC W s x y).2.1 i ^ 2 ≤ sq2 (selC W s x y).2.1 :=
      Finset.single_le_sum (f := fun j => (selC W s x y).2.1 j ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ i)
    exact hcoord _ _ (h1.trans ha) (by norm_num)
  have hY : ∀ i k, |(selC W s x y).2.2.2 i k| ≤ D / 2 / s := by
    intro i k
    have h1 : y (W.πY i k) ^ 2 ≤ ‖y‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      exact Finset.single_le_sum (f := fun c => y c ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ _)
    have h2 : |y (W.πY i k)| ≤ D / 2 :=
      hcoord _ _ (h1.trans (pow_le_pow_left₀ (norm_nonneg _) hy 2)) ((norm_nonneg _).trans hy)
    simp only [selC, abs_div, abs_of_pos hs]
    exact div_le_div_of_nonneg_right h2 hs.le
  have h := robF_close hθ hθ1 hτ hτ2 (selC W s x y).1 (selC W s x y).2.1 (selC W s x y).2.2.1
    (selC W s x y).2.2.2 (RU / s) (D / 2 / s) hU hA hb hY
  rw [fhat, fsg, Fc, ← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left h (by positivity)

noncomputable def Vf (θ τ : ℝ) (W : Word d n m) (s ℓ : ℝ) (Y : Set (Dual d)) (x : Prim d) : ℝ :=
  sSup (fhat θ τ W s ℓ x '' Y)

theorem Vf_close (W : Word d n m) {s ℓ θ τ RU D η : ℝ} (hs : 0 < s) (hℓ : 0 ≤ ℓ) (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) (hτα : alpha m ≤ τ) (hτ2 : τ ≤ 2) (hRU : 0 ≤ RU)
    (hη : ℓ * s ^ 2 * (θ * closeBound n m (RU / s) (D / 2 / s)) ≤ η)
    (hD : 8 * (s * (m + 1)) ^ 2 ≤ (D / 2) ^ 2) (hD0 : 0 ≤ D)
    (x : Prim d) (hx : x ∈ primBall RU (2 * s)) :
    |Vf θ τ W s ℓ (Metric.closedBall 0 (D / 2)) x - phiW W.coords s ℓ x| ≤ η := by
  have hτ : 0 < τ := lt_of_lt_of_le (alpha_pos m) hτα
  set Y := Metric.closedBall (0 : Dual d) (D / 2)
  have hup : ∀ y ∈ Y, fhat θ τ W s ℓ x y ≤ phiW W.coords s ℓ x + η := by
    intro y hy
    have hy' : ‖y‖ ≤ D / 2 := by simpa [Y] using hy
    have h1 := (abs_le.mp (fhat_close W hs hℓ hθ hθ1 hτ hτ2 x hx hRU y hy')).2
    have h2 := fsg_le W hs hℓ hτα x hx.2 y
    linarith
  have hstar : ystarY W s x ∈ Y := by
    have := ystarY_norm W hs x hx.2
    simp only [Y, Metric.mem_closedBall, dist_zero_right]
    have h0 : 0 ≤ D / 2 := by linarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) h0 (by norm_num)).mp (this.trans hD)
  have hne : (fhat θ τ W s ℓ x '' Y).Nonempty := ⟨_, Set.mem_image_of_mem _ hstar⟩
  have hbdd : BddAbove (fhat θ τ W s ℓ x '' Y) := ⟨phiW W.coords s ℓ x + η, by
    rintro _ ⟨y, hy, rfl⟩; exact hup y hy⟩
  rw [abs_le]
  constructor
  · have h1 : fhat θ τ W s ℓ x (ystarY W s x) ≤ Vf θ τ W s ℓ Y x :=
      le_csSup hbdd (Set.mem_image_of_mem _ hstar)
    have h2 := (abs_le.mp (fhat_close W hs hℓ hθ hθ1 hτ hτ2 x hx hRU (ystarY W s x)
      (by simpa [Y] using hstar))).1
    have h3 := fsg_star (ℓ := ℓ) W hs hτα x hx.2
    linarith
  · have : Vf θ τ W s ℓ Y x ≤ phiW W.coords s ℓ x + η :=
      csSup_le hne (by rintro _ ⟨y, hy, rfl⟩; exact hup y hy)
    linarith

theorem fhat_midpoint {θ τ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hτ : 0 < τ) (W : Word d n m)
    {s ℓ : ℝ} (hs : 0 < s) (hℓ : 0 ≤ ℓ) (z w : Prim d) (y : Dual d)
    (hm : blockSq ((1 / 2 : ℝ) • z + (1 / 2 : ℝ) • w) 1 ≤ (2 * s) ^ 2) :
    fhat θ τ W s ℓ ((1 / 2 : ℝ) • z + (1 / 2 : ℝ) • w) y ≤
      fhat θ τ W s ℓ z y / 2 + fhat θ τ W s ℓ w y / 2 + ℓ * cF 2 * ‖z - w‖ ^ 2 / 4 := by
  set c := (1 / 2 : ℝ) • z + (1 / 2 : ℝ) • w
  obtain ⟨ha, hb⟩ := selC_bounds_feasible W hs c y hm
  have h1 := (abs_le.mp (fhat_model hθ hθ1 hτ W hs hℓ 2 (by norm_num) c y ha hb z y)).1
  have h2 := (abs_le.mp (fhat_model hθ hθ1 hτ W hs hℓ 2 (by norm_num) c y ha hb w y)).1
  have ez : z - c = (1 / 2 : ℝ) • (z - w) := by simp only [c]; module
  have ew : w - c = -((1 / 2 : ℝ) • (z - w)) := by simp only [c]; module
  rw [ez] at h1; rw [ew] at h2
  simp only [sub_self, inner_zero_right, norm_zero, inner_neg_right, norm_neg, norm_smul,
    inner_smul_right] at h1 h2
  have hn : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by norm_num
  rw [hn] at h1 h2
  nlinarith

end LongTails.Proofs.NcConcaveValue
