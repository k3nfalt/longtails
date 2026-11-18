import LongTails.Algorithms.DistributedLocalExtragradientWarmStart
import LongTails.Proofs.AdaptiveEntropicCenter
import LongTails.Proofs.DistributedJacobianStrongGrowthProjection
import LongTails.Proofs.LocalExtragradientQuantization

namespace LongTails.Proofs.DistributedJacobianStrongGrowthMedian

lemma sorted_mapped_middle_interval {α : Type*} [LinearOrder α]
    (l : List α) (default : α) (f : α → ℝ) (hf : Monotone f) (a b : ℝ)
    (hg : l.length < 2 * l.countP (fun x => decide (a ≤ f x ∧ f x ≤ b))) :
    a ≤ f ((l.mergeSort (· ≤ ·)).getD (l.length / 2) default) ∧
      f ((l.mergeSort (· ≤ ·)).getD (l.length / 2) default) ≤ b := by
  classical
  let sorted := l.mergeSort (· ≤ ·)
  have hsorted : (sorted.map f).SortedLE := by
    apply List.Pairwise.sortedLE
    apply List.pairwise_map.mpr
    exact (List.sortedLE_mergeSort (l := l)).pairwise.imp (fun h => hf h)
  have hperm : sorted.Perm l := List.mergeSort_perm _ _
  have hmajor : (sorted.map f).length <
      2 * (sorted.map f).countP (fun x => decide (a ≤ x ∧ x ≤ b)) := by
    simp only [List.length_map, List.countP_map]
    rw [hperm.length_eq, hperm.countP_eq]
    exact hg
  have hh := OracleTemplate.AdaptiveHeavyTailSimplex.sorted_middle_interval
    (sorted.map f) hsorted a b hmajor
  have hlen : (sorted.map f).length = l.length := by rw [List.length_map, hperm.length_eq]
  have hk : l.length / 2 < (sorted.map f).length := by
    have hc := List.countP_le_length (p := fun x => decide (a ≤ f x ∧ f x ≤ b)) (l := l)
    rw [hlen]
    omega
  rw [hlen] at hh
  have he : (sorted.map f).getD (l.length / 2) 0 = (sorted.map f).getD (l.length / 2) (f default) := by
    rw [List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ hk]
  rw [he, List.getD_map] at hh
  exact hh

open LongTails.Algorithms.DistributedQuantization
open LongTails.Algorithms.DistributedLocalExtragradientWarmStart

lemma medianGrid_coordinate_bound {n d width : ℕ} (codes : Fin n → Grid d width)
    (spacing : ℝ) (hs : 0 ≤ spacing) (bad : Fin n → Bool)
    (y : EuclideanSpace ℝ (Fin d)) (a : ℝ)
    (hgood : ∀ i, ¬ bad i → ∀ j, |reconstruct spacing (codes i) j - y j| ≤ a)
    (hbad : (∑ i, if bad i then (1 : ℝ) else 0) < (n : ℝ) / 2) (j : Fin d) :
    |reconstruct spacing (medianGrid codes) j - y j| ≤ a := by
  classical
  let f : Fin (2 ^ width) → ℝ := fun z => spacing * ((z.val : ℝ) - ((2 ^ width - 1 : ℕ) : ℝ) / 2)
  have hf : Monotone f := by
    intro x z hxz
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right (by exact_mod_cast hxz : (x.val : ℝ) ≤ z.val) _) hs
  let pred : Fin (2 ^ width) → Bool := fun z => decide (y j - a ≤ f z ∧ f z ≤ y j + a)
  have hcount : (∑ i, if bad i then (0 : ℝ) else 1) ≤
      ((List.ofFn (fun i => codes i j)).countP pred : ℝ) := by
    rw [OracleTemplate.AdaptiveHeavyTailSimplex.countP_ofFn_real]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : bad i
    · simp only [ite_eq_left hi]
      split_ifs <;> norm_num
    · have hb := abs_le.mp (hgood i hi j)
      have hp : pred (codes i j) = true := by
        simp only [pred, decide_eq_true_eq]
        change y j - a ≤ reconstruct spacing (codes i) j ∧ reconstruct spacing (codes i) j ≤ y j + a
        constructor <;> linarith
      simp [hi, hp]
  have he : (∑ i, if bad i then (0 : ℝ) else 1) =
      (n : ℝ) - ∑ i, if bad i then (1 : ℝ) else 0 := by
    calc
      _ = ∑ i, ((1 : ℝ) - if bad i then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> norm_num
      _ = _ := by rw [Finset.sum_sub_distrib]; simp
  rw [he] at hcount
  have hnat : n < 2 * (List.ofFn (fun i => codes i j)).countP pred := by
    have hreal : (n : ℝ) < 2 * ((List.ofFn (fun i => codes i j)).countP pred : ℝ) := by linarith
    exact_mod_cast hreal
  have hh := sorted_mapped_middle_interval (List.ofFn (fun i => codes i j)) 0 f hf
    (y j - a) (y j + a) (by simpa only [List.length_ofFn] using hnat)
  simp only [List.length_ofFn] at hh
  change y j - a ≤ reconstruct spacing (medianGrid codes) j ∧
    reconstruct spacing (medianGrid codes) j ≤ y j + a at hh
  exact abs_le.mpr ⟨by linarith [hh.1], by linarith [hh.2]⟩

lemma medianGrid_accuracy {n d width : ℕ} (codes : Fin n → Grid d width)
    (spacing : ℝ) (hs : 0 ≤ spacing) (bad : Fin n → Bool)
    (y : EuclideanSpace ℝ (Fin d)) (a : ℝ) (ha : 0 ≤ a)
    (hgood : ∀ i, ¬ bad i → ∀ j, |reconstruct spacing (codes i) j - y j| ≤ a)
    (hbad : (∑ i, if bad i then (1 : ℝ) else 0) < (n : ℝ) / 2) :
    ‖reconstruct spacing (medianGrid codes) - y‖ ≤ Real.sqrt d * a := by
  have hb : ‖reconstruct spacing (medianGrid codes) - y‖ ^ 2 ≤ (d : ℝ) * a ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _ : Fin d, a ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        have hh := medianGrid_coordinate_bound codes spacing hs bad y a hgood hbad j
        have hh' := (sq_le_sq₀ (abs_nonneg _) ha).mpr hh
        simpa only [sq_abs, PiLp.sub_apply] using hh'
      _ = _ := by simp
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  exact hb

open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradient

lemma warmCenter_global (p : Params) (s width : ℕ) (spacing : ℝ)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω) (hR : 0 ≤ p.R) :
    ‖warmCenter p s width spacing g samples - p.x0‖ ≤ p.R :=
  DistributedJacobianStrongGrowthProjection.projectBall_mem p p.x0 _ hR

lemma warmCenter_accuracy (p : Params) (s width : ℕ) (spacing : ℝ) (hs : 0 < spacing)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω)
    (y : Point p) (a : ℝ) (ha : 0 ≤ a) (hR : 0 ≤ p.R) (hy : ‖y - p.x0‖ ≤ p.R)
    (hrange : p.R ≤ spacing * ((2 ^ width - 1 : ℕ) : ℝ) / 2)
    (bad : Fin p.n → Bool)
    (hgood : ∀ i, ¬ bad i →
      ‖LongTails.Algorithms.LocalNonlinearExtragradient.warmRun (p.μ / (p.ρ * p.L ^ 2))
        (g i) p.x0 (fun j => samples (p.n * j + i.val)) s - y‖ ≤ a)
    (hbad : (∑ i, if bad i then (1 : ℝ) else 0) < (p.n : ℝ) / 2) :
    ‖warmCenter p s width spacing g samples - y‖ ≤ Real.sqrt p.d * (a + spacing) := by
  let codes := warmCodes p s width spacing g samples
  have hcoord (i : Fin p.n) (hi : ¬ bad i) (j : Fin p.d) :
      |reconstruct spacing (codes i) j - (y - p.x0) j| ≤ a + spacing := by
    let v := warmPoint p s g i samples - p.x0
    have hv : ‖v‖ ≤ p.R :=
      DistributedJacobianStrongGrowthProjection.projectBall_mem p p.x0 _ hR
    have hvj : |v j| ≤ spacing * ((2 ^ width - 1 : ℕ) : ℝ) / 2 := by
      simpa only [Real.norm_eq_abs] using ((PiLp.norm_apply_le v j).trans hv).trans hrange
    have hquant := DistributedQuantization.coordinate_error p.d width spacing hs v j hvj
    have hdist : ‖warmPoint p s g i samples - y‖ ≤ a :=
      (DistributedJacobianStrongGrowthProjection.projectBall_distance p p.x0 _ y hR hy).trans (hgood i hi)
    have hpoint : |v j - (y - p.x0) j| ≤ a := by
      have hh := (PiLp.norm_apply_le (warmPoint p s g i samples - y) j).trans hdist
      simpa only [v, PiLp.sub_apply, Real.norm_eq_abs, sub_sub_sub_cancel_right] using hh
    calc
      _ = |(reconstruct spacing (codes i) j - v j) + (v j - (y - p.x0) j)| := by
        rw [sub_add_sub_cancel]
      _ ≤ |reconstruct spacing (codes i) j - v j| + |v j - (y - p.x0) j| := abs_add_le _ _
      _ ≤ spacing + a := add_le_add hquant hpoint
      _ = _ := add_comm _ _
  have hm := medianGrid_accuracy codes spacing hs.le bad (y - p.x0) (a + spacing)
    (by positivity) hcoord hbad
  have hp := DistributedJacobianStrongGrowthProjection.projectBall_distance p p.x0
    (p.x0 + reconstruct spacing (medianGrid codes)) y hR hy
  have he : p.x0 + reconstruct spacing (medianGrid codes) - y =
      reconstruct spacing (medianGrid codes) - (y - p.x0) := by abel
  rw [he] at hp
  exact hp.trans hm

end LongTails.Proofs.DistributedJacobianStrongGrowthMedian
