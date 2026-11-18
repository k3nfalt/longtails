import LongTails.Algorithms.DistributedNormalizedDownlink
import LongTails.Proofs.DistributedSparseCompression
import LongTails.Proofs.Clipping

open MeasureTheory

namespace LongTails.Proofs.DistributedNormalizedMeasurability

open LongTails.Setups.DistributedHessianLipschitzNonconvex
open LongTails.Algorithms.DistributedNormalizedDownlink

attribute [local irreducible] LongTails.Algorithms.DistributedNormalizedCompression.fullReceive
  LongTails.Algorithms.DistributedRandomRounding.message

variable {Z : Type*} [MeasurableSpace Z]

lemma measurable_draw (p : Params) {D : Z → Draws p} (hD : Measurable D)
    (phase : ℕ) (i : Fin p.n) (j : ℕ) : Measurable (fun z => D z phase i j) :=
  (measurable_pi_apply j).comp ((measurable_pi_apply i).comp
    ((measurable_pi_apply phase).comp hD))

set_option maxHeartbeats 800000 in
lemma measurable_uplink (p : Params) (cfg : Config) {D : Z → Draws p}
    {v : Z → Point p} (hD : Measurable D) (hv : Measurable v)
    (k : ℕ) (i : Fin p.n) : Measurable (fun z =>
      uplinkReceive p cfg (D z) k i (uplinkMessage p cfg (D z) k i (v z))) := by
  have hc := (OracleTemplate.measurable_clip cfg.clipRadius).comp hv
  unfold uplinkReceive uplinkMessage
  cases h : cfg.fullUplink
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact (DistributedSparseCompression.measurable_sparse_message_joint
      cfg.uplinkWidth cfg.uplinkCount cfg.uplinkSpacing).comp
      (hc.prodMk (Measurable.of_eval fun (q : Fin cfg.uplinkCount) => measurable_draw p hD (2 * k) i q.val))
  · simp only [↓reduceIte]
    exact (DistributedSparseCompression.measurable_full_message_joint
      p.d cfg.uplinkWidth cfg.uplinkSpacing).comp
      (hc.prodMk (Measurable.of_eval fun (q : Fin p.d) =>
        measurable_snd.comp (measurable_draw p hD (2 * k) i q.val)))

set_option maxHeartbeats 800000 in
lemma measurable_downlink (p : Params) (cfg : Config) {D : Z → Draws p}
    {x u v : Z → Point p} (hD : Measurable D) (hx : Measurable x)
    (hu : Measurable u) (hv : Measurable v) (k : ℕ) (i : Fin p.n) :
    Measurable (fun z => downlinkReceive p cfg (D z) k i (v z)
      (downlinkMessage p cfg (D z) k i (x z) (u z))) := by
  unfold downlinkReceive downlinkMessage
  cases h : refresh cfg k
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact hv.add ((DistributedSparseCompression.measurable_sparse_message_joint
      cfg.downlinkWidth cfg.downlinkCount cfg.incrementSpacing).comp
      (hu.prodMk (Measurable.of_eval fun (q : Fin cfg.downlinkCount) => measurable_draw p hD (2 * k + 1) i q.val)))
  · simp only [↓reduceIte]
    exact measurable_const.add ((DistributedSparseCompression.measurable_full_message_joint
      p.d cfg.downlinkWidth cfg.refreshSpacing).comp
      ((hx.sub measurable_const).prodMk (Measurable.of_eval fun (q : Fin p.d) =>
        measurable_snd.comp (measurable_draw p hD (2 * k + 1) i q.val))))

lemma measurable_batch (p : Params) (cfg : Config)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (hg : ∀ i, Measurable (Function.uncurry (g i)))
    {S : Z → LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams}
    {x : Z → Point p} (hS : Measurable S) (hx : Measurable x)
    (k : ℕ) (i : Fin p.n) :
    Measurable (fun z => batchMean p cfg g (S z) k i (x z)) := by
  unfold batchMean
  apply Measurable.fun_const_smul
  apply Finset.measurable_sum
  intro j _
  exact (hg i).comp (hx.prodMk ((measurable_pi_apply (k * cfg.batch + j)).comp
    ((measurable_pi_apply i).comp hS)))

lemma measurable_estimator (p : Params) (cfg : Config)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (hg : ∀ i, Measurable (Function.uncurry (g i)))
    {D : Z → Draws p}
    {S : Z → LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams}
    {s : Z → Iterate p} (hD : Measurable D) (hS : Measurable S)
    (hs : ∀ i, Measurable (fun z => (s z).workers i)) (k : ℕ) :
    Measurable (fun z => estimator p cfg (D z) g (S z) k (s z)) := by
  unfold estimator
  apply Measurable.fun_const_smul
  apply Finset.measurable_sum
  intro i _
  exact measurable_uplink p cfg hD (measurable_batch p cfg g hg hS (hs i) k i) k i

lemma measurable_increment (p : Params) (cfg : Config) {v : Z → Point p}
    (hv : Measurable v) : Measurable (fun z => increment cfg (v z)) :=
  ((measurable_const.div hv.norm).neg).smul hv

lemma measurable_trajectory (p : Params) (cfg : Config)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (hg : ∀ i, Measurable (Function.uncurry (g i)))
    {D : Z → Draws p}
    {S : Z → LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams}
    (hD : Measurable D) (hS : Measurable S) (k : ℕ) :
    Measurable (fun z => (trajectory p cfg (D z) g (S z) k).root) ∧
      ∀ i, Measurable (fun z => (trajectory p cfg (D z) g (S z) k).workers i) := by
  induction k with
  | zero => exact ⟨measurable_const, fun _ => measurable_const⟩
  | succ k ih =>
    have he := measurable_estimator p cfg g hg hD hS ih.2 k
    have hu := measurable_increment p cfg he
    have hx := ih.1.add hu
    exact ⟨hx, fun i => measurable_downlink p cfg hD hx hu (ih.2 i) k i⟩

lemma measurable_output (p : Params) (cfg : Config)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (hg : ∀ i, Measurable (Function.uncurry (g i)))
    {D : Z → Draws p}
    {S : Z → LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams}
    {I : Z → Fin cfg.iterations}
    (hD : Measurable D) (hS : Measurable S) (hI : Measurable I) :
    Measurable (fun z => output p cfg (D z) g (S z) (I z)) := by
  have h : Measurable (fun w : Z × Fin cfg.iterations =>
      (trajectory p cfg (D w.1) g (S w.1) w.2.val).root) :=
    measurable_from_prod_countable_left fun i =>
      (measurable_trajectory p cfg g hg hD hS i.val).1
  exact h.comp (measurable_id.prodMk hI)

end LongTails.Proofs.DistributedNormalizedMeasurability
