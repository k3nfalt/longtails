import LongTails.Algorithms.MultirateTrajectory
import LongTails.Proofs.MultiscaleAggregateError

namespace LongTails.Proofs.MultirateEncoding

open LongTails.Setups.MultirateSmoothNonconvex
open LongTails.Algorithms.MultirateTrajectory
open LongTails.Algorithms.MultiscaleAggregate
open MultiscaleAggregateCodec

variable {p : Params}

lemma read_pack (z : Code p) (suffix : List Bool) :
    read p (pack p z ++ suffix) = read p (pack p z) := by
  exact (read_packet (aggregate p) 0 z suffix).trans (read_packet_self (aggregate p) 0 z).symm

lemma pack_congruent (z : Code p) :
    congruent (width (aggregate p) 0) z (read p (pack p z)) := by
  change congruent _ z (readPacket _ 0 (packet _ 0 z))
  rw [read_packet_self]
  intro j
  simp

lemma exact_lift (hε : 0 < p.ε) (z r : Code p) (hc : congruent (width (aggregate p) 0) z r)
    (hz : ‖unpack (aggregate p) z‖ ≤ 3 * radius (aggregate p) 0) :
    liftCode p r = unpack (aggregate p) z := by
  apply recover_exact (p := aggregate p) hε hc
  simpa using hz

lemma lift_error (hε : 0 < p.ε) (z r : Code p) (hc : congruent (width (aggregate p) 0) z r)
    (G : Point p) (hG : ‖G‖ ≤ 2 * radius (aggregate p) 0) :
    ‖liftCode p r - G‖ ≤ 5 * ‖unpack (aggregate p) z - G‖ := by
  by_cases hz : ‖unpack (aggregate p) z‖ ≤ 3 * radius (aggregate p) 0
  · rw [exact_lift hε z r hc hz]
    linarith [norm_nonneg (unpack (aggregate p) z - G)]
  have ht := norm_sub_norm_le (unpack (aggregate p) z) G
  have hb := recover_move (p := aggregate p) hε 0 0 r
  simp only [sub_zero] at hb
  have h := norm_sub_le (liftCode p r) G
  change ‖liftCode p r‖ ≤ _ at hb
  linarith

lemma query_accuracy (hε : 0 < p.ε) (hL : 0 < (aggregate p).L) (x : Point p)
    (hx : (aggregate p).L * ‖x - p.x0‖ ≤ radius (aggregate p) 0) :
    ‖queryPoint p (queryPacket p x) - x‖ ≤ precision (aggregate p) / (aggregate p).L := by
  let a := aggregate p
  have ha : 0 < a.L := hL
  let y : Point p := a.L • (x - p.x0)
  let z := ∑ _i : Fin p.n, localCode a y
  have hn : (p.n : ℝ) ≠ 0 := by exact_mod_cast p.n.pos.ne'
  have he := MultiscaleAggregateError.rounding_error (p := a) hε (fun _ => y)
  change ‖unpack a z - (p.n : ℝ)⁻¹ • ∑ _i : Fin p.n, y‖ ≤ precision a at he
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul, inv_mul_cancel₀ hn, one_smul] at he
  have hy : ‖y‖ ≤ radius a 0 := by simpa [y, norm_smul, Real.norm_eq_abs, abs_of_pos ha] using hx
  have hr : precision a ≤ radius a 0 := by
    unfold radius
    exact le_mul_of_one_le_left (precision_pos (p := a) hε).le (one_le_pow₀ (by norm_num))
  have hz : ‖unpack a z‖ ≤ 3 * radius a 0 := by
    linarith [norm_sub_norm_le (unpack a z) y, norm_nonneg y]
  have hq : queryPoint p (queryPacket p x) = p.x0 + a.L⁻¹ • unpack a z := by
    change p.x0 + a.L⁻¹ • liftCode p (read p (pack p z)) = _
    rw [exact_lift hε z _ (pack_congruent z) hz]
  have hs : a.L⁻¹ • y = x - p.x0 := by simp [y, smul_smul, inv_mul_cancel₀ ha.ne']
  have heq : queryPoint p (queryPacket p x) - x = a.L⁻¹ • (unpack a z - y) := by
    rw [hq, smul_sub, hs]
    abel
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL), div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left he (inv_pos.mpr hL).le

end LongTails.Proofs.MultirateEncoding
