import LongTails.Setups.BroxGeneralNormConstrainedPL

noncomputable section

namespace OracleTemplate.WarmHalvingBrox

open LongTails.Setups.BroxGeneralNormConstrainedPL

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure State (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  updates : ℕ
  center : E
  trial : ℤ
  slope : Option (E →L[ℝ] ℝ)
  stopped : Bool

def radius (r : ℝ) (j : ℤ) : ℝ := r * 2 ^ j

def query (r : ℝ) (s : State E) : Fin 2 × BroxQuery E :=
  match s.stopped, s.slope with
  | false, some g => (1, .inr (s.center, radius r s.trial, g))
  | _, _ => (0, .inl s.center)

def update (L r : ℝ) (s : State E) (reply : BroxReply E) : State E :=
  match s.stopped, s.slope, reply with
  | false, none, .inl g => { s with slope := some g }
  | false, some g, .inr q =>
    if g (q - s.center) = 0 then { s with stopped := true }
    else if L * radius r s.trial ^ 2 ≤ -g (q - s.center) then
      { updates := s.updates + 1, center := q, trial := s.trial + 1, slope := none,
        stopped := false }
    else { s with trial := s.trial - 1 }
  | _, _, _ => s

def algorithm (L r : ℝ) (x0 : E) : Algorithm (BroxQuery E) (BroxReply E) E 2 where
  State := State E
  initial _ := ⟨0, x0, 0, none, false⟩
  query := query r
  update := update L r
  output s := s.center

end OracleTemplate.WarmHalvingBrox
