import LongTails.Setups.SpatialRankingLogistic

open OracleTemplate

namespace LongTails.Algorithms.SpatialRankingLogistic

open LongTails.Setups.SpatialRankingLogistic

noncomputable def algorithm (p : Params) : Algorithm (Query p) (Point p) (Point p) where
  State := Scan p
  initial _ := ⟨((1,0), 0), 0, 0⟩
  query s := (0, scanQuery p s)
  update s r := scanUpdate p .joint (4*p.n) s r
  output s := s.point

noncomputable def output (p : Params) (O : Oracle (Query p) (Point p)) (k : ℕ)
    (ω : (i : ℕ) → O.Seed i) : Point p :=
  execute O (algorithm p) (fun _ => k) () ω

lemma in_family (p : Params) (hn : 0 < p.n) : family p .joint (algorithm p) := by
  refine ⟨id, fun _ => (1,0), fun _ _ => 4*p.n, fun _ _ => by positivity,
    fun _ => ⟨fun _ => rfl, 4*p.n, fun _ _ => rfl⟩, ?_, ?_, ?_, ?_⟩ <;> intros <;> rfl

end LongTails.Algorithms.SpatialRankingLogistic
