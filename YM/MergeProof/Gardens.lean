import YM.MergeProof.Baskets
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local
open PhysicalNext.Repeat.Legato.Bandage Cells Extraction Exponential
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}(C:Family G)(N k m p d:ℕ)(v:C.label d)(a:ℝ)(ha:0<a)(B:Stock.Tabs C.path.levels)
variable (H:C.Makes) {W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
    (h:Geyser C W u ψ φ δ (fly C.path.levels) r D) (hx:∀ i:ℕ, 1≤r i)
set_option quotPrecheck false
local notation "b!"=> Cells.center C.S p
local notation "T"=> C.path.levels
local notation "A"=> Site (C.side m p)
local notation "P"=> C.path.levels.budget
local notation "F"=> C.labels.level d
include B h H hx
lemma gardena (hG:G.Simple)(hK:Mix.paidL C) : Extraction.Wcmain C:=by
   intro d a u ha hu
   let F':=C.labels.level d
   have hf : Continuous F'.coeffSize:= by unfold Labels.Frame.coeffSize; fun_prop
   obtain ⟨b,hb⟩:= (isCompact_closedBall (0:F'.Coeff) a).bddAbove_image hf.continuousOn
   let g:= max 1 b; have hg:0<g:=zero_lt_one.trans_le (le_max_left ..)
   let p i:= Stock.Tabs.chosen (T) 1 B i
   obtain ⟨k,h0⟩:= eventually_atTop.mp (coastwise C d g hg B hG hK hu)
   have hw(i:ℕ): Real.exp (((d:ℝ)+u)*C.S.scale i)= C.S.a i^(-(d:ℝ)-u):=by rw [Real.rpow_def_of_pos (C.S.a_pos _)]; unfold Schedule.scale; rw [Real.log_inv]; ring_nf
   let b i:=Real.exp (expense C g i (p i) d)/Real.exp (((d:ℝ)+u)*C.S.scale i); have hb'(i):0 ≤ b i:=by unfold b; positivity
   let y:= 1+∑ i∈Finset.range k,b i; have hy : 1 ≤ y:= le_add_of_nonneg_right (Finset.sum_nonneg fun i _=>hb' i)
   refine ⟨y,zero_le_one.trans hy, fun i hi=>?_⟩
   let X:=p i; have hX : Stock.Tabs.opens (T) 1 i X:= Stock.Tabs.opened (T) 1 B i
   have hW: Real.exp (expense C g i X d) ≤ y* C.S.a i^(-(d:ℝ)-u):=by
      rw [← hw]; rcases lt_or_ge i k with h|h
      · apply (div_le_iff₀ (Real.exp_pos _)).1; exact le_trans (Finset.single_le_sum (f:=b) (fun i _=>hb' _) (Finset.mem_range.mpr h)) (le_add_of_nonneg_left zero_le_one)
      exact (Real.exp_monotone (h0 _ h)).trans (le_mul_of_one_le_left (Real.exp_pos _).le hy)
   filter_upwards [eventually_gt_atTop X,Stock.clear_interior C H i d] with N hN hC p' v' hv'
   obtain ⟨hn,hh⟩:= hC
   have hp : F'.coeffSize v' ≤ g:= (hb ⟨v',Metric.mem_closedBall.mpr (by rwa [dist_zero_right]),rfl⟩).trans (le_max_right ..)
   refine ⟨hn,hi.trans hn,fun j=>⟨hh p' j v',?_⟩⟩
   change (center C.S p' hn j).rootTest (C.beta N p') (C.O N p' (d:=d) v' j) ≤ _; rw [Stock.translate_s (C:=C) hn j ⟨d,v'⟩ (hh p' 0 v')]; exact (tent C N X i p' d v' g hg B H h hx hX hi hN hp).trans hW
end YM.MergeProof.Accent
