import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Slide.Base
/-! # Patch continuity across periods geometry ONLY. Uses interior all flags for comparison
    without requiring support cluster touches. For arbitrary local revelation,
    construct actual globally clean in same sector before carriers. Uses radius chosen once.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Slide
open Function Filter Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck  Greenbelt
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {c C L:Side} {Z D:ℕ}
-- extend actual U to all V. use shift symmetry not pull orientation twist.

abbrev lev (k:ℕ) : Cover := fun _=> (k:ℤ)
lemma translate_crystal (w:ℕ) (i:Cover) : i∈Lattice.box w ↔ i + Slide.lev w ∈ crystal (2*w):= by
  rw [box_test, cryst]; unfold lev; simp only [Pi.add_apply]; constructor
  · rintro ⟨h,H⟩; constructor <;> intro j <;> have hb:=h j <;> have hp:=H j <;> omega
  rintro ⟨h,H⟩; constructor<;>intro j<;> have hb:=h j <;> have hp:=H j <;> omega
lemma shifts (U:Config G c) (t:Site c) (r:ℕ) (hc:2*(2*r) ≤ c.val) (p:ℝ) (hp : 0 ≤ p) (h:Healthy p (neighbors r t) U):∃ V, flags p V=∅ ∧ Agrees (Lattice.box r) (expandAt t V) (expandAt t U) := by
  let A:= cognac hc; let a:= Slide.lev r; let s:=wrap c a; let d:= t-s
  let Z:=translate (-d) (shape A d U)
  -- Shape at Site n base d, so shift original anchor to t
  have hv z : Slide.sites A d z∈neighbors r t:= by
    let q:=stage A z; let u:=q-a; have he:q∈crystal (2*r):= stamp hc z; have hg:u∈ Lattice.box r:= by apply (translate_crystal ..).2; rwa [show u+lev r=q from sub_add_cancel ..]
    apply (neighbors_mem ..).2; rw [show Slide.sites A d z=wrap c u+t from (by change wrap c q + (t-wrap c a)=_; unfold u; rw [map_sub]; abel)]; exact sep u t hg
  refine ⟨Z,?_,?_⟩; · unfold Z; rw [← pull_one]; exact Pane.tranquility _ (allFlag A d U _ hv p hp h) _ _
  rintro ⟨i,j⟩ hi hj; have hq:i+a∈crystal (2*r):= (translate_crystal r i).1 hi; have hm:(i+a+step j)∈crystal (2*r):= by rw [add_right_comm]; exact (translate_crystal r _).1 hj
  have h0 : wrap c (i+a) + d= wrap c i+t:= by rw [map_add]; unfold d s; abel
  change shape A d U (wrap c i+t + -d,j)=U (wrap c i+t,j)
  rw [← sub_eq_add_neg,← (eq_sub_of_add_eq h0),vested hc (i+a) hq j hm, h0]
-- Notation preserving references. no comparison proof on IO yet.
lemma rolls {c C:Side} (hc : C.val=c.val*D) (V:Config G c) (x:Site C):
    expandAt x ((normal (Deck.divides hc) hc).links V)=expandAt (splitter (Deck.divides hc) x) V := by
  funext ⟨i,j⟩; change V (((splitter (Deck.divides hc)) (wrap C i+x)), j) = _; rw [map_add, branch ..]; rfl
lemma increases {c: Side} (V:Config G c) (x:Site c): expandAt 0 (translate x V)= expandAt x V:= by funext i; simp [Lattice.translate, expandAt]
end YM.PhysicalNext.Repeat.Slide
