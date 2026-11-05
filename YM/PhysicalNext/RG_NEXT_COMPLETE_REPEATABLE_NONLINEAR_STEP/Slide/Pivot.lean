import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Slide.Base
/-!
 # Mirror carts at side TWICE w. Boundaries assigned even in right half exactly.
 Sign flip identity true Config. 
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Slide
open Function Filter Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck  Greenbelt
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {c C L:Side} {Z D w:ℕ}
variable (h:C.val=2*w)
local notation "A" => (Slide.cognac (h.ge))
include h
lemma reflected (i:Per C): point w (-i)=point w i:= by
  have hp:∀ i:Per C,point w i=i.valMinAbs.natAbs:=by intro i; rw [ZMod.valMinAbs_natAbs_eq_min]; unfold point; have hp:=ZMod.val_lt i; split <;> omega
  rw [hp,hp,ZMod.natAbs_valMinAbs_neg]
omit h
variable (v:Axis→Bool)
def slant : Signed:=⟨Equiv.refl _,v⟩
lemma gems (x:Site C) (i:Axis): (Slide.slant v|>.act x) i=if v i then - x i else x i:=rfl
lemma jumps (i:Axis): (Slide.slant v).act (step i:Site C)=if v i then -step i else step i:= by
  funext j; by_cases he:j=i; · subst i; rw [gems]; cases h:v j<;>simp
  rw [gems]; cases h:v i <;> simp [he]
include h
lemma still (o:Site c) (x:Site C): sites (A) o ((slant v).act x)=sites A o x:= by
  unfold sites; congr 2; ext i; unfold Slide.stage; rw [gems]; split; next=> exact congr_arg NatCast.natCast (Slide.reflected h (x i))
  rfl
lemma traps (V:Config G c) (o:Site c): pull (slant v) 0 (shape (A) o V)=shape (A) o V:= by
  funext ⟨x,i⟩; let s:= slant v; let t:=s.act x
  unfold Lattice.pull Lattice.affine; rw [add_zero]; cases hv : v i
  · have ht: grade A (s.act x,i)=grade A (x,i):= by simp only [grade,s,gems,hv]; rfl
    rw [show (posDir i).rotate (slant v)=posDir i from (by unfold Lattice.Step.rotate; simp [slant,posDir,hv]), Lattice.Step.pos_read]; change shape A o V (s.act x,i)=_
    unfold shape; rw [ht, Slide.still h]; rw [show s.act x+step i = s.act (x+step i) from (by rw [s.act_add, Slide.jumps, hv]; rfl), Slide.still h]
  have hx:s.act x-step i=s.act (x+step i):= by rw [s.act_add, Slide.jumps v i,hv]; simp [sub_eq_add_neg]
  rw [show (posDir i).rotate (slant v)=negDir i from (by unfold Lattice.Step.rotate; simp [slant, negDir,posDir,hv]),Lattice.Step.neg_read, hx]
  have hg: grade A (s.act (x+step i),i) = -(grade A (x,i)):= by
    let u:=x+step i
    have he: (A).pos = (fun i=>(point w i:ℤ)):=rfl
    have hk: s.act u i= -(x i+1):=by rw [gems,hv]; simp [u]
    change (A).pos (s.act u i + 1)- (A).pos (s.act u i)=_
    rw [hk,he,show -(x i+1)+1=-(x i) from by abel]; simp only [Slide.reflected h]; change _ = -( (point w (x i+1):ℤ)- (point w (x i):ℤ)); ring
  unfold shape; rw [hg, Slide.still h, ← hx,sub_add_cancel,Slide.still h]; rcases graded A (x,i) with hh|hh|hh <;> simp [hh]
-- Pivot recognized via mere projection. no explicit equivalence needed: classify counts through fibers.
def ascended (i:Site C) : Site C := wrap C (Slide.stage (A) i)
lemma untwist (i: Per C): i=((point w i):Per C) ∨ i=- ((point w i): Per C) -- coercions? annotation
    := by
  have ht:=ZMod.val_lt i
  unfold point; split; · left; simp
  right
  rw [← h,Nat.cast_sub (by omega),ZMod.natCast_self,ZMod.natCast_zmod_val]; simp
lemma snap (x:Site C): ∃ v:Axis→Bool,(slant v).act x= ascended h x:= by
  let u i:= (point w (x i):Per C); let v i:= decide (x i≠u i); refine ⟨v,funext fun i=>?_⟩
  rw [show ((ascended h x): Site C) i=u i from (by change ((↑((point w (x i):ℤ))):Per C)= _; rw [Int.cast_natCast]), gems]; unfold v; split
  next hH=> rcases untwist h (x i) with hi|hi; exact False.elim (of_decide_eq_true hH hi); exact (congr_arg Neg.neg hi).trans (neg_neg _)
  next hH=> exact Classical.byContradiction fun q=> hH (decide_eq_true q)
end YM.PhysicalNext.Repeat.Slide
