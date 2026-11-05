import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Slide.Pivot
/-!
 # Boundary types for periodic interpolation. independent of total w.
 Returns local cover sites of THIS patch, not inferred from deadline.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Slide
open Function Filter Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck  Greenbelt
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {c C L:Side} {Z D w m:ℕ}
abbrev Rose (Z : ℕ):= Option (Bool× Fin Z)
def bud (w r : ℕ) (i : ℕ): Rose r := if h:i<r then some (false,⟨i,h⟩) else if h:w-i<r then some (true, ⟨w-i,h⟩) else none
def tag (w r:ℕ) (i:Per C): Rose r:= Slide.bud w r (point w i)
abbrev Petals (Z:ℕ):= Axis→Rose Z
def charm (w r: ℕ) (a: Site C) : Petals r:= Slide.tag w r ∘ a
def offset (a: Rose Z) (x:ℤ): ℤ:= match a with
  | none => x
  | some (false,i)=> |i.val+x|-(i.val:ℤ)
  | some (true,i)=> (i.val:ℤ)-|(i.val:ℤ)-x|
def delta (t: Petals Z) (s:Cover): Cover:= fun i=> Slide.offset (t i) (s i)

section track
variable (h:C.val=2*w) (ht : 2*Z≤ w)
local notation "A" => (Slide.cognac (h.ge))
include h
lemma rising (i : ℤ) (hp:0 ≤ i) (hi:i≤w): (A).pos (i:Per C)=i:= by
  let b:= i.toNat; have hz : (b:ℤ)=i:= Int.toNat_of_nonneg hp; change (point w (i:Per C):ℤ)=i; rw [← hz, Int.cast_natCast, centerDown h.ge (by omega)]
lemma western (i : ℤ) (hp: -(w:ℤ) ≤ i) (hi:i≤w): (A).pos (i: Per C)=|i|:= by
  rcases le_or_gt 0 i with hx|hx
  · rw [abs_of_nonneg hx]; exact rising h i hx hi
  have hh:= rising h (-i) (by omega) (by omega); rw [abs_of_neg hx]; rw [Int.cast_neg] at hh; change (point w (-(i:Per C)):ℤ)=_ at hh; rw [reflected h] at hh; exact hh
lemma eastern (i : ℤ) (hp:0 ≤ i) (hi:i≤2*(w:ℤ)): (A).pos (i: Per C)= (w:ℤ)- |(w:ℤ)-i|:= by
  rcases le_or_gt i (w:ℤ) with hx|hx
  · rw [abs_of_nonneg (by omega),sub_sub_cancel]; exact rising h i hp hx
  have he := rising h (2*(w:ℤ)-i) (by omega) (by omega); rw [show ((↑(2*(w:ℤ)-i)): Per C)= -(i:Per C) from ?_] at he
  · rw [abs_of_neg (by omega)]; change (point w (-(i:Per C)):ℤ)= _ at he; rw [reflected h] at he; change (point w (i:Per C):ℤ)=_; rw [he]; ring
  rw [show 2*(w:ℤ)=(C.val:ℤ) from (by omega), Int.cast_sub,Int.cast_natCast, ZMod.natCast_self, zero_sub]
include ht
lemma vertical (x: Per C) (i : ℤ) (hi:i.natAbs ≤ Z):
    (A).pos (↑((A).pos x+i) : Per C)= (A).pos x+ Slide.offset (Slide.tag w Z x) i:= by
  let p:=point w x; have hV:p≤w:= Slide.stopped x; change (A).pos (↑((p:ℤ)+i):Per C)=(p:ℤ)+ Slide.offset (bud w Z p) i
  unfold bud; split
  next hP=> dsimp only [offset]; rw [western h ((p:ℤ)+i) (by omega) (by omega)]; abel
  next hv=> split
            next hP=> dsimp only [offset]; rw [eastern h ((p:ℤ)+i) (by omega) (by omega), Int.natCast_sub hV,show (w:ℤ)-(p+i)=w-p-i by abel]; abel
            next hP=> exact rising h ((p:ℤ)+i) (by omega) (by omega)
lemma touchUp (x: Site C) (i:Cover) (hi:i∈ Lattice.box Z):
    Slide.stage A (wrap C i + ascended h x)=Slide.stage A x+ Slide.delta (charm w Z x) i:= by
  funext j; unfold Slide.stage Slide.ascended
  have hv : (wrap C i+wrap C (Slide.stage A x)) j=(↑((A).pos (x j)+ i j):Per C):= by rw [add_comm,←map_add]; rfl -- edit
  rw [hv]; exact vertical h ht (x j) (i j) (by have hh:= (box_test.mp hi).1 j; have hz:=(box_test.mp hi).2 j; omega)
-- After centering at physical target x, reads exactly a typed local field (even in dislocated). use for sums.
omit h ht
def thing (p:Petals Z) (y:Site c) (V: Config G c) : Links ℤ G.El:= fun i=>
  let q:= Slide.delta p i.1
  let t:= Slide.delta p (i.1+step i.2)
  if t i.2-q i.2=1 then V (wrap c q+y,i.2) else if t i.2-q i.2= -1 then (V (wrap c t+y,i.2))⁻¹ else 1
abbrev rosy (Z:ℕ) : Petals Z:= fun _=>none
lemma self (V:Config G c) (y:Site c): thing (rosy Z) y V= expandAt y V:= by
  have hk (k:Cover): Slide.delta (rosy Z) k=k:= rfl
  funext i; unfold Slide.thing; simp only [hk, Pi.add_apply,step_apply,ite_true]; rw [show i.fst i.2+1-i.1 i.2=(1:ℤ) from add_sub_cancel_left .., if_pos rfl]; rfl
include h ht
lemma wandered (x:Site C) (y: Site c) (V:Config G c): Agrees (Lattice.box Z) (expandAt (Slide.ascended h x) (Slide.shape A (y-wrap c (Slide.stage A x)) V)) (Slide.thing (charm w Z x) y V) := by
  let u :=y-wrap c (Slide.stage A x); let p:= Slide.charm w Z x
  rintro ⟨i,j⟩ hi hj; let v:= wrap C i+ ascended h x; have hE: v+step j=wrap C (i+step j)+ascended h x:= by unfold v; rw [map_add,wrap_step]; abel
  have ha:stage A v=stage A x+Slide.delta p i:= Slide.touchUp h ht x i hi
  have hb : Slide.stage A (v+step j)=stage A x+Slide.delta p (i+step j):= hE.symm ▸ Slide.touchUp h ht x _ hj
  have hp : sites A u v=wrap c (delta p i)+ y := by unfold sites u; rw [ha,map_add]; abel
  have hq : sites A u (v+step j)=wrap c (delta p (i+step j))+ y := by unfold sites u; rw [hb,map_add]; abel
  rw [tops, ha] at hb; have he:= congr_fun hb j; have hv : grade A (v,j)= (delta p (i+step j) j-delta p i j):=by simp at he; omega
  change shape A u V (v,j)=thing p y V (i,j); unfold thing shape; rw [hp,hq,hv]
end track
end YM.PhysicalNext.Repeat.Slide
