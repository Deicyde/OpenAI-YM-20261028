import YM.Extra.SOURCE_HISTORIES.Reserve
import YM.Planned.PRIMARY_INTEGRAL_295.Chrysalis
/-!
# Principal center geometry for true compressed windows

Positive physical (link base and axis). W criterion at doubled lattice,
always retain all colors at a chosen link. Uses ALL filled axes; no retesting
trunks near window edge. Upper H envelope merely for evaluation comparison.
Receipts computed in output positions (basis & θ shifts accounted in masks
Footprints for actual Y; separate from these W numerical range checks).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Sparks
open Function Filter Set Metric MeasureTheory ProbabilityTheory
open Lattice RG Wilson Pressure Labels Source Source.Drops Extra.Histories
open Warehouse Precision Exterior Tree Carrier Bloch Next.Free Progress.StationaryScenes Bazaars Launch Shapes
open Next.Foundations Vintage Spurs 
open Villa Floor Glints Fizz Fizz.Gush   Cabins  Little Density
open WardBin.Lies
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {n c f : Side} {d : ℕ} {F : Labels.Frame G d}

abbrev twin (f:Side):= f*(2:Side)
def factor (f:Side) : Ratio f (twin f):= ⟨2, PNat.mul_coe _ _⟩
def axle (i:Bond f):Site (twin f):= (factor f).embed i.1+step i.2
lemma shifted (i:Bond f): separation (axle i) ((factor f).embed i.1) ≤ 1:=by
   rw [separation,axle,add_comm,add_sub_cancel_right]; exact pdist_step _


variable (S:StepData c f)(B:ℕ)
-- H hub.A all coordinates.Color. First order windows specified on doubled. Nat. powers zero accepted. `2r/20` scaled fine via count.
def alive (a b:Bond f) := 20*separation (axle a) (axle b) ≤ 2*B * S.ratio.count.val


lemma departures (x y:Bond f) (hc:300 ≤ B) :
   (alive S B x y → 10*separation (S.ratio.parent x.1) (S.ratio.parent y.1) ≤ B) ∧
   (¬alive S B x y → B/25 ≤ separation (S.ratio.parent x.1) (S.ratio.parent y.1)) :=by
   let r:=S.ratio; let L:=r.count.val; have hl:1≤L := r.count.property
   let e:= (factor f).embed; let X:= axle x; let Y:=axle y
   let A:= r.parent x.1; let D:= r.parent y.1; let n:=separation x.1 y.1; let k:=separation A D; let z:= separation X Y
   have hu : separation (e x.1) (e y.1) = 2*n:= le_antisymm (Next.Free.scaled_root ..) (Corona.below (factor f) x.1 y.1)
   have ht : 2*n≤z+2 ∧ z≤ 2*n+2:=by
     have ha:= separation_triangle (e x.1) X Y; have hb:= separation_triangle (e x.1) Y (e y.1)
     have hw:= separation_triangle X (e x.1) (e y.1); have hv:= separation_triangle X (e y.1) Y
     rw [separation_comm _ X] at ha; rw [separation_comm (e y.1) Y] at hv
     have hx :separation X (e x.1) ≤ 1:= shifted x; have hy :separation Y (e y.1) ≤ 1:= shifted y
     unfold z; omega
   have he : L*k ≤ n+ L:= Corona.foreshorten ..
   have hp : n ≤ L*k + L :=by
     have hx:= Corona.near r x.1; have hy:= Corona.near r y.1; rw [separation_comm y.1] at hy
     have hh:= separation_triangle x.1 (r.embed A) (r.embed D); have hv:= separation_triangle x.1 (r.embed D) y.1
     change 2*separation x.1 (r.embed A)≤L at hx; change 2*separation (r.embed D) y.1≤L at hy
     have hz: separation (r.embed A) (r.embed D) ≤ L*k:=scaled_root ..; unfold n; omega
   constructor
   · intro h; change 20*z≤2*B*L at h; change 10*k≤B
     apply Nat.le_of_mul_le_mul_left ?_ (show 0<L from hl)
     nlinarith
   intro h; change B/25 ≤ k; change ¬20*z≤2*B*L at h
   by_contra hh; have hi:k*25 ≤ B:= (Nat.le_div_iff_mul_le (show 0<(25:ℕ) by norm_num)).mp (le_of_lt (Nat.lt_of_not_ge hh))
   have he:= Nat.mul_le_mul_left L hi; nlinarith

section Bay
variable {S B}
/-- ALL data needed for linear halo checks include free I for masks
and canon argument halo. W includes coordinates with these exact criteria
in hub, versions tested only where `room` genuinely contains HWindow.I. -/
structure Bank (G:Gauge)(S:StepData c f) where
   tree : Forest S.ratio
   B : ℕ
   held : Finset tree.Free
   room : Finset (Bond f)
   seen (i : held) : ∀ j, alive S B i.val.val j → j∈room
namespace Bank
variable (M:Bank G S)
def grounds : Finset (Acres f G) := M.room.product Finset.univ
abbrev keys := Icebergs.Index M.held G
def move (i:M.keys):Acres f G := (i.1.val.val,i.2)
lemma central (i:M.keys): M.move i ∈ M.grounds :=Finset.mem_product.mpr ⟨M.seen i.1 _ (by simp [alive,move]),Finset.mem_univ _⟩
def bee : M.keys ↪ M.grounds := ⟨fun i=>⟨M.move i,M.central i⟩,by
   intro x y h; obtain ⟨x,i⟩:= x; obtain ⟨y,j⟩:=y
   have he := congr_arg Subtype.val h; change _root_.Prod.mk x.val.val i=_root_.Prod.mk y.val.val j at he
   exact Prod.ext (Subtype.ext (Subtype.ext (Prod.mk.inj he).1)) (Prod.mk.inj he).2 ⟩
def homes : Windows M.bee := ⟨fun i=>Finset.univ.filter (fun j=>alive S M.B (M.move i).1 j.val.1),by intro i; simp [bee,alive]⟩
lemma inward (i:M.keys) (j:M.grounds): j ∈ M.homes.W i ↔ alive S M.B (M.move i).1 j.val.1:=by simp [homes]

end Bank
end Bay
end YM.Planned.PrimaryIntegral295.Sparks
