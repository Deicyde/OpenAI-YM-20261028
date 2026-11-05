import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Deck.Plinth
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Sward.Hood
import YM.PhysicalNext.UNMASKED_THROUGH_LAUNCH.Use
import YM.Planned.RECIPE_STARTUP_PORT.Horizon
import YM.Progress.JOINT_CALENDAR.Delivery
/-! # Replicate Hilbert stencils on any period. Range selected through SAME T.R
     and common receipt. Script commutes with map only with this particular tight.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Deck
open Function Filter Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {c f C F m: Side} {P : Patch} {M : ℕ} -- G forward

section rack
variable {G : Gauge} {κ l E K I J : Type} {R : Type*} {c C:Side} {D' e:ℕ} [Fintype E] [Fintype K] [Fintype J] [Fintype I]
variable (h : c.val∣C.val) (p : E→I) (q : K→J) (x : E→Site C) (y : K→Site C) (u:I→Site c) (v:J→Site c)
structure Nary (h : c.val∣ C.val) (p:E→ I) (q:K→J) (x:E→Site C) (y:K→ Site C) (u:I→Site c) (v:J→ Site c) [Zero R] (A:E→K→R) (B:I→J→R) (D' : ℕ) : Prop where
  warps : Nest h p x u
  wefts : Nest h q y v
  fits : 2* D' < c.val
  pays i j : separation (x i) (y j)≤ D' → A i j=B (p i) (q j)
  old i j : A i j≠0 → separation (x i) (y j) ≤ D'
  new i j : B i j≠0 → separation (u i) (v j) ≤ D'
namespace Nary
variable {h p q x y u v} {A:E→K→Pay G} {B:I→J→Pay G} (H : Nary h p q x y u v A B D')
include H
omit [Fintype E] [Fintype I] in
lemma sails (u:K→ G.Color) (v:J→ G.Color) (he: u=v ∘ q) (i:E): Pressure.zip A u i=Pressure.zip B v (p i):= by
  let t:= H.wefts; apply Nest.all t D' (x i) H.fits
  · intro j hj
    rw [not_ne_iff.mp (mt (H.old i j) hj), _root_.zero_apply]
  · intro j hj; rw [H.warps.footing] at hj; rw [not_ne_iff.mp (mt (H.new _ _) hj), _root_.zero_apply]
  intro j hj; rw [H.pays _ _ hj,he]; rfl
omit [Fintype K] [Fintype J] in
lemma recedes (u:E→ G.Color) (v:I→ G.Color) (he:u=v ∘ p) (i:K): Pressure.unzip A u i= Pressure.unzip B v (q i):= by
  apply H.warps.all D' (y i) H.fits
  · intro j hj; rw [separation_comm] at hj; rw [not_ne_iff.mp (mt (H.old j i) hj),map_zero,_root_.zero_apply]
  · intro j hj; rw [H.wefts.footing,separation_comm] at hj; rw [not_ne_iff.mp (mt (H.new _ _) hj), map_zero,_root_.zero_apply]
  intro j hj; rw [separation_comm] at hj; rw [H.pays _ _ hj,he]; rfl
end Nary
end rack

variable {G : Gauge} {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q : KernelChoices} (hC : C.val=c.val*M) (he : 2 ≤ c.val)
def re (T : Tube G (stepped Q h)) : Tube G (stepped Q H) := ⟨T.R,T.up,T.high,T.down,T.low⟩
local notation "L" => Lace.project (h:=h) (H:=H) hC he
abbrev divides (h : C.val=c.val*M) : c.val∣C.val:=⟨M,h⟩
local notation "v" => (divides hC)
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
abbrev curr {c C : Side} {X : Type} (p:Site C→ Site c) (i:Site C × X):= Prod.map p id i
abbrev dip {c C : Side} (p:Site C→ Site c) (i:Twin C): Twin c:= Prod.map (curr p) id i
-- cut no width tilt yet.
variable {o m : ℕ} {T: Tube G (stepped Q h)} {X: Tube G (stepped Q H)} {Pt:Teller G} (hp:X=re T) (V: Config G c) (hv:2*o<c.val)
include hC he
include hp hv
omit hp he in
lemma crane {E F:Type} (R:Row E F) (hm : 0 < m) (i:Co C E) (j:Co C F) (hq:separation i.fst j.fst≤o) :
    lane o m ((normal v hC).links V) R i j= lane o m V R (curr (splitter (v)) i) (curr (splitter (v)) j):= by
  apply tsum_congr; intro w; unfold Pressure.priced; let f:=(splitter (v)); let d:= i.fst+wrap C w; let p:=route 0 w 1
  have hh : f d= f i.1+ wrap c w:= by unfold d; rw [map_add]; rw [branch]
  have he : (normal (v) hC).cut=f:=rfl
  simp only [curr, Prod.map_fst,Prod.map_snd,id_eq]; split
  next h=> rw [if_pos ⟨h.1,(congr_arg f h.2).trans hh⟩]; unfold rated
           rw [(normal (v) hC).traveller]; rfl
  next h=>
    rw [if_neg]; rintro ⟨a,b⟩; apply h; refine ⟨a,tiniest (v) ?_ ?_⟩; exact b.trans hh.symm
    apply Nat.lt_of_le_of_lt (separation_triangle j.1 i.1 d); have ht : separation i.1 d≤o:= by rw [show d=stop i.1 p from (by unfold d p; symm; simpa using stop_route i.1 0 w)]; exact (sep_walk id (sep_step (c:=C)) _ p).trans ((Nat.le_mul_of_pos_right _ hm).trans a)
    rw [separation_comm j.1]; omega

lemma upfrom (V:Config G c) (i:Twin F) (j:Twin C) (hh:separation ((decreed H).parent i.1.1) j.1.1 ≤ o): X.Φ o ((L).low.links V) i j=T.Φ o V (dip (L).high.cut i) (dip (L).low.cut j):= by
  subst X; let x:=(decreed H).parent i.1.1; let y:= L
  let i':=dip y.high.cut i; let j':=dip y.low.cut j
  apply tsum_congr; intro w; dsimp only [casted]; let p:=route (lift ((decreed H).residue i.1.1)) (P.L.val • w) 1
  have hz: (stepped Q h).ratio.residue (mesh i').1 = (decreed H).residue i.1.1:= y.room i.1.1; have hY:y.low.cut (x+wrap C w)= (decreed h).parent (mesh i').1+wrap c w:= (y.low.port ..).trans (by rw [← y.position]; rfl)
  rw [hz]; dsimp only
  split
  next he' =>
    rw [if_pos ⟨he'.1,congr_arg (fun i=> y.low.cut i) he'.2|>.trans hY⟩]; unfold rated
    have ht : travel (replica (Y).ratio (y.low.links V)) (mesh i).1 p=travel (replica (S).ratio V) (mesh i').1 p := by
      rw [show replica (Y).ratio _= _ from Lace.Fitted.replicate y V, y.high.traveller]; rfl
    exact congr_arg (fun g=> (T.R.mf ((decreed H).residue i.1.1,(mesh i).2) (mesh j).2 w) • (G.adjoint g).toContinuousLinearMap) ht
  next hB =>
    rw [if_neg]; rintro ⟨hx,hV⟩; apply hB; refine ⟨hx,tiniest (v) (hV.trans hY.symm) ?_⟩; change separation j.1.1 (x+wrap C w)< _; apply lt_of_le_of_lt (separation_triangle _ x _) _; have hp : separation x (x+wrap C w) ≤ o := by
      have hq : x+wrap C w= (decreed H).parent (stop i.1.1 p) := by rw [show stop i.1.1 p= (decreed H).embed (x+wrap C w) from casted_endpoint (stepped Q H) i.1.1 w, Ratio.embed_parent]
      rw [hq]; exact (sep_walk _ (parent_step (stepped Q H)) i.1.1 p).trans hx
    change separation x j.1.1 ≤ o at hh
    rw [separation_comm j.1.1]; omega
end YM.PhysicalNext.Repeat.Deck
