import YM.RG08.Weald.Incoming

/-!
# The formal receipt BEFORE L μ etc and normalized transport, produced
at any regulator. Serves full Ward demand (cofinal specialization still
uses Cooled limit).
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Weald
open Jetty Skiff Lattice Isles Forms Pert.Bulk Function Finset Laurent Filter Packets Steam Mount
open Room Gallery Camera MvPolynomial Glyph Hatch Quarry
open RG Wilson Stationary Precision Tack Tree Prism Slate Work.F05
open scoped Topology BigOperators ENNReal Classical PowerSeries ContDiff Matrix.Norms.Frobenius Matrix
variable {G:Gauge}{c:Side}(P:Patch)(K:KernelChoices)(F:Forest (rung P K c).ratio)(A B:Bed)
variable (Z:ChartRatio G)(hZ:LocalRatio Z)(d:G.El)(o: Site P.L)
private abbrev Xal:=Camera.Raw (Precision.Key F G) (RoomX G c)

def pie (i:Plot G (Site (c*P.L)))(x:podium (G:=G) (rung P K c) F):ℝ:= match i.2 with
 | Sum.inl ⟨a,l⟩ => firstF (rung P K c) F A B x ((slide P o (i.1,a,l): Lines G (c*P.L) 1).1,a) l
 | Sum.inr l => currentF (rung P K c) F x (i.1+wrap (c*P.L) (Lattice.lift o)) l

local notation "S" => rung P K c
lemma pie_low (i: Lines G (c*P.L) 1):
 (pie P K F A B o (i.1, Sum.inl i.2))=implant F A B (Quarry.badge (G:=G) c) (lowSlot S (slide P o i)):=by funext x;rfl
lemma pie_pace(i:Plot G (Site (c*P.L))):Pace (pie P K F A B o i):=by
 rcases i with ⟨i,z|z⟩
 · rw [show pie P K F A B o (i,Sum.inl z)=_ from pie_low P K F A B o (i,z)]; exact uniform F A B (Quarry.badge c) _
 let R : Site c:=(S).ratio.parent (i+wrap (c*P.L) (Lattice.lift o))
 change Pace (fun x:podium S F=> Quarry.spear (G:=G) R (Slate.envar x) z)
 exact ((Quarry.colorLens z).comp ((Quarry.spear _).contDiff.comp Slate.smooth2)).contDiffAt
lemma pie_center: Camera.roll (pie (G:=G) P K F A B o) 0=0:=by
 funext i; rcases i with ⟨x,i|i⟩
 · exact congrFun (seated F A B (Quarry.badge (G:=G) c)) (lowSlot S (slide P o (x,i)))
 change Quarry.spear (G:=G) _ (0:Cellar (RoomX G c)) i= (0:ℝ); rw [map_zero];rfl

lemma symbol (i:Lines G (c*P.L) 1)(x:podium (G:=G) S F):
 let j:= slide P o i
 ; boltF S F A B d x j i.2.2=(hot d).fare i.2 ((Camera.roll (pie P K F A B o) x) ∘ dodge (hot d) i):=by
 intro j
 unfold boltF Quarry.hot jaw Quarry.glaze
 let H:=Camera.roll (pie P K F A B o) x ∘ dodge (hot d) i
 change _=flourish d (fbar 0 H) (fbar 1 H) (fbar 2 H) i.2.2
 have ht(k:Fin 3)(l:G.ColorIndex): fbar k H l=H (k,l):= rfl
 have ha:fbar 0 H=firstF S F A B x (j.1,j.2.1):=by
    ext l;rw [ht]; let i0:= ((i.1+wrap (c*P.L) 0,.inl (i.2.1,l)):Plot G (Site (c*P.L))); change pie P K F A B o i0 x=_; unfold i0;rw [map_zero,add_zero];rfl
 have hb:fbar 1 H=currentF S F x j.1:=by
    ext l;rw [ht]; let i0:= ((i.1+wrap (c*P.L) 0,.inr l):Plot G (Site (c*P.L))); change pie P K F A B o i0 x=_;unfold i0;rw [map_zero,add_zero];rfl
 have hc:fbar 2 H=currentF S F x (j.1+step (Quarry.back j.2.1)):=by
    ext l;rw [ht]; let i0:= ((i.1+wrap (c*P.L) (step (Quarry.back i.2.1)),.inr l):Plot G (Site (c*P.L))); change currentF S F x (i0.1+wrap (c*P.L) (lift o)) l=currentF S F x ((i.1+wrap (c*P.L) (lift o))+step (Quarry.back i.2.1)) l;unfold i0;dsimp only;rw [wrap_step,add_right_comm]
 rw [ha,hb,hc]

lemma hall (i:Lines G (c*P.L) 1): belt (rescaleFields (Operandi S F A B Z hZ d).map) (rescaleFields (implant F A B id) (lowSlot S (slide P o i)))=
 belt (rescaleFields (pie P K F A B o)) (own d i):=by
 let O:=Operandi S F A B Z hZ d; let j:= lowSlot (G:=G) S (slide P o i)
 let H:= implant (G:=G) F A B id; let V:= pie (G:=G) P K F A B o
 let k:= hot d;let p:=fun z:foil G=> V (dodge k i z)
 let t:= i.2
 have ht: rescaleFields H j=eye (H j):=rfl; have he:rescaleFields O.map=(fun i=>eye (O.map i)):=rfl
 change belt (rescaleFields O.map) (rescaleFields H j)=belt (rescaleFields V) _
 rw [ht,he,← Quarry.eye_comp O.map O.fine O.level (H j) (Prism.uniform F A B id j) (congrFun (seated F A B id) j),own]
 conv_rhs=>change ((belt (rescaleFields V)).comp (belt (fun u:foil G=>rod (dodge k i u)))) (eye _);rw [switched]
 simp_rw [belt_x]
 have hp(u:foil G):Pace (p u):=pie_pace P K F A B o _
 have hg:Camera.roll p 0=0:=funext fun _=> congrFun (pie_center P K F A B o) _
 change eye _=belt (fun i=>eye (p i)) (eye (k.fare t))
 rw [← Quarry.eye_comp p hp hg _ (k.fit _) (k.origin _)]
 apply Quarry.eye_same
 filter_upwards [Weald.salute S F A B Z hZ d (slide P o i)] with x hx
 exact (congrArg (fun y:G.Color=> y i.2.2) hx).trans (symbol P K F A B d o i x)

private lemma straw {I J D:Type}[Fintype I][Fintype J][Fintype D](x:I→Port J)(y:J→Port D)(f:Port I):belt y (belt x f)=belt (fun i=>belt y (x i)) f:=by change ((belt y).comp (belt x)) f=_;rw [switched]

lemma endearing (i:Lines G (c*P.L) 1): belt (rescaleFields (pie P K F A B o)) (rod (i.1,Sum.inl i.2))=rescaleFields (implant F A B (Quarry.badge (G:=G) c)) (lowSlot S (slide P o i)):=by rw [belt_x,rescaleFields,pie_low P K F A B o i];rfl

variable {l:ℕ}
def plank (M:GrainS (Ed G Cover)):GrainS (Market (Tack.Head P G)):=fun i n=> Hatch.broom (Hatch.door P o) (M i n)
def raft (M:GrainS (Market (Tack.Head P G)))(c:Side):GrainS (Epic P G c):=fun i n=> Hatch.broom (port c) (M i n)

set_option maxHeartbeats 350000 in
/-- Exact Ward law at ALL finite tori of the pre-mean Source. Incoming transformations
need only C^omegaAt on specified neighborhoods, no cutoff dependence. -/
theorem welcomed (M:GrainS (Ed G Cover))(he:Calls l M)(hp:Pops M)(f:Pearl):
 let L:Camera.Strip (Camera.Raw (Precision.Key F G) (Lines G c 1)) (Xal (G:=G) P K F):=(Operandi S F A B Z hZ d).map
 let N:=Trickle.mark l (Weald.raft P (plank P o M) c) f
 ; belt (rescaleFields L) (belt (rescaleFields (implant F A B id)) N)=belt (rescaleFields (implant F A B (Quarry.badge c))) N:=by
 intro O N
 unfold N Weald.raft plank; rw [Hatch.door_read P o K c,straw,straw]
 let T:=Trickle.mark l (fun i n=> Hatch.broom (port (c*P.L)) (M i n)) f
 change belt _ T=belt _ _
 have hz:= summer he hp (c*P.L) f d
 dsimp only at hz
 change belt _ T=belt _ T at hz
 -- order simplify lhs = path→own; combine rhs reverse; maybe straws combined wrong
 rw [straw]
 simp_rw [belt_x]
 unfold O; simp_rw [hall P K F A B Z hZ d o,← endearing P K F A B o]
 rw [←straw,←straw,hz]
end YM.RG08.Weald
