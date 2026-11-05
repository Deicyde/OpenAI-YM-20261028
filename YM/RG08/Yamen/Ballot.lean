import YM.RG08.Yamen.Room
import YM.RG08.Yamen.Run
/-! # Steps on formal path over arbitrary rate W, fixed Levels. -/
noncomputable section
namespace YM.RG08.Yamen
open Lattice Laurent Pert.Bulk Forms Room Carrel Steam Isles Rows Rate Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry Prism Quarry Roost Packets Ducat Mason
open Filter
open scoped Classical Matrix BigOperators PowerSeries Topology
set_option autoImplicit false
variable {O:Type}{G:Gauge} {a:Levels G}(F:Horizon a)(P X:MapPrices)(hg:G.Simple)(Z:ChartRatio G)
-- case story W exact spacing; cutoff N map. W.top≤N; payment uniform over W per stamp.
structure Wheelhouse (a:Levels G)(e:ℕ)(W:Rate.Stair O) : Prop where
 along i : W.sched i=a.S
 walls (i:Haven W): e ≤ a.clock.J i.m

variable {E e r:ℕ}{W:Rate.Stair O} (K:Wheelhouse a E W)
include K

def charter :Charter W a.clock.kernel Z where
 patch i:=RG08.Supplies.stone a i.m
 branch i:=branches (a:=a) i.m
 yard _ i:=lamp P X a i
 same i:=by rw [Rate.Stair.length,K.along];rfl
-- N arguments
variable (N:O→ℕ)(hi:∀ i, W.top i ≤ N i)(L:Supplies F P Z)
 omit K
-- helpers. include hi section.
 omit K
include hi
theorem shoulders(i:Run W): i.m<N i.x:= Nat.lt_of_lt_of_le i.admit.2 (hi i.x)
theorem station(i:Haven W):i.m ≤ N i.x:= i.admit.2.trans (hi i.x)
variable {P}
 include K
-- K auto included in shoulder (sec vars uniform). omit

def Act: SliceSide (Yamen.charter P X Z K).patch (Yamen.charter P X Z K).warp a.clock.kernel Z where
 fine i:= F.H (N i.x) (i.m+1)
 coarse i:= F.H (N i.x) i.m
 letters i:= fed F P X hg Z (N i.x) (i.m+1)
 top i:=Yamen.base P X a i.m (F.H (N i.x) i.m)
 response i:= fine_share F (N i.x) i.m
 bulbs i:= ship X hg L (shoulders _ hi i)
 leaders i:= studio L.housed _ _ hg (shoulders _ hi i) (fun n=>L.herald _ _ _ (shoulders _ hi i).le) L.lodged _ (ship X hg L (shoulders _ hi i))
 aligned i:=
    let j:=a.clock.J (i.m+1)
    let p:= RG08.Supplies.PlanCurve G a.clock.kernel P j
    have he:0<p∧p≤1:=by obtain ⟨h,hk,-⟩:=RG08.Supplies.plan_hr G a.clock.kernel P j;exact ⟨h,hk⟩
    Ducat.chorus L.housed i.m _ (shoulders _ hi i) he.1 he.2 (warms L.housed _ _ (shoulders _ hi i))

def caliph : Pros (Yamen.charter P X Z K) where
 side:= Act _ X hg _ K N hi L
 current i n:= fed F P X hg Z (N i) n
 receipt _:=rfl
-- assembly proof
lemma receipts (i:Run W) :let Y:=Yamen.caliph F X hg Z K N hi L;Y.current i.x i.m=Y.side.car hg ((Yamen.charter P X Z K).branch) i:=by intro Y; exact mint_step (shoulders _ hi i)
end YM.RG08.Yamen
