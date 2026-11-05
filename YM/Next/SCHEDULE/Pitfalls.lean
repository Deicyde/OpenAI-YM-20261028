import YM.Next.SCHEDULE.Dues

/-!
# Schedule counter-checks

Some tempting SUFFICIENCY gates cannot work (in earliest x→∞
quantifier already). Not a claim that these gates are forced and hence
that YU as such is false. Include genuine path-width non-inclusion on the
`Bounds` type. These explain order of the bookings and limitations of
any attempt to fill the *estimate* holes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Scheduling
open Filter Function RG RG.Supply  Bid Lattice Clock Instrument Real
open scoped Topology





variable {G : Gauge}
-- fail monotonic forecast using Bounds on smaller width
private def slot (p : PlaqAxes) (i : ℕ) : Slot := ⟨List.replicate i (posDir 0),p⟩ -- namespace?
private def dummy (G : Gauge) (k : ℕ) (p : PlaqAxes) : Atom G k := ⟨fun _=>slot p 0,0⟩
private def cloud (G : Gauge) (t c : ℝ) : PathData G :=
    let p : PlaqAxes := ⟨(0,1),by decide⟩
    ⟨fun p i => (c*Real.exp (-t*i),slot p i),fun _ => dummy _ _ p,fun _ => dummy _ _ p,fun _ => dummy _ _ p⟩




end YM.Next.Scheduling

noncomputable section
namespace YM.Next.Scheduling
open Filter Function RG RG.Supply  Bid Lattice Clock Instrument Real
open scoped Topology


end YM.Next.Scheduling
