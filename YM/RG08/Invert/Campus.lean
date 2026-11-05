import YM.RG08.Invert.Pin
/-!
 # varphi orientation exact even on all roots.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Invert
open Function Filter Lattice Wilson Exterior Precision Laurent Next.Free Next.Free.Flight RG RG.Supply Bloch Input Matrix
open Planned.PrimaryIntegral295 Carrier
open Stationary Analysis FreeResolvent Tree UVExt.Paths Reflect
open scoped BigOperators Topology Real Classical Matrix ContDiff
variable {G:Gauge}{i j k t r:ℕ}{L c f:Side}{S:StepData c f}
lemma spry_c (Y:Chain)(p:G.ColorIndex)(h:Y.Wake G)(hk:i < j):
    let T:=contour Y G i j; let L:= Y.S.block i
    ∀ (c f:Side) (ht : f.val=c.val*L.val),∀ a b, installed (⟨L,ht⟩:Ratio c f) T a b= - installed (⟨L,ht⟩:Ratio c f) T (toneP G f 0 a) (toneP G c 1 b):= by
    intro T L c f ht a b; apply AntiTw (contour_l Y G i j).hw _ (⟨L,ht⟩:Ratio c f) (hx:=rfl)
    intro p' k S; let v:=Y.A₀ j i; let R:=Y.pair i p' k rfl; let H:= installed S v
    have he:HeatV (toneP G k 1) (toneP G p' 1) (patron G H):= by rw [tensor_same]; exact pigmentT (axial (Y.flight j i) Y.kernel.penalty Y.kernel.penalty_pos (Y.adm i) (c:=p') (f:=k) rfl|>.1)
    have hh := prediction_spin (c:=p') (f:=k) Y h p i j hk rfl
    have hz: installed S (Chain.predict G Y j i)= _:= Chain.predict_truth G h j i hk p' k rfl
    have hv: installed S T= patron G (straighten R (grove R) H):= Frosty.law R (T:=T) (contour_l ..)
    have hh:HeatV (toneP G k 1) (toneP G p' 1) (installed S (Chain.predict G Y j i)):= hh
    have hS: installed S (Chain.predict G Y j i)= patron G H + patron G (d 0 k)*installed S T:=by
       rw [hz,hv,extracted]; change patron G (H+_)= _; rw [patron_add,patron_mul]; rfl
    rw [hS] at hh
    constructor
    intro x z; have hp:= hh.yes x z; rw [Matrix.add_apply, Matrix.add_apply,he.yes x z] at hp; exact add_left_cancel hp
end YM.RG08.Invert
