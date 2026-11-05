import YM.TraceExtension.Turret.Drone
import YM.TraceExtension.Shepherd.Cant
import YM.TraceExtension.Shepherd.Cage
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Fen
open Lattice Pressure Gauge Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Lamp
open Filch Turret Function Filter Shepherd AnalyticBridge VerifiedReset
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n:Side} (R:Rep G n){d:ℕ}{σ A C:ℝ}{X:Type}

-- unmasked classical amplitudes from actual Rep
abbrev GreenA:= Low ⊕ High
def legF: GreenA→ Barley:= Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)
def loopF: ℕ→Barley:= Sum.inr ∘ Sum.inr
def ul (W:PathData G)(s:Clip): Barley→ Site n→ Config G n→ℝ:= Sum.elim (fun i o U=> Low.mark W s i * Low.plain W i o U) (Sum.elim (fun i o U=> High.plain W i o U) (fun i o U=> (W.loop i).unmasked U o))
def fer (s:Seat n)(i:Barley):Config G n→ℝ:= fun U=> VerifiedReset.factor * ul R.path R.clip i 0 (s.view U)
def mote(R:Rep G n):Barley→ℕ:= Sum.elim (Low.length R.path) (fun i=> (tooth R i).length)
def port(R:Rep G n): Barley→ℝ:= Sum.elim (fun i=> |Low.mark R.path R.clip i|) (fun i=>(tooth R i).magnitude)
abbrev officeC (s:Seat n)(i:Barley):= boothC R (.inl (s,i))
lemma offt (s:Seat n)(i:Barley):coverNumber R.p.B (officeC R s i) =coverNumber R.p.B (fort R i):=(Seat.visit_count (p:=R.p) s (fort R i))
lemma ports_n (i:Barley):0≤port R i:=by unfold port; cases i <;> dsimp only[Sum.elim_inl,Sum.elim_inr]; exact abs_nonneg _; unfold Atom.magnitude; positivity
lemma fresh_loop (i:Fleece)(o:Site n)(U:Config G n): ul R.path R.clip (.inr i) o U=(tooth R i).unmasked U o:=by cases i <;> rfl
lemma gasG {i}(h:R.path.Bounds R.clip σ A C): (tooth R i).Invariant:=by cases i with
 | inr j=>exact (h.invariant j).1
 | inl j=> cases j with
          | inl j=> exact (h.invariant j).2.1
          | inr j=> exact (h.invariant j).2.2
lemma ulInv (i:Barley)(o:Site n)(h:R.path.Bounds R.clip σ A C): GaugeInvariant (ul R.path R.clip i o):=by
   cases i with
   | inl j=> exact fun k U=> congr_arg (_ * ·) (Low.plain_gauge ..)
   | inr j=> simp_rw [funext (fresh_loop R j o)]; intro t U; simp only[Atom.unmasked,Work.F05.slot_gauge]; exact gasG R h (t o) _
lemma ulLoci (i:Barley)(hB:2 ≤ R.p.B): LocalOn (fort R i) (ul R.path R.clip i (0:Site n)):=by
    cases i with
    | inl i=> exact fun U V h=> congr_arg (_ * ·) (Low.plain_local R.path i R.p hB _ U V h)
    | inr i=> rw [funext (fresh_loop R i 0)]; exact Extra.Iteration.Derivs.atom_local (tooth R i) 0
lemma strong_move {X:Type}{F:Config G n→X}{A: Support n}(h:LocalOn A F)(s:Seat n): LocalOn (s.spread A) (F ∘ s.view):=by
    intro U V ht; apply h; exact Push.Local.agrees_pull s.1 s.2 ht
lemma ferInv (s:Seat n)(i:Barley)(h:R.path.Bounds R.clip σ A C): GaugeInvariant (fer R s i):=by
    intro k U; simp only[fer,Seat.view,Push.Local.pull_gauge]; exact congr_arg (_*·) (ulInv R i 0 h _ _)
lemma ferLocal (s:Seat n)(i:Barley)(hB:2 ≤ R.p.B): LocalOn (officeC R s i) (fer R s i):=by intro U V h; exact congr_arg (_* ·) (strong_move (ulLoci R i hB) s U V h)
lemma ceast (i:Barley)(s:Seat n){U:Config G n}(hv:WilsonStartup.Decent R.clip R.p)(h:Healthy R.p.threshold (officeC R s i) U): pieceC R (.inl (s,i)) U= -(wake R i*fer R s i U):=by
    have ht: coal R i (s.view U)=ul R.path R.clip i 0 (s.view U):=by
       have he:=Seat.healthy s _ (fort R i) U |>.mp h
       cases i with
       | inl j=> exact Low.live_plain R.path R.clip j hv _ he
       | inr j=> rw [fresh_loop]; exact masked_eq _ (fort R (Sum.inr j)) (fun U:Config G n=> (tooth R j).unmasked U 0) _ he
    change -VerifiedReset.factor * (wake R i * coal R i (s.view U))=_; unfold fer; rw[ht]; ring
end YM.Trace.Fen
