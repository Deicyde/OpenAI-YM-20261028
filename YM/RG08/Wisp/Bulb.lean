import YM.RG08.Wisp.Chord
import YM.RG08.Trickle.Fleet

/-!
# Single conditional transfer under the very same common denominator changes.
No dual number coercions required.
-/
noncomputable section
namespace YM.RG08.Wisp
open Function Finset PowerSeries Jetty Skiff Forms Steam Glyph Room Cloud Camera Room.Haze
open scoped BigOperators Topology PowerSeries Classical Matrix
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {I J R T A:Type}[Fintype I][Fintype J][Fintype R][Fintype T]

omit [Fintype I] in
private lemma stay_home {W:Finset I}{η:I→Port I}(h:anchored W η){f:Port I}(hf:Abroad W f):belt η f=f:= by rw [abroad_belt hf (y:=rod) h,belt_id]

section Center
variable (H:Ledger I R) (S:Ledger J T)

def forge (M:Port R):Port I:=belt (fun i=> liftInn (median H.view i)) M
def spit (M:Port I):Port I:=H.theater.brew (rise H.printed * M)
def valve (M:Port I):Port I:=spit H M*counter (rise H.connected)

lemma bulb (h:H.Sincere)(hs:S.Sincere){b:J→Port I}{η:I→Port I}(ht:Ledger.Covers H S b η)
   (M:Port I)(M':Port J)(hM:belt η (belt b M') = M):
   valve H M=belt b (valve S M'):=by
 obtain ⟨L,hL⟩:=ht.analytic
 let D : Port I:=belt b S.κ - H.κ
 let F : Port I:=belt b S.printed
 have hd:tiny D:=ht.scales;have hf:tiny F:= belt_tiny (hs |> S.cold) _
 let H' : Port I:= belt η F+belt η (liftInn H.K)-liftInn H.K
 have hh:tiny H':=neartiny ht.echo hf _
 have hy:= ht.law
 simp only [map_add,ht.first,stay_home ht.gateFix ht.outside] at hy
 rw [show (belt η (belt b S.printed) +belt η (liftInn H.K)+belt b S.κ-liftInn H.K-H.κ)=D+H' by unfold D H' F;abel, rise_together hd hh,mul_assoc] at hy
 have he:Abroad H.theater.foam (rise D):=abroad_rise (H:=H.theater) (show Abroad H.theater.foam D from fun i hi=>by unfold D;rw [map_sub,ht.outside i hi,h.perimeter i hi,sub_zero]) hd
 have hs':spit H M=rise D*belt b (spit S M'):=by
    unfold spit
    rw [←hy,←hM,mul_assoc,H.theater.brew_shunt he]
    have ht':= stirred H.theater ht.echo ht.gateFix h.boil hf (belt b M');dsimp only at ht'
    rw [ht', ←belt_rose _ (hs |> S.cold),←_root_.map_mul,entrusted hL] -- F let mismatch
 have hi: D+belt b S.connected=H.connected:=by
    have hd' := Ledger.impress H S h hs b η ht; rw [map_add] at hd'; unfold D; rw [add_comm _ H.connected] at hd'; rw [sub_add_eq_add_sub,hd']; abel
 have ha:rise H.connected=rise D*belt b (rise S.connected):=by rw [←hi,rise_together hd (belt_tiny (S.void hs) _),belt_rose _ (S.void hs)]
 have hl : (rise H.connected)* (valve H M)=spit H M:=by
    unfold valve;rw [counter_pays _ _ (rise_unit (H.void h)), mul_comm _ (rise _),←mul_assoc,rise_unit (H.void h), one_mul]
 have hr : (rise S.connected)* (valve S M')=spit S M':=by
    unfold valve;rw [counter_pays _ _ (rise_unit (S.void hs)), mul_comm _ (rise _),← mul_assoc,rise_unit (S.void hs),one_mul]
 have hz : IsUnit (rise H.connected) :=⟨⟨_,_,rise_unit (H.void h),mul_comm .. |>.trans (rise_unit (H.void h))⟩,rfl⟩
 apply hz.mul_right_inj.mp
 rw [hl,ha,mul_assoc,←_root_.map_mul,hr];exact hs'

/-- Track a mark polynomial through mean+centering, exact specialization, no phase arena. -/
theorem glowing (M:Port R)(h:H.Sincere) :
 spit H (forge H M)=Glyph.house H.prices (mView H.theater H.view) (rise (stock H.input)* M):=by
 have he:tiny (stock H.input):=by unfold tiny stock;rw [PowerSeries.coeff_mk];simp [showV,h.cards.2.1.dark,parley_zero]
 unfold spit Ledger.printed forge
 rw [←belt_rose _ he,←_root_.map_mul,Haze.stood h.deck h.cards.2.2]

theorem receipt (M:Port R)(h:H.Sincere):
 valve H (forge H M)=Glyph.house H.prices (mView H.theater H.view) (rise (stock H.input)* M)*counter (Glyph.house H.prices (mView H.theater H.view) (rise (stock H.input))):=by
 rw [valve,glowing H M h,housed _ h.cards.2.1 h.cards.1 h.cards.2.2];rfl

def pulse (l:ℕ)(S:GrainS R)(f:Pearl):Port I:=Trickle.mark l (Trickle.mouth (mView H.theater H.view) (Skiff.spin l H.prices H.input S 1)) f
lemma rush(l:ℕ)(P:GrainS R)(f:Pearl)(h:H.Sincere)(hs:Lit l P)(hP:Trickle.Combed P):pulse H l P f=valve H (forge H (Trickle.mark l P f)):=by rw [receipt H _ h]; exact Trickle.report _ h.cards.2.1 h.cards.1 hs hP h.cards.2.2 _
end Center
variable [Fintype A]{H : Ledger (Raw A I) R}{S:Ledger (Raw A J) T}{q:Rail A I J}
theorem journey (h:Rail.Decked H S q)(M:Port R)(M':Port T)(hh:belt q.x (forge S M')=forge H M):valve H (forge H M)=belt q.b (valve S (forge S M')):=bulb H S h.hH h.hS (Rail.scanned q h) _ _ (by rw [Rail.composed,hh])
-- # Reduce to actual EPS charts & cofinal in separate module
end YM.RG08.Wisp
