import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Turn.Fanfare
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cadre.Tournament
import YM.RemainderComparison.Script.Layout

/-!
# Rotation of the given chart and its real perturbations

LABELLED orientation, before taking products/capturing density. Needed also
for some of the unmarked real calibration clauses. Adaptations of
Repeat.Turn.tours/trumpets/retaining (Forests move BEFORE log).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Valse
open Function Filter Finset Lattice Wilson RG Pressure Pressure.Tube Precision Tree MeasureTheory
open AnalyticBridge.GaussianFieldAlignment Locations Channels
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Itinerary Raw Matter
open Next.Fluctuations Next.SectorChange Push.SectorMeasure Push.AbsoluteSums Oriented
open PhysicalNext.Repeat Lotus Merge Palette Turn
open Mosaic
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {ι ι' δ : Type} {G : Gauge} {c f : Side} {S : StepData c f} {s : Signed} {b : Site c}
    {F : Forest S.ratio} {P : Teller G} {T : Tube G S} {X : Coat T F} {Y : Coat T (Locations.forest s b F)}
    {W α μ C : ℝ} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {L : Side}
    {R : Rep G f} (π : R.activities.Moves s (S.ratio.embed b)) (H : Cash W α μ L Q o C T R)
variable (M : ι→Leaf R)(N:ι'→Leaf R)(u : ι≃ι')

-- no assumptions on Brush beyond Cash
structure Turns : Prop where
    clan i : badge R π ((M i).turn.badge S)= (N (u i)).turn.badge S
    pay i U : (M i).ingredient (pull s (S.ratio.embed b) U)=(N (u i)).ingredient U
namespace Turns
variable (B: Turns π M N u)
include B

def drums : Lyric.Drums M S ≃ Lyric.Drums N S:= Equiv.subtypeEquiv u.finsetCongr fun i=> by
    have he (j:ι): Palette.sign N S (u j)=badge R π (Palette.sign M S j):=(B.clan _).symm
    constructor
    · intro hp j; obtain ⟨j,rfl⟩:= u.surjective j; intro h k; obtain ⟨k,rfl⟩:=u.surjective k; intro hh hx
      refine congr_arg u (hp (show j∈i from by simpa using (show u j ∈ u.finsetCongr i from h)) (show k∈i from by simpa using (show u k∈u.finsetCongr i from hh)) ?_)
      rw [he,he] at hx; exact (badge R π).injective hx
    intro hp j h k hh hx; apply u.injective; exact hp (show u j∈ u.finsetCongr i from by simp [show j∈i from h]) (show u k∈ u.finsetCongr i from by simp [show k∈i from hh]) (by rw [he,he,hx])
local notation "D₁"=> drums π M N u 
lemma tran (i: Lyric.Drums M S) (j : ι): j∈ i.val ↔ u j∈(D₁ B i).val:= (Turn.given u i.val _).1 rfl j
lemma territory (i: Lyric.Drums M S) : (team N (D₁ B i)).signs S=Turn.caravan R π ((team M i).signs S):=by
    apply (Turn.given (badge R π) _ _).2; intro z; rw [Palette.label,Palette.label]; unfold Tickets.reach; rw [mem_image,mem_image]; conv_rhs=> rw [← u.exists_congr_right]
    exact exists_congr (fun j=> and_congr (tran π M N u B i j) (show _ ↔ Palette.sign N S (u j)=_ from by rw [show Palette.sign N S _=badge R π _ from (B.clan j).symm,Equiv.apply_eq_iff_eq]))

-- price of one leaf's tested multiplier (pull *input all*)
lemma peals (hp:Tuned s b X Y) (i:ι)(a:ℝ)(U:Directions G f) : (M i).paidU Y a (wheels (S:=S) s b X.V U)=(N (u i)).paidU X a U:=by
    unfold Leaf.paidU Leaf.fond; rw [hp.completed,B.pay,hp.toParked.aligned.2.1]
    apply congr_arg; apply hp.imposes; apply hp.plazas; rw [← B.clan i]; exact (display (StepData.sendSites s b) _ _).1 (Turn.insignia T R π 0 X.B _)

-- account even when multiple indices name same leaf copy
omit B in
lemma astray {ι:Type} (M:ι→Leaf R) (i: Lyric.Drums M S) (f:Leaf R→ℝ): ∏ j∈(team M i).own,f j=∏ j∈i.val,f (M j):= Finset.prod_image (fun _ h _ h' e=> i.prop h h' (congr_arg (fun k:Leaf R=>(k.turn).badge _) e))
lemma praise (hp:Tuned s b X Y) (i:Lyric.Drums M S)(a:ℝ)(U:Directions G f) : (team M i).paidU Y a (wheels (S:=S) s b X.V U)= (team N (D₁ B i)).paidU X a U:=by unfold Team.paidU; rw [astray,astray]; exact values u _ _ (tran π M N u B i) _ _ fun j _=> peals π M N u B hp j a U
include H
lemma reckons (h:Tuned s b X Y) (z:Air f G)(hα:X.x=α)(hK:X.width=o.K)(hx:X.manifest)(hy:Y.manifest)(l:Finset ℕ)(p:Molecule S)(w:Lyric.Drums M S): (team M w).premium Y W o.a Q.table l Q.halo (exhale s b X.V S z) p=(team N (D₁ B w)).premium X W o.a Q.table (π.kp.finsetCongr l) Q.halo z (caravan R π p):=by
   unfold Team.premium; rw [territory]; apply if_congr
   · simp
   · have ht:= H.laws.intake.ready; have hh: ShellAccess S G X.x W X.width o.γ:=by rw [hα,hK]; exact H.laws.data.access
     rw [h.axle ht hh]; refine congr_arg₂ (· * ·) (praise π M N u B h ..) (values (badge R π) _ _ ?_ _ _ fun j _=>Turn.commend R π H h z hα hK hx hy j _)
     intro i; simp [caravan]
   rfl
end Turns
end YM.RemainderComparison.Valse
