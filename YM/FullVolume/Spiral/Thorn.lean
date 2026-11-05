import YM.FullVolume.Spiral.Mystic
import YM.FullVolume.Spiral.Rune
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Paint.Tower
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus Next.Foundations Rank
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n m:Side}{Y:Hol G}
open MergeProof MergeProof.Matric FullVolume.Ray Jams Luna
variable {i:ℕ}{F:Labels.Frame G i}{B:BudgetPoint}{q t v a b s c u:ℝ}{p:sun→ Coefficient F n}{P:Desk G n}{y:F.Coeff}
local notation "A_"=> P.orient
set_option maxHeartbeats 380000
open Forum
open Extra.Histories.InputColumn
open UniformSpace
structure Swerve (f g: Coefficient F n)(Y:Hol G)(P:Desk G n): Prop where
   old:f.support=g.support
   axes : f.x=g.x
   stamp : (breakP f g).Format 0 Y P.orient
   bill : (breakP f g).remBound 0 P.orient P.k 0
variable (K:Keeper P.orient.p P.orient.activities)
namespace Swerve
variable {f g:Coefficient F n}(h:Swerve f g Y P)
include h
lemma twist (m:Motion)(x:P.orient.activities.Moves m.1 0)(R:SectionData F)(hs:R.Sound Y)(hc:2≤n.val): Swerve (audition x f) (audition x g) Y P:=by
   have he:= Hue.priceU m x R hs hc h.stamp h.bill; dsimp only at he; refine ⟨turn_same _ _ _ _ h.old, ?_ ,?_,?_⟩ -- x_eq simpler
   · unfold audition; split<;> simp [reorient,barAll,h.axes]
   · rw [← turn_br]; exact he.1
   rw [← turn_br]; simpa only [mul_zero] using he.2.1
lemma growing (z:ℂ): Swerve (Extra.Histories.stretch z f) (Extra.Histories.stretch z g) Y P:=⟨h.old,congr_arg (z • ·) h.axes,(stretch_br ..) ▸ stretch_format z h.stamp,mul_zero ‖z‖ ▸ ((stretch_br f g z) ▸ stretch_rem z h.bill)⟩
lemma warmth (hp:f.support=g.support)(hf: f.Format 0 Y P.orient)(hv:f.remBound 0 P.orient P.k t)(hg:g.Format 0 Y P.orient)(hX:g.remBound 0 P.orient P.k v) : ((alb f Y P K):Completion (Coin F Y P))=((alb g Y P K):Completion (Coin F Y P)):=by
   apply sub_eq_zero.mp; rw [← Completion.coe_sub]; apply norm_le_zero_iff.mp; rw [Completion.norm_coe]; apply (Coin.wealths ..).mpr; rw [map_sub,alb_read f Y K hf hv,alb_read g Y K hg hX, ← collected f g K hp hv hX]; exact alongPay ⟨⟨rfl,rfl⟩,rfl⟩ K _ h.stamp h.bill
omit h
lemma mortar {ι:Type}[Countable ι](L:ℕ≃ι×ℕ){p g:ι→ Coefficient F n}(h:∀ i,Swerve (p i) (g i) Y P)(hp:Summable fun i=>(p i).x)(hq:Summable fun i=>(g i).x)(he:∀ i V,Summable fun j=>(p j).forced i V)(hv:∀ i V,Summable fun j=>(g j).forced i V) :Swerve (Extra.Histories.merge L p) (Extra.Histories.merge L g) Y P:=by
    let q i:= breakP (p i) (g i); have hx:Extra.Histories.merge L q=breakP (Extra.Histories.merge L p) (Extra.Histories.merge L g):=melt L hp hq he hv
    refine ⟨funext (fun i=>congr_fun (h (L i|>.1)|>.old) (L i|>.2)),tsum_congr fun i=>(h i).axes,hx ▸ merge_format L q (fun i=> (h i).stamp),?_⟩
    rw [← hx]; have hP: (Extra.Histories.merge L q).remBound 0 P.orient P.k (∑' i:ι, (0:ℝ)):= (merge_budget L q P.sane (fun i=> (h i).bill) summable_zero).1; simpa only [tsum_zero] using hP
lemma piece (x z:Pin F n)(hx:(Matric.tell x).Format 0 Y P.orient)(hz:(Matric.tell z).Format 0 Y P.orient) (h:Rune x z P.orient.p):Swerve (Matric.tell x) (Matric.tell z) Y P:=by
   let V x':= P.k⁻¹*x'; let S:=(x-z).2; have hK:S.2=0:= sub_eq_zero.mpr h.force
   let y:=breakP (Matric.tell x) (Matric.tell z); have hh:y=Matric.tell (x-z):=rfl
   refine ⟨rfl,h.point,?_,0,0,le_rfl,le_rfl,(zero_add _|>.le),P.sane,⟨fun i=>0,budget0 ..,fun i=> ?_⟩,fun _=>0,by rw [mul_zero]; exact budget0 ..,fun i=>⟨le_rfl,fun V=>?_⟩⟩ -- hv forall
   · unfold Matric.tell at hx hz
     change (book (x-z).1 (x-z).2).Format _ _ _; let g:=(-1:ℂ); have hP: x.2-z.2=x.2+g • z.2:=by unfold g; simp; exact sub_eq_add_neg ..
     rw [show (x-z).2=(x.2+g • z.2) from hP]; exact formatK F _ _ (format_add F _ _ hx (show (book ..).Format .. from stretch_format g hz))
   · change (A_).p.supBounds 0 (mapSeat i) (x.2.1 i-z.2.1 i) 0; refine ⟨le_rfl,fun V hV j hj hA=>?_⟩
     have hZ: (x.2.1 i-z.2.1 i) ∘ increment V=ᶠ[𝓝 0] (fun _=> (0:ℂ)) ∘ increment V:=by filter_upwards [(h.germs i) V hV] with v hv; exact sub_eq_zero.mpr hv
     rw [Local.left_congr j V hZ]; exact (regular0 P.orient.p (mapSeat i) (0:Site n)|>.2).2 V hV j hj hA -- regular0 output implicit
   change ‖S.2 i V‖≤ 0; rw [hK]; simp
end Swerve
-- for Twist proof.As.Momentum
structure Elastic (Z:Plate F m n) (Y:Hol G)(R:Rep G n)(S:Rep G m):Prop where
  reg j f f' a b : RegFit S 0 i Y (mapSeat j) f→ RegFit S 0 i Y (mapSeat j) f'→ S.p.supBounds 0 (mapSeat j) f a→ S.p.supBounds 0 (mapSeat j) f' b→ (Matric.tell (Z.tint j f-Z.tint j f')).Format 0 Y R∧ Rune (Z.tint j f-Z.tint j f') (Z.tint j (f-f')) R.p
  force (j:ℕ) (f f':Config G m→ℂ) (a b:ℝ): SlotFit S 0 j f→SlotFit S 0 j f'→ (∀ V, ‖f V‖ ≤ a) → (∀ V,‖f' V‖ ≤ b) → (Matric.tell (Z.ink j f-Z.ink j f')).Format 0 Y R ∧ Rune (Z.ink j f-Z.ink j f') (Z.ink j (f-f')) R.p
end YM.FullVolume.Paint.Tower
