import YM.RG05Readout.Address.Sundrop
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Address
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Bid
open Extra.Histories Push Local Planned.GuardedAtom Guard MergeProof Extra.Histories.Relay Native
open PhysicalNext.Repeat Lotus Motion Trace.Physical Offsets
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{N m p d:ℕ} {s K α β γ A c t e:ℝ}
    {D:GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
set_option quotPrecheck false
local notation "Z"=> (C.path.levels.clock.op m p)
local notation "R"=> C.path.rep N p m
local notation "M"=> C.path.rep N p (m+1)
local notation "Kc"=> kappa C.path
local notation "O"=> Bud C p m
local notation "ψ"=> child C p m
local notation "L"=> C.path.S.block m
local notation "λ₀"=>(((L).val:ℝ)^d)
local notation "I"=> Palette C d
local notation "J"=> Mark C d
local notation "tilt"=> amplify d C L
local notation "N₀"=> Fintype.card J
local notation "η'"=> decay d L K c α* shiftFee (M).p
local notation "ϑ"=> tollP d K c β
local notation "π"=> tollV d L K c α β*shiftFee (M).p
local notation "Ω"=> margin d c K
local notation "v₀"=> wrap_price d C* Trace.Physical.Germ.wraps (M).p (C.side (m+1) p)
local notation "v₁"=> wrap_price d C* Trace.Physical.Germ.wraps (R).p (C.side m p)
variable {T:∀ i:Letter d,Heading (C.labels.level (kept i))} (hw:Plot D s K c α β T)
variable {u:∀ i:Bud C p m,(C.path.rep N p (m+1)).activities.Moves (1:Signed) (child C p m i)}

/-!
# Output calibrated primary graph on weighted addressed germs
-/

def beamCost (d:ℕ)(c K:ℝ):= margin d c K +1+c
variable {B Q B':ℝ}
variable {V:Palette C d→ₗ[ℂ]Tape G (C.side (m+1) p)}

-- Sized because need normalized log estimates in same graph
structure Onward (W:Palette C d→ₗ[ℂ]Tape G (C.side m p))(r:I≃ₗ[ℂ]I)(Q B B':ℝ) : Prop where
    aligned : ∀ x, Train (d:=d) D u (V x) (W (r x)) ((2*ϑ+π*B)*size (tilt x))
    back : Group C N m p d W B'
    pays x : size (tilt x) ≤ 2*Q*size (r x) ∧ size (r x) ≤ (beamCost d c K+(γ+oldCost d K*α))*size (tilt x)
    shape : Contour C m d (beamCost d c K) c (γ+oldCost d K*α) r.toLinearMap
variable (u)
variable (h:C.Makes)(hm:m<N)
include hw hm h u
lemma Onward.can (hc:Turns (K:=K) (β:=β) (c:=c) (α:=α) (γ:=γ) C N m p d B) (H:Group C N (m+1) p d V B)(hγ:0 ≤ γ)(hp:clipPrice (Fintype.card J) d (beamCost d c K) c≤ Q)(hk:0 ≤ Q)(he:Q*(γ+oldCost d K*α) ≤ 1/2)(hB:1 ≤ B')(hU: ahead K c d *(2*Q) ≤ B'):
     ∃ W Y, Onward (γ:=γ) (K:=K) (α:=α) (u:=u) (β:=β) (c:=c) (D:=D) (V:=V) W Y Q B B':=by
     obtain ⟨l,hS,hP⟩:= yield_now D hw u h hm
     choose P w z hW ht hV hL using angle (u:=u) hw H hS hc (fun x y r F hf=> hP F x y r hf)
     let Z' : Palette C d→ₗ[ℂ]Palette C d:= (slide_linear z).mk' _; have hr : Contour C m d (beamCost d c K) c (γ+oldCost d K*α) Z':= sails_now hw hW hL
     have hu:= hw.cursor.fits; have hv:=hw.a_pos
     have hΩ:0 ≤ Ω:= mul_nonneg (add_nonneg (sCpos (zero_le_one.trans hw.cursor.fits)) (aCpos (zero_le_one.trans hw.cursor.fits))) (zero_le_one.trans hw.posp)
     have hz x := hr.earns (show 0 ≤ beamCost d c K from add_nonneg (add_nonneg hΩ zero_le_one) (zero_le_one.trans hw.posp)) hw.posp (by unfold oldCost; positivity) hp hk he x
     have hy : Function.Injective Z':=by
           apply LinearMap.ker_eq_bot.mp; refine LinearMap.ker_eq_bot'.mpr fun v hv=>?_
           have hf:=hz v|>.1; rw [hv,size_zero,mul_zero] at hf; exact norm_le_zero_iff.mp ((size_norm v).trans ((size_refund L v).trans hf))
     let W:I≃ₗ[ℂ]I:= LinearEquiv.ofBijective Z' ⟨hy,LinearMap.injective_iff_surjective.mp hy⟩
     let X:I→ₗ[ℂ]Tape G (C.side m p):= ((slide_linear P).mk' _).comp W.symm.toLinearMap
     have hi (x):X (W x) = Slide x P := by change Slide (W.symm (W x)) P=_; rw [W.symm_apply_apply]
     let hi₀:=hw.cursor.sense d le_rfl
     have hw'(e: ℝ)(x:I): (∑ i:Mark C d,‖val x i‖*(e*chargeN L i))=e*size (tilt x):= by rw [← charge_sum L x,Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _=>mul_left_comm ..)
     refine ⟨X,W,fun x=>?_, ⟨fun x=>?_,hB⟩, hz,hr⟩
     · have ht':= Train.lots h hm Finset.univ hw.door (fun i _=> (hV i).gain (val x i)); rw [hw',show ∑ i:J,val x i • V (ticket i)=V x by simp_rw [← map_smul, ← map_sum, cardp x]] at ht'; rw [hi]; exact ht'
     obtain ⟨x,rfl⟩:=W.surjective x
     have hP:= Printed.all (Real.sqrt_pos.mpr (forcedPos ..)) (h.wilson.represents N p m hm.le).good Finset.univ hi₀.order hi₀.power (fun i _=>(ht i).twist hi₀.order hi₀.power (val x i)); rw [hw'] at hP; rw [hi]
     have ht :0 ≤ ahead K c d:= add_nonneg (mul_nonneg zero_le_two hΩ) zero_le_one
     refine ⟨_,Printed.grow hP ((mul_le_mul_of_nonneg_left (show _≤ 2*Q*size (W x) from hz x|>.1) ht).trans ?_)⟩
     rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hU (size_ge _)
end YM.RG05Readout.Address
