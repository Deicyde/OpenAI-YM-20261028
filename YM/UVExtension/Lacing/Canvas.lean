import YM.UVExtension.Lacing.Remnant
/-! need `Flow` on any convergent step input. UT scales used Only real data.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Lacing
open Function Filter MeasureTheory Set Lattice Wilson RG Source Extra.Histories Labels
open Planned.GuardedAtom Guard Push Local MergeProof Motion Next.Foundations
open Bid Concert BoundedContinuousFunction Eyelet RoutesF Work.G08 Remnant
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n n':Side}{d:ℕ} {F:Frame G d}{p P :BudgetPoint}{H:Hol G}
local notation "R"=> RoutesF F n n' p P H
local notation "E"=> Cow G n' p d H
local notation "B"=> Cow G n P d H
local notation "Lc"=> Bucket F P H n
set_option quotPrecheck false
set_option synthInstance.maxHeartbeats 110000
open RoutesF
structure Course (L:ℕ→R) : Prop where
    useP (v:ℕ→E)(i:Option F.Index): Arrives v → Arrives fun n=> (L n).rain (v n) i
variable {L:ℕ→ Motion→RoutesF F n n' p P H}{Y:ℕ→ Motion→ (F.Coeff→ₗ[ℂ] Cow G n' p d H)}(hn: 2 ≤ n.val)
section
variable (hP:∀ i, Course (fun n=>L n i))(ht:∀ m i, Arrives fun n=>Y n m i)
include hP ht
lemma painted (i:Tally F) : Arrives fun k=> sell (L k) (Y k) hn i:=by
   exact ((((hP i.1).useP (fun k=>Y k i.1 (Size.axis F i.2)) (some i.2) (ht ..)).post (Eyelet.cap n F H P i.1 hn).continuous).post (rooms n F H P (aisleN (code (Tally F)) i)).continuous)

lemma wares (x:F.Coeff): Arrives (fun k=> major (L k) (Y k) hn x) ∧ Arrives (fun k=> minor (L k) (Y k) hn x):=by
   have hp(k):= pieces (L k) (Y k) hn x
   simp_rw [fun k=>(hp k).1,fun k=>(hp k).2]; constructor
   · exact Arrives.sum _ (fun i _=> ((painted hn hP ht i).post continuous_fst).post (continuous_const_smul _))
   exact Arrives.sum _ (fun i _=> ((painted hn hP ht i).post continuous_snd).post (continuous_const_smul (chips F x i)))
lemma pilastered (c:ℝ)(h:∀ᶠ k in atTop,∀ x:F.Coeff,F.coeffSize x ≤ c*F.coeffSize (major (L k) (Y k) hn x))(he:0≤ c)(x:F.Coeff): Arrives (fun k=> (steer (L k) (Y k) hn).symm x) ∧ Arrives (fun k=> crown (L k) (Y k) hn x):=by
   have hL:= Remnant.solved (f:=fun k=> major (L k) (Y k) hn) (fun i=>(wares hn hP ht i).1) (c*(F.extra+1:ℕ)) (by
     filter_upwards [h] with i hi x; exact (Local.norm_le_size ..).trans ((hi x).trans ((mul_le_mul_of_nonneg_left (Local.size_le_norm ..) he).trans_eq (mul_assoc ..).symm))) x
   refine ⟨hL,?_⟩
   have hh:= Remnant.loops (f:=fun k=> (minor (L k) (Y k) hn).toLinearMap) (x:=fun k=> (steer (L k) (Y k) hn).symm x) (fun i=>(wares hn hP ht i).2) hL
   unfold crown; simp only [LinearMap.comp_apply,LinearEquiv.coe_toLinearMap]; convert! hh
end
end YM.UVExtension.Lacing
