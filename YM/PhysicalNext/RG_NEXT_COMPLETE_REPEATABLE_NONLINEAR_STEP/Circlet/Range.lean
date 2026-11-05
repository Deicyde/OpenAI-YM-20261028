import YM.Further.DENSE_MIXED_KERNELS.Hall
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Roost.Foundry
import YM.Planned.PRIMARY_INTEGRAL_295.Gala
/-!
 # Support carrying invoice. Purchased BEFORE requests on period. Not mistaking lesser A.Fits chart on ℓ=500.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Circlet
open Function Filter Set Lattice Wilson RG RG.Supply Pressure Tree Next.SectorChange Finset
open Push Push.AbsoluteSums Gas JointLoad JointLoad.Heir JointLoad.Heir.Suite Input Org Labels
open Extra.Histories Extra.Histories.Doors Next.Foundations
open AnalyticBridge.VerifiedReset.Time Next.Scheduling Next.Fluctuations
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{c f:Side}{S:StepData c f} {x:ℝ}{r d:ℕ} (o : Site f){P B:BudgetPoint}
section near
variable {Y: Support c} (hw: Walled S ((localSection G d).footprint (0:Site f)) Y x r)(ht:P.B=radiusB x) (hs:B.B ≤2*P.B)
include hw ht hs
-- d unit etc. Padded.Support.C.Condition even at touching corner.
lemma setting (ha:minSide G d ≤ B.B) (hq:11*Planned.AtomRegular.toll r ≤ P.B) (hp:100*(r+20)*(P.B+1)≤ c.val): Nonwrapping Y 0 ∧ coverNumber P.B Y ≤ P.B:=by
   have he:=close_stencil G d B.B f ha 0; let U:= (localSection G d).footprint (0:Site f)
   have hz : (0:Site f)∈U:= mem_image.mpr ⟨0,(sound G d).anchored,by simp⟩
   have h0:= P.B_pos; have hm:Y ⊆ Footprint.enlargement S.ratio r P.B U:= ht.symm ▸ hw
   constructor
   · intro y hy; have hh:= Footprint.where_from S.ratio r P.B B.B U hz (hm hy) h0 hs; let v:=S.ratio
     have hv:v.parent 0=0 := v.root.map_zero ▸ v.embed_parent 0 -- syntax
     unfold Footprint.extentCost at hh; rw [show S.ratio.parent 0=0 from hv] at hh
     have he:1+coverNumber B.B U ≤ 1+1:= Nat.add_le_add_left he _
     have hk:10*((r+20)*P.B*(1+1))< c.val:=by nlinarith only [hp, h0, Nat.zero_le r]
     exact lt_of_le_of_lt (Nat.mul_le_mul_left 10 (hh.trans (Nat.mul_le_mul_left _ he))) hk
   have hv:= Corona.collapse S.ratio U B.B P.B h0 hs r
   apply (Corona.cover_mono hm _).trans; apply Nat.le_of_mul_le_mul_left _ S.patch.L.property
   apply hv.trans; let L:=S.patch.L.val; have hL:= S.patch.L.property
   have hx:L+10*coverNumber B.B U ≤ L*11:=by have hL:1≤L:=hL; change coverNumber B.B U ≤ 1 at he; omega
   apply (Nat.mul_le_mul_right (Planned.AtomRegular.toll r) hx).trans; rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ hq
include hw
end near
end YM.PhysicalNext.Repeat.Circlet
