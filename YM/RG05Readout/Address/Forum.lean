import YM.RG05Readout.Address.Skein
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Address
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Bid
open Extra.Histories Push Local Planned.GuardedAtom Guard MergeProof Extra.Histories.Relay Native
open PhysicalNext.Repeat Lotus Motion Trace.Physical Offsets
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical

variable {G:Gauge}
variable {C:Family G} {N m p d:ℕ}{δ:E4}
set_option quotPrecheck false
local notation "Z"=>C.path.levels.clock.op m p
local notation "R"=> C.path.rep N p m
local notation "M"=> C.path.rep N p (m+1)
local notation "F"=>C.labels.level
local notation "Y"=> C.params
local notation "S"=> C.localSection
local notation "κ"=> kappa C.path
local notation "L"=> C.path.S.block m
local notation "v"=> ((L).val:ℂ)^d
local notation "ℓ"=> (((L).val:ℝ)⁻¹)
variable {s t K u τ α c β a:ℝ}{D:GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)} (hp:Cursor C N m p d s K) (h:C.Makes)(hm:m<N)(hx:SoundDoor (C.path.levels.clock.op m p) D)(hδ: δ∈Native.box)
/-!
# Composing all charges on a physical snapshot
-/
/-!
# Snapshot recurrence per-child

This costs in threshold field column convention, including script letters on
root test. Each inequality holds for the ONE same represented history. Underlying
valuation paths pay separate addressed root counts in the outer application.
-/
variable (o:Site (C.side (m+1) p)) (ho:(C.path.levels.clock.op m p).ratio.parent o=0)
variable {T:∀ i:Letter d,Heading (C.labels.level (kept i))}(hw:Plot D s K c α β T) (he:MapsTo (fun x=>δ+(((C.path.S.block m).val:ℝ)⁻¹) • x) Native.box Native.box)
local notation "r"=> Native.pull δ ℓ
local notation "Pr"=> Printed C d R 0 (κ m)
local notation "acc"=> aCost d K
local notation "sta"=> stCost d K

def Slide {A:Type*} [AddCommGroup A] [Module ℂ A] (x:Palette C d)(z:Mark C d→A):A:=∑ i:Mark C d,val x i • z i -- remove out
lemma slide_linear {A:Type*} [AddCommGroup A][Module ℂ A] (s:Mark C d→A): IsLinearMap ℂ fun x:Palette C d=> Slide x s:=by
   constructor
   · intro x y; unfold Slide val;simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
   intro a x; unfold Slide val; simp only [Pi.smul_apply,smul_assoc,Finset.smul_sum]

def decay (d:ℕ)(P:Side)(K c α:ℝ):ℝ:= (stCost d K+aCost d K)*α+ (↑P.val:ℝ)⁻¹*(2*(c+α))
def margin (d:ℕ)(c K:ℝ):= (stCost d K + aCost d K)*c
-- trivial estimates high
lemma aCpos (hp:0 ≤ K):0 ≤ aCost d K:= by unfold aCost; positivity
lemma sCpos (hp:0 ≤ K):0 ≤ stCost d K:= by unfold stCost; positivity
lemma decays (P:Side)(hp:0 ≤ K)(hc:0 ≤ c)(hα:0 ≤ α): 0 ≤ decay d P K c α:=by unfold decay; have hu:=aCpos (d:=d) hp; have he:=sCpos (d:=d) hp; positivity

def tollV (d:ℕ)(L':Side)(K c α β:ℝ):= aCost d K*((2+α)+K*α)+(↑L'.val:ℝ)⁻¹*((1+c+β)+(2+α))
def tollP (d:ℕ)(K c β:ℝ) := aCost d K*(1+c+β+K*c)
-- ONE primary letter inventory prices with that common T. choose per stamp witnesses first. In addition Φ shift
structure Swells (o:Site (C.side (m+1) p)) (z:Mark C d→Tape G (C.side m p))(x y:Mark C d→Palette C d) :Prop where
   current i : Course (D:=D) o ((micro C i o M).comp (Native.pull δ ℓ)) (z i) (x i) (y i) (margin d c K*chargeN L i) (tollP d K c β*chargeN L i)
   age i: size (x i) ≤ margin d c K*chargeN L i
   debits i: size (Address.clear C d (weights i) (x i - leadScale C L i (T i.1)))≤ oldCost d K*α
-- Stage orientation. only anchor iteration below.
include hw he h hm ho
lemma slip : ∃ z x y, Swells (δ:=δ) (T:=T) (K:=K) (D:=D) (c:=c) (α:=α) (β:=β) o z x y:=by
   have hB(i:Mark C d): ∃ z x y, Course (d:=d) (D:=D) o ((micro C i o M).comp (Native.pull δ ℓ)) z x y (margin d c K*chargeN L i) (tollP d K c β*chargeN L i)∧ size x ≤ margin d c K*chargeN L i∧ size (Address.clear C d (weights i) (x - leadScale C L i (T i.1))) ≤ oldCost d K*α:=by
      have hδ:δ∈Native.box:= by simpa using he Native.box0
      obtain ⟨k,hk⟩:=hw.star i.1
      obtain ⟨V,x,z,hC,hV,hy⟩:=primary_curve hw.cursor h hm hδ i.1 o i.2 ho hk.1 hw.posp hw.a_pos hw.b_pos
      let F':=(micro C i o M); let Q:=chargeN L i; have h1 :1 ≤ Q:=charge_one _ _; have hu:=zero_le_one.trans hw.cursor.fits; have hc:= zero_le_one.trans hw.posp; refine ⟨V,x,z,Course.rise hC ?_ ?_,?_,hy⟩
      · unfold margin; rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (aCpos hu)) (mul_nonneg hc (zero_le_one.trans h1))
      · change aCost d K * (1+c*Q+β+K*(c*Q))≤ tollP d K c β*Q
        unfold tollP; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ (aCpos hu); nlinarith only [mul_le_mul_of_nonneg_left h1 hw.b_pos,h1]
      apply hV.trans; unfold margin; rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (sCpos hu)) (mul_nonneg hc (zero_le_one.trans h1))
   choose z x y hC hV hW using hB; exact ⟨z,x,y,hC,hV,hW⟩
-- assembled Travel estimates. Cancellation needs simultaneous log/k partner snapshots; priced at root after stencil placement.
omit he ho
lemma all_sheet (x:Palette C d) {z:Mark C d→Tape G (C.side m p)}{w g:Mark C d→Palette C d} (hs : Swells (δ:=δ) (T:=T) (K:=K) (D:=D) (c:=c) (α:=α) (β:=β) o z w g): -- z variable? update
    Course (D:=D) o ((Slide x (fun i=>micro C i o M)).comp r) (Slide x z) (Slide x w) (Slide x g) (margin d c K *size (amplify d C L x)) (tollP d K c β*size (amplify d C L x))∧ size (Slide x w) ≤ margin d c K*size (amplify d C L x):=by
    have hz':= hs.current
    have hx (i:Mark C d):= (hz' i).rescale hw.cursor (val x i); have hw'(e:ℝ) : (∑ i:Mark C d,‖val x i‖ * (e*chargeN L i))=e*size (amplify d C L x):=by rw [← charge_sum L x,Finset.mul_sum]; exact Finset.sum_congr rfl fun i _=>mul_left_comm ..
    have hk:= Course.faith hw.cursor h hm hw.door Finset.univ (fun i _=>hx i)
    rw [hw',hw'] at hk
    refine ⟨?_,?_⟩
    · rw [Slide]; rw [show ((∑ i:Mark C d,val x i • micro C i o M):Tape G (C.side (m+1) p)).comp (Native.pull δ ℓ)=∑ i:Mark C d,val x i • (micro C i o M).comp (Native.pull δ ℓ) from ?_]
      · exact hk
      ext1 u; simp only [LinearMap.comp_apply,LinearMap.smul_apply,LinearMap.sum_apply]
    rw [← hw']; apply (size_sum ..).trans; apply Finset.sum_le_sum; intro i _; rw [size_smul]; exact mul_le_mul_of_nonneg_left (hs.age _) (norm_nonneg _)
end YM.RG05Readout.Address
