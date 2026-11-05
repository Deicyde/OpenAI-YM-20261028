import YM.MergeProof.North.Lyme
import YM.OPE.Replicas.Corn

/-!
# Many slots per cell: port of YM/MergeProof/North/Lyme.lean

Most of the proof can be shared verbatim with that for pairs. Costs at every step
use the same register though the group being transported can now be quite different.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus Switch
open Extra.Trajectories
open scoped Topology BigOperators Classical
variable {slotsZ : Type}[Fintype slotsZ][DecidableEq slotsZ] {V ι J : Type}[Fintype V][DecidableEq V][Fintype ι]{G:Gauge}{f c:Side}{R:Rep G f}
local notation "X"=> Names V slotsZ
variable (v u:V)(B:Equiv.Perm V)(m:Motion)(x:Site f)(π:R.activities.Moves m.1 x)
def shuttled (M:Hat (X) R): Hat (X) R:= ⟨M.M.route π,drum B M.s, M.shiny.image (nome B),scalar m M.charge⟩
variable {w:(V×slotsZ)→ℝ}
local notation "M'"=> shuttled B m x π
lemma forecast (he:B v=u)(hw:∀ i:slotsZ,w (v,i)=w (u,i))(A: Hat X R)(ht:Focused v A.s): fare (M' A) w=fare A w:=by
   have hx : Poly.toll w (drum B A.s)=Poly.toll w A.s:=by
      unfold Poly.toll; rw [drum,pares,prod_image (nome B).injective.injOn]; apply prod_congr rfl; rintro ⟨i,j⟩ hi; rw [show i=v from mem_singleton.mp (ht (mem_image_of_mem Prod.fst hi))]; change w (B v,j)= _; rw [he,hw]
   unfold Menu.fare sumFee shuttled; simp only [hx,norm_scalar]; rfl
lemma amounts (s:(X).Mode) (f': Config G f→ℂ)(A:ι→Hat X R)(he:∀ i,(A i).s=s)(hh:∀ U,∑ i,amount (A i) U=Poly.send s (f' U)) (U: Config G f): ∑ i,amount (M' (A i)) U=Poly.send (drum B s) (stepUp m x f' U):=by
   ext p; rw [Poly.part_sum,Poly.part_send]; simp_rw [varnish, Poly.part_send,shuttled,he]; split
   next ht=>
      have hx:= congr_arg (fun p:Poly X=>p.part s) (hh (pull m.1 x U)); simp only [Poly.part_sum,varnish,he,Poly.part_send,↓reduceIte] at hx; unfold stepUp; rw [← hx,← scales]; refine sum_congr rfl (fun i _=>?_); rw [scalar_mul,scalar_real];rfl
   simp
end YM.MergeProof.Ribbons.ManyCopies
