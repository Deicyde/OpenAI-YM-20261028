import YM.MergeProof.North.Corn
import YM.MergeProof.Routes
import YM.MultipleContact.Bunch.Focal
import YM.MultipleContact.Bunch.Dew
import YM.MultipleContact.Bunch.Gush
import YM.MultipleContact.Bunch.Sugary
import YM.MultipleContact.Bunch.Stained
import YM.MultipleContact.Bunch.Stator
import YM.MultipleContact.Bunch.Fermi
import YM.MultipleContact.Bunch.Corn

/- generalized from YM.MergeProof.North.Lyme to arbitrary arity -/



/-! # Simultaneous support pricing at related pairs. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.MergeProof.BatchRibbons
variable {slot:Type}[Fintype slot][DecidableEq slot][Inhabited slot]
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent BatchRibbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus Switch
open Extra.Trajectories
open scoped Topology BigOperators Classical
variable {V ι J : Type}[Fintype V][DecidableEq V][Fintype ι]{G:Gauge}{f c:Side}{R:Rep G f}
local notation "X"=> Aged V slot
variable (v u:V)(B:Equiv.Perm V)(m:Motion)(x:Site f)(π:R.activities.Moves m.1 x)
def shuttled (M:Hat (X) R): Hat (X) R:= ⟨M.M.route π,drum (slot:=slot) B M.s, M.shiny.image (nome (slot:=slot) B),scalar m M.charge⟩
variable {w:Name V slot→ℝ}
lemma pull_onto : Surjective (pull m.1 x : Config G f→ Config G f):=fun U=>by
   let s:= m.1; refine ⟨pull s⁻¹ (-((s⁻¹).act x)) U,?_⟩ -- syntax inv
   rw [pull_pull,show affine s⁻¹ _ x=(0:Site f) from (by simp [affine]),show s⁻¹*m.1=1 from inv_mul_cancel _,pull_one]; funext e; simp [Lattice.translate]
local notation "M'"=> shuttled B m x π
lemma forecast (he:B v=u)(hw:∀ i:slot,w (v,i)=w (u,i))(A: Hat X R)(ht:Focused v A.s): fare (M' A) w=fare A w:=by
   have hx : Poly.toll w (drum (slot:=slot) B A.s)=Poly.toll w A.s:=by
      unfold Poly.toll; rw [drum,pares,prod_image (nome (slot:=slot) B).injective.injOn]; apply prod_congr rfl; rintro ⟨i,j⟩ hi; rw [show i=v from mem_singleton.mp (ht (mem_image_of_mem Prod.fst hi))]; change w (B v,j)= _; rw [he,hw]
   unfold Menu.fare sumFee shuttled; simp only [hx,norm_scalar]; rfl
lemma amounts (s:(X).Mode) (f': Config G f→ℂ)(A:ι→Hat X R)(he:∀ i,(A i).s=s)(hh:∀ U,∑ i,amount (A i) U=Poly.send s (f' U)) (U: Config G f): ∑ i,amount (M' (A i)) U=Poly.send (drum (slot:=slot) B s) (stepUp m x f' U):=by
   ext p; rw [Poly.part_sum,Poly.part_send]; simp_rw [varnish, Poly.part_send,shuttled,he]; split
   next ht=>
      have hx:= congr_arg (fun p:Poly X=>p.part s) (hh (pull m.1 x U)); simp only [Poly.part_sum,varnish,he,Poly.part_send,↓reduceIte] at hx; unfold stepUp; rw [← hx,← scales]; refine sum_congr rfl (fun i _=>?_); rw [scalar_mul,scalar_real];rfl
   simp
end YM.MergeProof.BatchRibbons
