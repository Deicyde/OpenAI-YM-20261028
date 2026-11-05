import YM.RG05Readout.Address.Shaper
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
section
variable {P Q:Tape G (C.side (m+1) p)}{U V: Tape G (C.side m p)} {x z x' z':Palette C d} (o:Site (C.side (m+1) p)) {r:ℝ}
variable {o}
lemma Course.rise (hC:Course (D:=D) o P U x z u t)(hu:u ≤ s)(ht:t≤r):Course (D:=D) o P U x z s r:= ⟨hC.paid.grow hu,hC.ready.extend ht⟩
include hp h hm hx
lemma Course.dual (hP:Course (D:=D) o P U x z u t)(hQ:Course (D:=D) o Q V x' z' r c): Course (D:=D) o (P+Q) (U+V) (x+x') (z+z') (u+r) (t+c):= ⟨hP.paid.addP hQ.paid (h.wilson.represents N p m hm.le|>.good) (hp.sense d le_rfl).order (hp.sense d le_rfl).power,hP.ready.add hQ.ready h hm hx⟩
lemma Course.faith {I:Type*} {f:I→Tape G (C.side (m+1) p)}{g:I→Tape G (C.side m p)}{u r:I→ℝ}{x z:I→Palette C d}(A:Finset I)(he:∀ i∈A,Course (D:=D) o (f i) (g i) (x i) (z i) (u i) (r i)) : Course (D:=D) o (∑ i∈A, f i) (∑ i∈A,g i) (∑ i∈A,x i) (∑ i∈A,z i) (∑ i∈A,u i) (∑ i∈A,r i):=by
   exact ⟨Printed.all (Real.sqrt_pos.mpr (forcedPos ..)) (h.wilson.represents N p m hm.le).good A (hp.sense d le_rfl).order (hp.sense d le_rfl).power (fun i hi=>(he i hi).paid),Travel.list A h hm hx (fun i hi=>(he i hi).ready)⟩
omit h hm hx
lemma Course.rescale (j:ℂ)(hP:Course (D:=D) o P U x z t u) : Course (D:=D) o (j • P) (j • U) (j • x) (j • z) (‖j‖*t) (‖j‖*u):=⟨hP.paid.twist (hp.sense d le_rfl).order (hp.sense d le_rfl).power j, hP.ready.smul j⟩
end
section
variable (D)
structure Plot (s K c α β:ℝ) (T:∀ i:Letter d,Heading (C.labels.level (kept i))) : Prop where
    cursor : Cursor C N m p d s K
    posp : 1 ≤ c
    a_pos : 0≤α
    b_pos : 0≤β
    star i : ∃ a:ℝ, Pricing (S (kept i)) C.path N p m Y D (T i) a c α β ∧ triangularPrice (F (kept i)) a ≤ c
    anyT : ∃ B:Heading (C.labels.level 0),∃ a:ℝ, Pricing (S 0) C.path N p m Y D B a c α β
    door : SoundDoor Z D
    enter : κ (m+1) ≤ 1
end
variable (o:Site (C.side (m+1) p)) (ho:(C.path.levels.clock.op m p).ratio.parent o=0)
variable {T:∀ i:Letter d,Heading (C.labels.level (kept i))}(hw:Plot D s K c α β T) (he:MapsTo (fun x=>δ+(((C.path.S.block m).val:ℝ)⁻¹) • x) Native.box Native.box)
-- Lean D explicit from structure.
local notation "r"=> Native.pull δ ℓ
-- remainder rate payments scalar & address. ν_t scaling.
include hw he h hm ho
lemma jewels (V:Tape G (C.side (m+1) p))(η:ℝ) (hP:Necklace (F 0) (S 0) Y M o (κ (m+1)) d V η):
     let A:= ℓ*(2*(c+α)); let B':= ℓ*((1+c+β)+(2+α))
     ∃ W:Tape G (C.side m p), Course (d:=d) (D:=D) o (V.comp r) W 0 0 (A*η) (B'*η):=by
   intro A B'; induction hP with
   | empty=> refine ⟨0,?_⟩; simp only [LinearMap.zero_comp,mul_zero]; exact ⟨Printed.blank (Real.sqrt_pos.mpr (forcedPos ..)),Travel.vac le_rfl⟩
   | @chain Vv r' k b f hf hp P hu ht hs ih=>
      obtain ⟨F',hF⟩:=ih; obtain ⟨P0,a,h₀⟩:=hw.anyT
      obtain ⟨U,hU⟩:= high_curve h hm o ho h₀ he f hf hp P hu ht hw.posp hw.a_pos hw.b_pos hw.enter
      have hW:=hU.dual (D:=D) hw.cursor h hm hw.door hF
      simp only [add_zero] at hW
      refine ⟨U+F',?_⟩; rw [LinearMap.add_comp]; refine hW.rise ?_ ?_
      · let u:=(F 0).coeffSize P.x; have hv:0 ≤ u:= Work.G08.size_nonneg ..; have ht0:= rem_nonneg ht; have hc:= hw.a_pos; have hc':= zero_le_one.trans hw.posp; have hf0:= Priced.nonneg d hp
        rw [mul_add A]; apply add_le_add_left
        change k*ℓ*(c*u+α*r'+(c*u+α*r')) ≤ A*(k*(u+r'))
        rw [show A*(k*(_+_))=k*ℓ*(2*((c+α)*(u+r'))) by unfold A;ring]; apply mul_le_mul_of_nonneg_left _ (by positivity); nlinarith only [hc,hc',ht0,hv,mul_nonneg hc hv,mul_nonneg hc' ht0]
      let u:=(F 0).coeffSize P.x; have hv:0 ≤ u:= Work.G08.size_nonneg ..; have ht0:= rem_nonneg ht; have hc:= hw.a_pos; have hc':= zero_le_one.trans hw.posp; have hb:= hw.b_pos; have hf0:= Priced.nonneg d hp
      rw [mul_add B']; apply add_le_add_left
      rw [show B'*(k*(u+r'))=k*ℓ*(((1+c+β)+(2+α))*(u+r')) by unfold B';ring]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      change _*u+_ ≤ _; nlinarith only [mul_nonneg (show 0 ≤ 1+c+β by positivity) ht0, mul_nonneg (show 0≤2+α by positivity) hv]

-- first compile
end YM.RG05Readout.Address
