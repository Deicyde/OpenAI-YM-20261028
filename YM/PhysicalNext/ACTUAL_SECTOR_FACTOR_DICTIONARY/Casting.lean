import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Seats

/-! Cast saved letters back into the actual currency of the scripts. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Dictionary.Lobbies.Casting
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores Tree Precision Exterior MeasureTheory Matrix Bloch
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Push.SectorMeasure Push.SectorMeasure.Oriented
open AnalyticBridge.Annulus.Map
open AnalyticBridge.RelativeLogdet
open AnalyticBridge.Sharp
open AnalyticBridge.LocalGaussian Spot Spot.Programme
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Wires Geo Notify Voice Voice.Defenses Voice.Check Parcel Shipment SectorNext.Reconnect SectorNext.Reconnect.Words
variable {G : Gauge} {ι : Type} [DecidableEq ι] {c f : Side} {S : StepData c f}
variable (D : AnalyticBridge.LocalGaussian.Desk G S) (Z : Art ι D) (t : ℝ) (h : Lit D)
    {F : Forest S.ratio} {A : Stores S} {a : Ensign S ι} (C : Casting D Z a F A) (k₀ k : S.Choices) (V : Config G c)
local notation "u₀" => chosen D F k₀ A k
local notation "b₀" => Fleet.kSet a
local notation "X₀" => wood D Z a
local notation "N₀" => Shipment.key D Z a
local notation "H₀" => Native.kinetic D.tube F k₀ D.betaHat

-- Paying letters accumulated here. Keep complete marks outside this
-- product (same p and mean in both). This distinction includes
-- a **qualified K** in the ordinance outside, since the run stamps demand
-- a vacuum gate, not a mark on that slot.
def load (F : Forest S.ratio) (A : Stores S) (a : Ensign S ι) (p : Refs G f) :=
    let s := ∏ i∈major D a A F, latch D i F A (Fleet.kSet a) k V p
    let e := ∑ i∈paper D a A F, sew D i F A (Fleet.kSet a) k V p
    let z := ∏ i∈alternates a, shine D t i.1 i.2 F A (Fleet.kSet a) k V p
    s*Real.exp e * z

def tax (F : Forest S.ratio) (A : Stores S) (a : Ensign S ι) (p : Refs G f) :=
    let w:= (Fleet.addSet a).toRight.toRight
    (∏ i ∈ w, choices D Z t (.inr (.inr i)) F A (Fleet.kSet a) k V p) *
      ∏ j∈Fleet.kSet a\vacuum a, shutter D Z t (known j) a F A (Fleet.kSet a) k V p

include C h
private lemma sheet (p : Refs G f) :
    let O:= plumage D a A F; let E:= paper D a A F
    ∏ i∈ a.toLeft,Booklet.vitalPage D i F A b₀ k V p = (∏ j∈O,latch D (Sum.inl j) F A b₀ k V p)*Real.exp
      (∑ j∈E,sew D j F A b₀ k V p) := by
  intro O E
  have hm : (a.toLeft:Set (Fleet.Packet c f)).PairwiseDisjoint (fun i=>Booklet.checks D i F A) :=
    fun i hi j hj h₁=> (Booklet.sheets D Z h.toApp ∅ (Finset.Subset.refl _) (Finset.Subset.refl _) C.connected.1 hi hj h₁ F A).1
  have hf : (a.toLeft:Set (Fleet.Packet c f)).PairwiseDisjoint (fun i=>Booklet.history D i F A) :=
    fun i hi j hj h₁=>(Booklet.sheets D Z h.toApp ∅ (Finset.Subset.refl _) (Finset.Subset.refl _) C.connected.1 hi hj h₁ F A).2
  unfold Booklet.vitalPage; rw [Finset.prod_mul_distrib,←Real.exp_sum]
  unfold O E plumage paper; rw [Finset.prod_biUnion hm,Finset.sum_biUnion hf]
  refine congr_arg₂ HMul.hMul (Finset.prod_congr rfl fun i hi=>Finset.prod_congr rfl fun j hj=>?_) rfl
  exact (if_pos (Lobbies.reserved C (Finset.mem_biUnion.mpr ⟨i,hi,hj⟩)).2).symm

lemma combine (p : Refs G f) :
    (∏ i∈a,shutter D Z t i a F A b₀ k V p)= ((load D t k V F A a p:ℝ):ℂ) * tax D Z t k V F A a p := by
  let P (i:Bill S ι):=shutter D Z t i a F A b₀ k V p
  let K i := latch D i F A b₀ k V p
  let Y:=a.toLeft; let O := plumage D a A F; let E := paper D a A F
  have he : Disjoint O (optionalTests a) := Finset.disjoint_left.mpr fun i h₁ h₂=> (free C h₂).2 (Lobbies.reserved C h₁).2
  have hf := Finset.prod_union he (f:=fun i=>K (.inl i))
  unfold load tax; dsimp only
  rw [Finset.prod_sum_eq_prod_toLeft_mul_prod_toRight]; rw [Finset.prod_sum_eq_prod_toLeft_mul_prod_toRight (s:=a.toRight)]
  rw [Finset.prod_sum_eq_prod_toLeft_mul_prod_toRight (s:=a.toRight.toRight)]
  rw [Finset.prod_sum_eq_prod_toLeft_mul_prod_toRight (s:=a.toRight.toRight.toRight)]
  let R:=a.toRight.toRight.toRight.toRight
  let e := ∏ i∈alternates a, shine D t i.1 i.2 F A b₀ k V p
  let m:=∑ j∈E,sew D j F A b₀ k V p
  have hu : ∏ i∈Y,P (.inl i) = (↑((∏ i∈O,K (.inl i))*Real.exp m):ℂ) := by rw [←sheet D Z h C k V p]; push_cast; rfl
  have hk (i) (hi : i∈vacuum a) : P (known i)=(↑(K (.inr i)):ℂ) := by
    change Shipment.job D Z i (qualifierAt a i) F A b₀ k V p=_
    rw [(Finset.mem_filter.mp hi).2]; rfl
  have hb (i) (hi : i∈optionalTests a) : P (suggest (supplement i))=(↑(K (.inl i)):ℂ) := by
    have he:= (free C hi).2
    change (↑(complement D i F A b₀ k V p):ℂ) =_
    unfold K latch; dsimp only; rw [if_neg he]
  change (∏ i∈Y,P (.inl i))*((∏ i∈b₀,P (.inr (.inl i)))*((∏ i∈optionalTests a,P (suggest (supplement i)))*
    ((∏ i∈alternates a,P (suggest (.inr (.inl i))))* ∏ j∈ R,P (suggest (.inr (.inr j)))))) =
    (↑((∏ i ∈ major D a A F, K i)*Real.exp m*e) : ℂ) *((∏ j∈ R,P (suggest (.inr (.inr j)))) * (∏ j∈b₀\vacuum a,P (known j)))
  rw [hu,← Finset.prod_sdiff (f:=fun i : ℕ=> P (.inr (.inl i))) (show vacuum a ⊆ Fleet.kSet a from Finset.filter_subset ..),
    Finset.prod_congr rfl hk,Finset.prod_congr rfl hb]
  have hv : (∏ i∈alternates a,P (suggest (.inr (.inl i))))=(e:ℂ) := by unfold e; push_cast; rfl
  rw [hv,major,Finset.prod_disjSum]; change _ = (↑(((∏ i∈O∪optionalTests a,K (.inl i))*_)*_ * _):ℂ) * _
  rw [hf]; push_cast; ring

lemma unity (p : (N₀).Person D F A) :
    let v:= (N₀).embed D F A p
    (showtime D Z t h C k₀ k).word V p=load D t k V F A a v := by
  intro v
  unfold Reading.word; change (∏ i : Casting.Alien (D:=D) (A:=A) (F:=F) (a:=a), Casting.lounge t i F A b₀ k V v) *
    Real.exp (∑ i : paper D a A F,sew D i F A b₀ k V v)*(∏ i:everyday a,(_-1)) =_
  let f (i : ListID S × Bool) := shine D t i.1 i.2 F A b₀ k V v
  have he : alternates a=specials a ∪ everyday a := by ext i; simp [specials,everyday]; cases hasVersions i.1 <;> simp_all
  have ht : Disjoint (specials a) (everyday a) := Finset.disjoint_left.mpr fun i h h' => by
    have hx:=(Finset.mem_filter.mp h).2; have hh:=(Finset.mem_filter.mp h').2; rw [hx] at hh; contradiction
  have hh (i : everyday a) : Real.exp (introduce D i.val.1 F A b₀ k V v)-1=f i := by
    have hu:= (Finset.mem_filter.mp i.property).2
    have ha:= (worlds C (Casting.dial i).property).2.2
    change i.val.2=false ∨ hasVersions i.val.1=true at ha
    cases hi : i.val.1 with
    | letter j=>change hasVersions i.val.1=false at hu; rw [hi] at hu; contradiction
    | _=>cases hl : i.val.2 <;> simp [f,hi,hl,hasVersions,shine] at ha ⊢
  unfold Casting.Alien; rw [Fintype.prod_sum_type]
  unfold load; dsimp only
  rw [show (∏ i∈alternates a, shine D t i.1 i.2 F A b₀ k V v) = ∏ i∈specials a∪everyday a,f i from he.symm ▸ rfl, Finset.prod_union ht]
  have hq : (∏ i : everyday a,(Real.exp (introduce D i.val.1 F A b₀ k V v)-1))=∏ i∈everyday a,f i := by simp_rw [hh]; exact Finset.prod_coe_sort ..
  change _ * _ * (∏ i : everyday a,(Real.exp (introduce D i.val.1 F A b₀ k V v)-1))=_
  rw [hq,← Finset.prod_coe_sort (major D a A F),← Finset.prod_coe_sort (specials a),← Finset.sum_coe_sort (paper D a A F)]
  unfold f Casting.lounge; dsimp only [Sum.elim_inl, Sum.elim_inr]; ring
end YM.PhysicalNext.Dictionary.Lobbies.Casting
