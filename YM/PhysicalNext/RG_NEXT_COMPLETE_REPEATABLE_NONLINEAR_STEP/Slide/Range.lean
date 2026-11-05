import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE.Delay
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Deck.Festal
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Yearling.Garter
import YM.ProjectorNext.EQUATION_CAMPAIGN.Receiving
/-!
 # Retraction onto a genuine periodic subview. Projection linking any unframed all-good field.
   Covers actual flags. Design through every coordinate Patch family. 
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Slide
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck  Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {C c : Side}
structure Track (n : Side) where
  pos : Per n→ℤ
  step (v): pos (v+1)=pos v ∨ pos (v+1)=pos v+1 ∨ pos (v+1)=pos v-1

def stage (A : Track C) (x:Site C) : Cover := fun i=> A.pos (x i)
def sites (A:Track C) (o:Site c) (x : Site C) : Site c := wrap c (stage A x)+ o
variable (A:Track C) (o:Site c)
def grade (i:Pressure.Bond C) := A.pos (i.1 i.2 + 1)-A.pos (i.1 i.2)
lemma tops (x : Site C) (i:Axis) : stage A (x+step i)=stage A x+grade A (x,i) • step i:= by
  ext k; unfold stage grade; simp only [Pi.add_apply,Pi.smul_apply, step_apply]; split_ifs with h
  · rw [h]; simp
  simp
lemma falls (x : Site C) (i:Axis) : sites A o (x+step i) = sites A o x+grade A (x,i) • step i:= by unfold sites; rw [tops,map_add,map_zsmul,wrap_step,add_right_comm]
lemma graded (x:Pressure.Bond C): grade A x=0∨ grade A x=1 ∨ grade A x= -1:= by have hp:=A.step (x.1 x.2); unfold grade; omega
-- define by grade; convenience bool invert.
variable {K : Type*} [Group K]
def shape (U:Links (Per c) K) : Links (Per C) K := fun i=>if grade A i=1 then U (sites A o i.1,i.2) else if grade A i= -1 then (U (sites A o (i.1+step i.2),i.2))⁻¹ else 1
lemma here (x : Site C) (i:Axis) (h: grade A (x,i)=1) : sites A o (x+step i)=sites A o x+step i:= by rw [falls,h,one_smul]
lemma there (x : Site C) (i:Axis) (h: grade A (x,i)= -1): sites A o (x+step i)+step i=sites A o x:= by rw [falls,h,neg_one_smul]; simp
lemma down (x : Site C) (i:Axis) (h: grade A (x,i)= -1): sites A o (x+step i)=sites A o x-step i:= eq_sub_of_add_eq (there A o x i h)
lemma lateral (x : Site C) {i j: Axis} (he:i≠j): grade A (x+step j,i) = grade A (x,i):= by simp [grade,step_apply, he]
lemma shape_gauge (z : Site c → K) (U:Links (Per c) K): shape A o (gauge z U) = gauge (z ∘ sites A o) (shape A o U):= by
  funext ⟨x,i⟩; unfold shape Lattice.gauge; simp only [Function.comp_apply]; rcases graded A (x,i) with h|h|h
  · simp [h,falls]
  · rw [if_pos h, if_pos h,here A o _ _ h]
  rw [if_neg (show grade A _≠1 from h ▸ (by norm_num : (-1:ℤ)≠1)),if_neg (show grade A _≠1 from h ▸ (by norm_num :(-1:ℤ)≠1)),if_pos h, if_pos h, there A o _ _ h]; group
set_option maxHeartbeats 650000 in
lemma directionWord (U: Config G c) (i:PlaqAxes) (z:Site C) (X:Support c) (hX:∀ i,sites A o i∈X) (t:ℝ) (ht:0≤t) (h: Healthy t X U): G.chord (faceValue (shape A o U) (z,i))≤ t:= by
  obtain ⟨⟨i,j⟩,hi⟩:=i; change i<j at hi
  let V:= shape A o U
  have he (x:Site C): G.chord (faceValue U (sites A o x,⟨(i,j),hi⟩)) ≤ t:= by
    by_contra! H; exact disjoint_left.mp h (hX x) (flags_spec _ _ _|>.2 ⟨_,WilsonStartup.anchor_visit _, H⟩)
  have hY (G : Gauge) (n : Side) (V : Config G n) (x : Site n) : faceValue V (x,⟨(i,j),hi⟩)=V (x,i)*V (x+step i,j)*(V (x+step j,i))⁻¹*(V (x,j))⁻¹ := by simp [faceValue,square,travel,mul_assoc]; congr 4 <;> abel -- edit
  let a:= z+step i; let b:= z+step j; let c' := z+step i+step j
  rw [hY]
  have hu : grade A (z+step i,j)=grade A (z,j):= lateral A z (Ne.symm (ne_of_lt hi)); have hy : grade A (z+step j,i)=grade A (z,i):= lateral A z (ne_of_lt hi)
  have hZ : z+step i+step j=z+step j+step i:=add_right_comm ..
  unfold shape; simp only [hu,hy]
  rcases graded A (z,i) with hi'|hi'|hi' <;> rcases graded A (z,j) with hj'|hj'|hj'
  case inl.inl=> simpa [hi',hj',Gauge.chord] using ht
  case inl.inr.inl=> simpa [hi',hj',falls A o, Gauge.chord] using ht
  case inl.inr.inr=> simp [hi',hj', hZ,falls A o _ i, hy,Gauge.chord]; exact ht
  case inr.inl.inl=> simpa [hi',hj',falls A o,Gauge.chord] using ht
  case inr.inr.inl=> simp [hi',hj',← hZ,falls A o _ j, hu,Gauge.chord]; exact ht
  case inr.inl.inr.inl=>
    have hm₁:= here A o z i hi'; have hm₂:= here A o z j hj'
    simpa [hi',hj',hm₁,hm₂] using (hY G c U (sites A o z)) ▸ he z -- edit
  case inr.inr.inr.inl=>
    -- i negative. normal orient reversed, start at shifted right. flip formula (U(x→-i) = -edge)
    let x:=sites A o z; let p:=sites A o a; have hpi : p+step i=x := there A o z i hi'; have hP : sites A o (z+step i+step j)=p+step j:= here _ _ _ _ (hu ▸ hj')
    let u:=faceValue U (p,⟨(i,j), hi⟩); let e := U (p,i)
    suffices HH: V (z,i)*V (z+step i,j)*(V (z+step j,i))⁻¹*(V (z,j))⁻¹=e⁻¹*u⁻¹* (e⁻¹)⁻¹ by
      have hx : G.chord (e⁻¹*u⁻¹*(e⁻¹)⁻¹)=G.chord u:= by rw [G.chord_conj,G.chord_inv]
      -- V shape unfolded goal
      unfold V shape at HH; rw [hu,hy] at HH; rw [HH,hx]; exact he a
    change _=e⁻¹*(faceValue _ _)⁻¹*_ ; rw [hY,hpi]; unfold V shape; simp only [hu,hy,hi',hj']; norm_num; rw [← hZ,hP]; change _* U (p,j) * _ * _=_; unfold e p a x; group
  case inr.inl.inr.inr=>
    let x:=sites A o z; let p:=sites A o b; have hpi : p+step j=x := there A o z j hj'; have hP : sites A o (z+step j+step i)=p+step i:= here _ _ _ _ (hy ▸ hi')
    let u:=faceValue U (p,⟨(i,j), hi⟩); let e := U (p,j)
    suffices HH: V (z,i)*V (z+step i,j)*(V (z+step j,i))⁻¹*(V (z,j))⁻¹=e⁻¹*u⁻¹* (e⁻¹)⁻¹ by
      have hx : G.chord (e⁻¹*u⁻¹*(e⁻¹)⁻¹)=G.chord u:= by rw [G.chord_conj,G.chord_inv]; -- edit
      unfold V shape at HH; rw [hu,hy] at HH; rw [HH,hx]; exact he b
    change _=e⁻¹*(faceValue _ _)⁻¹*_ ; rw [hY,hpi]; unfold V shape; simp only [hu,hy,hi',hj']; norm_num; rw [hZ,hP]; unfold e p b x; group
  case inr.inr.inr.inr=>
    let x:=sites A o z; let p:=sites A o c'; have hpi : p+step j=sites A o a := there A o a j (hu ▸ hj'); have hP : p+step i=sites A o b:=by unfold p c'; rw [hZ]; exact there A o b i (hy ▸ hi')
    let u:=faceValue U (p,⟨(i,j), hi⟩); let e := U (p,i)*U (sites A o b,j)
    suffices HH: V (z,i)*V (z+step i,j)*(V (z+step j,i))⁻¹*(V (z,j))⁻¹=e⁻¹*u* (e⁻¹)⁻¹ by
      unfold V shape at HH; rw [hu,hy] at HH; rw [HH,G.chord_conj]; exact he c'
    change _=e⁻¹*(faceValue _ _)*_ ; rw [hY,hpi,hP]; unfold V shape; simp only [hu,hy,hi',hj']; norm_num; rw [← hZ]; unfold e b p a c'; group
lemma allFlag (U: Config G c) (X:Support c) (hX:∀ i,sites A o i∈X) (t:ℝ) (ht:0≤t) (h: Healthy t X U): flags t (shape A o U)= ∅:= by
  ext i; simp only [flags_spec, Finset.notMem_empty, iff_false]; rintro ⟨⟨x,k⟩, _,hv⟩; exact (directionWord A o U k x X hX t ht h).not_gt hv
lemma stable (Z:Support c) (hB : ∀ i,sites A o i∈Z) (x y:Config G c) (hx:Agrees Z x y): shape A o x=shape A o y:= by
  funext ⟨v,w⟩; unfold shape; dsimp only; split
  next h=> exact hx (sites A o v,w) (hB v) (here A o _ _ h ▸ hB (v+step w))
  split; next h=> exact congr_arg Inv.inv (hx (sites A o (v+step w),w) (hB _) ((there A o _ _ h).symm ▸ hB v))
  rfl
end YM.PhysicalNext.Repeat.Slide
