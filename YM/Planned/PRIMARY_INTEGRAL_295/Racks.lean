import YM.Next.EXTRACTION.Base
import YM.Planned.PRIMARY_INTEGRAL_295.Fizz


/-!
# One coarse axial gauge on a true hull, zero-root sharp cost

Needed Before-L coefficient by coefficient locally. Work.E08.axial_patch
pays sum over slab good for post only. Use same actual cover tools to read
starting bond below with constant chosen for direction norm not volume. No
argument beyond tested torus hull. Only coarse, no gauge assertion across H
origins. Later differentiate WITH this evaluation gauge fixed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Racks
open Filter Function Lattice RG RG.Patch Axial Wilson Finset Precision Tree
open Pressure Pressure.Stores Pressure.Teller Bid Work.E08
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge}

lemma varied {r:ℕ} {f : ℤ→ℝ} {v:ℝ} (h : ∀ i∈layers r,i+1 ∈ layers r → |f (i+1)-f i|≤v) (w:ℤ) (hw : w∈layers r)
    (hv:0 ≤ v) : |f w-f 0| ≤ r*v := by
  have he (u z:ℤ) (hz : u≤z) (hu : u∈layers r) (hZ : z∈layers r) : |f z - f u| ≤ (z-u:ℤ)*v:= by
    induction z, hz using Int.leInduction with
    | base => simp
    | succ k hk ih =>
      have hK : k∈layers r:= by simp only [layers,mem_Icc] at hu hZ ⊢; omega
      have ht:=abs_add_le (f (k+1)-f k) (f k-f u); rw [sub_add_sub_cancel] at ht
      apply ht.trans (((add_le_add (h k hK hZ) (ih hK))).trans_eq ?_); push_cast; ring
  rcases le_total w 0 with hz|hz
  · rw [abs_sub_comm]; apply (he w _ hz hw (by simp [layers])).trans; refine mul_le_mul_of_nonneg_right ?_ hv
    simp only [layers,mem_Icc] at hw; exact_mod_cast (show 0-w ≤ r from by omega)
  apply (he 0 _ hz (by simp [layers]) hw).trans; refine mul_le_mul_of_nonneg_right ?_ hv
  simp only [layers,mem_Icc] at hw; exact_mod_cast (show w-0 ≤ r from by omega)

private lemma from0 (l:List Axis) (r:ℕ) (θ:ℝ) (hp : 0≤θ) (U : CoverConfig G)
    (hu : ∀ x ∈ box r,∀ p:PlaqAxes,G.chord (faceValue U (x,p)) ≤ θ) (hl:l.Nodup) :
    let P:=slab r 0 l; ∀ x:Cover, x∈ P → ∀ i : Axis,x+step i∈P →
      G.chord (Lattice.gauge (traveller l U 0) U (x,i)) ≤ l.length*r*((Fintype.card PlaqAxes:ℝ)*θ) := by
  induction l using List.reverseRecOn with
  | nil =>
    have he (x) (hx:x∈slab r 0 []) : x=0 :=funext fun i=> (slab_iff.mp hx).2 i (by simp)
    intro _ x hx i hi; have h:= he (x+step i) hi; rw [he _ hx] at h; have hX:=congr_fun h i; simp at hX
  | append_singleton l j ih =>
    rw [List.nodup_append] at hl
    intro X x hx i hi
    have hj : j ∉ l:= fun h=>hl.2.2 j h j (by simp) rfl
    let V:=Lattice.gauge (traveller (l++[j]) U 0) U
    let P : ℤ→Finset Cover:=fun i=>slab r (update 0 j i) l
    let q:=(Fintype.card PlaqAxes:ℝ)*θ
    have hq:0≤q:=by unfold q; positivity
    change G.chord (V (x,i))≤ _
    have he : P 0=slab r 0 l := by unfold P; rw [show update (0:Cover) j 0=0 by ext i; by_cases h:i=j <;> simp [h]]
    have hd (y) (hy:y∈X) : V (y,j)=1:= vertical (z:=0) hj hl.1 hy (by change 0∈P 0; rw [he]; rw [slab_iff]; exact ⟨center_box _,by simp⟩) U
    by_cases hf:i=j
    · rw [hf,hd x hx,G.chord_one]; positivity
    let w:=x j; let T(z:ℤ):=x+(z-w) • step j
    have hw : w∈layers r:=(box_iff_layers ..).mp (slab_iff.mp hx).1 j
    have hg (z) (hz:z∈layers r): T z∈ P z∧ T z+step i∈ P z:= by
      have hv : x∈P w:= (lower_pin hj x).2 ⟨hx,rfl⟩
      have hv':x+step i∈P w:= (lower_pin hj _).2 ⟨hi,by simp [Ne.symm hf,w]⟩
      exact ⟨step_between hj w z hz hv,(add_right_comm x ((z-w) • step j) (step i)).symm ▸ step_between hj w z hz hv'⟩
    have hP (z) (t): t∈P z→ t∈ X := fun H=> ((lower_pin hj _).1 H).1
    have hg' (z) (hz:z∈layers r): T z∈X ∧ T z+step i∈X:=⟨hP z _ (hg z hz).1,hP z _ (hg z hz).2⟩
    let A (z:ℤ):=G.chord (V (T z,i))
    have hz1 : 0∈layers r:=by simp [layers]
    have ht : A 0 ≤ l.length*r*q := by
      have h (x) (hx : x∈P 0) : traveller (l++[j]) U 0 x=traveller l U 0 x:= by
        rw [traveller,axisRoute_append]; simp only [axisRoute,List.flatMap_cons,List.flatMap_nil,List.append_nil];
        rw [((lower_pin hj _).mp hx).2]; simp [straight,traveller,axisRoute]
      obtain ⟨hg,hg'⟩:=hg 0 hz1
      unfold A V; simp only [Lattice.gauge,h _ hg,h _ hg']; exact ih hl.1 _ (he ▸ hg) i (he ▸ hg')
    have hz : ∀ z∈layers r,z+1∈layers r → |A (z+1)-A z|≤q := by
      intro z hz hh
      have H:T (z+1)=T z+step j:= by unfold T; rw [show z+1-w=z-w+1 by omega,add_smul,one_smul,add_assoc]
      obtain ⟨hs,hs'⟩:=hg' z hz; obtain ⟨ht,ht'⟩:=hg' (z+1) hh
      rw [H] at ht ht'
      unfold A; rw [H]; refine ((variation V (hd _ hs) (hd _ hs')).trans (squares V hf X hs hs' ht ((add_right_comm (T z) (step i) (step j)).symm ▸ ht'))).trans ?_
      unfold field; apply (Finset.sum_le_sum (g:=fun _ : PlaqAxes=>θ) (fun i _=>?_)).trans_eq (by simp [q])
      rw [show face X V _ _=face X U (T z) i from face_gauge_symm ..]; unfold face; split_ifs; exacts [hu _ (slab_iff.mp hs).1 _,hp]
    have hK := (abs_le.mp (varied (r:=r) hz w hw hq)).2
    rw [show V (x,i)=V (T w,i) from by unfold T; simp]
    change A w ≤ (l++[j]).length*r*q; simp only [List.length_append,List.length_singleton,Nat.cast_add,Nat.cast_one]
    linarith

private def rise (s : Lattice.Order) (U:CoverConfig G) := traveller (allAxes s) U 0
lemma axle (k:Lattice.Order) (r:ℕ) (θ:ℝ) (hp:0≤θ) (U:CoverConfig G)
    (hu:∀ x∈box r,∀ p:PlaqAxes,G.chord (faceValue U (x,p))≤θ) (i:Edge Cover) (hi:i.1∈box r) (hv:i.1+step i.2∈box r) :
    G.chord (Lattice.gauge (rise k U) U i) ≤ 4*r*((Fintype.card PlaqAxes:ℝ)*θ):=by
  let l:=allAxes k
  have hl : slab r 0 l=box r:=by
    have he (i:Axis):i∈l:=List.mem_map.mpr ⟨k.symm i,List.mem_finRange _,k.apply_symm_apply _⟩
    ext i; simp [slab_iff,he]
  have hh:=from0 l r θ hp U hu ((List.nodup_finRange _).map k.injective) i.1 (hl.symm ▸ hi) i.2 (hl.symm ▸ hv)
  rw [show l.length=4 by simp [l,allAxes]] at hh; exact_mod_cast hh

section True
variable {c f:Side}
def cardAt (k:Lattice.Order) (U:Config G c) := fun y:Site c=>rise k (expandAt 0 U) (lift y)
lemma within {r n:ℕ} (hr : r≤n) : box r ⊆ box n := by
  intro x hx; obtain ⟨ha,hb⟩:=box_test.mp hx; rw [box_test]; constructor <;> intro i <;> have ht:=ha i <;> have hg:=hb i <;> omega
lemma peel {r:ℕ} (hc : 2*r<c.val) (x:Cover) (hx:x∈box r) : lift (wrap c x) = x := by
   apply lift_eq_iff.mpr ⟨rfl,?_⟩; intro j; have hl := (box_test.mp hx).1 j; have hu:=(box_test.mp hx).2 j; omega
lemma costs (k:Lattice.Order) (r:ℕ) (hc : 2*r<c.val) (X:Support c) (hx:∀ y : Site c,separation 0 y ≤r → y∈X)
    (θ:ℝ) (hp:0≤θ) (U:Config G c) (hu:Healthy θ X U) (i:Edge (Site c)) (he:separation 0 i.1 < r) :
    G.chord (Lattice.gauge (cardAt k U) U i) ≤ 4*(1+(separation 0 i.1:ℝ))*((Fintype.card PlaqAxes:ℝ)*θ) := by
   let d:= separation 0 i.1; let D:=d+1
   let x:=lift i.1; let W:=expandAt 0 U
   have hD : D≤r:= Nat.succ_le_of_lt he
   have ht : x∈box d := by simpa [x] using lift_mem_box (le_refl d)
   have hv:x+step i.2∈box D:= by
     obtain ⟨h,h'⟩:= box_test.mp ht; unfold D; rw [box_test]; constructor <;> intro j <;> simp only [Pi.add_apply,step_apply] <;> split <;>
       have hg:=h j <;> have hH:=h' j <;> omega
   have hg : x∈box D:=within d.le_succ ht
   have hF(z) (hz:z∈box D) (p:PlaqAxes) : G.chord (faceValue W (z,p))≤θ := by
     unfold W faceValue; rw [travel_at]; let y:= wrap c z+0
     by_contra! ht
     have hy: y ∈ flags θ U:= (flags_spec _ _ _).mpr ⟨(y,p),by simp [touched,Lattice.visits,square],ht⟩
     exact Finset.disjoint_left.mp hu (hx y (separation_box_add 0 (within hD hz))) hy
   have hs := axle k D θ hp W hF (x,i.2) hg hv
   have hA : (wrap c x)=i.1:=wrap_lift _
   have hM : (wrap c (x+step i.2))=i.1+step i.2:= by rw [map_add,hA,wrap_step]
   have hn : (D:ℝ)=1+(separation 0 i.1:ℝ):= by simp [D,d,add_comm]
   rw [hn] at hs; apply le_trans (Eq.le ?_) hs
   unfold Lattice.gauge cardAt; rw [show lift (i.1+step i.2)=x+step i.2 from hM ▸ peel (by omega : 2*D<c.val) _ hv]; unfold W expandAt x; rw [wrap_lift, add_zero]
end True
end YM.Planned.PrimaryIntegral295.Racks
