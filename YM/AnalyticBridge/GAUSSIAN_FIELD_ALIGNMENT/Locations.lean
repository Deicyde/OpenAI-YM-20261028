import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Tensor

set_option warningAsError false

/-!
# Affine lattice turns of the actual key space

Move BOTH endpoints even across centered block boundaries. Read replica itself,
not merely its derivative at identity. Coarse translations embedded at roots.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.GaussianFieldAlignment.Locations
open Function Filter Set Lattice RG Precision Exterior Wilson Tree Pressure Stores
open Next.SectorChange Push.SectorMeasure.Oriented
open scoped Classical Topology BigOperators
variable {G : Gauge} {c f n : Side} {S : StepData c f}
variable (s : Signed) (b : Site c)

lemma parent_map (i : Site f) : S.ratio.parent (affine s (S.ratio.embed b) i)=affine s b (S.ratio.parent i) :=
  Push.Local.parent_affine _ S.patch.odd_side ..
lemma affine_plus (d : Step) (x t : Site n) : affine s t (x + d.vec) = affine s t x + (d.rotate s).vec := by
  rw [Step.vec_rotate,affine,affine,s.act_add]; abel
lemma send_used (t i : Site n) (d : Step) : sendEdge s t (d.used i) = (d.rotate s).used (affine s t i) := by
  rcases d with ⟨a,v|v⟩
  · rfl
  change sendEdge s t (i-step a,a) = ((negDir a).rotate s).used _
  have h := affine_plus s (posDir a) (i-step a) t; rw [Step.vec_pos,sub_add_cancel] at h
  rw [h]; unfold sendEdge; cases hs : s.flip a <;> simp [Step.used,Step.rotate,Step.vec,hs,posDir,negDir,sub_eq_add_neg]
lemma pin_map (t : Site n) (i : Bond n) : pinPos (sendEdge s t i)=(pinPos i).image (affine s t) := by
  unfold pinPos; rw [Finset.image_insert,Finset.image_singleton, ← Step.vec_pos (i:=i.2),affine_plus,sendEdge]
  let d := (posDir i.2).rotate s
  change {_,_}={_,_ + d.vec}
  unfold d; cases h : ((posDir i.2).rotate s).neg <;> simp [h,Step.used,Step.vec,Finset.pair_comm,sub_eq_add_neg]

abbrev shiftFaces (s : Signed) (b : Site n) : Equiv.Perm (Cell n) := Equiv.ofBijective (Face.send s b)
  ⟨Face.injective_send ..,Finite.injective_iff_surjective.mp (Face.injective_send ..)⟩
variable (A : Stores S)
def book : Stores S := ⟨A.costs.map (shiftFaces s (S.ratio.embed b)).symm.toEmbedding,
      A.aisles.map (StepData.sendBonds s b).symm.toEmbedding,A.flags.map (StepData.sendSites s b).symm.toEmbedding⟩

lemma start_map (i : Cell f) : startPos S (shiftFaces s (S.ratio.embed b) i)=(startPos S i).image (affine s b) := by
  unfold startPos; change (touched (Face.send ..)).image _ = _
  rw [Work.H03.touched_send,Finset.image_image,Finset.image_image]; congr 1; exact funext (parent_map (S:=S) s b)

lemma place_map (x : Site c) : x∈(book s b A).place ↔ affine s b x ∈ A.place := by
  simp only [book,Stores.place, Finset.mem_union,Finset.mem_biUnion]
  refine or_congr (or_congr ?_ ?_) ?_
  · let e := shiftFaces s (S.ratio.embed b)
    rw [← e.exists_congr_right (q:=fun p => p∈A.costs ∧ affine s b x∈startPos S p)]; simp_rw [Finset.mem_map_equiv, Equiv.symm_symm]
    simp only [show ∀ i,startPos S (e i)=_ from start_map (S:=S) s b]; simp [e,Finset.mem_image, (show Function.Injective (affine s b) from (StepData.sendSites s b).injective).eq_iff]
  · let e := StepData.sendBonds s b
    rw [← e.exists_congr_right (q:=fun p => p∈A.aisles ∧ affine s b x∈pinPos p)]; simp_rw [Finset.mem_map_equiv, Equiv.symm_symm,show ⇑e = sendEdge s b from rfl,pin_map]
    simp [Finset.mem_image, (show Function.Injective (affine s b) from (StepData.sendSites s b).injective).eq_iff]
  exact Finset.mem_map_equiv

lemma dome_map (r : ℕ) (x : Site c) : x∈(book s b A).dome r ↔ affine s b x∈A.dome r := by
  rw [Stores.dome,Stores.dome,halo_spec,halo_spec]; refine ⟨fun ⟨w,hw,he⟩ => ⟨affine s b w,(place_map ..).mp hw,?_⟩,?_⟩
  · simpa [affine,separation_translate,separation_signed] using! he
  rintro ⟨w,hw,he⟩; obtain ⟨w,rfl⟩ := (StepData.sendSites s b).surjective w
  change separation (affine s b w) _ ≤ _ at he
  exact ⟨w,(place_map ..).mpr hw,by simpa [affine,separation_translate,separation_signed] using he⟩

variable (F : Forest S.ratio)
lemma affine_root (v : Site c) : S.ratio.embed (affine s b v) = affine s (S.ratio.embed b) (S.ratio.embed v) := by
  unfold affine; rw [show S.ratio.embed (s.act v+b) = _ from S.ratio.root.map_add (s.act v) b,Ratio.root_embed,Ratio.root_embed,S.ratio.signed]
lemma leaves (i : Site f) : leaf S.ratio (affine s (S.ratio.embed b) i) ↔ leaf S.ratio i := by unfold leaf; dsimp only; rw [parent_map, affine_root]; exact not_congr (StepData.sendSites .. |>.injective.eq_iff)

def up (i : Site f) := (F.up (affine s (S.ratio.embed b) i)).rotate s⁻¹
lemma climbs (i : Site f) : affine s (S.ratio.embed b) (i+(up s b F i).vec)=affine s (S.ratio.embed b) i+(F.up (affine s (S.ratio.embed b) i)).vec := by rw [affine_plus,up,Step.rotate_mul,mul_inv_cancel,Step.rotate_one]

def forest : Forest S.ratio where
  up := up s b F
  height i := F.height (affine s (S.ratio.embed b) i)
  bound i := F.bound _
  rise i hi := by rw [climbs]; exact F.rise _ ((leaves ..).mpr hi)
  stays i hi := by apply (StepData.sendSites s b).injective; change affine s b _=affine s b _; rw [← parent_map, ← parent_map, climbs]; exact F.stays _ ((leaves ..).mpr hi)
lemma trunk_map (i : Bond f) : i∈(forest s b F).trunks ↔ sendEdge s (S.ratio.embed b) i ∈ F.trunks := by
  let L := S.ratio.embed b
  have hv (j : Site f) : (F.up (affine s L j)).used (affine s L j) = sendEdge s L (((forest s b F).up j).used j) := by
    rw [send_used]; simp only [forest,up,Step.rotate_mul,mul_inv_cancel,Step.rotate_one,L]
  rw [Forest.trunk_mem_iff,Forest.trunk_mem_iff]; refine ⟨fun ⟨j,hj,h⟩ => ⟨affine s L j,(leaves ..).mpr hj,(hv j).trans (congr_arg _ h)⟩,?_⟩
  rintro ⟨j,hj,h⟩
  obtain ⟨j,rfl⟩ := (StepData.sendSites s L).surjective j
  exact ⟨j,(leaves ..).mp hj, sendEdge_injective s L ((hv j).symm.trans h)⟩

def free : (forest s b F).Free ≃ F.Free := Equiv.subtypeEquiv (StepData.sendBonds s (S.ratio.embed b)) (fun i => not_congr (trunk_map s b F i))
lemma free_site (i : (forest s b F).Free) : (free s b F i).val=sendEdge s (S.ratio.embed b) i.val := rfl
variable (x : ℝ)
lemma chill_points (i : F.Free) : chill A x F i ↔ ∃ p∈Next.SectorChange.points S i.val,p∈A.dome (10*radiusB x) := by simp [chill,Next.SectorChange.points]
lemma chill_map (i : (forest s b F).Free) : chill (book s b A) x (forest s b F) i ↔ chill A x F (free s b F i) := by rw [chill_points,chill_points,free_site, Tensor.moves_points]; simp only [exists_mem_image,dome_map]

def active := (Equiv.subtypeEquiv (free s b F) (fun i => not_congr (chill_map s b A F x i)) : Active (book s b A) x (forest s b F) ≃ Active A x F)
def frozen := (Equiv.subtypeEquiv (free s b F) (fun i => chill_map s b A F x i) : Frozen (book s b A) x (forest s b F) ≃ Frozen A x F)

-- replica on reversed bonds, crossing detection in the *fine* parent geometry
lemma crossing (i : Bond f) (h : S.ratio.parent (i.1+step i.2) ≠ S.ratio.parent i.1) : S.ratio.parent (i.1+step i.2)=S.ratio.parent i.1+step i.2 := by have he := S.ratio.parents_hop S.patch.odd_side i.1 i.2; split at he <;> simp_all
lemma replica_move (V : Config G c) : replica S.ratio (pull s b V) = pull s (S.ratio.embed b) (replica S.ratio V) := by
  funext i
  let d := (posDir i.2).rotate s
  let g := S.ratio
  let p := affine s (g.embed b) i.1
  let q := affine s b (g.parent i.1)
  have he : g.parent p=q := parent_map ..
  have hv : g.parent (p+d.vec)=affine s b (g.parent (i.1+step i.2)) := by rw [← affine_plus s (posDir i.2),parent_map,Step.vec_pos]
  have hx : g.parent (i.1+step i.2)=g.parent i.1 ↔ g.parent (p+d.vec)=g.parent p := by rw [hv,he]; exact (StepData.sendSites s b).injective.eq_iff.symm
  have hh : ¬g.parent (i.1+step i.2)=g.parent i.1 → g.parent (p+d.vec)=q+d.vec := by intro h; rw [hv, crossing i h,← Step.vec_pos,affine_plus]
  change (if g.parent _ = g.parent _ then 1 else d.read V q)=d.read (replica g V) p
  rcases hy : d with ⟨a,h|h⟩
  · simp only [Step.vec, Bool.false_eq_true,↓reduceIte,hy] at hx hh
    simp only [Step.read, Step.used,Bool.false_eq_true,↓reduceIte, replica]; split
    next h => rw [if_pos (hx.mp h)]
    next h => rw [if_neg (mt hx.mpr h),he]
  simp only [Step.vec,↓reduceIte,hy,← sub_eq_add_neg] at hx hh
  simp only [Step.read,Step.used,↓reduceIte,replica, sub_add_cancel]
  by_cases h : g.parent (i.1+step i.2)=g.parent i.1
  · rw [if_pos h,if_pos (hx.mp h).symm,inv_one]
  rw [if_neg h,if_neg (fun hi => h (hx.mpr hi.symm)),hh h]
end YM.AnalyticBridge.GaussianFieldAlignment.Locations
