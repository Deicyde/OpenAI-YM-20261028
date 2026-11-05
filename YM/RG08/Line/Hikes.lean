import YM.RG08.Line.Solid

/-!
# Linear tree straightening. Scalar orientation.
-/
noncomputable section
namespace YM.RG08.Line
open Stationary Function Matrix Lattice Exterior Precision RG Tree Wilson
open scoped Matrix BigOperators Topology
set_option autoImplicit false
variable {c f : Side} (S : StepData c f)

/-- Box average and centered left inverse. -/
def boxMap : Matrix (Body 0 c) (Body 0 f) ℝ := LinearMap.toMatrix'
  (LinearMap.pi fun i : Body 0 c=> ∑ a:S.patch.Points, S.patch.weight a • (LinearMap.proj (Precision.atPoint S i.1 a,vac): form 0 f →ₗ[ℝ] ℝ))
def baseMap : Matrix (Body 0 c) (Body 0 f) ℝ := LinearMap.toMatrix'
  (LinearMap.pi fun i : Body 0 c=> (LinearMap.proj ((S.ratio.embed i.1),vac): form 0 f →ₗ[ℝ] ℝ))
def padMap : Matrix (Body 0 f) (Body 0 c) ℝ := LinearMap.toMatrix'
  (LinearMap.pi fun i : Body 0 f=> (LinearMap.proj ((S.ratio.parent i.1),vac): form 0 c →ₗ[ℝ] ℝ))
def hikeMap (F:Forest S.ratio) : Matrix (Body 0 f) (Body 1 f) ℝ := LinearMap.toMatrix'
  (LinearMap.pi fun i : Body 0 f=> integralLink i.1 (F.hike i.1))

lemma box_at (v : form 0 f) (i : Body 0 c) : (boxMap S *ᵥ v) i = ∑ a:S.patch.Points, S.patch.weight a * v (Precision.atPoint S i.1 a,vac) := by simp [boxMap,LinearMap.toMatrix'_mulVec,LinearMap.pi_apply]
lemma base_at (v : form 0 f) (i : Body 0 c) : (baseMap S*ᵥ v) i=v ((S.ratio.embed i.1),vac):= by rw [baseMap,LinearMap.toMatrix'_mulVec]; rfl
lemma pad_at (v : form 0 c)(i: Body 0 f) : (padMap S *ᵥ v) i=v (S.ratio.parent i.1,vac) := by rw [padMap,LinearMap.toMatrix'_mulVec]; rfl
lemma hike_at (F : Forest S.ratio) (v : form 1 f)(i: Body 0 f) : (hikeMap S F *ᵥ v) i=integralLink i.1 (F.hike i.1) v := by rw [hikeMap,LinearMap.toMatrix'_mulVec]; rfl

variable {i j : Type} [Fintype j] [DecidableEq j]
lemma perVec {A B : Matrix i j ℝ} (h : ∀ v,A*ᵥ v=B*ᵥ v): A=B := by
  ext a b
  simpa [mulVec_single,mul_one] using congr_fun (h (Pi.single b 1)) a

lemma rooted_box : fixRoot S * d 0 f=baseMap S-boxMap S := by
  refine perVec fun v=>?_
  funext i; rw [← mulVec_mulVec, Matrix.sub_mulVec]; change _=(baseMap S *ᵥ v) i-(boxMap S *ᵥ v) i
  rw [box_at,base_at,psi_proj]

lemma mean_diff : mean S*d 0 f=d 0 c*boxMap S := by
  refine perVec fun v=>?_
  funext i; rw [← mulVec_mulVec, ← mulVec_mulVec,mean_site]
  obtain ⟨i,h⟩:= i
  obtain ⟨k,rfl⟩:= axisEquiv.surjective h
  simp only [show ∀ i,axisEquiv.symm (coord i)=i from fun i=>axisEquiv.symm_apply_apply i, coord_map,d_sites,box_at,mul_sub,Finset.sum_sub_distrib]

lemma hike_diff (F : Forest S.ratio) : hikeMap S F*d 0 f=padMap S*baseMap S-1 := by
  refine perVec fun v=> ?_
  funext i
  rw [← mulVec_mulVec, Matrix.sub_mulVec,← mulVec_mulVec, Matrix.one_mulVec,hike_at,telescopes,F.hike_root]
  change _ = (padMap S *ᵥ _) _-v _
  rw [pad_at,base_at]
  rcases i with ⟨i,b⟩; rw [vac_only b]

lemma hike_base (F : Forest S.ratio) : baseMap S*hikeMap S F=0 := by
  refine perVec fun v=>?_
  funext i
  rw [← mulVec_mulVec,base_at,hike_at,Forest.hike,dif_neg ?_,Matrix.zero_mulVec]
  · rfl
  unfold Tree.leaf; rw [S.ratio.embed_parent]; simp

lemma base_pad : baseMap S*padMap S=1 := by
  refine perVec fun v=>?_
  funext i; rw [← mulVec_mulVec,base_at,pad_at, S.ratio.embed_parent, Matrix.one_mulVec]
  rcases i with ⟨i,b⟩; rw [vac_only b]

def gaugePin (F:Forest S.ratio): Matrix (Body 1 f) (Body 1 f) ℝ := 1+d 0 f*hikeMap S F
def gaugeFrame : Matrix (Body 1 f) (Body 0 c) ℝ := d 0 f*padMap S

lemma gaugePin_fix (F : Forest S.ratio)(v:form 1 f)(hk:Precision.marked (S:=S) F v): gaugePin S F *ᵥ v=v:= by
  have h : hikeMap S F *ᵥ v=0 := by
    funext ⟨x,i⟩; rw [hike_at]
    induction x using Forest.hike.induct F with
    | case1 x hx he =>
      rw [Forest.hike,dif_pos hx]
      change (if (F.up x).neg then -v _ else v _) + integralLink _ _ v = 0
      have hF := hk ((F.up x).used x) ((F.trunk_mem_iff _).2 ⟨x,hx,rfl⟩)
      split <;> rename_i hJ
      all_goals
        -- force use used x def
        rw [show v _=0 from hF] -- should match exactly
        simpa using he
    | case2 x hx => rw [Forest.hike,dif_neg hx]; rfl
  unfold gaugePin; rw [add_mulVec,one_mulVec, ← mulVec_mulVec,h,mulVec_zero,add_zero]

lemma tree_stop (F:Forest S.ratio)(v:form 1 f): Precision.marked (S:=S) F (gaugePin S F *ᵥ v) := by
  rintro i hi
  obtain ⟨x,hx,rfl⟩:= (F.trunk_mem_iff _).mp hi
  have hI: integralLink x (F.hike x) v=(if (F.up x).neg then -v ((F.up x).used x |>.1,coord ((F.up x).used x).2) else v ((F.up x).used x |>.1,coord ((F.up x).used x).2)) + integralLink (x+(F.up x).vec) (F.hike (x+(F.up x).vec)) v:= by rw [Forest.hike,dif_pos hx]; rfl
  rw [gaugePin,add_mulVec,one_mulVec,Pi.add_apply,← mulVec_mulVec,d_sites,hike_at,hike_at]
  cases hs : F.up x with
  | mk j b => cases b <;> rw [hs] at hI <;> simp only [Step.used,Bool.false_eq_true, ↓reduceIte,Step.vec,sub_add_cancel, ← sub_eq_add_neg] at hI ⊢ <;> linarith

lemma tree_roots (F:Forest S.ratio)(v:form 0 c): Precision.marked (S:=S) F (gaugeFrame S *ᵥ v) := by
  rintro ⟨x,i⟩ hi
  rw [gaugeFrame,← mulVec_mulVec,d_sites]; simp_rw [pad_at]; exact sub_eq_zero.mpr (by rw [F.trunk_internal hi])
end YM.RG08.Line
