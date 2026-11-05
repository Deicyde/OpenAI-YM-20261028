import YM.RG08.Line.Hikes

/-!
# Color-diagonal stencils: arithmetic before any slice index
-/
noncomputable section
namespace YM.RG08.Line
open Stationary Function Matrix Lattice Exterior Precision RG Tree Wilson Laurent
open scoped Matrix BigOperators Topology
set_option autoImplicit false
variable {c f u: Side} {i j k : ℕ} (G : Gauge)
variable (X Y : Matrix (Body i c) (Body j f) ℝ)
lemma painted (v : Corn (Lines G f j))(a : G.ColorIndex) (t : Body i c):
    (patron G X *ᵥ v) (t.1,t.2,a) = (X*ᵥ (fun x => v (x.1,x.2,a))) t := by rw [patron_fee]; rfl

lemma ink_add_general : patron G (X+Y)=patron G X+patron G Y:= by
  refine perVec fun v=> ?_; funext ⟨t,i',a⟩
  rw [add_mulVec,Pi.add_apply]
  -- type Body ? ambiguity
  change _ = (patron G X *ᵥ v) (_,_,a) + (patron G Y *ᵥ v) (_,_,a)
  rw [painted G X v a ((t,i'):Body i c), painted G Y v a ((t,i'):Body i c), ← Pi.add_apply, ← add_mulVec, ← painted G (X+Y) v a ((t,i'):Body i c)]
lemma ink_factor_general (p : ℝ) : patron G (p • X)=p • patron G X:= by
  refine perVec fun v=> ?_; funext ⟨t,i',a⟩
  rw [smul_mulVec,Pi.smul_apply, painted G (p • X) v a ((t,i'):Body i c),smul_mulVec,Pi.smul_apply]
  rw [painted G X v a ((t,i'):Body i c)]
lemma ink_zero : patron G (0:Matrix (Body i c) (Body j f) ℝ)=0 := by
  have hh := ink_factor_general G (0:Matrix (Body i c) (Body j f) ℝ) 0; simpa using hh
lemma ink_neg : patron G (-X) = - patron G X:= by simpa using ink_factor_general G X (-1)
lemma ink_sub : patron G (X-Y)=patron G X-patron G Y:=by rw [sub_eq_add_neg,ink_add_general,ink_neg,sub_eq_add_neg]
lemma ink_id : patron G (1:Matrix (Body i c) (Body i c) ℝ)=1 := by
  refine perVec fun v=>?_ ; funext ⟨t,i',a⟩
  rw [painted G _ v a ((t,i'):Body i c),one_mulVec,one_mulVec]

lemma ink_box (S : StepData c f) : curryG G S = patron G (boxMap S):= by
  apply perVec; intro v; funext ⟨i,j,k⟩
  rw [curry_at,painted G (boxMap S) _ k ((i,j):Body 0 c),box_at, vac_only j]

-- extract uncoloring for bounds
lemma patron_cell (x : Body i c)(y:Body j f)(a b : G.ColorIndex) :
    patron G X (x.1,x.2,a) (y.1,y.2,b)= if a=b then X x y else 0 := by
  let w : Corn (Lines G f j) := Pi.single (y.1,(y.2,b)) (1:ℝ)
  have ht:=painted G X w a x
  simp_rw [w,Matrix.mulVec_single] at ht
  have hk : (fun x:Body j f=> w (x.1,(x.2,a))) = if a=b then Pi.single y (1:ℝ) else 0 := by ext1 z; split <;> rename_i h <;> simp [w,h,Pi.single_apply, Prod.ext_iff]
  change _=ite ..
  suffices he : (patron G X*ᵥ w) _ = _ by simpa [w,Matrix.mulVec_single] using he
  rw [painted G X w a x, hk]; split <;> simp [Matrix.mulVec_single]
end YM.RG08.Line
