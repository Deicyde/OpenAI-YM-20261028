import YM.WilsonBulk.Trees.Map

/-! Exact lift along any actual tree. Use ANY tags for the joint completion,
and any forest built on that period; the algebra works on MESSES too. Later
when using Fourier rows stick to one compatible repeated tree.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
open Lattice Laurent Filter Function Bloch
open RG Finset Precision Exterior Stationary Audience Matrix FreeResolvent Tree
open scoped Topology BigOperators Matrix -- Classical

variable {c f : Side} {G : Gauge} {S : StepData c f} {η : ℝ}

/-- gauge project using actual tree coordinates -/
def hiking (_G : Gauge) (S : StepData c f) (T : Forest S.ratio) : Matrix (Body 0 f) (Body 1 f) ℝ :=
  LinearMap.toMatrix' (LinearMap.pi fun i => integralLink i.1 (T.hike i.1))

def projectFull (G : Gauge) (S : StepData c f) (T : Forest S.ratio) :=
  1 + patron G (d 0 f * hiking G S T)
lemma projectFull_on (T : Forest S.ratio) (v : FreeResolvent.Vec G f 1) :
    projectFull G S T *ᵥ v = representative S T v := by
  rw [projectFull, patron_mul,Matrix.add_mulVec, Matrix.one_mulVec,← Matrix.mulVec_mulVec,match_tensor G,match_tensor G]
  have h : tensor G (hiking G S T) *ᵥ v= potential T v := by
    ext1 ⟨x,i,j⟩; change component (tensor G _ *ᵥ v) j (x,i)= integralLink _ _ _
    rw [component_mul,hiking,LinearMap.toMatrix'_mulVec]; rfl
  rw [h]; rfl

lemma fixes_Gram (T : Forest S.ratio) (H : FreeResolvent.FaceRow) (he : (H.acts f).transpose = H.acts f) :
    (projectFull G S T).transpose* fullMatrix G S H * projectFull G S T = fullMatrix G S H := by
  let A:=projectFull G S T; let K:=fullMatrix G S H
  have hz: K*A=K:=matSeen fun x=> by unfold K A; rw [← Matrix.mulVec_mulVec,projectFull_on,invariant T H x]
  have h: Kᵀ= K:= full_symmetric H he
  have hu:= congrArg Matrix.transpose hz
  rw [Matrix.transpose_mul,h] at hu
  change Aᵀ*K*A=K; rw [hu,hz]

lemma to_slice (G : Gauge) (T : Forest S.ratio) :
    insertion (plant (G:=G) T) * (reduce G S T*projectFull G S T)=projectFull G S T := by
  apply matSeen; intro v; rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,projectFull_on]
  exact projects T _ (onto_slice T v)

lemma obtained (T : Forest S.ratio) : projectFull G S T * insertion (plant (G:=G) T)=insertion (plant (G:=G) T) := by
  classical
  apply matSeen; intro v
  rw [← Matrix.mulVec_mulVec, projectFull_on]
  apply fixes T; intro i x hx
  apply Finset.sum_eq_zero; intro j _
  change (if plant (G:=G) T j = ix (x.1,coord x.2) i then 1 else 0) * v j = 0
  rw [if_neg,zero_mul]
  intro he; apply j.1.property; have hv : j.1.val=x := by
    simp only [plant,ix,Prod.mk.injEq,coord_iff] at he; exact Prod.ext he.1 he.2.1
  rw [hv]; exact hx

def casting (G : Gauge) (S : StepData c f) (T : Forest S.ratio) := projectFull G S T * collapse G S
def toActive (G : Gauge) (S : StepData c f) (T : Forest S.ratio) := reduce G S T * casting G S T
lemma recast (T : Forest S.ratio) : casting G S T = insertion (plant (G:=G) T) * toActive G S T := by
  unfold toActive casting; rw [← Matrix.mul_assoc (reduce G S T),← Matrix.mul_assoc (insertion _), to_slice]

lemma to_Gram (B : Bed) (T : Forest S.ratio) (h : (B.metric.acts f).transpose= B.metric.acts f) :
    frontR G S B=(toActive G S T).transpose* treeMatrix G S T B.metric * toActive G S T := by
  let A:= collapse G S; let U:= projectFull G S T; let V:= fullMatrix G S B.metric
  calc
    _ = Aᵀ * (Uᵀ*V*U)*A := by rw [show Uᵀ*V*U=V from fixes_Gram T _ h]; exact collapse_equal G S B h
    _ = (casting G S T).transpose* V * casting G S T := by unfold casting A U; simp only [Matrix.mul_assoc, Matrix.transpose_mul]
    _ = _ := by unfold V treeMatrix; rw [recast T,transpose_mul,← insertion.compress (A:=fullMatrix G S B.metric)]; simp only [Matrix.mul_assoc] -- adjust

def stretchJoint (G : Gauge) (S : StepData c f) : Matrix (Bodies G c f) (Lines G f 1) ℝ := Matrix.of fun x y =>
    Sum.elim (fun u => (1:Matrix (Lines G f 1) _ ℝ) u y) (fun v => -(patron G (fixRoot S) v y)) x
lemma stretch_first (G : Gauge) (S : StepData c f) : butt G c f * stretchJoint G S=1 := by
  rw [helmet_butt]; apply matSeen; intro i; rw [← mulVec_mulVec,sliceX,one_mulVec]; funext z
  change ((1:Matrix (Lines G f 1) _ ℝ)*ᵥ i) z=i z; rw [Matrix.one_mulVec]
lemma stretch_second (G : Gauge) (S : StepData c f) : brim G c f * stretchJoint G S= -patron G (fixRoot S):= by
  rw [helmet_brim]; apply matSeen; intro i; rw [← mulVec_mulVec,sliceY]; rfl
lemma right_collapse (G : Gauge) (S : StepData c f) : collapse G S * stretchJoint G S=1 := by
  unfold collapse; rw [Matrix.sub_mul,Matrix.mul_assoc,Matrix.add_mul,Matrix.mul_assoc,stretch_first,
    stretch_second,Matrix.mul_one,neg_add_cancel,Matrix.mul_zero,sub_zero]
lemma extend_active (G : Gauge) (T : Forest S.ratio) :
    toActive G S T*(stretchJoint G S * insertion (plant (G:=G) T))=1 := by
  let V:= projectFull G S T; let R:= reduce G S T
  simp only [toActive, casting, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (collapse G S), right_collapse,Matrix.one_mul,obtained];
  exact insertion.orthogonal (plant T) (plant_inj T)
end YM.WilsonBulk
