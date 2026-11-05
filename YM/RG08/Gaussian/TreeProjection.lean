import YM.RG08.Gaussian.Completion
import YM.Push.FREE_RESOLVENT.GaugeProjection

/-!
# Projection along joint gauge directions onto the conditional root/tree slice

Counts a coarse gauge parameter in the joint variables. Dropping it without
projection would generally not give the correct covariance even at quadratic
order. Works before period or patch cost estimates. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open Function Filter Lattice Wilson RG Exterior Precision Bloch Matrix
open Stationary Next.Free Work.F08 Tree FreeResolvent
open scoped Topology BigOperators Classical

variable {c f m n : Side} {G : Gauge}

lemma matrix_eq {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {A B : Matrix α β ℝ} (h : ∀ x,A*ᵥ x=B*ᵥ x) : A=B :=
  Matrix.toLin'.injective (LinearMap.ext h)

/-- Color-packing adapters, ordinary coordinates, no metric on test currents. -/
lemma tensor_same (G : Gauge) {i j : ℕ} (M : Matrix (Body i m) (Body j n) ℝ) :
    patron G M=tensor G M := by
  apply matrix_eq
  intro x; rw [patron_fee]
  funext y
  rcases y with ⟨u,z,k⟩
  exact (congr_fun (component_mul M x k) (u,z)).symm
lemma patron_add (G : Gauge) {i j : ℕ} (M N : Matrix (Body i m) (Body j n) ℝ) : patron G (M+N)= patron G M + patron G N := by
  simp_rw [tensor_same]
  ext i j; by_cases h : i.2.2=j.2.2 <;> simp [tensor,h]
lemma patron_scale (G : Gauge) {i j : ℕ} (t : ℝ) (M : Matrix (Body i m) (Body j n) ℝ) :
    patron G (t • M)=t • patron G M := by
  simp_rw [tensor_same]; ext i j; by_cases h : i.2.2=j.2.2 <;> simp [tensor,h]
lemma first_gradient (x : BaseSites G f) : gradientA G f x = gradient x := by
  rw [first_uniform,← patron_fee,tensor_same,gradient]
lemma base_test (S : StepData c f) :
    patron G (Precision.probe S) = bondsM G S + tensor G (d 0 c)*tensor G (fixRoot S) := by
  unfold probe; rw [patron_add,patron_mul (G:=G),tensor_same G (d 0 c), tensor_same G (fixRoot S)]
  rfl

section projector
variable (S : StepData c f)

def cutoffCenter (v : BaseSites G f) : BaseSites G c := fun i => v (S.ratio.embed i.1,i.2)
def stampZone (G : Gauge) := tensor G (fixRoot S)
lemma gaugeZone (v : BaseSites G f) :
    stampZone S G *ᵥ gradient v=cutoffCenter S v-curryG G S *ᵥ v := by
  funext x; obtain ⟨x,i,b⟩ := x; rw [vac_only i]
  change component (stampZone S G *ᵥ _) b (x,vac) = v _ - _
  rw [stampZone,component_mul,gradient,component_mul,psi_proj, curry_at]; rfl

def duplicateM (G : Gauge) : Matrix (Lines G f 0) (Lines G c 0) ℝ := LinearMap.toMatrix'
    (LinearMap.pi fun i : Lines G f 0 => LinearMap.proj (S.ratio.parent i.1,i.2))
lemma duplicate_reads (v : BaseSites G c) (x : Lines G f 0) :
    (duplicateM S G *ᵥ v) x = v (S.ratio.parent x.1,x.2) := by rw [duplicateM,LinearMap.toMatrix'_mulVec]; rfl
lemma duplicate_has (v : BaseSites G c) : cutoffCenter S (duplicateM S G *ᵥ v)=v := by
  ext1 x; simp [cutoffCenter,duplicate_reads,S.ratio.embed_parent]
lemma duplicate_frees (T : Forest S.ratio) (v : BaseSites G c) : Vanishes (S:=S) T (gradient (duplicateM S G *ᵥ v)) := by
  intro i e h
  rcases e with ⟨x,j⟩
  rw [gradient, component_mul,d_sites]
  simp only [component,ix,duplicate_reads,T.trunk_internal h,sub_self]

/-- Matrix of backward hikes in additive logs. -/
def hikeM (G : Gauge) (T : Forest S.ratio) : Matrix (Lines G f 0) (Lines G f 1) ℝ := LinearMap.toMatrix' {
  toFun := fun v => potential (S:=S) T v
  map_add' := fun x y => by
    funext i; unfold potential; change integralLink i.1 (T.hike i.1) (component x _ + component y _) = _
    rw [map_add]; rfl
  map_smul' := fun t v => by
    funext i; unfold potential; change integralLink i.1 (T.hike i.1) (t • component v _) = _
    rw [map_smul]; rfl }

variable (T : Forest S.ratio)
lemma hikeM_pay (v : Vec G f 1) : hikeM S G T *ᵥ v = potential (S:=S) T v := by rw [hikeM,LinearMap.toMatrix'_mulVec]; rfl
lemma root_center (v : Vec G f 1) : cutoffCenter S (potential T v)=0 := by
  ext1 i
  exact congr_fun (roots_pinned (S:=S) T v i.2.2) (i.1,i.2.1)
lemma root_duplicate (v : Vec G f 0) : potential (S:=S) T (gradient v)=duplicateM S G *ᵥ cutoffCenter S v-v := by
  ext1 x; obtain ⟨x,a,b⟩ := x; rw [vac_only a]; unfold potential; rw [gradient, component_mul, telescopes,T.hike_root, Pi.sub_apply,duplicate_reads]; rfl

/-- Joint gauge parameter. Explicit (important for block-dependent post cost). -/
def turnParameter (G : Gauge) := duplicateM S G * (brim G c f+stampZone S G * butt G c f) - hikeM S G T * butt G c f

def projection (G : Gauge) : Matrix (Lines G f 1) (Bodies G c f) ℝ := butt G c f -
    tensor G (d 0 f)*turnParameter S T G

def cropJoint (G : Gauge) := (butt G c f)ᵀ - (brim G c f)ᵀ*stampZone S G

lemma sets (x : Link G f) : cropJoint S G *ᵥ x=Sum.elim x (-(stampZone S G*ᵥ x)) := by
  rw [cropJoint,helmet_butt,helmet_brim]; funext i; rcases i with i|i <;> rw [Matrix.sub_mulVec,← Matrix.mulVec_mulVec] <;>
    simp [-Matrix.mulVec_mulVec,shardX, shardY,Matrix.mulVec, dotProduct,LinearMap.toMatrix'_apply,Pi.single_apply,ite_mul]

lemma picks_butt : butt G c f*cropJoint S G=1 := by
  apply matrix_eq; intro v; rw [← Matrix.mulVec_mulVec,sets,helmet_butt,sliceX,one_mulVec]; rfl
lemma picks_brim : brim G c f*cropJoint S G = -(stampZone S G) := by
  apply matrix_eq; intro v; rw [← Matrix.mulVec_mulVec,sets,helmet_brim,sliceY,neg_mulVec]; rfl

lemma roll_sum (x : Vault G c f) : turnParameter S T G *ᵥ (Sum.elim x.1 x.2) =
    duplicateM S G *ᵥ (x.2+stampZone S G *ᵥ x.1) - potential (S:=S) T x.1 := by
  rw [turnParameter, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,helmet_butt,helmet_brim,sliceX,sliceY,hikeM_pay]; rfl
lemma pays_projection (x : Vault G c f) : projection S T G *ᵥ (Sum.elim x.1 x.2) =
    representative S T x.1 - gradient (duplicateM S G *ᵥ (x.2+stampZone S G *ᵥ x.1)) := by
  rw [projection,sub_mulVec,← mulVec_mulVec,roll_sum S T x,helmet_butt,sliceX,mulVec_sub,gradient,representative,gradient]; change x.1-(_-_) = _; abel
lemma waypoint (x : Vault G c f) : stampZone S G *ᵥ (projection S T G *ᵥ Sum.elim x.1 x.2) = -(x.2 - curryG G S *ᵥ (turnParameter S T G *ᵥ Sum.elim x.1 x.2)) := by
  let v := turnParameter S T G *ᵥ Sum.elim x.1 x.2
  have hx : cutoffCenter S v=x.2+stampZone S G *ᵥ x.1 := by
    rw [show v=_ from roll_sum S T x,show cutoffCenter S (_-potential T x.1)=cutoffCenter S (duplicateM S G *ᵥ _) - cutoffCenter S (potential T x.1) from rfl,
      root_center, sub_zero,duplicate_has]
  rw [show projection S T G *ᵥ Sum.elim x.1 x.2=x.1-gradient v by
    rw [projection,sub_mulVec,← Matrix.mulVec_mulVec, helmet_butt,sliceX]; rfl,
    Matrix.mulVec_sub,gaugeZone,hx]; change _ = -(_ - _*ᵥ v); abel

/-- Exact joint projection onto the tree injection. -/
theorem tree_path : cropJoint S G * projection S T G = 1 + spreadM S * turnParameter S T G := by
  apply matrix_eq; intro v
  let x : Vault G c f := (v ∘ Sum.inl,v ∘ Sum.inr)
  have hx : v=Sum.elim x.1 x.2 := funext fun i => by cases i <;> rfl
  rw [Matrix.add_mulVec,one_mulVec, ← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,parliament S,helmet_ear,first_gradient,hx,sets,waypoint S T x,projection, sub_mulVec,← Matrix.mulVec_mulVec, helmet_butt,sliceX]
  ext1 i; rcases i with i|i
  · change x.1 i-_ = x.1 i+ -_
    simp [sub_eq_add_neg,gradient]
  change - (- (x.2-_)) i = x.2 i + -_
  simp [sub_eq_add_neg]

lemma lowered (v : BaseSites G f) : turnParameter S T G *ᵥ (spreadM S *ᵥ v)=-v := by
  rw [parliament, helmet_ear,roll_sum S T, first_gradient]; dsimp only
  rw [Matrix.mulVec_neg,gaugeZone,show -(curryG G S *ᵥ v)+ - (cutoffCenter S v-curryG G S *ᵥ v) = - cutoffCenter S v from by abel,
    ← hikeM_pay S T (-gradient v), Matrix.mulVec_neg, Matrix.mulVec_neg,hikeM_pay,root_duplicate]; abel
lemma tree_kills : projection S T G * spreadM (G:=G) S=0 := by
  apply matrix_eq; intro v
  rw [← Matrix.mulVec_mulVec, projection,Matrix.sub_mulVec, ← Matrix.mulVec_mulVec,lowered S T v,mulVec_neg,parliament S, helmet_ear,first_gradient,helmet_butt,sliceX]; change -gradient v - -gradient v= _; rw [sub_self,zero_mulVec]

/-- `sprig` inserts active cotree coordinates with color. -/
def sprig (G : Gauge) : Matrix (Lines G f 1) (Active G T) ℝ := insertion (plant T)
lemma sprig_in (u : Active G T→ℝ) : Vanishes (S:=S) T (sprig S T G *ᵥ u) := by
  intro i j h
  refine Finset.sum_eq_zero (fun y hy => ?_)
  change (if plant T y = _ then _ else _) * _=0
  rw [if_neg,zero_mul]
  intro hz
  apply y.1.property
  rw [show y.1.val=j from Prod.ext (congr_arg (fun z : Lines G f 1 => z.1) hz)
        ((coord_iff ..).mp (congr_arg (fun z : Lines G f 1 => z.2.1) hz))]; exact h
lemma tree_on (x : Vault G c f) : Vanishes (S:=S) T (projection S T G *ᵥ Sum.elim x.1 x.2) := by
  rw [pays_projection S T x]
  intro i e he
  change component (representative S T x.1) i _ - component (gradient _) i _= _
  rw [onto_slice T x.1 i e he, duplicate_frees S T _ i e he]; simp
lemma life : sprig S T G * (sprig S T G)ᵀ * projection S T G= projection S T G := by
  apply matrix_eq; intro v
  let x : Vault G c f := (v ∘ Sum.inl,v ∘ Sum.inr)
  rw [show v=Sum.elim x.1 x.2 from funext fun i => by cases i <;> rfl]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact projects T _ (tree_on S T x)
lemma tree_go : projection S T G *cropJoint S G * sprig S T G = sprig S T G := by
  apply matrix_eq; intro v
  rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,sets]
  let w := sprig S T G *ᵥ v
  change projection S T G*ᵥ Sum.elim w _= w
  have h := pays_projection S T (w, -(stampZone S G*ᵥ w)); dsimp only at h
  rw [h, FreeResolvent.fixes T (sprig_in S T v),neg_add_cancel,mulVec_zero,gradient,mulVec_zero,sub_zero]

end projector
end YM.RG08
