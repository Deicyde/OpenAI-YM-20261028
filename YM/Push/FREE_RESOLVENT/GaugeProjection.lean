import YM.Push.FREE_RESOLVENT.Flat
import YM.Push.FREE_RESOLVENT.Inverse

/-!
# Gauge and harmonic conventions of the inverse

`treeInverse` inverts on *exactly* the free active slots. All momenta,
including harmonic. For fixed coarse links, use quotient by root-pinned
gauge (subtracted gradients, roots zero), **not** by all gradients. This
completion is possible even on tori without global axial gauge; no decision
that winding plaquettes vanish. The direction spaces use counting real Lie
coordinates. `representative` straightens on the actual forest;
`covariance` zero extends the slice inverse, times the full operator this
is the explicit oblique gauge projection (not a Moore-Penrose claim).

Input `Larger` (when taking the gap) from E02's length etc. Not assuming
invertibility on any frequency sector. No stochastic averaging of trees/tags.
-/

set_option autoImplicit false
noncomputable section
namespace YM.FreeResolvent
open Lattice Wilson RG Matrix Laurent Bloch Exterior Precision Tree Bid
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
variable {n c f : Side} {S : StepData c f} {G : Gauge} {r : ℕ}

def Rooted (S : StepData c f) (u : Vec G f 0) : Prop := ∀ i, Precision.centered S (component u i) = 0
def gradient (u : Vec G f 0) : Vec G f 1 := tensor G (d 0 f) *ᵥ u

/-- Kills even before proving any gaps. Constant gauge at *all* roots
is accounted for by a gradient of a rooted parameter too (subtract a constant).
No eliminating a physical mode at the harmonic as if K alone had to invert. -/
lemma invisible (H : FaceRow) (u : Vec G f 0) (h : Rooted S u) :
    fullMatrix G S H *ᵥ gradient u = 0 := by
  funext x; rcases x with ⟨x,b,i⟩
  change component (fullMatrix G S H *ᵥ gradient u) i (x,b) = 0
  rw [fullMatrix, component_mul,gradient,component_mul,baseMatrix,Matrix.add_mulVec,
      mulVec_mulVec, K_kills, Matrix.zero_mulVec, zero_add, Matrix.smul_mulVec,
      ← Matrix.mulVec_mulVec, root_gradient, h i, Matrix.mulVec_zero, Matrix.mulVec_zero, smul_zero]
  rfl

def Vanishes (T : Forest S.ratio) (v : Vec G f 1) : Prop := ∀ i, Precision.marked (S:=S) T (component v i)



lemma hike_zero (T : Forest S.ratio) (u : form 1 f) (hu : marked (S:=S) T u) (x : Site f) :
    integralLink x (T.hike x) u = 0 := by
  induction x using Forest.hike.induct T with
  | case1 x h ih =>
    have hx := hu ((T.up x).used x) ((T.trunk_mem_iff _).mpr ⟨_,h,rfl⟩)
    rw [Forest.hike,dif_pos h]
    change linkSum (fun e => u (e.1,coord e.2)) x (_ :: _) = _
    rw [linkSum]; change _ + integralLink _ _ u = 0
    rw [hx, ih]; split <;> simp
  | case2 x h => rw [Forest.hike,dif_neg h]; rfl

/-- Root-fixed potential used to gauge TO the chosen tree. It adds the
integral in the backwards direction (check for negative edge orientation). -/
def potential (T : Forest S.ratio) (v : Vec G f 1) : Vec G f 0 := fun x =>
  integralLink x.1 (T.hike x.1) (component v x.2.2)

def representative (S : StepData c f) (T : Forest S.ratio) (v : Vec G f 1) := v + gradient (potential (S:=S) T v)

lemma roots_pinned (T : Forest S.ratio) (v : Vec G f 1) : Rooted S (potential T v) := by
  intro i; funext z
  unfold Precision.centered component ix potential
  simp only
  rw [Forest.hike,dif_neg]; · rfl
  simp [Tree.leaf,Ratio.embed_parent]

lemma onto_slice (T : Forest S.ratio) (v : Vec G f 1) : Vanishes T (representative S T v) := by
  intro i j hj
  obtain ⟨x,hx,rfl⟩ := (T.trunk_mem_iff j).mp hj
  have H1 : component (representative S T v) i = component v i +
      d 0 f *ᵥ component (potential (S:=S) T v) i := by rw [← component_mul]; rfl
  have H2 (x) : component (potential (S:=S) T v) i (x,vac) = integralLink x (T.hike x) (component v i) := rfl
  rw [H1,Pi.add_apply,d_sites,H2,H2]
  have he : integralLink x (T.hike x) (component v i) =
      (if (T.up x).neg then -component v i (((T.up x).used x).1,coord ((T.up x).used x).2) else
        component v i (((T.up x).used x).1,coord ((T.up x).used x).2)) +
      integralLink (x+(T.up x).vec) (T.hike (x+(T.up x).vec)) (component v i) := by
    rw [Forest.hike,dif_pos hx]; rfl
  cases h : T.up x with
  | mk k b =>
    rw [h] at he
    cases b
    · simp only [Step.used,Step.vec,Bool.false_eq_true,↓reduceIte] at he ⊢
      rw [he]; ring
    simp only [Step.used,Step.vec,↓reduceIte,sub_add_cancel] at he ⊢
    rw [← sub_eq_add_neg] at he
    rw [he]; ring

lemma fixes (T : Forest S.ratio) {v : Vec G f 1} (h : Vanishes T v) : representative S T v = v := by
  have he : potential (S:=S) T v = 0 := funext fun i => hike_zero T _ (h i.2.2) _
  simp only [representative,gradient,he,Matrix.mulVec_zero,add_zero]







lemma invariant (T : Forest S.ratio) (H : FaceRow) (v : Vec G f 1) :
    fullMatrix G S H *ᵥ representative S T v = fullMatrix G S H *ᵥ v := by
  rw [representative,Matrix.mulVec_add,invisible H _ (roots_pinned T v),add_zero]

/-- Selection from full coordinates. -/
def reduce (G : Gauge) (S : StepData c f) (T : Forest S.ratio) := (insertion (plant (G:=G) T)).transpose

lemma reduce_actual (T : Forest S.ratio) (v : Vec G f 1) : reduce G S T *ᵥ v = v ∘ plant T := by
  ext i; simp [reduce,mulVec,dotProduct,insertion]

lemma projects (T : Forest S.ratio) (v : Vec G f 1) (h : Vanishes T v) :
    insertion (plant T) *ᵥ (reduce G S T *ᵥ v) = v := by
  rw [reduce_actual]
  funext x; rcases x with ⟨x,b,j⟩
  obtain ⟨k,hk⟩ := axisEquiv.surjective b; rw [coord_map] at hk; subst b
  by_cases he : (x,k) ∈ T.trunks
  · rw [show v (x,coord k,j) = 0 from h j (x,k) he]
    refine Finset.sum_eq_zero fun i _ => ?_
    change (if plant T i = (x,coord k,j) then 1 else 0)*_ = 0
    rw [if_neg,zero_mul]; intro hx
    apply i.1.property
    rw [show i.1.val=(x,k) from Prod.ext (congr_arg (fun i : Slot G f 1 => i.1) hx)
      ((coord_iff ..).mp (congr_arg (fun i : Slot G f 1 => i.2.1) hx))]; exact he
  let u : Active G T := (⟨(x,k), he⟩, j)
  change (insertion (plant T) *ᵥ _) (plant T u) = v (plant T u)
  simp [insertion,mulVec,dotProduct,(plant_inj T).eq_iff]

/-- The actual periodic free block resolvent, real slots. -/
def treeInverse (G : Gauge) (S : StepData c f) (T : Forest S.ratio) (H : FaceRow) (u : ℝ) :=
  resolve (treeMatrix G S T H) u

lemma tree_laws (T : Forest S.ratio) (H : FaceRow) (hS : Larger (G:=G) S)
    {a u : ℝ} (ha : 0 < a) (hg : Gap (H.acts f) a) (hu : 0 ≤ u) :
    let A := treeMatrix G S T H + u • 1
    let C := treeInverse G S T H u
    C * A = 1 ∧ A * C = 1 :=
  ⟨resolve_left (tree_gap S T H hS ha hg) (treeFare_pos _ _ _ ha) hu,
    resolve_right (tree_gap S T H hS ha hg) (treeFare_pos _ _ _ ha) hu⟩

def covariance (G : Gauge) (S : StepData c f) (T : Forest S.ratio) (H : FaceRow) :=
  insertion (plant T) * treeInverse G S T H 0 * reduce G S T

/-- Covariance times full precision projects to the actual slice. -/
lemma block_solve (T : Forest S.ratio) (H : FaceRow) (hS : Larger (G:=G) S)
    {a : ℝ} (ha : 0 < a) (hg : Gap (H.acts f) a) (v : Vec G f 1) :
    covariance G S T H *ᵥ (fullMatrix G S H *ᵥ v) = representative S T v := by
  let w := representative S T v
  let u := reduce G S T *ᵥ w
  let I := insertion (plant (G:=G) T)
  have he : I *ᵥ u = w := projects T w (onto_slice T v)
  calc
    _ = covariance G S T H *ᵥ (fullMatrix G S H *ᵥ (I *ᵥ u)) := by rw [he]; unfold w; rw [invariant]
    _ = I *ᵥ u := by
      have hh : treeInverse G S T H 0 * treeMatrix G S T H = 1 := by
        simpa using (tree_laws T H hS ha hg (u:=0) le_rfl).1
      rw [covariance, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        Matrix.mulVec_mulVec _ (reduce G S T), Matrix.mulVec_mulVec u (reduce G S T * fullMatrix G S H),
        show reduce G S T * fullMatrix G S H * I = treeMatrix G S T H from insertion.compress (plant T) (fullMatrix G S H),
        Matrix.mulVec_mulVec u (treeInverse G S T H 0), hh, Matrix.one_mulVec]
    _ = _ := he



lemma full_symmetric (H : FaceRow) (he : (H.acts f).transpose = H.acts f) :
    (fullMatrix G S H).transpose = fullMatrix G S H := by
  rw [fullMatrix,tensor_transpose]; unfold baseMatrix
  simp only [transpose_add,transpose_smul, Precision.K, transpose_mul,he,transpose_transpose,Matrix.mul_assoc]

lemma covariance_symmetric (T : Forest S.ratio) (H : FaceRow) (he : (H.acts f).transpose = H.acts f) :
    (covariance G S T H).transpose = covariance G S T H := by
  have h : (treeMatrix G S T H).transpose = treeMatrix G S T H := by
    unfold treeMatrix; rw [transpose_submatrix, full_symmetric H he]
  have hh : (treeInverse G S T H 0).transpose = treeInverse G S T H 0 := by
    unfold treeInverse resolve; simp [Matrix.transpose_nonsing_inv,h]
  unfold covariance reduce; simp only [transpose_mul,transpose_transpose,hh,Matrix.mul_assoc]

end YM.FreeResolvent
