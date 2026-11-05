import YM.Push.CUTOFF_PROJECTORS.Along

/-!
# Left coordinates across a signed change of links

Use pullback (positive link in the pulled configuration may read a *negative*
link, with BOTH endpoints moved).

Thus when varying the independent links by
LEFT increments we have to transport the colors too.

Use the same conventions
on any side (even small side with equal vertices, no case distinction on side
size or on color dimension here).
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Equivariance
open Function Filter Lattice Wilson RG NormedSpace Push.CutoffProjectors
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side}

abbrev cbasis (G : Gauge) := EuclideanSpace.basisFun G.ColorIndex ℝ
abbrev bonds (s : Signed) (b : Site n) := RG.StepData.sendBonds s b

lemma send_formula (s : Signed) (b : Site n) (e : Edge (Site n)) :
    bonds s b e = if s.flip e.2 then
      (affine s b e.1 - step (s.perm e.2), s.perm e.2) else
      (affine s b e.1, s.perm e.2) := by
  change ((posDir e.2).rotate s).used _ = _
  simp [Step.used,Step.rotate,posDir]

lemma pull_formula (s : Signed) (b : Site n) (e : Edge (Site n)) (U : Config G n) :
    pull s b U e = if s.flip e.2 then (U (bonds s b e))⁻¹ else U (bonds s b e) := by
  change ((posDir e.2).rotate s).read _ _ = _
  rw [send_formula]; cases hs : s.flip e.2 <;> simp [Step.read,Step.rotate,posDir,hs,Step.used]

lemma affine_end (s : Signed) (b : Site n) (x : Site n) (i : Axis) :
    affine s b (x + step i) = affine s b x + ((posDir i).rotate s).vec := by
  rw [affine, affine, Signed.act_add, Step.vec_rotate, Step.vec_pos]; abel

/-- Both endpoint predicates, even on the edges sent to negative
orientation. -/
lemma send_mem (s : Signed) (b : Site n) (B : Support n) (e : Edge (Site n)) :
    let D := B.image (affine s b)
    let q := bonds s b e
    (q.1 ∈ D ∧ q.1 + step q.2 ∈ D) ↔ e.1 ∈ B ∧ e.1 + step e.2 ∈ B := by
  dsimp only
  have hi : Injective (affine s b) := fun x y h => s.act_injective (add_right_cancel h)
  have hx (x) : affine s b x ∈ B.image (affine s b) ↔ x ∈ B := by simp [Finset.mem_image, hi.eq_iff]
  have he := affine_end s b e.1 e.2
  rw [send_formula]; cases hs : s.flip e.2
  · simp [Step.vec,Step.rotate,posDir,hs] at he
    simp only [Bool.false_eq_true, ↓reduceIte, ← he, hx]
  simp [Step.vec,Step.rotate,posDir,hs, ← sub_eq_add_neg] at he
  simp only [↓reduceIte, sub_add_cancel]
  simp only [← he, hx]; exact and_comm

lemma agrees_pull (s : Signed) (b : Site n) (B : Support n) {U V : Config G n}
    (h : Agrees (B.image (affine s b)) U V) : Agrees (B : Set (Site n)) (pull s b U) (pull s b V) := by
  intro e h1 h2
  have he := (send_mem s b B e).2 ⟨h1,h2⟩
  rw [pull_formula,pull_formula,h (bonds s b e) he.1 he.2]

lemma local_pull {Y : Type*} (s : Signed) (b : Site n) (B : Support n) {f : Config G n → Y}
    (h : LocalOn B f) : LocalOn (B.image (affine s b)) (f ∘ pull s b) :=
  fun _ _ he => h _ _ (agrees_pull s b B he)

section Color

lemma exp_adjoint (u : G.El) (x : G.Color) : G.lieExp (G.adjoint u x) = u * G.lieExp x * u⁻¹ := by
  apply G.mat_injective
  simp only [G.mat_mul, G.mat_inv, G.mat_lieExp,G.mat_adjoint]; exact G.exp_conjugate _ _

lemma exp_opposite (x : G.Color) : G.lieExp (-x) = (G.lieExp x)⁻¹ := by
  apply Eq.symm
  haveI : NormedAlgebra ℚ G.Mat := .restrictScalars ℚ ℝ _
  have h : exp (G.colorMat x + (- G.colorMat x)) = exp (G.colorMat x)* exp (- G.colorMat x) := exp_add_of_commute ((Commute.refl _).neg_right)
  have he : G.lieExp x * G.lieExp (-x) = 1 := G.mat_injective (by
    rw [G.mat_mul, G.mat_one, G.mat_lieExp, G.mat_lieExp, map_neg,
      ← h]; simp)
  exact inv_eq_of_mul_eq_one_right he

lemma adjoint_fix_line (x : G.Color) (t : ℝ) : G.adjoint (G.lieExp (t • x)) x = x := by
  apply G.colorMat_injective
  haveI : NormedAlgebra ℚ G.Mat := .restrictScalars ℚ ℝ _
  have he : Commute (exp (t • G.colorMat x)) (G.colorMat x) := ((Commute.refl _).smul_left t).exp_left
  have hv : G.mat (G.lieExp (t • x)) * G.colorMat x = G.colorMat x * G.mat (G.lieExp (t • x)) := by
    rwa [G.mat_lieExp,map_smul]
  rw [G.mat_adjoint,Gauge.conjugate,hv,mul_assoc,G.mat_mul_star,mul_one]

lemma adjoint_fix_inv_line (x : G.Color) (t : ℝ) : G.adjoint ((G.lieExp (t • x))⁻¹) x = x := by
  rw [← exp_opposite, ← neg_smul, adjoint_fix_line]

/-- Real orthogonal map from target to pulled-left coordinates, at a
positive edge of the pulled configuration. This sign is the one on , not just a permutation sign, and it depends on the link! -/
def roll (s : Signed) (b : Site n) (U : Config G n) (e : Edge (Site n)) : G.Color ≃ₗᵢ[ℝ] G.Color :=
  let u := U (bonds s b e)
  let D (u : G.El) : G.Color →ₗ[ℝ] G.Color := if s.flip e.2 then -(G.adjoint u⁻¹) else LinearMap.id
  { D u with
    invFun := D u⁻¹
    left_inv := fun x => by
      change D u⁻¹ (D u x) = x
      unfold D; split
      · simp [← G.adjoint_mul]
      rfl
    right_inv := fun x => by
      change D u (D u⁻¹ x) = x
      unfold D; split
      · simp [← G.adjoint_mul]
      rfl
    norm_map' := fun x => by
      change ‖D u x‖ = _
      unfold D; split
      · simp
      rfl }

lemma roll_apply (s : Signed) (b : Site n) (U : Config G n) (e : Edge (Site n)) (x : G.Color) :
    roll s b U e x = if s.flip e.2 then - G.adjoint (U (bonds s b e))⁻¹ x else x := by
  change (if s.flip e.2 then -(G.adjoint _) else LinearMap.id) x = _
  split <;> rfl

end Color

section Increment

/-- The linear direction for this same `pull`. Domain and range in physical
colors. -/
def pulledDirection (s : Signed) (b : Site n) (U : Config G n) : Directions G n →ₗ[ℝ] Directions G n where
  toFun A e := roll s b U e (A (bonds s b e))
  map_add' A B := by ext1 e; change roll _ _ _ _ (_+_) = _; rw [map_add]; rfl
  map_smul' t A := by ext1 e; change roll _ _ _ _ (t • _) = _; rw [map_smul]; rfl

lemma pull_increment (s : Signed) (b : Site n) (U : Config G n) (A : Directions G n) :
    pull s b (increment U A) = increment (pull s b U) (pulledDirection s b U A) := by
  funext e
  rw [pull_formula]
  change _ = G.lieExp (roll s b U e _) * pull s b U e
  rw [roll_apply,pull_formula]; split
  · rw [exp_opposite,exp_adjoint]; unfold increment; group
  rfl

/-- Vary only one link, in an arbitrary color. -/
abbrev single (e : Edge (Site n)) (x : G.Color) : Directions G n := Pi.single e x

lemma pull_single (s : Signed) (b : Site n) (U : Config G n) (e : Edge (Site n)) (x : G.Color) :
    pulledDirection s b U (single (bonds s b e) x) = single e (roll s b U e x) := by
  funext f
  by_cases h : f = e
  · subst f; simp [pulledDirection,single]
  have hh : sendEdge s b f ≠ sendEdge s b e := (sendEdge_injective s b).ne h
  simp [pulledDirection,single,h,hh]

/-- Diagonal directions in the divergence computation. The roll at a
negative link is not constant, but *this column at points along the same
variation* is. -/
lemma roll_increment (s : Signed) (b : Site n) (U : Config G n) (A : Directions G n) (e : Edge (Site n)) (t : ℝ) :
    roll s b (increment U (t • A)) e (A (bonds s b e)) = roll s b U e (A (bonds s b e)) := by
  rw [roll_apply,roll_apply]; split
  · unfold increment
    rw [mul_inv_rev, G.adjoint_mul, Pi.smul_apply,adjoint_fix_inv_line]
  rfl

end Increment
end YM.ProjectorNext.Equivariance
