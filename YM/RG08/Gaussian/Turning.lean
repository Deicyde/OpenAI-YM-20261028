import YM.RG08.Gaussian.Stability

/-!
# A-tree/A₀ projection and costs
Use mean directions, not covariances. At unchanged grade transformation
by this gradient will still need the lower-grade Ward identities. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open Function Filter Lattice Wilson RG Precision Exterior Bloch Matrix Laurent
open Next.Free Work.F08 Tree Stationary FreeResolvent
open scoped Topology BigOperators Classical

variable {G : Gauge} {P : Patch} {c f L : Side} {σ τ C : ℝ}

def painted (G : Gauge) {i j : ℕ} (U : Cross L (TypeFace i) (TypeFace j)) : Cross L (Loc G i) (Loc G j) :=
    fun x y z => colored G U ((x.1,x.2.1),x.2.2) y z
lemma paint_budget {i j : ℕ} {A : Cross L (TypeFace i) (TypeFace j)} (h : A.strip σ C) :
    (painted G A).strip σ C := fun _ y => colored_price G h _ y
lemma paint_diff {i j : ℕ} (A : Cross L (TypeFace i) (TypeFace j)) (s : Axis) :
    forwardC L (painted G A) s=painted G (forwardC L A s) := by
    funext x y z; by_cases h : x.2.2=y.2 <;> simp [forwardC,painted,colored,h]
lemma paint_diffs {i j : ℕ} (A : Cross L (TypeFace i) (TypeFace j)) (s : List Axis) :
    advanceC L (painted G A) s=painted G (advanceC L A s) := by
    induction s with
    | nil => rfl
    | cons u v IH => rw [advanceC,IH,paint_diff,advanceC]
lemma paint_port (g : Ratio c f) {i j : ℕ} (A : Cross g.count (TypeFace i) (TypeFace j)) :
    installed g (painted G A)=patron G (installed g A) := by
    rw [tensor_same]; ext ⟨x,p,v⟩ ⟨y,q,w⟩; by_cases h : v=w <;> simp [installed, split_co, Row.acts,painted,colored,tensor,h]
lemma paint_cup (S : StepData c f) {i j : ℕ} (A : Cross S.patch.L (TypeFace i) (TypeFace j)) :
    Row.acts (painted G A) c=repackM (unitSplit G S i) (Equiv.refl _) (patron G (installed S.ratio A)) := by
  erw [← paint_port S.ratio]; ext x y; simp [installed,repackM,unitSplit]; rfl

lemma route_credits (S : StepData c f) (T : Forest S.ratio) (U : Matrix (Body 1 f) (Body 1 c) ℝ) :
    patron G (straighten S T U) = (hikeM S G T - duplicateM S G*stampZone S G)*patron G U := by
  apply matrix_eq; intro v; rw [← Matrix.mulVec_mulVec, tensor_same,tensor_same]
  ext1 x; rcases x with ⟨x,i,j⟩
  rw [Matrix.sub_mulVec,← Matrix.mulVec_mulVec,vac_only i,hikeM_pay]
  change component (tensor G (straighten S T U) *ᵥ v) j (x,vac)=_ - (duplicateM S G *ᵥ _) _
  rw [component_mul,books,duplicate_reads]; unfold potential
  rw [component_mul]
  rw [show (stampZone S G*ᵥ (tensor G U*ᵥ v)) (S.ratio.parent x,vac,j)= (fixRoot S*ᵥ (U *ᵥ component v j)) (S.ratio.parent x,vac) by
    change component (tensor G (fixRoot S)*ᵥ (tensor G U *ᵥ v)) j (S.ratio.parent x,vac)=_
    rw [component_mul,component_mul]]

lemma turn_fee (G : Gauge) (P : Patch) (X : Repeated P.L) (K : KernelChoices) (σ : ℝ) (hp : 0<σ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (A : Cross P.L (TypeFace 1) (TypeFace 1)) (B : ℝ), A.strip σ B →
      ∃ φ : Row (Co P.L (Loc G 0)) (Loc G 1), φ.strip σ (M*B) ∧
        ∀ (c f : Side) (h : f.val=c.val*P.L.val),
          let S := linked P K c f h
          φ.acts c=repackM (unitSplit G S 0) (Equiv.refl _) (patron G (straighten S (X.forest S.ratio) (installed S.ratio A))) := by
  obtain ⟨C,hC,Q,hQ,H⟩ := (hike_offer G K X σ hp).minus
        ((dup_offer G P K σ hp).mult (root_offer G P K σ hp) hp.le) hp.le
  refine ⟨(Fintype.card (Co P.L (Loc G 1)) : ℝ)*C,by positivity, fun A B h => ?_⟩
  let R:= composeRows Q (painted G A)
  rw [mul_assoc]; refine ⟨R,strip_compose hp.le hQ (paint_budget h),?_⟩
  intro c f hf S
  unfold R; rw [acts_compose hp.le hQ (paint_budget h), H c f hf]
  erw [paint_cup S (G:=G) A]
  rw [route_credits, repack_multiply _ (unitSplit G S 1), show repackM _ (unitSplit G S 1) (_-_)=
      repackM (unitSplit G S 0) (unitSplit G S 1) (hikeM S G (X.forest S.ratio)) - repackM (unitSplit G S 0) (unitSplit G S 1) (duplicateM S G*stampZone S G) from rfl,
      repack_multiply _ (Equiv.refl _)]
  rfl
end YM.RG08
