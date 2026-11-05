import YM.AnalyticBridge.NONFLAT_COVARIANCE_LOCALITY.Full
import YM.AnalyticBridge.NONFLAT_COVARIANCE_LOCALITY.Rows
import YM.AnalyticBridge.NONFLAT_COVARIANCE_LOCALITY.Sites

/-!
# Ambient entry computation of D

The window identifies on the active portion of D/A; for comparing shape
choices of this kernel it's convenient to keep full addresses even with
junk at unused tangents. We re-prove the kernel has finite dependence at a
column *before* applying any tests or pairing to a real cost. Do not drop
the possible curb/keep queries.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.NonflatCovarianceLocality.Matching
open Function Filter Lattice RG Pressure Precision Wilson Tree Matrix
open Next.SectorChange Next.SectorChange.Schur Next.SectorChange.Wisps Next.Fluctuations
open Next.SectorChange.Completion Next.SectorChange.Rows Full Push.SectorMeasure
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff

variable {G : Gauge} {c f : Side} {S : StepData c f} {x C Y s : ℝ}

abbrev pointer {x : ℝ} (A : Stores S) (F : Forest S.ratio) (p : In x A F (G:=G)) : Index G f :=
  (fundEdge A F p.1,p.2)
lemma pointer_injective {x : ℝ} (A : Stores S) (F : Forest S.ratio) (G : Gauge) :
    Function.Injective (pointer A F (G:=G) (x:=x)) :=
  (sorted A F).injective.comp Sum.inl_injective

def longPulse (p : Index G f) : Directions G f := Pi.single p.1 (EuclideanSpace.basisFun G.ColorIndex ℝ p.2)
lemma pointer_bond (x : ℝ) (A : Stores S) (F : Forest S.ratio) (p : In x A F (G:=G)) :
    longPulse (pointer A F p)=fresh x (shots S x) A F (axisPrice p) := by
  funext i
  by_cases h : i=p.1.val.val
  · rw [h]; simp only [Gap.freshly_read, pointer,longPulse,on_axis, Pi.single_eq_same]
  · rw [(sparsity x A F p).1 i h]; exact Pi.single_eq_of_ne h _

def feature (x : ℝ) (T : Tube G S) (A : Stores S) (F : Forest S.ratio)
    (k : S.Choices) (V : Config G c) : Matrix (Receipt G S) (Index G f) ℝ := of fun i j =>
  if engaged x A F j.1 then tape.symm (Rows.selected T x V k (shots S x) A F (longPulse j)) i else 0

def identityRest (x : ℝ) (A : Stores S) (F : Forest S.ratio) (G : Gauge) :=
  diagonal fun i : Index G f => if engaged x A F i.1 then 0 else (1:ℝ)

lemma side_active (x : ℝ) (T : Tube G S) (A : Stores S) (F : Forest S.ratio)
    (V : Config G c) (k : S.Choices) (i : In x A F (G:=G)) (q : Receipt G S) :
    feature x T A F k V q (pointer A F i)=Rows.move T x V k (shots S x) A F q i := by
  rw [feature, Matrix.of_apply, if_pos (show engaged x A F (pointer A F i).1 from fresh_active ..),
    pointer_bond]; rfl
lemma side_unused (x : ℝ) (T : Tube G S) (A : Stores S) (F : Forest S.ratio)
    (V : Config G c) (k : S.Choices) (i : vacant A F x G) (q : Receipt G S) :
    feature x T A F k V q i.val=0 := by
  rw [feature, Matrix.of_apply, if_neg (vacant_pass A F i)]

-- shape-independent proof with the empty halves still allowed
private lemma diagram {α β γ δ : Type} [Fintype α] [Fintype δ] [DecidableEq γ] [DecidableEq β]
    (e : (α⊕β) ≃ γ) (w : γ → ℝ) (M : Matrix δ α ℝ) (D : Matrix δ γ ℝ)
    (ht : ∀ x (b : α), D x (e (.inl b))=M x b) (hx : ∀ x (b : β), D x (e (.inr b))=0)
    (hv : ∀ b : α, w (e (.inl b))=0) (hw : ∀ b : β, w (e (.inr b))=1) :
    (wide (M.transpose*M) (1:Gaussian.Table β)).submatrix e.symm e.symm=
      D.transpose*D + diagonal w := by
  ext i j
  obtain ⟨a|a,rfl⟩ := e.surjective i <;>
    obtain ⟨b|b,rfl⟩ := e.surjective j <;>
    simp [Matrix.mul_apply,ht,hx,diagonal_apply,wide,hv,hw,Matrix.one_apply]

lemma from_data (x : ℝ) (T : Tube G S) (A : Stores S) (F : Forest S.ratio)
    (V : Config G c) (k : S.Choices) :
    let M := feature x T A F k V
    board x A F G (Rows.gram T x V k (shots S x) A F)=M.transpose*M + identityRest x A F G := by
  intro M
  let Q := Rows.move T x V k (shots S x) A F
  let e := sorted A F (G:=G) (x:=x)
  let w (y : Index G f) : ℝ := if engaged x A F y.1 then 0 else 1
  have ht q i : M q (e (.inl i))=Q q i := by
    change feature x T A F k V q (pointer A F i)=_
    exact side_active x T A F V k i q
  have hx q i : M q (e (.inr i))=0 := by
    change M q i.val=0
    exact side_unused x T A F V k i q
  have hh : ∀ i : Rows.In x A F (G:=G), w (e (.inl i))=0 := fun i =>
    if_pos (fresh_active x A F i.1)
  have hy i : w (e (.inr i))=1 := if_neg (vacant_pass A F i)
  have he := diagram e w Q M ht hx hh hy
  unfold board Rows.gram identityRest
  convert he using 3

variable {V : Config G c} {T : Tube G S} {k : S.Choices} {F : Forest S.ratio}

lemma feature_range (hp : S.patch.Branches S.kernel G) (A : Stores S) (i : Receipt G S)
    (j : Index G f) (hz : ¬ separation (down S i) (point S j) ≤ span S.patch x) :
    feature x T A F k V i j=0 := by
  obtain ⟨⟨s,p⟩,t⟩ := i
  rw [feature,Matrix.of_apply]; split
  · change Rows.restrict x (shots S x) A F _ _ t=0
    unfold Rows.restrict; split
    · rw [bump_dep T x V k s p (longPulse j) 0 hp ?_]
      · rcases p with a|a
        · change (slip • faceKick T x V 0 s a) t=0
          rw [show faceKick T x V 0 s a=0 by unfold faceKick; simp [barrel],smul_zero]; rfl
        change (slip • noiseKick V k 0 s a) t=0
        rw [show noiseKick V k 0 s a=0 by simp [noiseKick],smul_zero]; rfl
      intro b hb
      have he : b≠j.1 := fun hh => hz (show separation _ (S.ratio.parent j.1.1) ≤ _ from
        (contains ..).1 (hh ▸ hb))
      exact Pi.single_eq_of_ne he _
    · rfl
  rfl

end YM.AnalyticBridge.NonflatCovarianceLocality.Matching
