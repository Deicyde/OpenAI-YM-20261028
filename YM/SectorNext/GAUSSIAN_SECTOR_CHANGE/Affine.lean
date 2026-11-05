import YM.Bid.Craft
import YM.Push.SECTOR_MEASURE.Oriented
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Counting
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Held




set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Gram and source on this sector, from the actual affine rows

 and 6014--35. D uses the given tree,
orientation and retained horizon/path data of this step's `Tube`.
Intermediate values on all finite periodic indices (no diagonalization
or harmonic-mode deletion; e.g. in the `Flat` and `Bed` checks, the
zero mesh point is present). No truncation of branch stencils. For $
ℓ_R$ uses the cut and true path sum exactly. For generality, we take
potential stencils as parameter here; also provide choices below (can
take conservative whole balls, not based on the realized zeros). D is
written as an everywhere expression (fderiv has default-zero convention
if not differentiable, doesn't assert that branch/path derivatives for
unselected data exist). Use `Authorized` to read it as the indicated
linearizations in estimates. For integral identity no such *estimates*
assumed. See consumption and gap checks.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.SectorChange
open Function Filter Lattice Wilson RG Precision Exterior Tree MeasureTheory Metric Matrix Gaussian
open YM.Pressure (Cell Bond Twin Tube toll plotted shoot shorten cuff crown)
open YM.Pressure YM.Pressure.Tube YM.Pressure.Stores YM.Bid YM.Push.SectorMeasure
open YM.Next.Fluctuations.Sector YM.Push.SectorMeasure.Oriented
open scoped Topology BigOperators Classical RealInnerProductSpace ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f} {x : ℝ}

/-- Both coordinates in a Twin p-block will have same stencil (store by
p or by noise b only). Stencils here in COMMON physical positive bonds. -/
abbrev Where (S : StepData c f) := Cell f ⊕ Bond c
abbrev Stencils (S : StepData c f) := Signed → Where S → Finset (Bond f)
abbrev Slots (S : StepData c f) := Signed × (Twin f ⊕ Bond c)

def curb (W : Stencils S) (A : Stores S) (F : Forest S.ratio) (x : ℝ) (s : Signed) (j : Where S) : Prop :=
    ∃ i : Active A x F, i.val.val ∈ W s j

def facade (S : StepData c f) (s : Signed) (V : Config G c) (a : Directions G f) : Config G f :=
  pull s 0 (increment (replica S.ratio V) a)

lemma fixed_facade (S : StepData c f) (s : Signed) (V : Config G c) :
    facade S s V 0 = pull s 0 (replica S.ratio V) := by
  unfold facade; congr 1; funext i; simp [increment]

-- The two actual fixed-L branch tests for differentiated data.
-- Compute Q rotation by first pulling back the whole *group* read.
def plaquetteJet (S : StepData c f) (V : Config G c) (s : Signed) (p : Cell f) :
    Directions G f →L[ℝ] G.Color :=
  fderiv ℝ (fun a => G.curvature (faceValue (facade S s V a) p)) 0

def predictGroup (V : Config G c) (k : S.Choices) (s : Signed) (i : Bond c) (a : Directions G f) :=
  S.prediction (facade S s V a) (choice s k) i

def predictorTurn (V : Config G c) (k : S.Choices) (s : Signed) (i : Bond c) (a : Directions G f) :=
  predictGroup V k s i a * (predictGroup V k s i 0)⁻¹

def blockJet (V : Config G c) (k : S.Choices) (s : Signed) (i : Bond c) : Directions G f →L[ℝ] G.Color :=
  fderiv ℝ (fun a => G.curvature (predictorTurn V k s i a)) 0

section stack
variable (P : PathData G) (r : ℕ) (U : Config G f) (b : LogArray G (Cell f)) (p : Cell f)

/-- `$ℓ_R^U b$`; cut at native fine length R. slotFace implements the
actual anchor p.1, also for winding. -/
def barrel := ∑' i : ℕ, let s := (P.row p.2 i).2; if s.length ≤ r then (P.row p.2 i).1 •
    G.adjoint (travel U p.1 s.walk) (b (Work.F03.slotFace s p.1)) else 0

variable {C σ Λ : ℝ} {o : Clip} (hb : P.Bounds o σ C Λ)
include hb

lemma barrel_summed : Summable (fun i : ℕ => let s := (P.row p.2 i).2; if s.length ≤ r then (P.row p.2 i).1 •
    G.adjoint (travel U p.1 s.walk) (b (Work.F03.slotFace s p.1)) else 0) := by
  refine Summable.of_norm_bounded ((Work.F03.row_abs_summable P hb p.2).mul_right ‖b‖) ?_
  intro i
  dsimp only; split
  · rw [norm_smul,G.norm_adjoint,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm ..) (abs_nonneg _)
  · rw [norm_zero]; positivity

lemma barrel_add (t : LogArray G (Cell f)) :
    barrel P r U (b+t) p = barrel P r U b p + barrel P r U t p := by
  unfold barrel
  rw [← Summable.tsum_add (barrel_summed _ _ _ b p hb) (barrel_summed _ _ _ t p hb)]
  refine tsum_congr fun i => ?_
  dsimp only; split <;> simp [*,smul_add]

lemma barrel_smul (d : ℝ) : barrel P r U (d • b) p = d • barrel P r U b p := by
  unfold barrel; rw [← Summable.tsum_const_smul d (barrel_summed _ _ _ b p hb)]
  refine tsum_congr fun i => ?_; dsimp only; split <;> simp [*, smul_comm (P.row p.2 i).1]

omit hb in
lemma barrel_term : barrel P r U (fun x => G.curvature (faceValue U x)) p = shorten P r 1 U p := by
  unfold barrel shorten shortenTerm
  refine tsum_congr fun i => ?_; dsimp only; simp [PathData.ellTerms,Work.F03.atSite_path]
end stack

namespace Rows
variable (T : Tube G S) (x : ℝ) (V : Config G c) (k : S.Choices)

/-- Unweighted vector at zero displacement. Does not include m_p on the
input second component (selected subtraction). Keeps v via literal horizon
truncations on the actual rotated V, including thinned selector on output.
No conditioning the predictor on separate copies of the tag. -/
def faceFixed (s : Signed) (V : Config G c) (j : Twin f) : G.Color :=
  T.Xf (till x) (facade S s V 0) j - T.Mv (till x) (temp x) (pull s 0 V) j

def noiseFixed (s : Signed) (j : Bond c) : G.Color :=
  Z S (S.prediction (facade S s V 0) (choice s k)) (pull s 0 V) j - T.Mw (till x) (temp x) (pull s 0 V) j

-- linear part, use dbar through paths with actual *constant* transports
-- evaluated at bar (no derivative on transports)
def faceKick (a : Directions G f) (s : Signed) (j : Twin f) : G.Color :=
  if j.2 then barrel T.up (till x) (facade S s V 0) (fun i => plaquetteJet S V s i a) j.1 else
    Real.sqrt T.high.direct • plaquetteJet S V s j.1 a

def noiseKick (a : Directions G f) (s : Signed) (j : Bond c) : G.Color :=
  -(Real.sqrt S.kernel.penalty • blockJet V k s j a)

def bump (a : Directions G f) : LogArray G (Slots S) :=
  fun i => i.2.elim (fun j => faceKick T x V a i.1 j) (fun j => noiseKick V k a i.1 j)

def base : LogArray G (Slots S) := fun i => i.2.elim (fun j => faceFixed T x i.1 V j) (fun j => noiseFixed x V k i.1 j (T:=T))

def keep (W : Stencils S) (A : Stores S) (F : Forest S.ratio) (i : Slots S) : Prop :=
    i.2.elim (fun j => curb W A F x i.1 (.inl j.1)) (fun b => curb W A F x i.1 (.inr b))

def slip := (Real.sqrt (Fintype.card Signed : ℝ))⁻¹

lemma slip_pos : 0 < slip := by
  have h := Fintype.card_pos (α:=Signed)
  unfold slip; positivity

def restrict (W : Stencils S) (A : Stores S) (F : Forest S.ratio) (z : LogArray G (Slots S)) : LogArray G (Slots S) := fun i =>
  if keep x W A F i then slip • z i else 0

def selected (W : Stencils S) (A : Stores S) (F : Forest S.ratio) (a : Directions G f) :=
  restrict x W A F (bump T x V k a)

variable {σ Λ ω₀ : ℝ} {o : Clip}

lemma bump_add (hT : T.up.Bounds o σ ω₀ Λ) (a b : Directions G f) :
    bump T x V k (a+b)=bump T x V k a + bump T x V k b := by
  funext i
  obtain ⟨s,j|j⟩ := i
  · simp only [bump, Pi.add_apply, Sum.elim_inl,faceKick,map_add]; split
    · exact barrel_add _ _ _ _ _ hT _
    next hh => rw [smul_add]
  simp only [bump,Pi.add_apply,Sum.elim_inr, noiseKick,map_add,smul_add,neg_add]

lemma bump_smul (hT : T.up.Bounds o σ ω₀ Λ) (a : Directions G f) (w : ℝ) :
    bump T x V k (w • a)=w • bump T x V k a := by
  funext i
  obtain ⟨s,j|j⟩ := i
  · simp only [bump, Pi.smul_apply, Sum.elim_inl,faceKick,map_smul]; split
    · exact barrel_smul _ _ _ _ _ hT w
    next hh => rw [smul_comm]
  simp only [bump,Pi.smul_apply,Sum.elim_inr, noiseKick,map_smul,smul_neg,smul_comm w]

lemma restrict_add (W : Stencils S) (A : Stores S) (F : Forest S.ratio) (a b : LogArray G (Slots S)) :
    restrict x W A F (a+b)=restrict x W A F a+restrict x W A F b := by funext i; unfold restrict; split <;> simp [*,smul_add]
lemma restrict_smul (W : Stencils S) (A : Stores S) (F : Forest S.ratio) (a : LogArray G (Slots S)) (w : ℝ) :
    restrict x W A F (w • a)=w • restrict x W A F a := by funext i; unfold restrict; split <;> simp [*,smul_comm slip]

/-- Include regular a on the physical bond array with zero on tree AND
frozen. -/
def fresh (W : Stencils S) (A : Stores S) (F : Forest S.ratio) (v : LogArray G (Active A x F)) : Directions G f := fun e =>
  if he : e∉F.trunks then
    if hk : ¬chill A x F ⟨e,he⟩ then v ⟨⟨e,he⟩,hk⟩ else 0 else 0

/-- And pass the patched frozen displacements at their correct positive
coordinates. -/
def input (A : Stores S) (F : Forest S.ratio) (a : LogArray G (Frozen A x F)) : Directions G f := fun e =>
  if he : e∉F.trunks then
    if hk : chill A x F ⟨e,he⟩ then a ⟨⟨e,he⟩,hk⟩ else 0 else 0

variable (W : Stencils S) (A : Stores S) (F : Forest S.ratio)

lemma fresh_add (a b : LogArray G (Active A x F)) : fresh x W A F (a+b)=fresh x W A F a+fresh x W A F b := by
  funext i; unfold fresh; split
  · split <;> simp_all
  · simp_all
lemma fresh_smul (a : LogArray G (Active A x F)) (w : ℝ) : fresh x W A F (w • a)=w • fresh x W A F a := by
  funext i; unfold fresh; split
  · split <;> simp_all
  · simp_all

def drift (hT : T.up.Bounds o σ ω₀ Λ) : LogArray G (Active A x F) →ₗ[ℝ] LogArray G (Slots S) where
  toFun v := selected T x V k W A F (fresh x W A F v)
  map_add' a b := by unfold selected; rw [fresh_add, bump_add _ _ _ _ hT, restrict_add]
  map_smul' w a := by unfold selected; rw [fresh_smul,bump_smul _ _ _ _ hT, restrict_smul]; rfl

/-- Matrix D. Doesn't depend on Y. Counting matrix, no inverse-spacing
factors, no cardinality division except channel square-root. -/
def move : Matrix (Slots S × G.ColorIndex) (Active A x F × G.ColorIndex) ℝ := Matrix.of fun i j =>
  tape.symm (selected T x V k W A F (fresh x W A F (axisPrice j))) i

/-- F0, all Y factors as actual link reads, no price-measure factor
hidden. Holds V fixed. -/
def source (q : Chi) (d : ℝ) (Y : LinkArray G (Frozen A x F)) : Prices G (Slots S) :=
  tape.symm (restrict x W A F (base T x V k + bump T x V k (input x A F (autoShell q d V Y))))

lemma moved (h : T.up.Bounds o σ ω₀ Λ) (a : Prices G (Active A x F)) :
    move T x V k W A F *ᵥ a = tape.symm (selected T x V k W A F (fresh x W A F (tape a))) := by
  let J := (colors (ι:=Slots S) (G:=G)).symm.toLinearMap ∘ₗ (drift T x V k W A F h) ∘ₗ colors.toLinearMap
  have he : LinearMap.toMatrix' J=move T x V k W A F := by
    ext i j
    rw [LinearMap.toMatrix'_apply]
    rfl
  rw [← he,LinearMap.toMatrix'_mulVec]
  rfl

end Rows
end YM.Next.SectorChange
