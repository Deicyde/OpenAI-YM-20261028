import Mathlib.Analysis.Fourier.Convolution
import YM.Next.BOUNDARY.Coordinates
import YM.Next.FREE_KERNELS.Lifts
import YM.Next.ROTATIONS.Charge
import YM.Next.SCHEDULE.GridCost
import YM.Next.SCHEDULE.Stadium
import YM.Push.CUTOFF_PROJECTORS.Along
import YM.Push.FREE_RESOLVENT.Envelope
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Flat
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Joint



/-!
# Aligned free mean, I. Actual period linear equations and common orientation

Shortcut proof: compare all L² bills on the
same period.

`m,n,o` acts on actual rooted colors and harmonic
patches.

Recall this is about real linear rows; no differentiation of
PathData.kept on big fields or assuming b frontier determined by Type shape.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussianLaws.Lift
open Function Lattice RG Wilson Finset Pressure Pressure.Tube Precision Exterior Tree Bloch Bid Matrix
open Next Next.Fluctuations SectorChange SectorChange.Rows SectorChange.Gaussian Push.SectorMeasure
open scoped Topology InnerProductSpace BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f n : Side} {S : StepData c f} (s : Signed)

def test {i : Type} [Fintype i] (a : i→G.Color) := ∑ x, inner ℝ (a x) (a x)

lemma test_neutral {i : Type} [Fintype i] (a : i→G.Color) : 0≤test a := Finset.sum_nonneg fun _ _ => real_inner_self_nonneg
lemma test_eq_zero {i : Type} [Fintype i] (a : i→G.Color) (h : test a≤0) : a=0 := by
  funext x; change _=0; apply inner_self_eq_zero (𝕜:=ℝ)|>.mp
  exact le_antisymm ((single_le_sum (f:=fun x => inner ℝ (a x) (a x)) (fun i _ => real_inner_self_nonneg) (mem_univ x)).trans h) real_inner_self_nonneg

variable {H : Bed} {W : PathData G} {C σ Λ a b : ℝ} {p : Clip}

lemma firstX (B : Dir G n) (h1 : Attached H W) (h2 : W.Bounds p σ C Λ) (h3 : Floor H p n a b) :
    test (xLin p W B)=gaugeFiscal H B B := by
  rw [test,Fintype.sum_prod_type,Work.F03.metric_pair H h2 h1 B B h3] -- gaugeFiscal unfold not correct
  apply Finset.sum_congr rfl; intro i _
  rw [Fintype.sum_bool]; simp only [Bool.false_eq_true,↓reduceIte, xLin,real_inner_smul_left,real_inner_smul_right,← mul_assoc,Real.mul_self_sqrt p.quadratic_pos.le, add_comm]

private lemma pulled_test (a : Dir G n) : test (fun i : Bond n=>pulled a s (pole i))=test a := by
  let F := StepData.sendBonds s (0:Site n); let L:=Work.E03.poleEquiv n; let w i:= inner ℝ (a (L i)) (a (L i))
  have he (i : Bond n) : inner ℝ (pulled a s (pole i)) (pulled a s (pole i))=w (F i) := by
    unfold pulled pole
    have hh : axisEquiv.symm (coord i.2)=i.2 := axisEquiv.symm_apply_apply _
    simp only [hh]; split <;> first | rfl | rw [inner_neg_left,inner_neg_right,neg_neg]; rfl
  unfold test; simp_rw [he,Equiv.sum_comp]; exact Equiv.sum_comp L (fun i => inner ℝ (a i) (a i))

section Joint
variable (T : Tube G S) (F : Forest S.ratio) (k : S.Choices) {J : Bed}

/-- The true tangent relative to copied V with every tree held. -/
def low (v : Dir G c) : Dir G f := stretch (S:=S) F (v,relative F (installed S.ratio T.R.A0) v)
def rest (v : Dir G c) := v-bills S (low T F v)

lemma full_cost (h : Towers.Diagonal S H J T.R) (v : Dir G c) :
    let x := low T F v
    gaugeFiscal H x x+S.kernel.penalty*test (rest T F v)=gaugeFiscal J v v := by
  intro x
  let Y:=extracted S F (installed S.ratio T.R.A0)
  let U:=1-probe S*Y
  have hi := Precision.action F (installed S.ratio T.R.A0) (H.metric.acts f) (J.metric.acts c) h.trial
  simp only at hi
  have he (i : G.ColorIndex) : parts G 1 x i=Y *ᵥ parts G 1 v i := Work.F04.parts_stretch F (installed S.ratio T.R.A0) v i
  have ht (i : G.ColorIndex) : parts G 1 (rest T F v) i=U *ᵥ parts G 1 v i := by
    change parts G 1 v i - (probe S)*ᵥ parts G 1 x i=_
    rw [he,Matrix.mulVec_mulVec,Matrix.sub_mulVec,Matrix.one_mulVec]
  rw [test,Work.F04.counting_inner,gaugeFiscal,gaugeFiscal, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  let q:=parts G 1 v i
  have hx {m n : Type} [Fintype m] [Fintype n] (A : Matrix m n ℝ) (x : m→ℝ) (u : n→ℝ) :
      dotProduct (A*ᵥ u) x=dotProduct u (A.transpose*ᵥ x) := by rw [dotProduct_transpose_mulVec,dotProduct_comm]
  rw [he,ht,hx Y,hx U, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [← hi,Matrix.add_mulVec,dotProduct_add,Matrix.smul_mulVec,dotProduct_smul]; rfl

include k
lemma staged_cost (hs : S.patch.Branches S.kernel G) (h : Towers.Diagonal S H J T.R)
    (v : Dir G c) (hH : Attached H T.up) (hp : T.up.Bounds T.high σ C Λ) (hp' : Floor H T.high f a b) (hb : Sworn H f G) :
    let x:=pulled (low T F v) s
    test (xLin T.high T.up x)+test (zLin S x (pulled v s))=gaugeFiscal J v v := by
  intro x
  rw [firstX x hH hp hp',hb s]
  have hx (B : Bond c) : zLin S x (pulled v s) B=Real.sqrt S.kernel.penalty • pulled (rest T F v) s (pole B) := by
    change _ • ((pulled v s) (pole B)-(bills S x) (pole B))=_ • _
    rw [Flat.bills_signed S s k _ _ hs]; unfold pulled rest; dsimp only; split; congr 1; simp only [Pi.sub_apply]; abel
    rfl
  rw [show zLin S x (pulled v s)=fun B=>_ from funext hx]
  conv_lhs => rhs; rw [test]
  simp_rw [real_inner_smul_left,real_inner_smul_right,← mul_assoc,Real.mul_self_sqrt S.kernel.penalty_pos.le,← Finset.mul_sum]
  exact Eq.trans (congr_arg (fun b => _+ S.kernel.penalty*b) (pulled_test s (rest T F v))) (full_cost T F h v)

-- E equation on all rows within channel

theorem uncut (hs : S.patch.Branches S.kernel G) (hd : Towers.Diagonal S H J T.R) (hr : Towers.Roll S H J T.R T.high T.low) (v : Dir G c)
    (hH : Attached H T.up) (hp : T.up.Bounds T.high σ C Λ) (hp' : Floor H T.high f a b) (hb : Sworn H f G)
    {τ E t d b' : ℝ} (hC : Attached J T.down) (hc : T.down.Bounds T.low τ E t) (he : Floor J T.low c d b') (hJ : Sworn J c G) :
    let x:=pulled (low T F v) s; let V:=pulled v s
    let q:=xLin T.low T.down V
    xLin T.high T.up x=zip (flatF T) q ∧ zLin S x V=zip (flatI T) q ∧ zip (flatN T) q=0 := by
  intro x V q
  let a := xLin T.high T.up x; let b := zLin S x V
  let Y:=zip (flatF T) q; let Z:=zip (flatI T) q; let N:=zip (flatN T) q
  have hu := (firstX V hC hc he).trans (hJ s v v)
  change test q=_ at hu
  have h₁ : test a+test b=test q := (staged_cost s T F k hs hd v hH hp hp' hb).trans hu.symm
  let bill {i : Type} [Fintype i] (x y : i→G.Color) := ∑ i, inner ℝ (x i) (y i)
  have are {i j : Type} [Fintype i] [Fintype j] (P : i→j→Pay G) (t u) : bill (zip P u) t=bill u (unzip P t) := Pressure.arity _ _ _
  have plus {i : Type} [Fintype i] (x y z : i→G.Color) : bill x y+bill x z=bill x (y+z) := by unfold bill; simp only [Pi.add_apply,inner_add_right, Finset.sum_add_distrib]
  have h : test Y+test Z+test N=test q := by
    change bill Y Y+bill Z Z+bill N N=_
    rw [show bill Y Y=_ from are _ Y q, show bill Z Z=_ from are _ Z q,show bill N N=_ from are _ N q,plus,plus,
      show unzip _ Y+unzip _ Z+unzip _ N=q from funext fun i=> (sub_eq_zero.mp (roll_d T hr q i)).symm]; rfl
  have ht : bill Y a+bill Z b=test q := by rw [show bill Y a=_ from are _ a q,show bill Z b=_ from are _ b q,plus,
    show unzip (flatF T) a+unzip (flatI T) b=q from funext fun i => sub_eq_zero.mp (roll_l T hr hp hc hH hC x V i)]; rfl
  have hb {i : Type} [Fintype i] (x y : i→G.Color) : test (x-y)=test x+test y-(bill y x+bill y x) := by
    unfold test bill; simp_rw [Pi.sub_apply,inner_sub_left,inner_sub_right,real_inner_comm (x _) (y _),Finset.sum_sub_distrib]; ring
  have hh : test (a-Y)+test (b-Z)+test N=0 := by rw [hb, hb]; linarith
  have he:= test_neutral (a-Y); have hf:=test_neutral (b-Z); have hm:=test_neutral N
  exact ⟨sub_eq_zero.mp (test_eq_zero _ (by linarith)), sub_eq_zero.mp (test_eq_zero _ (by linarith)),test_eq_zero N (by linarith)⟩
end Joint
end YM.AnalyticBridge.LocalGaussianLaws.Lift
