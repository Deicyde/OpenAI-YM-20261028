import YM.WilsonBulk.Slice.Print
import YM.WilsonBulk.Trees.Predictor
import YM.Work.F05.Reindex

/-!
# K.k contact to independent finite-coordinate step

Compass κ, unit conventions unchanged. Use absolute log and mean
(compatible every index basis) to shift. Seed Scripts obtains all Cradle
shapes, caller must give actual `Scripts` and `LocalRatio`. Branch noise
uses *all* likelihood, but predictors analytic/constant theta-independent
near the formal branch; later shown. These claims do not calculate a bare
sector integral.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
namespace Atelier
open Lattice Laurent Function Bloch RG Precision Exterior Stationary FreeResolvent
open scoped Classical Topology BigOperators Matrix
open Sheet Matrix
variable {c f n : Side} {P : Patch} {G : Gauge} {S : StepData c f} {p : ℝ}
variable (G)
abbrev Pennant (n : Side) := FreeResolvent.Slot G n 1
abbrev Logbook (n : Side) := Tape (Pennant G n)
-- canonical data from Bed metrics
def matrixK (n : Side) (P : Bed) : Matrix (Pennant G n) (Pennant G n) ℝ := patron G (Precision.K (P.metric.acts n))
abbrev Ticket (x : ℝ) (n : Side) (P : Bed) := (P.metric.acts n).IsSymm ∧ Gap (P.metric.acts n) x
omit G in
lemma floor_qual {P : Bed} {p : Clip} {σ C : ℝ} {n : Side} (hf : Floor P p n σ C) : Ticket σ n P := ⟨hf.symmetric.1,⟨fun v=> (hf.uniform.1 v).1⟩⟩

def probeX (S : StepData c f) : Matrix (Pennant G c) (Pennant G f) ℝ := patron G (probe S)
def regionJ (F : Tree.Forest S.ratio) (P : Bed) : Matrix (Pennant G f) (Pennant G f) ℝ := covariance G S F P.metric
def predictor (F : Tree.Forest S.ratio) (P : Bed) := S.kernel.penalty • (regionJ G F P*(probeX G S).transpose)

structure Coursing (ι : Type) (S : StepData c f) where
  tree : Tree.Forest S.ratio
  label : ι ≃ tree.Free

namespace Coursing
variable {ι : Type} (F : Coursing ι S)
abbrev LegsT (ι : Type) := ι × G.ColorIndex
def flag : LegsT G ι ≃ Active G F.tree := Equiv.prodCongr F.label (Equiv.refl _)
abbrev dock := plant F.tree ∘ flag G F
def trunk : Matrix (Pennant G f) (LegsT G ι) ℝ := insertion (dock G F)
def isolate (P : Bed) := (treeInverse G S F.tree P.metric 0).submatrix (F.flag G) (F.flag G)
def gravity (P : Bed) := (treeMatrix G S F.tree P.metric).submatrix (F.flag G) (F.flag G)

lemma trunk_past : F.trunk G=(insertion (plant F.tree)).submatrix id (F.flag G) := rfl
lemma trunk_formula (P : Bed) : (trunk G F).transpose*fullMatrix G S P.metric*trunk G F=gravity G F P := insertion.compress (F.dock G) _
variable [Fintype ι]
lemma region_project (P : Bed) : trunk G F*isolate G F P*(trunk G F).transpose=regionJ G F.tree P := by
  rw [trunk_past, isolate, submatrix_mul_equiv,transpose_submatrix,submatrix_mul_equiv]; rfl
omit [Fintype ι] in
lemma confines (P : Bed) (h : Ticket p f P) : (gravity G F P).IsSymm := by rw [gravity,treeMatrix,Matrix.IsSymm, transpose_submatrix,transpose_submatrix,full_symmetric P.metric h.1]
omit [Fintype ι] in
lemma short_law (P : Bed) (h : Ticket p f P) : (isolate G F P).IsSymm := by
  unfold Matrix.IsSymm isolate treeInverse resolve; rw [transpose_submatrix]; refine congrArg (fun x=>Matrix.submatrix x _ _) ?_; rw [Matrix.transpose_nonsing_inv]; simp only [treeMatrix,transpose_add,transpose_smul,transpose_one,transpose_submatrix, full_symmetric P.metric h.1]
lemma prepared [DecidableEq ι] (hl : Bid.Larger (G:=G) S) (hp : 0<p) (P : Bed) (h : Ticket p f P) : gravity G F P * isolate G F P=1 := by
  unfold gravity isolate; rw [submatrix_mul_equiv,show treeMatrix G S F.tree P.metric*treeInverse G S F.tree P.metric 0=1 from by simpa using (tree_laws F.tree _ hl hp h.2 (u:=0) le_rfl).2]; exact submatrix_one_equiv _
lemma sticking (P : Bed) :
    let q := trunk G F; q*q.transpose*predictor G F.tree P=predictor G F.tree P := by
  intro q; unfold predictor; rw [Matrix.mul_smul, ← F.region_project G]; simp_rw [Matrix.mul_assoc]; congr 1
  rw [← Matrix.mul_assoc (trunk G F).transpose, show (trunk G F).transpose*trunk G F=1 from insertion.orthogonal (F.dock G) ((plant_inj F.tree).comp (flag G F).injective),Matrix.one_mul] -- check
end Coursing

def Consoles (B D : Bed) (S : StepData c f) := ∃ W : Matrix (Body 1 f) (Body 1 c) ℝ, Precision.Inputs S W (B.metric.acts f) (D.metric.acts c)
abbrev glimmer (ι : Type) (P : Bed) (F : Coursing ι S) (M N : StageD (Pennant G f) (Pennant G c)) (R : Tape (Pennant G c)) :=
    Scripts (predictor G F.tree P) (regionJ G F.tree P) (matrixK G f P) (probeX G S) S.kernel.penalty M N R
lemma patron_minus {r t} (P Q : Matrix (Body r c) (Body t n) ℝ) : patron G (P-Q)=patron G P-patron G Q := by rw [sub_eq_add_neg, show -Q = (-1:ℝ) • Q by simp, patron_plus, patron_weight]; simp [sub_eq_add_neg]
lemma patron_life (f : Side) (r : ℕ) : patron G (1:Matrix (Body r f) (Body r f) ℝ)=1 := by rw [match_tensor]; apply matSeen; intro v; ext1 ⟨x,i,j⟩; exact Eq.trans (show component (tensor G 1*ᵥ v) j (x,i)=v (x,i,j) by rw [component_mul,one_mulVec]; rfl) (by rw [one_mulVec])
lemma recipe {ι δ : Type} [Fintype ι] [Fintype δ] {P Q : Bed} {F : Coursing ι S}
    (h : Ticket p f P) (hp : 0<p) (hs : Bid.Larger (G:=G) S) (he : Consoles P Q S)
    (u : Pennant G c → Tape δ) {M N : StageD (Pennant G f) (Pennant G c)} {R : Tape (Pennant G c)} (hz : glimmer G ι P F M N R) :
    let U := submit (seating (predictor G F.tree P) (F.trunk G) u)
    Cradle (F.gravity G P) (F.isolate G P) (U M) (U N) (U (curtain (matrixK G f P) (probeX G S) S.kernel.penalty M N)) (submit u (grains (matrixK G c Q))) (submit u R) := by
  intro U
  obtain ⟨W,hW⟩:= he -- remove
  have hf : predictor G F.tree P=patron G (extracted S F.tree W) := (beams_exact G P Q _ W hW hs hp h.2).symm
  refine Scripts.present _ _ u _ hz (F.region_project G P) (wired_full G S P).symm (F.trunk_formula G P) (full_symmetric P.metric h.1) ?_ ?_
  · rw [hf]; exact holo G P Q F.tree W hW
  rw [hf, probeX,← patron_mul, (stationed F.tree W _ _ hW).1, patron_minus, patron_life, patron_weight]; rw [sub_sub_cancel, smul_smul, mul_inv_cancel₀ S.kernel.penalty_pos.ne',one_smul]; rfl
end Atelier
end YM.WilsonBulk
