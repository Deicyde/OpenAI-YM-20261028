import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Ac.Table
import YM.Analysis.Polydisc
import YM.Bid.Drops
import YM.Bid.Fuels
import YM.Pressure.Seeds
import YM.Work.A05.Read
import YM.Work.A07


/-!
# What might go wrong with volume/depth-independent division

On the *actual* nonabelian group. Prune to one orientation and alternate
layers; all the selected plaquettes have their own pivot edge, so we can
pay a vanishing strict fraction per site. Gives a concrete obstruction
to strengthening  to omit the vacuum scalar (or bounding v at
fixed m over finer depths). Requires only two dividing side; n=1, ties
etc aren't extrapolated. Also gives cost at any β in Wilson.Law before
shooting. No asymptotic coefficient or thermodynamic assertion needed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Vacuum
open RG Precision Wilson Lattice MeasureTheory Filter Set Function 
open scoped Matrix.Norms.Frobenius BigOperators Classical Topology ENNReal
variable (G : Gauge) {n : Side}



def mouth (β : ℝ) (g : G.El) := Real.exp (-β*G.price g)
def linkZ (β : ℝ) := ∫ u,mouth G β u ∂G.probHaar

@[fun_prop] lemma mouth_cont (β : ℝ) : Continuous (mouth G β) := by unfold mouth; fun_prop
lemma mouth_int (β : ℝ) : Integrable (mouth G β) G.probHaar := (mouth_cont G _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
lemma mouth_pos (β : ℝ) (g : G.El) : 0 < mouth G β g := Real.exp_pos _




private abbrev stripe (n : Side) := Edge (Site n)
private def retained {n : Side} (h : 2 ∣ n.val) (e : stripe n) :=
  e.2=0 ∧ ZMod.castHom h (ZMod 2) (e.1 1) = 0
private abbrev Pivot {n : Side} (h : 2 ∣ n.val) := {e : stripe n // retained h e}
private abbrev Other {n : Side} (h : 2 ∣ n.val) := {e : stripe n // ¬retained h e}




private def orient : PlaqAxes := ⟨(0,1),by decide⟩
private def pane {n : Side} (i : Site n) : Face (Per n) := (i,orient)
private lemma square_explicit (U : Config G n) (i : Site n) :
    faceValue U (pane i) = U (i,0)*(U (i+step 0,1)*((U (i+step 1,0))⁻¹*(U (i,1))⁻¹)) := by
  simp only [faceValue,pane,orient,square,travel,Step.pos_read,Step.neg_read,Step.vec_pos,Step.vec_neg,mul_one]
  congr 4 <;> abel_nf

private lemma rail₁ {h : 2∣n.val} (j : Site n) : ¬retained h (j,(1:Axis)) := by
  intro hj; exact (by decide : (1:Axis) ≠ 0) hj.1
private lemma rail₀ {h : 2∣n.val} (i : Pivot h) : ¬retained h (i.1.1+step 1,0) := by
  intro hi
  have he := hi.2
  simp only [Pi.add_apply,step_apply,if_pos,map_add,i.property.2,map_one,zero_add] at he
  exact one_ne_zero he

private def railQ {h : 2∣n.val} (i : Pivot h) (a : Other h → G.El) : G.El :=
  a ⟨(i.1.1+step 0,1),rail₁ _⟩ * ((a ⟨(i.1.1+step 1,0), rail₀ i⟩)⁻¹ * (a ⟨(i.1.1,1), rail₁ _⟩)⁻¹)

private def chartWays (h : 2∣n.val) := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : stripe n => G.El) (retained h)

private lemma split_face {h : 2∣n.val} (i : Pivot h) (a : Pivot h → G.El) (b : Other h → G.El) :
    faceValue ((chartWays G h).symm (a,b)) (pane i.val.1) = a i * railQ G i b := by
  let V := (chartWays G h).symm (a,b)
  have hf (i : Pivot h) : V i = a i := congr_fun (congr_arg Prod.fst ((chartWays G h).apply_symm_apply (a,b))) i
  have hh (i : Other h) : V i = b i := congr_fun (congr_arg Prod.snd ((chartWays G h).apply_symm_apply (a,b))) i
  unfold railQ
  rw [square_explicit]
  congr 2
  · change V (i.val.1,0) = a i
    rw [← i.property.1,Prod.mk.eta]; exact hf i
  · exact hh ⟨(_,1),rail₁ (h:=h) (i.val.1+step 0)⟩
  congr 2
  · exact hh ⟨(_,0),rail₀ i⟩
  exact hh ⟨(_,1),rail₁ (h:=h) i.val.1⟩


private def skeleton (h : 2 ∣ n.val) (β : ℝ) (U : Config G n) := ∏ i : Pivot h,mouth G β (faceValue U (pane i.val.1))
@[fun_prop] private lemma cont_skeleton (h : 2 ∣ n.val) (β : ℝ) : Continuous (skeleton G h β) := by
  unfold skeleton faceValue; fun_prop



private theorem paid (h : 2∣n.val) (β : ℝ) :
    (∫ U,skeleton G h β U ∂prior G n) = linkZ G β ^ Fintype.card (Pivot h) := by
  let P : Measure (Pivot h → G.El) := Measure.pi (fun _ => G.probHaar)
  let O : Measure (Other h → G.El) := Measure.pi (fun _ => G.probHaar)
  letI : IsProbabilityMeasure P := by unfold P; infer_instance
  letI : IsProbabilityMeasure O := by unfold O; infer_instance
  let T := chartWays G h
  have he : MeasurePreserving T (prior G n) (P.prod O) := measurePreserving_piEquivPiSubtypeProd (fun _ : stripe n => G.probHaar) _
  let X := skeleton G h β ∘ T.symm
  have hh : Integrable X (P.prod O) := (he.symm.integrable_comp_emb T.symm.measurableEmbedding).mpr
    ((cont_skeleton G h β).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  rw [← he.symm.integral_comp T.symm.measurableEmbedding (skeleton G h β)]
  change (∫ i,X i ∂P.prod O)=_
  rw [integral_prod_symm _ hh]
  have hm (b : Other h → G.El) (i : Pivot h) : (∫ v, mouth G β (v * railQ G i b) ∂G.probHaar)=linkZ G β :=
    (measurePreserving_mul_right G.probHaar (railQ G i b)).integral_comp
      ((Homeomorph.mulRight (railQ G i b)).measurableEmbedding) (mouth G β)
  have hp (b : Other h → G.El) : (∫ a, skeleton G h β (T.symm (a,b)) ∂P) = linkZ G β ^ Fintype.card (Pivot h) := by
    unfold skeleton T; simp_rw [split_face]
    unfold P; rw [integral_fintype_prod_eq_prod (fun i v => mouth G β (v*railQ G i b))]
    simp_rw [hm b]; simp
  unfold X; simp_rw [Function.comp_apply,hp]; simp









end YM.SectorNext.Vacuum
