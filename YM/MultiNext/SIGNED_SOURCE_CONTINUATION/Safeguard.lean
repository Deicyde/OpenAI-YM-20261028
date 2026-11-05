import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Ac.Table
import YM.Bid.Drops
import YM.Bid.Fuels
import YM.Next.FLUCTUATIONS.Charts
import YM.Next.FREE_KERNELS.Signal
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.B04



set_option warningAsError false

/-!
# Pay derivatives & true Healthy along leading S arc on small supports

Quantitative supplement to JHs. Need `dColor` comparison on the supps,
all plaquette touched positions. Only by already supplying exponential
buffered estimate from the patch covariance threshold comparison (e.g.
with .stays using `Forecast.foresail`). Receipt absorptions: one numerical
delay needs at EACH clock index including caller knowing L and stage at that
step (don't infer from slow), and no claim those & the OTHER costs have been
bought jointly. -/
set_option autoImplicit false
noncomputable section
namespace YM.MultiNext.SignedSource.Flair
open Function Filter Finset Lattice Wilson RG Labels Laurent Bloch Exterior Matrix Set Precision
open    Next.Free   Next.Fluctuations
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {c n : Side} {G : Gauge} {P : BudgetPoint} {U : Directions G n}

private abbrev Panel (G : Gauge) := Fin 4 → G.Color
private def dial (x : Panel G) := G.lieExp (x 0)*G.lieExp (x 1)*(G.lieExp (x 2))⁻¹*(G.lieExp (x 3))⁻¹
private def answer (x : Panel G) := x 0+x 1-x 2-x 3

private lemma paid (G : Gauge) : ∃ C r : ℝ,0<C ∧ 0<r ∧ ∀ v : Panel G,‖v‖ ≤ r →
    G.chord (dial v) ≤ ‖answer v‖+C*‖v‖^2 := by
  let f := G.mat ∘ (dial (G:=G))
  have he (i : Fin 4) : ContDiff ℝ ω (fun x : Panel G => G.mat (G.lieExp (x i))) := G.exp_jet.comp (contDiff_apply ℝ _ i)
  have hf : ContDiff ℝ ω f := by
    simp only [f]
    exact (((he 0).mul (he 1)).mul (((starL ℝ:G.Mat≃L[ℝ]G.Mat).contDiff).comp (he 2))).mul (((starL ℝ:G.Mat≃L[ℝ]G.Mat).contDiff).comp (he 3))
  have hx v : HasDerivAt (fun t : ℝ => f (t • v)) (G.colorMat (answer v)) 0 := by
    have hv (i) : HasDerivAt (fun t : ℝ => G.mat (G.lieExp (t • v i))) (G.colorMat (v i)) 0 := G.expDiff_zero.comp_hasDerivAt_of_eq (0:ℝ)
      (show HasDerivAt (fun t : ℝ => t • v i) (v i) 0 from by simpa using (hasDerivAt_id' (0:ℝ)).smul_const (v i)) (by simp)
    simp only [f,dial,Function.comp,G.mat_mul,G.mat_inv,Pi.smul_apply]
    apply ((((hv 0).mul (hv 1)).mul (hv 2).star).mul (hv 3).star).congr_deriv
    unfold answer; simp only [Pi.mul_apply,zero_smul,G.mat_lieExp_zero,G.mat_one,star_one,
      mul_one,one_mul,G.colorMat_skew,map_sub,map_add]
    abel
  obtain ⟨D,r,hD,hr,h⟩:= chart_quadratic_cost f _ hf.contDiffAt.analyticAt hx
  refine ⟨D/G.colorScale, r,div_pos hD G.colorScale_pos,hr,fun x he => ?_⟩
  apply le_of_mul_le_mul_left _ G.colorScale_pos
  rw [chord_dist,mul_add, ← mul_assoc G.colorScale, show G.colorScale*(D/G.colorScale)=D by field_simp [G.colorScale_pos.ne']]
  have hf : f 0=1 := by simp [f,dial]
  obtain hx := (h x).2 he; rw [hf] at hx
  have hc := G.colorMat_norm (answer x)
  have hh := norm_add_le (f x-(1+G.colorMat (answer x))) (G.colorMat (answer x))
  rw [show f x-(1+G.colorMat (answer x))+G.colorMat (answer x)= f x-1 from by abel, hc] at hh
  exact hh.trans ((add_le_add_left hx _).trans_eq (add_comm ..))

private def quadruple (p : Face (Per n)) : Fin 4 → Edge (Site n) := let a:=p.2.val.1; let b:=p.2.val.2
    ![(p.1,a),(p.1+Lattice.step a,b),(p.1+Lattice.step b,a),(p.1,b)]



private lemma nearby (p : Face (Per n)) (i : Fin 4) (y : Site n) (h : y∈RG.touched p) : separation (quadruple p i).1 y ≤ 5 := by
  have h' (i : Axis) (x : Site n) : separation x (x+Lattice.step i) ≤ 1 := by rw [separation_comm]; unfold separation; rw [add_sub_cancel_left]; exact pdist_step _
  have he : separation p.1 y ≤ 2 := by
    have hh (i j : Axis) : p.1+step i+step j+ -step i=p.1+step j := by abel
    simp only [RG.touched,visits,square,Step.vec_pos,Step.vec_neg,hh,add_neg_cancel_right,List.toFinset_cons,List.toFinset_nil,
      Finset.mem_insert,Finset.notMem_empty, or_false] at h
    rcases h with h|h|h|h|h
    · simp only [h,separation_self,Nat.zero_le]
    · exact by rw [h]; exact le_trans (h' _ _) (by decide)
    · rw [h]; exact (separation_triangle _ (p.1+step p.2.val.1) _).trans (show _ ≤ 1+1 from Nat.add_le_add (h' _ _) (h' _ _))
    · exact by rw [h]; exact le_trans (h' _ _) (by decide)
    rw [h,separation_self]; decide
  apply (separation_triangle _ p.1 _).trans
  have hx : separation (quadruple p i).1 p.1 ≤ 1 := by
    rw [separation_comm]
    fin_cases i
    · exact (by change separation p.1 p.1 ≤ 1; simp only [separation_self,Nat.zero_le])
    · exact h' p.2.val.1 p.1
    · exact h' p.2.val.2 p.1
    change separation p.1 p.1 ≤ 1; rw [separation_self]; decide
  omega






end YM.MultiNext.SignedSource.Flair
namespace YM.MultiNext.SignedSource.Flair
open Function Filter Finset Lattice Wilson RG Labels Laurent Bloch Exterior Matrix Set Precision
open    Next.Free   Next.Fluctuations
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {c n : Side} {G : Gauge} {P : BudgetPoint} {U : Directions G n}

private lemma guitar {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] (g : E → F) (he : ContDiff ℝ ω g) :
    ∃ Q : ℝ,1 ≤ Q ∧ ∀ v : E,‖v‖ ≤ 1 → ∀ r ∈ Set.Icc (0:ℝ) 1,
      ‖g (r • v)-g 0‖ ≤ r*‖g v-g 0‖ + Q*(1-r)*‖v‖^2 := by
  let L := fderiv ℝ g
  have hl : ContDiff ℝ ω L := he.fderiv_right le_top
  let f (x : E) := ‖fderiv ℝ L x‖
  obtain ⟨C,h⟩:= (isCompact_closedBall (0:E) 1).bddAbove_image (f:=f) (hl.continuous_fderiv (by simp)|>.norm.continuousOn)
  let C' := 1+|C|; have hC : 1 ≤ C' := le_add_of_nonneg_right (abs_nonneg _)
  refine ⟨2*C',by linarith,fun v hv r hr => ?_⟩
  have hh (y : E) := (convex_closedBall (0:E) 1).norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ) (y:=y) (fun x _ => hl.differentiable (by simp) x)
    (C:=C') (fun x hx => (h (Set.mem_image_of_mem f hx)).trans (show C ≤ C' from (le_abs_self C).trans (le_add_of_nonneg_left zero_le_one))) (show 0∈Metric.closedBall (0:E) 1 by simp)
  let a (x : E) := g x - g 0 - L 0 x
  have hq (x : E) : HasFDerivAt a (L x-L 0) x := by
    exact (((he.differentiable (by simp) x).hasFDerivAt.sub_const (g 0)).sub (L 0).hasFDerivAt)
  have hx : v∈Metric.closedBall (0:E) ‖v‖ := by simp
  have hy : r • v∈ Metric.closedBall (0:E) ‖v‖ := by simpa [norm_smul,abs_of_nonneg hr.1] using mul_le_of_le_one_left (norm_nonneg v) hr.2
  have hz : (0:E)∈Metric.closedBall (0:E) ‖v‖ := by simp
  have hW (x y : E) := (convex_closedBall (0:E) ‖v‖).norm_image_sub_le_of_norm_fderiv_le (C:=C'*‖v‖) (x:=x) (y:=y) (𝕜:=ℝ) (fun x _ => (hq x).differentiableAt) (fun x hi => by
    have he := (hh _ (Metric.closedBall_subset_closedBall hv hi))
    rw [sub_zero] at he; rw [(hq x).fderiv]
    exact he.trans (mul_le_mul_of_nonneg_left (by simpa using hi) (zero_le_one.trans hC)))
  have Hp : ‖a v‖ ≤ C'*‖v‖^2 := by have he := hW _ _ hz hx; simpa [a,sq,mul_assoc] using he
  have hi := hW _ _ hx hy
  rw [show r • v-v=(r-1) • v by simp [sub_smul], norm_smul,Real.norm_eq_abs,abs_of_nonpos (by linarith [hr.2]),neg_sub] at hi
  calc
    _ = ‖r • (g v-g 0)+(a (r • v)-a v+(1-r) • a v)‖ := by
      unfold a; rw [map_smul]; simp only [one_smul,smul_sub,sub_smul]; congr 1; abel
    _ ≤ r*‖g v-g 0‖ + (‖a (r • v)-a v‖ + (1-r)*‖a v‖) := by
      apply (norm_add_le ..).trans
      apply add_le_add _ ((norm_add_le ..).trans _)
      · rw [norm_smul,Real.norm_of_nonneg hr.1]
      rw [norm_smul,Real.norm_of_nonneg (show 0≤1-r by linarith only [hr.2])]
    _ ≤ _ := by nlinarith only [hi,mul_le_mul_of_nonneg_left Hp (show 0 ≤ 1-r by linarith only [hr.2])]

/-- Radial *random endpoint* from its ACTUAL chord test, with no
sharper threshold at endpoint or Sobolev estimate for the noise curl.
Pays constant on that same gauge at 4 links only. -/
lemma strings (G : Gauge) : ∃ C : ℝ,0<C ∧ ∀ (n : Side) (Y : Support n) (τ b : ℝ) (v : Directions G n),
    b ≤1 → 0 ≤ b → C*b^2 ≤ τ → (∀ (x : Edge (Site n)), (∃ z∈Y,separation x.1 z ≤ 5) → ‖v x‖ ≤ b) → Healthy τ Y (increment 1 v) →
    ∀ s ∈ Set.Icc (0:ℝ) 1,Healthy τ Y (increment 1 (s • v)) := by
  have he (i : Fin 4) : ContDiff ℝ ω (fun x : Panel G => G.mat (G.lieExp (x i))) := G.exp_jet.comp (contDiff_apply ℝ _ i)
  let f := G.mat ∘ (dial (G:=G))
  have hf : ContDiff ℝ ω f := by
    simp only [f]; exact (((he 0).mul (he 1)).mul (((starL ℝ:G.Mat≃L[ℝ]G.Mat).contDiff).comp (he 2))).mul (((starL ℝ:G.Mat≃L[ℝ]G.Mat).contDiff).comp (he 3))
  letI : ProperSpace (Panel G) := FiniteDimensional.proper ℝ _
  obtain ⟨C,hC,H⟩:=guitar f hf
  refine ⟨C/G.colorScale, div_pos (zero_lt_one.trans_le hC) G.colorScale_pos,fun n Y τ b v hb he ht hy hh s hs => Finset.disjoint_left.mpr ?_⟩
  intro i hi hI
  obtain ⟨y,hx,h⟩ := (flags_spec ..).mp hI
  have hq : G.chord (faceValue (increment 1 v) y) ≤ τ := not_lt.mp (fun h => Finset.disjoint_left.mp hh hi ((flags_spec ..).mpr ⟨y,hx,h⟩))
  have hv (u : Directions G n) : dial (fun i => u (quadruple y i)) = faceValue (increment 1 u) y := by
    have h (x : Site n) (i j : Axis) : x+step i+step j-step i=x+step j := by abel
    have H (x : Site n) (i j : Axis) : x+step i+step j+ -step i=x+step j := by abel
    simp [increment,dial,quadruple,faceValue,square,travel,Step.vec_pos,Step.vec_neg,Step.pos_read,Step.neg_read,h,H,add_sub_cancel_right,mul_assoc]
  let U := fun i => v (quadruple y i)
  have hF : ‖U‖ ≤ b := (pi_norm_le_iff_of_nonneg he).mpr (fun j => hy _ ⟨i,hi,nearby y j i hx⟩)
  have he' := H _ (hF.trans hb) s hs
  have hG : f 0=1 := by simp [f,dial]
  rw [← hv] at h hq
  rw [hG] at he'
  have hA := G.colorScale_pos
  unfold f at he'; rw [Function.comp_apply,Function.comp_apply, ← chord_dist,← chord_dist] at he'
  change τ < G.chord (dial (s • U)) at h
  change G.chord (dial U) ≤ τ at hq
  have ht := ht; field_simp at ht
  have hV := mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hF 2) (zero_le_one.trans hC)).trans ht) (show 0 ≤ 1-s by linarith only [hs.2])
  nlinarith only [he',hV,mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq hA.le) hs.1, mul_lt_mul_of_pos_left h hA]
end YM.MultiNext.SignedSource.Flair
