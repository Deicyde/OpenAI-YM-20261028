import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Data.Set.Finite.List
import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Inverse
import YM.Next.BOUNDARY.Coordinates
import YM.Next.FREE_KERNELS.Amend
import YM.Next.ROTATIONS.Response
import YM.Next.SCHEDULE.Blocks
import YM.Next.SCHEDULE.GridCost
import YM.Push.CUTOFF_PROJECTORS.Along
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Author
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Remainder



/-!
# Smoothness input on true sector precision at fixed decision data

Using `Authorized` where noise is actually differentiated and the PathData
row sums; no need to assume a realization by fine links. Keep the specified
finite cuts (not necessarily finite sums over labels!); first combine by
absolute summability at matching slots. Does not estimate these jets, or
differentiate `A.flags`, `shots`, any frozen-set decisions, etc.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SelectedOrderedKernels.Sector
open Lattice Wilson RG Function Filter WardBin.Lies Precision Tree Next.SectorChange
  Next.SectorChange.Motion Next.Fluctuations Rows YM.Pressure YM.Pressure.Stores
  YM.Push.SectorMeasure.Oriented
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G : Gauge} {c f m : Side} {S : StepData c f} {V : Config G c} {U : Config G m} {q : ℕ∞ω}
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {F : X → Config G m} {w : X}
section group
lemma read_smooth (d : Step) (i : Site m) (h : ∀ e, ContDiffAt ℝ q (fun x => G.mat (F x e)) w) :
    ContDiffAt ℝ q (fun x => G.mat (d.read (F x) i)) w := by
  unfold Step.read; split
  · simp only [G.mat_inv]; exact (starL ℝ : G.Mat ≃L[ℝ] G.Mat).contDiff.contDiffAt.comp _ (h _)
  exact h _

lemma travel_smooth (i : Site m) (l : Walk) (h : ∀ e, ContDiffAt ℝ q (fun x => G.mat (F x e)) w) :
    ContDiffAt ℝ q (fun x => G.mat (travel (F x) i l)) w := by
  induction l generalizing i with
  | nil => exact contDiffAt_const
  | cons d l ih => simp only [travel,G.mat_mul]; exact (read_smooth _ _ h).mul (ih _)

lemma curve_smooth (H : X → G.El) (h : ContDiffAt ℝ q (fun x => G.mat (H x)) w) :
    ContDiffAt ℝ q (fun x => G.curvature (H x)) w := by
  have he := (starL ℝ : G.Mat ≃L[ℝ] G.Mat).contDiff.contDiffAt.comp _ h
  exact G.projectColor.toContinuousLinearMap.contDiff.contDiffAt.comp _ ((h.sub he).const_smul (1/2:ℝ))

lemma ad_smooth (H : X → G.El) (h : ContDiffAt ℝ q (fun x => G.mat (H x)) w) {B : X → G.Color} (hB : ContDiffAt ℝ q B w) :
    ContDiffAt ℝ q (fun x => G.adjoint (H x) (B x)) w := by
  have he := (starL ℝ : G.Mat ≃L[ℝ] G.Mat).contDiff.contDiffAt.comp _ h
  exact G.projectColor.toContinuousLinearMap.contDiff.contDiffAt.comp _
    ((h.mul (G.colorMat.toContinuousLinearMap.contDiff.contDiffAt.comp _ hB)).mul he)

variable (s : Signed)
abbrev both (G : Gauge) (c f : Side) := Directions G c × Directions G f

def joint (s : Signed) (V : Config G c) (b : both G c f) := facade S s (increment V b.1) b.2

lemma joint_smooth (e : Bond f) : ContDiffAt ℝ q (fun b : both G c f => G.mat (joint (S:=S) s V b e)) 0 := by
  apply read_smooth; intro i; unfold increment; simp_rw [G.mat_mul]
  apply ((G.exp_jet.of_le le_top).contDiffAt.comp (f:=fun b : both G c f => b.2 i) 0
    ((contDiff_apply ℝ G.Color i).contDiffAt.comp 0 contDiffAt_snd)).mul
  unfold replica; split
  · exact contDiffAt_const
  simp only [G.mat_mul]
  exact ((G.exp_jet.of_le le_top).contDiffAt.comp (f:=fun b : both G c f => b.1 _) 0
    ((contDiff_apply ℝ G.Color _).contDiffAt.comp 0 contDiffAt_fst)).mul contDiffAt_const

lemma zero_joint : joint (S:=S) s V 0 = pull s 0 (replica S.ratio V) := by unfold joint facade; rw [Prod.fst_zero,Prod.snd_zero,Motion.increment_zero,Motion.increment_zero]
lemma plaquette_smooth (a : Directions G f) (p : Cell f) :
    ContDiffAt ℝ q (fun b => plaquetteJet S (increment V b) s p a) 0 := by
  have hp : ContDiffAt ℝ ω (fun b : both G c f => G.curvature (faceValue (joint (S:=S) s V b) p)) 0 := curve_smooth _ (travel_smooth _ _ (joint_smooth s))
  exact (hp.fderiv (f:=fun b z => sourceFace (S:=S) (increment V b) s p z) (g:=fun _ => 0) (m:=q) contDiffAt_const le_top).clm_apply contDiffAt_const

variable {A : Stores S} {x B : ℝ} {T : Forest S.ratio} {j : Bond c} {k : ℕ}
  (ha : Authorized A V T x B) (hs : curb (shots S x) A T x s (.inr j))
include ha hs

lemma prediction_smooth (t : S.Choices) : ContDiffAt ℝ k (fun b : both G c f => G.mat (predictGroup (increment V b.1) t s j b.2)) 0 := by
  let g := choice s t
  let K := pull s 0 (replica S.ratio V)
  let F (y : Config G f) := G.mat (S.prediction y g j)
  have he (a : Directions G f) : F (increment K a) = G.mat (Motion.out K g j a) * F K := by simp [F,Motion.out,mul_assoc]
  have hF : Germ k F K := by
    unfold WardBin.Lies.Germ; simp_rw [he]
    exact ((ha.noise s t j hs).1.of_le le_top).mul contDiffAt_const
  exact hF.curves (Z:=joint s V) (zero_joint _) (joint_smooth s)

lemma block_smooth (a : Directions G f) (k₀ : S.Choices) :
    ContDiffAt ℝ k (fun b => blockJet (increment V b) k₀ s j a) 0 := by
  let F(b : Directions G c) z := G.curvature (predictorTurn (increment V b) k₀ s j z)
  have hg := prediction_smooth (k:=k+1) s ha hs k₀
  have hh : ContDiffAt ℝ (↑(k+1):ℕ∞ω) (uncurry F) 0 := by
    apply curve_smooth
    simp_rw [predictorTurn,G.mat_mul,G.mat_inv]
    exact hg.mul ((starL ℝ : G.Mat ≃L[ℝ] G.Mat).contDiff.contDiffAt.comp _
      (hg.comp (f:=fun b : both G c f => (b.1,0)) 0 (contDiffAt_fst.prodMk contDiffAt_const)))
  exact (hh.fderiv (f:=F) (g:=fun _ => 0) (m:=k) contDiffAt_const (by push_cast; rfl)).clm_apply contDiffAt_const
end group

section barrel
private lemma cut_finite (r : ℕ) : {s : RG.Slot | s.length ≤ r}.Finite := by
  let _ : Finite Step := Finite.of_injective (fun t : Step => (t.dir,t.neg)) (by rintro ⟨_,_⟩ ⟨_,_⟩ h; simpa using h)
  apply ((List.finite_length_le Step r).prod (Set.finite_univ (α:=PlaqAxes))).preimage
    (show Injective (fun t : RG.Slot => (t.walk,t.plaq)) from by rintro ⟨_,_⟩ ⟨_,_⟩ h; simpa using h).injOn |>.subset
  exact fun t ht => ⟨(Nat.le_add_right _ _).trans ht, Set.mem_univ _⟩

private def toll (P : PathData G) (p : PlaqAxes) (r : RG.Slot) (i : ℕ) := if (P.row p i).2=r then (P.row p i).1 else 0

variable {P : PathData G} {σ M θ : ℝ} {o : Clip} (hP : P.Bounds o σ M θ)
include hP

lemma barrel_split (r : ℕ) (U : Config G f) (b : LogArray G (Cell f)) (p : Cell f) :
    barrel P r U b p = ∑ t ∈ (cut_finite r).toFinset, (∑' i, toll P p.2 t i) •
      G.adjoint (travel U p.1 t.walk) (b (YM.Work.F03.slotFace t p.1)) := by
  let F (t : RG.Slot) := G.adjoint (travel U p.1 t.walk) (b (YM.Work.F03.slotFace t p.1))
  have ht (t : RG.Slot) : Summable (toll P p.2 t) := Summable.of_norm_bounded (Work.F03.row_abs_summable P hP _) fun i => by
    unfold toll; split
    · rfl
    rw [norm_zero]; apply abs_nonneg
  simp_rw [← (ht _).tsum_smul_const]
  change _ = ∑ t ∈ (cut_finite r).toFinset, ∑' i, toll P p.2 t i • F t
  rw [barrel,← Summable.tsum_finsetSum (f:=fun t i => toll P p.2 t i • F t) (fun t _ => (ht t).smul_const (F t))]
  apply tsum_congr; intro i
  simp only [toll,ite_smul,zero_smul,Finset.sum_ite_eq,Set.Finite.mem_toFinset,Set.mem_setOf_eq]
  rfl

variable {b : X → LogArray G (Cell f)} {U : X → Config G f}
lemma barrel_smooth (r : ℕ) (p : Cell f) (h : ∀ e, ContDiffAt ℝ q (fun w => G.mat (U w e)) w)
    (hb : ∀ i, ContDiffAt ℝ q (fun w => b w i) w) : ContDiffAt ℝ q (fun w => barrel P r (U w) (b w) p) w := by
  simp_rw [barrel_split hP]
  exact ContDiffAt.sum (fun _ _ => (ad_smooth _ (travel_smooth _ _ h) (hb _)).const_smul _)
end barrel

variable {A : Stores S} {x B : ℝ} {q : ℕ} (H : Tube G S)
  {T : Forest S.ratio} {P : Teller G} (hP : P.Funds S H)
  (ha : Authorized A V T x B)
include hP ha
lemma move_smooth (k : S.Choices) : WardBin.Lies.Germ q (fun V : Config G c => move H x V k (shots S x) A T) V := by
  obtain ⟨u,-,hp,-⟩ := hP.feeds
  apply FreeResolvent.TestD.rectangle_smooth
  intro i j
  let a := fresh x (shots S x) A T (axisPrice (G:=G) j)
  change ContDiffAt ℝ _ (fun b => tape.symm (selected H x (increment V b) k (shots S x) A T a) i) 0
  change ContDiffAt ℝ _ (fun b => (Rows.restrict x (shots S x) A T (bump H x (increment V b) k a) i.1) i.2) 0
  unfold Rows.restrict
  split
  swap; · exact contDiffAt_const
  rename_i h
  obtain ⟨⟨s,l⟩,z⟩ := i
  refine ContDiffAt.comp (f:=fun b => slip • bump H x (increment V b) k a (s,l)) (g:=PiLp.proj (𝕜:=ℝ) 2 (fun _ : G.ColorIndex => ℝ) z) _ (ContinuousLinearMap.contDiff _).contDiffAt ?_
  apply ContDiffAt.const_smul
  cases l with
  | inl l =>
    unfold bump faceKick; simp only [Sum.elim_inl]; split
    · refine barrel_smooth hp _ _ (fun e => ?_) (plaquette_smooth s a)
      exact (joint_smooth (q:=q) (S:=S) (V:=V) s e).comp (f:=fun b : Directions G c => (b,(0:Directions G f))) 0 (contDiffAt_id.prodMk contDiffAt_const)
    apply (plaquette_smooth _ _ _).const_smul
  | inr l => exact ((block_smooth s ha h a k).const_smul _).neg

theorem gram_smooth (k : S.Choices) : WardBin.Lies.Germ q (fun V : Config G c => Rows.gram H x V k (shots S x) A T) V := by
  have h := move_smooth (q:=q) H hP ha k
  exact FreeResolvent.TestD.prod_smooth ((FreeResolvent.Bundle.switch (Rows.Receipt G S) (Rows.In (G:=G) x A T)).contDiff.contDiffAt.comp _ h) h
end YM.SelectedOrderedKernels.Sector
