import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Patch
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Stencils
import YM.Work.F05.Actions



set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Authorize the jets in the affvd stencils

On all channels, including noise on *its own* oriented group inputs.
Pass along if recorded V prescription passes, regardless of realization
of the tags or likelihood (only Branches on the dynamics). D-entry test
below uses the same orthogonal direction shift through these gates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.SectorChange
open Function Filter Lattice RG RG.Patch Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch Tree
open YM.Work.F01 YM.Push.SectorMeasure YM.Bid YM.Next.Fluctuations Matrix
open YM.Push.SectorMeasure.Oriented Motion LocalJet Rows Gaussian NormedSpace
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f : Side} {S : StepData c f} {x : ℝ}

/-- Authorization buys also the uniform LOCAL upper price on the rotated
block test. The mat expression includes the right leg, so its tangent is
in the left trivialization, not assuming m translation invariance. -/
structure Authorized (A : Stores S) (V : Config G c) (F : Forest S.ratio) (x : ℝ) (B : ℝ) : Prop where
  noise (s : Signed) (k : S.Choices) (i : Bond c) : curb (shots S x) A F x s (.inr i) →
    let U := pull s 0 (replica S.ratio V); let t := choice s k
    ContDiffAt ℝ ω (fun a : Directions G f => G.mat (out U t i a)) 0 ∧ ContDiffAt ℝ ω (bTest U t i) 0 ∧
    ∀ a : Directions G f, ‖fderiv ℝ (bTest U t i) 0 a‖ ≤ B * settle S i.1 (predReach S.patch) a

private lemma unwind (hp : S.patch.Branches S.kernel G) (w : Site f → G.El) (U : Config G f) (t : S.Choices) (i : Bond c)
    (h : ContDiffAt ℝ ω (fun a : Directions G f => G.mat (out (Lattice.gauge w U) t i a)) 0) :
    ContDiffAt ℝ ω (fun a : Directions G f => G.mat (out U t i a)) 0 := by
  let v := w (S.ratio.embed i.1)
  have he a : out U t i a = v⁻¹ * out (Lattice.gauge w U) t i (swing w a) * v := by
    unfold out; rw [swing_increment,(choice_gauge hp _ _ w).2,(choice_gauge hp _ _ w).2]; unfold Lattice.gauge v
    dsimp only [Function.comp]; group
  let x := fun a => G.mat (out (Lattice.gauge w U) t i a)
  let L := swing w
  have hp : ContDiffAt ℝ ω x (L 0) := (L.map_zero).symm ▸ h
  have hr : ContDiffAt ℝ ω (fun a => x (L a)) 0 := hp.comp (f:=L) 0 L.contDiff.contDiffAt
  simp_rw [he,G.mat_mul]
  exact (contDiffAt_const.mul hr).mul contDiffAt_const

/-- Trim the *original output neighborhood* at turned anchor; no
approximation of copied fields on big tori by globally small fields. -/
lemma earned (P : Patch) (K : KernelChoices) (G : Gauge) (h : P.Branches K G) :
    ∃ C δ : ℝ, 0<C ∧ 0<δ ∧ ∀ {c f : Side} (S : StepData c f),
    S.patch=P → S.kernel=K → ∀ (F : Forest S.ratio) (A : Stores S) (V : Config G c) (x : ℝ),
    A.flags = RG.flags (temp x) V → span P x ≤ radiusB x/50 → allot P+1 ≤ 9*radiusB x →
    2*(allot P+1)<c.val → permit P*temp x ≤ δ → Authorized A V F x C := by
  obtain ⟨C,δ,hC,hδ,H⟩ := LocalJet.Block.block_comparison G P K h (ε:=1) (by norm_num)
  refine ⟨C,δ,hC,hδ,?_⟩
  intro c f S hP hK F A V x hA hx he hR hr
  refine ⟨?_⟩
  intro s k i ht U t
  let l := s.act i.1
  have hl : l ∉ A.dome (9*radiusB x+9*radiusB x/10) := (guarded (hP.symm ▸ hx) ht).1
  obtain ⟨w,hw⟩ := trim (allot P) hl (by omega) hR hA
  let v := fun i : Site f => w (affine s 0 i)
  let u := Lattice.gauge v U
  have hu (e : Bond f) (hy : separation i.1 (S.ratio.parent e.1) ≤ predReach P) : G.chord (u e) ≤ δ := by
    have hh : u = pull s 0 (Lattice.gauge w (replica S.ratio V)) := (Work.F05.pull_gauge_zero ..).symm
    rw [hh,turn_read]; have hC := spin_separation (S:=S) e s i.1
    have hv := hw (sendEdge s 0 e) (by unfold l allot; omega)
    split
    next h => rw [G.chord_inv]; exact hv.trans hr
    next h => exact hv.trans hr
  obtain ⟨hb,hb',he⟩ := H S hP hK t u i hu
  have hS : S.patch.Branches S.kernel G := (by rw [hP,hK]; exact h)
  obtain ⟨hp,he'⟩ := b_auth hS v U i t hb'
  refine ⟨unwind hS v U t i hb,hp,fun a => ?_⟩
  have hf := (he (swing v a)).1
  rw [he',G.norm_adjoint,swing_settle] at hf
  simpa only [hP] using hf




end YM.Next.SectorChange
