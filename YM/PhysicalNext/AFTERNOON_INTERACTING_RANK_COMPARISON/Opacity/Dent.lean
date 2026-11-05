import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE.Borel
import YM.AnalyticBridge.MARGINAL_MULTIPLIER_3B1D.Integrated
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Tablets
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Necklace
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Stagecraft
import YM.Progress.JOINT_CALENDAR.Branches

/-!
# Comparing the exact two affine D rows at exterior patches

Flat coincidence (not asserted away from identity) and gauge transport
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Milk
open Lattice Wilson Pressure Precision RG RG.Supply Laurent Bloch Matrix Finset Filter
     PhysicalGuard7f546.Curved AnalyticBridge.LocalGaussianLaws Exterior Remote Local Lift Tree Bid
    Function Assembly Current Next.SectorChange Next.SectorChange.Rows Next.Fluctuations
    Push.SectorMeasure Pressure.Stores Gaussian Wisps 
open AnalyticNext.ConnectedActivity
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {A : Stores S} {F : Forest S.ratio}
    {V : Config G c} {P : Teller G} {T : Tube G S} {i : Site c} {x β C : ℝ} {X : Config G f}
section flat
lemma map_now (s : Signed) (w : Directions G f) : Aff.form (Turn.maps s 1 w)=pulled (Flat.labels w) s := by
  ext i u
  simp_rw [Aff.form,Turn.maps_apply]
  unfold pulled; split
    <;> simp only [Pi.one_apply,inv_one,G.adjoint_one]
  · rename_i he
    rw [if_pos he]; simp only [Flat.labels,show (coord) = axisEquiv from rfl,Equiv.symm_apply_apply,Prod.mk.eta]; rfl
  rename_i he
  rw [if_neg he]; simp only [Flat.labels,show (coord) = axisEquiv from rfl, Equiv.symm_apply_apply,Prod.mk.eta]; rfl
lemma concord (P : Teller G) (h : P.Funds S T) (x : ℝ) (w : Directions G f) (k : S.Choices) (p : Slots S) :
    Rows.bump T x 1 k w p = Aff.derivative T (till x) p 1 w := by
  have hp := funds_branch h
  have ht : Aff.untwine S p 1 w=Turn.maps p.1 1 w:= by
    unfold Aff.untwine; rw [replica_one,show pull _ _ (1:Config G c)=1 from funext fun i=> by simp [pull,Step.read]]; funext; simp [Aff.rotateG,Aff.corner_flat]
  have hu := congr_arg Aff.form ht|>.trans (map_now ..)
  rcases p with ⟨s,j|j⟩
  · unfold Rows.bump Aff.derivative; dsimp only
    unfold Rows.faceKick Aff.level; simp only [Sum.elim_inl]; split
    next h => unfold barrel; refine tsum_congr (fun i=>?_); dsimp only; split
              next h => rw [Flat.flat_curl,←hu, fixed_facade, replica_one,travel_pull,← Precision.link_one, YM.Push.stroll_zero,G.adjoint_one]
              rfl
    next h => rw [Flat.flat_curl,hu]
  change -(Real.sqrt S.kernel.penalty • blockJet _ k s j w) = zLin S (Aff.form _) _ _
  rw [Flat.flat_probe s k j w hp,hu]; unfold zLin; simp only [Pi.zero_apply,zero_sub,smul_neg]; rfl

open AnalyticBridge.RelativeLogdet.Physical in
lemma twist_bump (P : Teller G) (h : P.Funds S T) (x : ℝ) (k : S.Choices) (z : Site c→G.El) (a : Directions G f) (p : Slots S) :
    Rows.bump T x (Lattice.gauge z V) k (Aff.rotateG a (z ∘ S.ratio.parent)) p = G.adjoint (z (Aff.base S p)) (Rows.bump T x V k a p) := by
  obtain ⟨c,b,H,-⟩:=h.feeds
  rw [show Aff.rotateG a (z ∘ S.ratio.parent)=Motion.swing (constantGauge z S.ratio) a from ?_,bump_flip z V k a T (funds_branch h) x H]
  swap; rfl
  rw [show zenith S z p=z (Aff.base S p) from ?_]
  obtain ⟨s,i|i⟩:=p <;> simp only [zenith, Sum.elim_inr,Sum.elim_inl,AnalyticBridge.RelativeLogdet.Physical.wind,constantGauge,Function.comp_apply]
  · rw [Ratio.parent_signed S.ratio S.patch.odd_side]; rfl
  rw [Ratio.parent_signed S.ratio S.patch.odd_side,Ratio.embed_parent]; rfl

lemma tallyBase (k : S.Choices) (j : Slots S) : Rows.base T x V k j=Aff.target T (till x) (temp x) j k V (replica S.ratio V) := by
  rcases j with ⟨s,r|r⟩
  · unfold Rows.base Aff.target; dsimp only [Sum.elim_inl]
    unfold Rows.faceFixed; rw [fixed_facade]
  unfold Rows.base Aff.target; dsimp only [Sum.elim_inr]
  unfold Rows.noiseFixed; rw [fixed_facade]
end flat
end YM.PhysicalNext.InteractingRank.Milk
