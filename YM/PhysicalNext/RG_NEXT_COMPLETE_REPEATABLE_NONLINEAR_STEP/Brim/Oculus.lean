import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Opacity
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cadre.Tassel
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Islet
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Malachite.Plot


/-! # Local germ of actual single incoming E. All forests constitutive

 Extent unchanged. Use Θ estimates on incap even if later eligible with K.
 Requires points at tested chart with Coat flags in outer; doesn't switch
 probabilistic allocation when exposing principal arithmetic.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Brim
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell Flux Poll Pond Silica Eider Metric Set Gaussian Tablet Quill  
open WardBin.Lies Push.PriceCompiler Foramen Gate
open Packets Art Gas Ursell Trees Multiple Letter OmitClusters Stained March
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}
variable {B B' : BudgetPoint} {Y : Support c} {K : Support f} {U : Config G c} {p j n m k : ℕ} {L : Side}
variable {d A α t C w M N v q r η W μ x : ℝ} {Q : ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W} {R : Rep G f}
variable (H : Cash W x μ L Q o α T R)
open Shield

section inscription
variable (i : ℕ)
def head : Molecule S := {Opacity.key S i}
def plate (_H : Cash W x μ L Q o α T R) (i : ℕ) : RegularAddress c := headed (S:=S) (R.activities.reg i) x Q.halo

lemma caption (i : ℕ) : H.supportP (Opacity.key S i)= (plate H i).support := rfl
lemma concern : H.unionP (head i) = (plate H i).support := by unfold Cash.unionP head; rw [Finset.singleton_biUnion, caption]
lemma pistil (l : ℕ) (b : ℕ) : troupe T R l b (head i) ∧ roster (head i (S:=S))=bareStores S := by
  have he: (head i (S:=S)).toLeft=∅:= by ext; simp [head,Opacity.key]
  have hd: roster (head i (S:=S))=bareStores S := by unfold roster; rw [he]; simp only [Finset.biUnion_empty]; simp [Packets.store,bareStores]; refine ⟨?_,?_,?_⟩ <;> ext <;> simp
  have hl: own (head i (S:=S))=∅:= by ext; simp [head,Opacity.key,own]
  unfold troupe; rw [he,hl,hd]; refine ⟨⟨⟨fun i hi=> (Finset.notMem_empty i hi).elim,by simp,?_⟩,?_,?_⟩,rfl⟩
  · simp [Packets.seeds,bareStores]
  · simp [Contract.sealed]
  · simp [Contract.incidence]

def once : H.ThinP:= ⟨head i,(concern H i).symm ▸ ⟨(plate H i).site,(plate H i).anchor⟩,by rw [(pistil (T:=T) (R:=R) i Q.halo 0).2]; rfl⟩

def icon : H.fragrances := ⟨0,fun _=>once H i⟩
lemma sites_icon : H.bookFoot (.inr (icon H i))=(plate H i).support := by
  change unionOf H.smallAt (fun _ : Option (Fin 0)=> once H i)=_
  rw [unionOf]; ext i; simp; exact congr( i ∈ $(concern H _)) -- edit

lemma lily {χ : Chi} (V : Config G c) : stream H χ V (icon H i)=leaflet H χ V (once H i) := by
  unfold stream Gas.term icon; dsimp only; have ht {Z : H.ThinP} : coefficient H.seam (fun _: Option (Fin 0)=> Z)=1 := by
    unfold coefficient
    let v : Option (Fin 0) → H.ThinP:=fun _=>Z
    have he : pot H.seam v=∅:= by
      apply Finset.eq_empty_iff_forall_notMem.mpr; intro p hp; have h:= (potential_mem H.seam v p |>.mp hp).1
      have hv : p.card ≤ 1:= (Finset.card_le_univ _).trans (by simp); omega
    change Graph.mass (pot H.seam v)=1; rw [he]; unfold Graph.mass; have hh : Graph.reaches (∅: Graph.Network (Option (Fin 0))) := by
      intro i j; rw [Subsingleton.elim i j]
    have he : Graph.connectedGroups (∅:Graph.Network (Option (Fin 0)))={∅}:= by ext i; simp only [Graph.belongs,Finset.subset_empty,Finset.mem_singleton]; exact ⟨And.left,fun e=> e.symm ▸ ⟨rfl,hh⟩⟩
    rw [he]; simp [Graph.alternating]
  rw [ht]; simp
end inscription
end YM.PhysicalNext.Repeat.Brim
