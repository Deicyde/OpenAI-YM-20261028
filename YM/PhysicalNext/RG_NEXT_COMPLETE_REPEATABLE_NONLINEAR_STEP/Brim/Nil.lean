import YM.Next.MULTISOURCE.Chime
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Brim.Oculus
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Brim.Rim

/-! # The inherited occupancy after WaterColors. Germ at masked S.V
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
open Packets Art Gas Ursell Trees Multiple Letter OmitClusters Stained March Shield
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}
variable {p j n m k : ℕ} {L : Side} {V : Config G c}
variable {d A α t C w M N v q r η W μ x b : ℝ} {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W} {R : Rep G f}
variable (H : Cash W x μ L Q o α T R)

section curve
variable {χ : Chi} (u : Slab G c j)
lemma rescaleY (t : ℝ) (ht : 0<t) : ∃ q : Panels j→L[ℝ] Panels j,
    (∃ u', Mode (journey V j u ∘ q) 0 n u' ∧ u'≤t) ∧ (𝓝 0:Filter (Panels j)) ≤ Filter.map q (𝓝 0) := by
  obtain ⟨Z,hZ,hE⟩:= oar G n
  let p:= ‖u‖; let U:(Sailor G p (Z*p) n):= ⟨fun d=> hE d _ (norm_nonneg _)⟩
  have hp:= oars_j U V u (fun i=> norm_le_pi_norm _ i); let m:=(j:ℝ)*(Z*p)
  let s:= t/(1+m); have hv:0 ≤ m:= hp.pos; have hs:0<s:= by unfold s; positivity
  let L := (s • ContinuousLinearMap.id ℝ (Panels j))
  have hL : ‖L‖ ≤ s := by unfold L; rw [norm_smul,Real.norm_of_nonneg hs.le]; exact mul_le_of_le_one_right hs.le ContinuousLinearMap.norm_id_le
  let f:= journey V j u
  let Y:= s⁻¹ • ContinuousLinearMap.id ℝ (Panels j); have hh: L ∘ Y=id := funext fun i=>by simp [Y,L,smul_smul,hs.ne']
  have hQ : map L (map Y (𝓝 0))=𝓝 0:= by rw [Filter.map_map,hh]; exact map_id
  have he : map Y (𝓝 0) ≤ 𝓝 0:= by nth_rw 2 [← Y.map_zero]; exact Y.continuous.continuousAt
  refine ⟨L,⟨m*s,⟨mul_nonneg hp.pos hs.le,fun i=> Brush.reading L (g:=fun j=> G.mat (f j i)) (by rw [map_zero]; exact hp.atLink i) hL⟩,?_⟩,hQ.symm.trans_le (map_mono he)⟩
  calc
    _ ≤ (1+m)*s:= by gcongr; linarith
    _ = _:= by unfold s; field_simp

variable (hN : Captain H n C d v t A b r M q k χ) (i:ℕ) (hp : Healthy (Pressure.temp x) (plate H i).support V) (F: Forest S.ratio)

include hN hp
lemma custody :
    let X := Greenbelt.prism T x χ o.K V F
    let s:= journey V j u
    ∀ᶠ z : Panels j in 𝓝 0, fringe (vary X (s z)) W o.a (head i) R Q.table Q.halo =
      likely fun j : S.Choices => Shield.bars (podium S G (plate H i).support (radiusB x)) (vary ((planted X (head i)).taggedL j) (s z)) (head i) R Q.table W o.a Q.halo := by
  intro X s; have hp : Healthy (Pressure.temp x) (H.unionP (head i)) V:= (concern H i).symm ▸ hp
  have hx := (once H i).property.2
  obtain ⟨L,⟨t,he,hv⟩,ht⟩:= rescaleY (V:=V) (n:=n) u v hN.position
  have h:= Stained.rainbow (head i) hN.oboe (X:=X) rfl rfl rfl hx hp
    (show Mode (s ∘ L) (0:Panels j) n v from ⟨hN.position.le,fun i=> (he.atLink i).climb le_rfl hv⟩)
    (show (s ∘ L) 0=V by rw [Function.comp_apply,map_zero]; exact Planned.AtomRegular.Sample.journey_origin ..)
  have he : ∀ᶠ z in 𝓝 0, fringe (vary X (s z)) W o.a (head i) R Q.table Q.halo=shelter (vary X (s z)) W o.a (head i) R Q.table Q.halo := by
    apply Filter.Eventually.filter_mono ht; rw [Filter.eventually_map]; exact h
  filter_upwards [he] with z hz
  let P:=head i (S:=S); have hh : Ac.Spark H.supportP P ∧ troupe T R Q.halo (radiusB x) P:= by
    refine ⟨?_,(pistil i Q.halo (radiusB x)).1⟩  -- holes in have?
    constructor; exact Finset.singleton_nonempty _
    intro i hi j hj; have he:= (Finset.mem_singleton.mp hi).trans (Finset.mem_singleton.mp hj).symm; subst j; exact .refl
  rw [hz,shelter,show (vary X (s z)).B=radiusB x from rfl,if_pos (show Ac.Spark (areas R T Q.halo _) _ ∧ _ from hh)]
  apply congr_arg likely; funext j; have hh:= spices (head i) H X rfl (s z) (s z) (fun _ _ _=>rfl) hp hx j; rw [← concern]; exact hh.symm
end curve
end YM.PhysicalNext.Repeat.Brim
