import YM.AnalyticBridge.ANNULUS_RATIO_INSERTIONS.Ship
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Brim.Idyll

/-!
# Price inheritance on actual unsigned representation. Use Ψ for the principal,
 quote residual with SAME pre-exponent. Anchor at project. Eligibility for this
 debit if size fits from Forb Lore, not claiming all sectors inherit.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Brim
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell Flux Poll Pond Silica Eider Metric Set Gaussian Tablet Quill Baffle 
open WardBin.Lies Push.PriceCompiler Foramen Gate
open Packets Art Gas Ursell Trees Multiple Letter OmitClusters Stained March Shield Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}
variable {p j n m k : ℕ} {L : Side} {V : Config G c}
variable {d A α t C w M N v q r η W μ x b : ℝ} {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W} {R : Rep G f}
variable (H : Cash W x μ L Q o α T R) (D : Record) (q' κ χ : Chi) (ε : ℝ)

section estate
variable {B : BudgetPoint} {C₀ : Libretto G p} (hP : Plays C₀ D B R.p P T x) (i : ℕ)
    (hN : Captain H n C d v t A b r M q k χ) (hn : B.order≤n)

def glyph (i : ℕ) (V : Config G c) := stream H χ V (icon H i)+announced H D q' κ ε i V

lemma zipped {D : Support c} {f g: Config G c→ ℝ} (h : B.Regular D f) (hp : B.Regular D g) : B.Regular D (f+g) := by
  have hP U (hh : Healthy B.threshold D U) : Germ B.order (f+g) U:= ContDiffAt.add (h.smooth U hh) (hp.smooth U hh)
  exact ⟨fun U V hh=> congr_arg₂ (·+·) (h.sites _ _ hh) (hp.sites _ _ hh),h.borel.add hp.borel,fun g V=> congr_arg₂ (·+·) (h.symmetry g V) (hp.symmetry g V),hP,fun U hv A l hl=> (hP U hv).has l A hl⟩
include hP hn hN
lemma legal (hp : B.Regular (plate H i).support (announced H D q' κ ε i)) : B.Regular (plate H i).support (glyph H D q' κ χ ε i) := by
  have hh:= (hN.gloryBudget (icon H i) B hP.rehearsed.temp_eq hn).2.1
  refine zipped (?_: B.Regular _ (fun V=> stream H χ V (icon H i))) hp
  rw [← sites_icon]; exact hh

variable {τ : ℝ}
lemma round (hr : B.B=radiusB x) (hS : B.Regular (plate H i).support (announced H D q' κ ε i)) (hτ : 0≤τ)
    (hh : coverNumber B.B (plate H i).support ≤ B.B) (hp : ∀ V, Healthy B.threshold (plate H i).support V → ∀ j ≤ p, ∀ U : Slab G c j,
      (∀ k,B.dirBound (plate H i).site (U k)) → (∀ k, ‖U k‖≤ canopyW G L B.power x) →
        Brush p τ 1 (glyph H D q' κ χ ε i ∘ journey V j U) 0) : B.supBounds (plate H i).site (plate H i).support (glyph H D q' κ χ ε i) τ := by
  refine ⟨hτ,fun V hV l hl hz=>?_⟩
  let Y:=(plate H i).support; let T:= glyph H D q' κ χ ε i; have hf:= legal H D q' κ χ ε hP i hN hn hS
  let L' (s:Directions G c) (i:Bond c):= if i.1∈Y then s i else 0
  let l': List (Directions G c):=l.map L'
  have hx := March.stays hf.sites l L' (fun v hv j hj=> if_pos hj) V V (fun _ _ _=>rfl)
  have he := H.laws.data.room; have hm : B.threshold≤ 2*fiery G x L:= by rw [hP.rehearsed.temp_eq,← H.laws.data.funds.length_eq]; exact he.temperatures
  have hv (z) (hi:z∈l'): B.dirBound (plate H i).site z := by
    obtain ⟨i,hh,rfl⟩:=List.mem_map.mp hi; intro b; unfold L'; split
    · exact hz _ hh b
    rw [norm_zero]; positivity [B.threshold_pos]
  have hc k : ‖l'.get k‖ ≤ canopyW G L B.power x:= by
    have hj:=List.get_mem l' k
    refine pacing _ Y ?_ B (plate H i).anchor rfl (hv _ hj) x L (hr ▸ hh) hm
    obtain ⟨i',hd,hk⟩:= List.mem_map.mp hj
    intro k hk'; rw [← hk]; exact if_neg hk'
  have hJ : l'.length ≤ p:= by unfold l'; rw [List.length_map,← hP.rehearsed.test]; exact hl -- edit
  have he := hp V hV l'.length hJ l'.get (fun j=>hv _ (List.get_mem l' _)) hc
  rw [hx]; change ‖leftDerivs T l' V‖ ≤ τ
  rw [← List.ofFn_get l',Germ.ordered l'.get ((show Germ B.order T V from hf.smooth _ hV).prod (hP.rehearsed.test.symm ▸ hJ))]
  have hh := he.order l'.length hJ; rw [one_pow,mul_one] at hh
  simpa only [Finset.prod_const_one,mul_one] using! ContinuousMultilinearMap.le_mul_prod_of_opNorm_le_of_le hh (show ∀ j:Fin l'.length, ‖WardBin.Lies.cart j‖≤ (1:ℝ) from fun i=> (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun j => by simp only [WardBin.Lies.cart,Pi.single_apply]; split <;> norm_num))
end estate
end YM.PhysicalNext.Repeat.Brim
