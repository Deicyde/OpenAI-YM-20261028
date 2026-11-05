import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Forecast
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Baffle.Patch
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Brim.Fog
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Brim.Gills
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Brim.Rim
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Prism.Sail

/-! # Pay both C and A and μ turns on the plateau arcs

 Simultaneous prices N, Kernels, views. No W inheritance assumption on
 positivity/Scope of Heir (uses true committed *data* already in Stage).
 h.D kept fixed. Full Arc trajectory pricing requires hX width fixed by
 operator earnings. Once per desk across all θ.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Brim
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell Flux Poll Pond Silica Eider Metric Set Gaussian Tablet Quill Baffle Prism
open WardBin.Lies Push.PriceCompiler Foramen Gate
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}
variable {B B' : BudgetPoint} {Y : Support c} {K : Support f} {U : Config G c} {n p j : ℕ}

structure Tentacle (M C J v t l : ℝ) (X : Coat T F) {I:Type} [Fintype I] [DecidableEq I]
    (a : Museum F X.x (bareStores S) K Y I) (q : Chi) (b : ℝ) (U : Slab G c j) (n : ℕ) : Prop where
  sunny : Mode (journey X.V j U) 0 n M
  horizon : ∀ i, dotProduct i (lamp6 X a X.V*ᵥ i) ≤ t*dotProduct i i
  area : Prism.Holds (lamp6 X a ∘ journey X.V j U) 0 C n
  skies : Prism.Holds (lamp9 X a ∘ journey X.V j U) 0 C n
  offset k : Brush n J 1 (offsetRun X a k q b 1 ∘ journey X.V j U) 0 -- edit
  trends : EdgePay ((lamp9 X a ∘ journey X.V j U)-(lamp6 X a ∘ journey X.V j U)) n v 1 0
  out k : Brush n l 1 (volume6 X a k ∘ journey X.V j U) 0
  toward : ∀ᶠ x in 𝓝 (0:Panels j), (vary X (journey X.V j U x)).relating.PosDef ∧ (lamp9 X a (journey X.V j U x)).PosDef

section forecast
variable (G : Gauge) (P : Teller G) (L : Side) (D : Patch) (hD : D.Branches P.bind G) (n p : ℕ) (C : Libretto G n) (D' : Record) (hn : 2≤n)
variable (W : ℝ) (o : ConnectedActivityE6.Target.Order G W) (χ : Chi)
include hn hD
lemma spicules : ∃ (M X J v l : ℝ→ℝ) (t : ℝ), Rate G L (-(1/2)) M ∧ (∀ x, 0 ≤ M x) ∧ Rate G L 0 X ∧ Rate G L (-1) J ∧
    Rate G L (-(1/2)) v ∧ Rate G L (-(1/2)) l ∧ ∀ᶠ s in atTop,
    ∀ (c f:Side) (S : StepData c f) (T : Tube G S), S.patch=D → Works P L s S T → ShellAccess S G s W o.K o.γ →
      ∀ (F : Forest S.ratio) (Y : Coat T F), Y.x=s→Y.χ=χ→ Y.width=o.K→ Y.manifest→ Rotator P L o.eta o.gap o.ample o.indexPay Y →
      ∀ (B B' : BudgetPoint), B.power=p → Plays C D' B B' P T s → ∀ (I:Type) [Fintype I] [DecidableEq I]
      (H : Support c) (Z : Support f) (a : Museum F Y.x (bareStores S) Z H I) (q : Chi) (b : ℝ), ∀ k∈H, B.B=radiusB s → coverNumber B.B H≤ B.B → Scrim Y a → Healthy B.threshold H Y.V →
      ∀ j (U : Slab G c j), j≤n → (∀ i,B.dirBound k (U i)) → (∀ i, ‖U i‖ ≤ canopyW G L p s) →
        Tentacle (M s) (|X s|) (|J s|) (|v s|) t (|l s|) Y a q b U n := by
  obtain ⟨M,hM,hV,hb⟩:= aura G P L p n
  obtain ⟨K,v,hK,hv,hX⟩:= canopies G P L D hD n χ W o hM (Eventually.of_forall hV)
  obtain ⟨m,f,h₀,h₁,hL⟩ := saleD G P L D hD n p C.Z hn
  let X:= silver G L o.eta o.gap o.ample; let y s := Heir.canopy D'.Z (radiusD s) p n; let C' x:= K x+ |f x|+X+y x
  have hg : Rate G L 0 (fun x=>|f x|) := (h₁.weaken (by norm_num)).compare (Eventually.of_forall fun x=> (abs_abs _).le)
  refine ⟨M,C',m,f,v,1+Window.payE o.eta o.gap o.ample (tubularPrice G L),hM,hV,((hK.add hg).add (Rate.const _)).add (can_pay G L n p D'),h₀,h₁,hv,?_⟩
  filter_upwards [hL,hX] with s hL hZ c f' S T hS hT he F Y hx hχ hw hn hA B B' hP hp I _ _ H Z a q b k hk hf hl hs hY j U hJ hU hC'
  subst s; let S':=Y.x; let C'₀:= |C' S'|; rw [hf] at hl
  have hV := hb S' c f' S T hA.room hT.length_eq B hP hp.rehearsed.temp_eq Y.V j U hC' hJ
  have hz : journey Y.V j U 0=Y.V:= Planned.AtomRegular.Sample.journey_origin ..
  obtain ⟨hK,hv,h₁,h₂,h₃⟩:= hZ c f' S T hS hT he F Y rfl hχ hw hn hA _ (journey Y.V j U) 0 hz hV
  have hh := hL c f' S T hS hT hp.bulletin F Y rfl B hP hp.rehearsed.temp_eq hp.rehearsed.wire H Z I a k hl hk hs.outer _ hY j U hJ hU
  have h : EdgePay (lamp6 Y a ∘ journey Y.V j U) n (K S') 1 0:= fun i j=> h₁ (scoop Y a i) (scoop Y a j)
  have h₄ := illum a hk hl hY hp; have hk : 0≤y S' := zero_le_one.trans (canopy_one D'.chimes ..)
  have ht : 0 ≤ X := (arbors hA).disc; have he₀ : K S'+|f S'|+X+y S' = C' S' := rfl
  have hu: K S' ≤ C'₀ := le_trans (by linarith only [ht,hk,abs_nonneg (f S'),he₀] : K S' ≤ C' S') (le_abs_self _)
  have hD : EdgePay ((lamp9 Y a ∘ journey Y.V j U)-(lamp6 Y a ∘ journey Y.V j U)) n (|f S'|) 1 0:= fun k l=> (((hh.2 k l).opposite).climb (le_abs_self _) le_rfl).shimmy (Eventually.of_forall (fun i=> by exact (neg_sub (lamp6 Y a (journey Y.V j U i) k l) (lamp9 Y a (journey Y.V j U i) k l)).symm))
  have he' : ∀ᶠ t in 𝓝 (0:Panels j), (lamp9 Y a (journey Y.V j U t)).PosDef:= (flowJourney Y.V U).eventually h₄.near
  have hY := (arbors hA).sub (scoop Y a)
  refine ⟨hV,fun u=> (le_abs_self _).trans (Control.top (density _ _ _ hY.symmetry hY.price) hY.eta.le u), ⟨fun i j=> (h i j).climb hu le_rfl,fun i j=> (Brim.value6 a hA hz i j).trans (show X ≤ _ from ?_),
      (h₃.mono (fun t ht=> ht.submatrix (scoop Y a).injective)).self_of_nhds⟩,⟨fun i j=>?_,fun i j=>?_,he'.self_of_nhds⟩,fun i=>
        ((hh.1 W _ (hw.symm ▸ he) q i b 1)).climb (le_abs_self _) le_rfl,hD,fun i=> (h₂ (a.address i)).climb (le_abs_self _) le_rfl,
        h₃.and he'⟩
  · refine le_trans (b:=C' S') ?_ (le_abs_self _); change X≤ _; linarith only [he₀,ht,hk, hK,abs_nonneg (f S')]
  · refine (((hD i j).gathering (h i j)).climb ?_ le_rfl).shimmy (Eventually.of_forall (fun i=> ?_))
    · refine le_trans (b:=C' S') ?_ (le_abs_self _); linarith only [he₀,hk,ht]
    exact (sub_add_cancel ..).symm
  have hh:= h₄.val i j; rw [Function.comp_apply,hz]
  change ‖(((lamp9 Y a Y.V)⁻¹ i j:ℝ):ℂ)‖≤_ at hh
  rw [Complex.norm_real,hP] at hh
  exact hh.trans (le_trans (show y S' ≤ C' S' from by linarith only [he₀,hK,hk,abs_nonneg (f S'),ht]) (le_abs_self _))
end forecast
end YM.PhysicalNext.Repeat.Brim
