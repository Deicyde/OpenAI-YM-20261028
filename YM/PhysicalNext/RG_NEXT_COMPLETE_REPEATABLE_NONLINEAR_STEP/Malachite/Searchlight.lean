import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Malachite.Iceland

/-!
# Compact-stencil jet quotes for the μ dislocation and C gap

Buy Theta-independent table priced in coordinates of all tags; uses actual
h.tired layout threshold in OUTPUT cover number. Powers unchanged. Shares
rates even if V partly flagged. Does not claim open equality with all-good;
holds the flags. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Malachite
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Gate Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open WardBin.Lies Offset Metric Planned.AtomRegular.Foliage
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}

-- measure from size provider only. Doesn't alter Sector's knobs
abbrev radiusD (x : ℝ) := radiusB x*(4*radiusB x+2)+2*radiusB x
variable (G : Gauge) (P : Teller G) (L : Side) (D : Patch)
def horns (n : ℕ) (C : ℝ) (x : ℝ) := C*(2*fiery G x L)*(1+(Heir.reach x:ℝ))^n * (1+(radiusD x:ℝ))^n
lemma sugars (n : ℕ) (C : ℝ) : Rate G L (-(1/2)) (horns G L n C) := by
  have hp := Rate.radius_price (G:=G) (L:=L); have ht := Rate.const (G:=G) (L:=L) (1:ℝ)
  have hr : Rate G L 0 (fun x=> (Heir.reach x:ℝ)) := by unfold Heir.reach; push_cast; exact (ht.add hp).mul_left _
  have hf : Rate G L 0 (fun x=> (radiusD x:ℝ)) := by
    unfold radiusD; push_cast
    exact Rate.add (by simpa only [zero_add] using! hp.mul (((hp.mul_left 4).add (Rate.const 2)))) (hp.mul_left 2)
  simpa only [zero_mul,add_zero] using! ((((Rate.flame (G:=G) (L:=L)).mul_left 2).mul_left C).mul ((ht.add hr).pow n)).mul ((ht.add hf).pow n)

variable (hD : D.Branches P.bind G) (n p : ℕ) (V : Planned.AtomRegular.Foliage.Collar G n) (hn : 2 ≤ n)
-- auxiliary rank before Output Curve
include hD hn
lemma saleD : ∃ M J : ℝ→ℝ, Rate G L (-1) M ∧ Rate G L (-(1/2)) J ∧ ∀ᶠ x : ℝ in atTop,
    ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch=D → Works P L x S T → Folio.Bulletin x P T→
    ∀ (F : Forest S.ratio) (X : Coat T F), X.x=x → ∀ B : BudgetPoint, B.power=p → B.threshold=temp x → Cube.Wire B (reach X.x) V →
    ∀ (Y : Support c) (E : Support f) (I : Type) [Fintype I] [DecidableEq I] (a : Museum F X.x (bareStores S) E Y I) (o : Site c),
    coverNumber (radiusB x) Y≤ radiusB x → o ∈ Y → Disjoint X.seeds.place Y → ∀ W, Healthy B.threshold Y W →
    ∀ j (U : Slab G c j), j ≤ n → (∀ i,B.dirBound o (U i)) →
    (∀ (w d : ℝ), ShellAccess S G X.x w X.width d→ ∀ q : Chi, ∀ k t z, Brush n (M x) 1 (offsetRun X a k q t z ∘ journey W j U) 0) ∧
    ∀ k l, Brush n (J x) 1 (fun z=> (lamp6 X a-lamp9 X a) (journey W j U z) k l) 0 := by
  let Z:= Cube.fee V; have hz := Cube.fee_one V; let v := horns G L p Z; have hv: Rate G L (-(1/2)) v := sugars G L p Z
  have he : ∀ᶠ x in atTop,0≤v x:= Eventually.of_forall fun x=> by unfold v Z horns; have he : 0≤ fiery G x L:= temp_nonneg _; positivity
  obtain ⟨t,C,ht,hC,H⟩:= treasure G P L D hD n hn hv he (-(1/2))
  refine ⟨fun x=> shot G (C x) (t x) (v x) n,fun x=> chordPay G (C x) (t x) (v x) n,?_,?_,?_⟩
  · have hi : Rate G L (-1) (fun x=> C x*(t x+v x)*v x+C x*v x^2) := by
      refine Rate.add ?_ ?_
      · convert ((hC.mul (ht.add hv)).mul hv) using 1; norm_num
      convert hC.mul (hv.pow 2) using 1; norm_num
    exact ((hi.mul_left _).mul_right _).mul_left _
  · have hi : Rate G L (-(1/2)) (fun x=> t x+(C x+C x)*v x) := Rate.add ht (by simpa only [zero_add] using! (hC.add hC).mul hv)
    exact (((hi.mul_left _).mul_right _).mul_left _).mul_left _
  filter_upwards [ConnectedActivityE6.room G P L,H,hv.below (by norm_num) 1 zero_lt_one] with x hR H he c f S T hs hW b F X hX B hm hb h Y E I _ _ a o hx ho hy W hV j U hL hU
  subst x; have hr:= hR c f S T hW; obtain ⟨hp,hz',hP⟩:= H c f S T hs hW F X rfl
  have hg i : halo (Heir.reach X.x+1) ({pole X a i}:Support c) ⊆ Y:= (Corona.halo_mono (by omega) (Finset.Subset.refl _)).trans (a.stores i)
  have hx' i : separation (pole X a i) o ≤ radiusD X.x:= (Corona.extent _ (radiusB X.x) (hg i (halo_subset _ _ (Finset.mem_singleton_self _))) ho).trans (by unfold radiusD; gcongr)
  choose! g hg using fun k:I=> primed hV (hg k) (roomy hr.buys) V (by omega) h
  have hb' k : loom B (reach X.x) (Cube.fee V)*spine B.power (pole X a k) o ≤ v X.x := by
    unfold loom v Z horns spine; rw [hm,hb,← hW.length_eq]; have he := hr.temperatures
    have he' := hr.fiery; gcongr
    exact hx' _
  constructor
  · intro w d hd q k t' Y
    exact pounds X a k q U hr b hd hy (hg k) hP hn hz (hb' k) ((le_abs_self _).trans he) hL hU t' Y
  intro k l
  exact latitude X a k.1 U hr b hy (hg k.1) hP hn hz (hb' k.1) ((le_abs_self _).trans he) hL hU l.1 k.2 l.2
end YM.PhysicalNext.Repeat.Malachite
