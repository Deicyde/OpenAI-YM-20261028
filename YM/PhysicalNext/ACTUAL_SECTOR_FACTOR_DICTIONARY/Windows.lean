import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Wires

/-! Panel prescriptions in the common read convention.
Full inverse never used to define the *local covariance*. Use the protocol
on the identity completion only via `cloudX_exact`/`perX_exact` (stocked
alignment). In particular don't reroll the full C on raw optional
crossings. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Dictionary
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores Tree Precision Exterior MeasureTheory Matrix
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Push.SectorMeasure Push.SectorMeasure.Oriented
open AnalyticBridge.Annulus AnalyticBridge.Annulus.Map
open AnalyticBridge.RelativeLogdet
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

namespace Numerals
section matrices
variable {ι : Type} [DecidableEq ι] [Fintype ι] {X : Type*} [MeasurableSpace X]
    (W : ι → Set ι) {A B : X → Square ι}

abbrev Watched (A : X → Square ι) := ∀ i j, Measurable fun x => A x i j
namespace Watched
lemma minus (h : Watched A) (he : Watched B) : Watched (fun x => A x-B x) := fun i j => (h i j).sub (he i j)
lemma plus (h : Watched A) (he : Watched B) : Watched (fun x => A x+B x) := fun i j => (h i j).add (he i j)
lemma times (h : Watched A) (he : Watched B) : Watched (fun x => A x*B x) := by
  intro i j; simp only [Matrix.mul_apply]; exact Finset.measurable_fun_sum _ fun k _=> (h i k).mul (he k j)
lemma negative (h : Watched A) : Watched (fun x => -A x) := fun i j=>(h i j).neg

lemma sub {κ : Type} [Fintype κ] (h : Watched A) (f : κ→ι) : Watched (fun x => (A x).submatrix f f) := fun i j => h ..
lemma one : Watched (fun _ : X=> (1:Square ι)) := fun _ _=>measurable_const

lemma inverse (h : Watched A) : Watched (fun x=>(A x)⁻¹) := by
  let _ : MeasurableSpace (Square ι) := borel (Square ι)
  have : BorelSpace (Square ι) := ⟨rfl⟩
  have hv : Measurable A := by
    -- matrix topology is product topology
    change @Measurable X (ι → ι → ℝ) _ (borel (ι → ι → ℝ)) _
    rw [← BorelSpace.measurable_eq (α:=ι → ι → ℝ)]
    exact measurable_pi_lambda _ fun i=>measurable_pi_lambda _ fun j=>h ..
  have he : Measurable (fun x => (A x).det) :=
    (continuous_id (X:=Square ι)).matrix_det.measurable.comp hv
  intro i j
  have hl : Continuous (fun x : Square ι => x i j) := (continuous_apply j).comp (continuous_apply i)
  have ht := (hl.comp (continuous_id (X:=Square ι)).matrix_adjugate).measurable.comp hv
  simp only [Matrix.inv_def,Matrix.smul_apply, Ring.inverse_eq_inv,smul_eq_mul]
  exact he.inv.mul ht

lemma panel (h : Watched A) : Watched (fun x => Schur.per W (A x)) := by
  intro i j
  by_cases hj : j∈W j
  · by_cases hi : i∈W j
    · simp_rw [Schur.per_read W _ hj hi]
      let s := W j
      have ht : Watched (fun x => ((A x).submatrix ((↑): (↥s) → ι) (↑))⁻¹) := inverse (sub h ((↑): ↥s → ι))
      exact ht (⟨i,hi⟩) (⟨j,hj⟩)
    simp_rw [Schur.per_zero W _ hi]; exact measurable_const
  unfold Schur.per; simp only [Matrix.of_apply,dif_neg hj]
  exact measurable_const

lemma weather (h : Watched A) : Watched (fun x => Schur.clouded W (A x)) :=
  fun i j => measurable_const.mul (((panel W h) i j).add ((panel W h) j i))

end Watched
end matrices
end Numerals

namespace Wires
open Schur Completion
variable {G : Gauge} {c f : Side} {S : StepData c f} (T : Tube G S) (x : ℝ)

abbrev perX (k : S.Choices) (V : Config G c) (A : Stores S) (F : Forest S.ratio) :=
    Schur.per (Physical.windows S x) (beam T k V x A F)
abbrev cloudX (k : S.Choices) (V : Config G c) (A : Stores S) (F : Forest S.ratio) :=
    clouded (Physical.windows S x) (beam T k V x A F)

lemma perX_meas (k : S.Choices) (A : Stores S) (F : Forest S.ratio) (h : S.patch.Branches S.kernel G) :
    Numerals.Watched (fun V => perX T x k V A F) := Numerals.Watched.panel _ (fun i j=>beam_meas T k x A F i j h)
lemma cloudX_meas (k : S.Choices) (A : Stores S) (F : Forest S.ratio) (h : S.patch.Branches S.kernel G) :
    Numerals.Watched (fun V => cloudX T x k V A F) := Numerals.Watched.weather _ (fun i j=>beam_meas T k x A F i j h)

theorem cloudX_exact (hA : Map.Aperture S T x) (k : S.Choices) (V : Config G c) (A : Stores S) (F : Forest S.ratio)
    {m η : ℝ} (h : Authorized A V F x m) (hη : 0<η) (hp : Gapped (Rows.gram T x V k (shots S x) A F) η) :
    cloudX T x k V A F = Physical.CFull T A F x V k := by
  unfold cloudX; rw [beam_exact T k V x A F hA h,Physical.produced T A F hA.scale V k hη hp]

theorem perX_exact (hA : Map.Aperture S T x) (k : S.Choices) (V : Config G c) (A : Stores S) (F : Forest S.ratio)
    {m η : ℝ} (h : Authorized A V F x m) (hη : 0<η) (hp : Gapped (Rows.gram T x V k (shots S x) A F) η) :
    let e := (sorted (G:=G) (x:=x) A F).symm
    perX T x k V A F = (wide (Schur.per (panels A F) (Rows.gram T x V k (shots S x) A F))
      (1:Square (vacant A F x G))).submatrix e e := by
  intro E
  unfold perX; rw [beam_exact _ _ _ _ _ _ hA h]
  let I:=wide (Rows.gram T x V k (shots S x) A F) (1:Square (vacant A F x G))
  let w:=allPanels A F (x:=x) (G:=G); let u := Physical.windows S x (G:=G)
  have hw (i j : Full G f) : i∈u j ↔ E i∈w (E j) := by
    change meeting S x _ _ ↔ meeting S x ((sorted A F (x:=x) (G:=G)) (E j)).1 ((sorted A F (x:=x) (G:=G)) (E i)).1; unfold E; simp only [Equiv.apply_symm_apply]
  have ht := equiv_pie I w u E hw (Physical.centered hA.scale) 0
  simp only [pie,zero_smul,add_zero] at ht
  change Schur.per u (I.submatrix E E)=_
  rw [ht]; rw [show Schur.per w I = _ from (stocked A F x T k V hη hp hA.scale).1]

lemma perX_read {X : Support c} {A A' : Stores S} {F F' : Forest S.ratio} {V V' : Config G c} {k k' : S.Choices}
    (hA : Map.Aperture S T x) (h : Physical.Reads X A A' F F' V V' k k') (i j : Full G f)
    (hp : Shields X (Physical.place S i) (15*radiusB x)) : perX T x k V A F j i=perX T x k' V' A' F' j i := by
  have he := (positioned T hA h).column i hp 0 j
  simpa only [perX,pie,zero_smul,add_zero] using he

lemma cloudX_read {X : Support c} {A A' : Stores S} {F F' : Forest S.ratio} {V V' : Config G c} {k k' : S.Choices}
    (hA : Map.Aperture S T x) (h : Physical.Reads X A A' F F' V V' k k') (i j : Full G f)
    (hp : Shields X (Physical.place S i) (16*radiusB x)) : cloudX T x k V A F j i=cloudX T x k' V' A' F' j i := (positioned T hA h).fog_column i hp j
end Wires
end YM.PhysicalNext.Dictionary
