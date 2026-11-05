import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Beaches


/-!
# Sift colors on Hot bonds
Use Equiv not ghost convention depending on F-order. Transformation
with shifts at SYNCHED Y. No need constants from dimensions of Lie groups (integers).
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary
open Packets Presented LabelSum Sector
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f n : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {ι κ : Type} [Fintype ι] [Fintype κ]

lemma preserving_curry (ι κ : Type) [Fintype ι] [Fintype κ] : MeasurePreserving (MeasurableEquiv.curry ι κ ℝ) := by
  let e:= MeasurableEquiv.curry ι κ ℝ
  suffices h : MeasurePreserving e.symm by exact h.symm
  refine ⟨e.symm.measurable,Eq.symm (Measure.pi_eq ?_)⟩
  intro s hs
  let X := Set.univ.pi s
  let U i := Set.univ.pi (fun j:κ => s (i,j))
  have hx : e.symm ⁻¹' X = Set.univ.pi U := by
    ext y; simp only [Set.mem_preimage]; constructor
    · intro h i _ j _; exact h (i,j) (Set.mem_univ _)
    intro h i _; exact h i.1 (Set.mem_univ _) i.2 (Set.mem_univ _)
  rw [Measure.map_apply e.symm.measurable (MeasurableSet.univ_pi hs), show e.symm ⁻¹' (Set.univ.pi s)=Set.univ.pi U from hx,Fintype.prod_prod_type]
  change (Measure.pi fun _ : ι=> volume) (Set.univ.pi U)=_; rw [Measure.pi_pi];
  apply prod_congr rfl; intro i _; exact Measure.pi_pi ..

/-- shift & scale via full Pi. -/
def blast (g : ℝˣ) (z : ι→ℝ) : (ι→ℝ)≃ᵐ(ι→ℝ) :=
    ((Homeomorph.smul g).trans (Homeomorph.addLeft z)).toMeasurableEquiv

lemma preserving_blast (g : ℝˣ) (hg : 0<(g:ℝ)) (z : ι→ℝ) : MeasurePreserving
    (blast g z) (ENNReal.ofReal ((g:ℝ)^Fintype.card ι) • volume) volume := by
  let q : ℝ := g
  let F : (ι→ℝ) →ₗ[ℝ] (ι→ℝ) := q • LinearMap.id
  let u := q ^ Fintype.card ι
  have hu : 0<u := pow_pos hg _
  have ht : LinearMap.det F=u := by unfold F u; rw [LinearMap.det_smul,Module.finrank_pi,LinearMap.det_id,mul_one]
  have he : Measure.map F volume=ENNReal.ofReal u⁻¹ • (volume : Measure (ι→ℝ)) := by
    rw [Real.map_linearMap_volume_pi_eq_smul_volume_pi, ht, abs_of_pos (inv_pos.mpr hu)]
    rw [ht]; exact hu.ne'
  let f:= (Homeomorph.smul (α:=ι→ℝ) g).toMeasurableEquiv
  have hF : (⇑f)=F := rfl
  have hf : MeasurePreserving f (ENNReal.ofReal u • volume) volume := by
    refine ⟨f.measurable,?_⟩
    rw [hF, Measure.map_smul,he,smul_smul, ← ENNReal.ofReal_mul hu.le,mul_inv_cancel₀ hu.ne', ENNReal.ofReal_one,one_smul]
  have hh := measurePreserving_add_left (volume:Measure (ι→ℝ)) z
  exact hh.comp hf

namespace Coat
variable (X : Coat T F)

abbrev Speck := {i : Tubular f G // X.Hot i.1}
abbrev Vacant := {i : Tubular f G // ¬ X.Hot i.1}
def shiftP : X.Speck≃(X.Signal × G.ColorIndex) where
  toFun := fun i=> (⟨⟨i.val.1,i.2.1⟩,i.2⟩,i.val.2)
  invFun := fun i=> ⟨(i.1.val.val,i.2),i.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def tunes : (X.Speck→ℝ)≃ᵐ(X.Signal→G.Color) :=
    ((MeasurableEquiv.piCongrLeft (fun _ => ℝ) X.shiftP).trans (MeasurableEquiv.curry _ _ ℝ)).trans
      (MeasurableEquiv.piCongrRight fun _=> MeasurableEquiv.toLp 2 _)

lemma preserves_tunes : MeasurePreserving X.tunes := by
  let e:= MeasurableEquiv.piCongrLeft (fun _=>ℝ) X.shiftP
  let f:= MeasurableEquiv.curry X.Signal G.ColorIndex ℝ
  let h:= MeasurableEquiv.piCongrRight fun _ : X.Signal=> MeasurableEquiv.toLp 2 (G.ColorIndex→ℝ)
  have he : MeasurePreserving e := measurePreserving_piCongrLeft (fun _=>volume) X.shiftP
  have hf : MeasurePreserving f := preserving_curry ..
  have hh : MeasurePreserving h := measurePreserving_pi _ _ (fun i : X.Signal=>
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp G.ColorIndex).symm)
  exact hh.comp (hf.comp he)

theorem tunes_val (w) (p) (i : X.Signal) (j : G.ColorIndex) (he : X.shiftP p=(i,j)) :
    X.tunes w i j=w p := by
  change ((MeasurableEquiv.piCongrLeft (fun _=>ℝ) X.shiftP) w (i,j))=w p
  rw [← he,MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply_apply]

/-- Air split. -/
def partB : Air f G≃ᵐ((X.Speck→ℝ) × (X.Vacant→ℝ)) :=
    (MeasurableEquiv.toLp 2 _).symm.trans (MeasurableEquiv.piEquivPiSubtypeProd (fun _=> ℝ) _)
lemma partP : MeasurePreserving X.partB := (volume_preserving_piEquivPiSubtypeProd (fun _=>ℝ) (fun i:Tubular f G=> X.Hot i.1)).comp
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp _)

lemma arised_size : X.arised.card=Fintype.card X.Speck := by
  rw [Fintype.card_congr X.shiftP,Fintype.card_prod,Fintype.card_congr X.advance,X.count_dots,Fintype.card_coe]

def vacancies : X.Vacant≃X.dozing where
  toFun := fun i=> ⟨i.1,mem_filter.mpr ⟨mem_univ _,i.2⟩⟩
  invFun := fun i=> ⟨i.1,(mem_filter.mp i.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
end Coat
end YM.ConnectedActivityE6
