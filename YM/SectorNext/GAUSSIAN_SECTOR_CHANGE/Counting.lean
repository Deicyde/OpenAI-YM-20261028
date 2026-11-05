import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Gaussian
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Haar



set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Counting volume of log arrays

Link price uses Haar chart on *each* `G.Color`. Bind this with the
Gaussian's Euclidean price on the keys, and with Lie basis extraction.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.SectorChange
open Function Filter Set MeasureTheory Lattice Wilson RG Precision Metric Matrix WithLp Gaussian
open scoped Topology ENNReal BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {ι θ : Type} [Fintype ι] [Fintype θ]

def fibres : Vec (ι × θ) ≃ᵐ (ι → Vec θ) where
  toFun := curry
  invFun := uncurry
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := by
    change Measurable (fun x : Vec (ι × θ) => fun i j => x (i,j)); fun_prop
  measurable_invFun := by
    change Measurable (fun x : ι → Vec θ => fun i : ι × θ => x i.1 i.2); fun_prop

lemma fibre_volume : MeasurePreserving (fibres (ι:=ι) (θ:=θ)) volume volume := by
  suffices h : MeasurePreserving (fibres (ι:=ι) (θ:=θ)).symm volume volume by exact h.symm
  refine ⟨fibres.symm.measurable, Eq.symm (Measure.pi_eq (μ:=fun _ : ι × θ => (volume : Measure ℝ)) (fun s hs => ?_))⟩
  rw [Measure.map_apply fibres.symm.measurable (MeasurableSet.univ_pi hs)]
  rw [show fibres.symm ⁻¹' (Set.univ.pi s) = Set.univ.pi (fun i => Set.univ.pi (fun j => s (i,j))) from ?_]
  · simp_rw [volume_pi_pi, Fintype.prod_prod_type]
  ext x
  simp [fibres, Set.mem_pi, uncurry]

abbrev Prices (G : Gauge) (ι : Type) := Vec (ι × G.ColorIndex)

def colors : Prices G ι ≃ₗ[ℝ] LogArray G ι where
  toFun := fun v i => toLp 2 (curry v i)
  invFun := fun a => uncurry (fun i => ofLp (a i))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def gaugeCount : Prices G ι ≃L[ℝ] LogArray G ι := colors.toContinuousLinearEquiv

def tape : Prices G ι ≃ᵐ LogArray G ι := gaugeCount.toHomeomorph.toMeasurableEquiv

lemma tape_ap (v : Prices G ι) (i : ι) (j : G.ColorIndex) : tape v i j = v (i,j) := rfl
lemma tape_read (a : LogArray G ι) (i : ι) (j : G.ColorIndex) : tape.symm a (i,j) = a i j := rfl

lemma tape_volume : MeasurePreserving (tape (G:=G) (ι:=ι)) volume volume :=
  (measurePreserving_pi (μ:=fun _ : ι => (volume : Measure (Vec G.ColorIndex)))
    (ν:=fun _ : ι => (volume : Measure G.Color)) (fun _ => PiLp.volume_preserving_toLp G.ColorIndex)).comp fibre_volume

variable [DecidableEq ι]

lemma price_square (v : Prices G ι) : v ⬝ᵥ v = ∑ i, ‖tape v i‖^2 := by
  simp_rw [EuclideanSpace.real_norm_sq_eq,dotProduct,Fintype.sum_prod_type]
  simp_rw [sq]; rfl

def axisPrice (i : ι × G.ColorIndex) : LogArray G ι := tape (Pi.single i (1:ℝ))

lemma on_axis (i : ι × G.ColorIndex) : axisPrice i = Pi.single i.1 (EuclideanSpace.basisFun G.ColorIndex ℝ i.2) := by
  classical
  ext j a
  by_cases h : j=i.1
  · subst j
    rcases i with ⟨i,b⟩
    change Pi.single (i,b) (1:ℝ) (M:=fun _ => ℝ) (i,a) = _
    by_cases hi : a=b
    · subst a; simp
    simp [Pi.single_apply, hi,Ne.symm hi]
  change Pi.single i (1:ℝ) (M:=fun _ => ℝ) (j,a) = _
  have he : i ≠ (j,a) := fun e => h (congr_arg Prod.fst e).symm
  simp [Pi.single_apply, h, Ne.symm h, he, Ne.symm he]

/-- Link prices under the actual covariance (specified on these links'
keys). -/
def linkCloud (C : Table (ι × G.ColorIndex)) : Measure (LogArray G ι) := (cloud C).map tape



instance (C : Table (ι × G.ColorIndex)) : IsProbabilityMeasure (linkCloud C) :=
  Measure.isProbabilityMeasure_map (tape.measurable.aemeasurable)





variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Same convention as E `(2πg²)^(n_a/2)*sqrt(det C)`. -/
def chartCost (C : Table (ι × G.ColorIndex)) (g : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi * g^2)) ^ Fintype.card (ι × G.ColorIndex) * Real.sqrt C.det

lemma chartCost_eq (C : Table (ι × G.ColorIndex)) {g : ℝ} (hg : 0<g) :
    chartCost C g = g ^ Fintype.card (ι × G.ColorIndex) * coat C := by
  unfold chartCost coat Gaussian.dome
  rw [Real.sqrt_mul (by positivity),Real.sqrt_sq hg.le,mul_comm _ g,mul_pow,mul_assoc]

lemma chartCost_pos (C : Table (ι × G.ColorIndex)) (h : C.PosDef) {g : ℝ} (hg : 0 < g) : 0 < chartCost C g := by
  rw [chartCost_eq _ hg]
  exact mul_pos (pow_pos hg _) (coat_pos h)

def displaced (m : Prices G ι) (g : ℝ) (x : Prices G ι) : LogArray G ι := tape (m + g • x)

lemma at_price (C : Table (ι × G.ColorIndex)) (h : C.PosDef) {g : ℝ} (hg : 0 < g) (m : Prices G ι)
    (f : LogArray G ι → X) :
    let u := fun x : Prices G ι => Real.exp (force C x / 2) • f (displaced m g x)
    (Integrable f ↔ Integrable u (cloud C)) ∧ (∫ a, f a) = chartCost C g • ∫ x, u x ∂cloud C := by
  intro u
  obtain ⟨hp,ht⟩ := gauged h hg m (f ∘ tape)
  rw [← (tape_volume (G:=G) (ι:=ι)).integral_comp' f]
  rw [chartCost_eq _ hg]
  exact ⟨((tape_volume (G:=G) (ι:=ι)).integrable_comp_emb tape.measurableEmbedding).symm.trans hp,ht⟩

end YM.Next.SectorChange
