import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Scale
import YM.Next.MAXWELL.Caps
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Colors
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Reconstruct
import YM.Push.CUTOFF_PROJECTORS.Quotient




/-!
# The section on which to take the actual Xi coefficients

Use the same projection convention and frame. Choose representatives of the
**free** basis that transform together, to respect signed letters even when a
letter is not mapped to a single basis element. The section carries the unit
precisely and respects engineering *and* slot dilations. Does NOT say
Reader.xi sends this to the retained cutoff complement.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CorrectedLift
open Function Lattice Wilson Labels RG Cells Source Filter Extraction
open Push.Corrected Push.CutoffProjectors
open scoped Topology BigOperators
variable {G : Gauge} {C : Family G} {S : Table C.book} {d m k N p : ℕ}

lemma scaled_pair (F : Frame G d) (t : ℝ) (x y : F.Coeff) :
    pair F (F.scaled t x) y = pair F x (F.scaled t y) := by
  rw [pair_formula,pair_formula]; refine Finset.sum_congr rfl fun i _ => ?_
  rw [turn,← F.scaling,← F.scaling]
  simp only [Frame.scaled_apply,star_mul',Complex.star_def,Complex.conj_ofReal]; ring

lemma zoom_pair (F : Frame G d) (t : ℝ) (x y : F.Coeff) :
    pair F (zoom F t x) y = pair F x (zoom F t y) := by
  rw [pair_formula,pair_formula]; refine Finset.sum_congr rfl fun i _ => ?_
  rw [turn,zoom_turn,zoom_turn]
  simp only [zoom,LinearMap.coe_mk, AddHom.coe_mk,star_mul',Complex.star_def,Complex.conj_ofReal]; ring

lemma read_zoom (J : Jet G) (F : Frame G d) (t : ℝ) (x : F.Coeff) :
    Labels.read J (F.coords.symm (zoom F t x)).val = Labels.read (scaleJet J t) (F.coords.symm x).val := by
  obtain ⟨x,rfl⟩ := F.coords.surjective x
  rw [LinearEquiv.symm_apply_apply]
  rw [← F.basis.sum_repr x]; simp only [map_sum,map_smul,AddSubmonoidClass.coe_finsetSum,Submodule.coe_smul_of_tower]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [zoom_pure F t _ (F.pure i),map_smul,LinearEquiv.symm_apply_apply,
    ProjectorNext.Calibration.read_weight (F.pure i),Submodule.coe_smul_of_tower,map_smul]
  simp [Complex.real_smul]

lemma zoom_equation (F : Frame G d) (t : ℝ) (x : F.Coeff) (hx : x∈equationSpace F) :
    zoom F t x ∈ equationSpace F := by
  rw [equation_iff] at hx ⊢
  intro X
  rw [read_zoom]; have hu := hx fun i => (t^(i+2)) • X i
  simp_rw [map_smul] at hu; exact hu

lemma freeKernel (C : Family G) (d : ℕ) : (Cells.standard C).null d = equationSpace (C.labels.level d) :=
    (free_null d (Maxwell.Free.no_residual G d)).symm

private lemma freeRet {T : Frame G d} (K : Submodule ℂ T.Coeff) (D : T.Coeff →ₗ[ℂ] T.Coeff)
    (hm : ∀ x∈K, D x ∈ K) (he : ∀ x y, pair T (D x) y=pair T x (D y)) (x) :
    retain T K (D x) = D (retain T K x) := by
  apply eq_retain
  · rw [normal_iff]; intro y hy
    rw [← he]; exact (normal_iff ..).mp (retain_mem T K x) _ (hm _ hy)
  rw [← map_sub]; exact hm _ (removed T K x)

variable (C) in
lemma free_scaled (t : ℝ) (x : C.label d) :
    retain _ ((Cells.standard C).null d) ((C.labels.level d).scaled t x) =
      (C.labels.level d).scaled t (retain _ ((Cells.standard C).null d) x) := by
  let F := C.labels.level d
  change retain F _ _=F.scaled t (retain F _ _)
  rw [freeKernel]
  exact freeRet _ _ (fun _ he => scaled_mem _ t he) (scaled_pair F t) _

variable (C) in
lemma free_zoom (t : ℝ) (x : C.label d) :
    retain (C.labels.level d) ((Cells.standard C).null d) (zoom (C.labels.level d) t x) =
      zoom _ t (retain _ ((Cells.standard C).null d) x) := by
  let F := C.labels.level d
  change retain F _ _=zoom F t (retain F _ _)
  rw [freeKernel]
  exact freeRet _ _ (zoom_equation F t) (zoom_pair F t) _

private lemma same_zero (C : Family G) (d : ℕ) :
    (Maxwell.standard C.labels).scalar d = (C.labels.level d).e0 := by
  simp [Maxwell.standard,Register.scalar,Register.coord]; exact one_smul ..

private lemma scaled_scalar (F : Frame G d) (x : F.Coeff) : F.scaled 0 x = x 0 • F.e0 := by
  ext1 i
  by_cases h : i=0
  · subst i; simp [F.zero_degree,Frame.e0]
  simp [Frame.e0,h,(F.factors_pos i h).ne']

lemma unit_normal (C : Family G) (d : ℕ) : (C.labels.level d).e0 ∈
    normal (C.labels.level d) ((Cells.standard C).null d) := by
  let F := C.labels.level d
  let T := Cells.standard C
  have he (v) (hv : v∈T.null d) : F.scaled 0 v = 0 := by
    have hu : F.scaled 0 v ∈ T.null d := by
      rw [show T.null d=equationSpace F from freeKernel ..] at *
      exact scaled_mem F _ hv
    rw [scaled_scalar] at *
    let u := (Maxwell.standard C.labels).scalar d
    have hA : v 0 • u ∈ T.null d := by rw [show u=F.e0 from same_zero ..]; exact hu
    have ht : T.project d (v 0 • u)=0 := (Submodule.Quotient.mk_eq_zero (T.null d)).mpr hA
    rw [map_smul, smul_eq_zero] at ht
    exact smul_eq_zero.mpr (Or.inl (ht.resolve_right (T.alive d (Maxwell.table_regular _))))
  refine (Push.CutoffProjectors.normal_iff _ _ _).2 fun v hv => ?_
  change pair F v F.e0=_
  have hh := scaled_pair F 0 v F.e0
  rw [F.scaled_unit, he v hv] at hh; rw [← hh]; simp [pair]

/-- Canonical equivariant section to the reference-coordinate copy. -/
def ladder (C : Family G) (d : ℕ) : (Cells.standard C).Field d →L[ℂ] C.label d :=
    (((Cells.standard C).null d).liftQ (retain (C.labels.level d) ((Cells.standard C).null d)).toLinearMap
      (by change _ ≤ LinearMap.ker (retain _ _).toLinearMap; rw [retain_ker])).toContinuousLinearMap

variable (C) in
lemma ladder_on (x : C.label d) : ladder C d ((Cells.standard C).project d x)=
    retain (C.labels.level d) ((Cells.standard C).null d) x := rfl

lemma ladder_reads (x : (Cells.standard C).Field d) : (Cells.standard C).project d (ladder C d x)=x := by
  obtain ⟨x,rfl⟩ := (Cells.standard C).onto d x
  rw [ladder_on, eq_comm,← sub_eq_zero, ← map_sub]
  exact (Submodule.Quotient.mk_eq_zero _).2 (removed ..)

@[simp] lemma ladder_unit (C : Family G) (d) : ladder C d ((Cells.standard C).unit d)=(C.labels.level d).e0 := by
  rw [Table.unit,same_zero,ladder_on]; exact (retain_fix _ _).mpr (unit_normal C d)

theorem ladder_spin (H : (Cells.standard C).RealSpin) (s : Signed) (x : (Cells.standard C).Field d) :
    ladder C d ((Cells.standard C).mirror H d s x)=turn (C.labels.level d) s (ladder C d x) := by
  obtain ⟨x,rfl⟩ := (Cells.standard C).onto d x
  rw [Table.mirror_project,ladder_on,ladder_on]
  exact retain_turn _ _ (fun s _ he => (Cells.standard C).move_null H s d he) s _

theorem ladder_conj (H : (Cells.standard C).RealSpin) (x : (Cells.standard C).Field d) :
    ladder C d ((Cells.standard C).conj H d x)=star (ladder C d x) := by
  obtain ⟨x,rfl⟩ := (Cells.standard C).onto d x
  rw [Table.conj_project,ladder_on,ladder_on]
  exact retain_star _ _ (fun _ hx => (Cells.standard C).real_null H d hx) _
end YM.Further.CorrectedLift
