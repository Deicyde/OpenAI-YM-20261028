import Mathlib
import YM.AnalyticBridge.SECTOR_AFFINE_JETS.Directions
import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Inverse
import YM.Extra.MULTISOURCE_TRAJECTORIES.Probes
import YM.Extra.WEAK_SCALING_ACTLAW.Divergence
import YM.Next.MULTISOURCE.Curves
import YM.Next.WARD_BIN.Rays
import YM.Progress.DIRECTED_RECIPE.Economy
import YM.Progress.DIRECTED_RECIPE.Symmetry
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Models
import YM.Push.CORRECTED_COLUMNS.Funding
import YM.Push.GRID_APPROXIMATION.AttachDefs
import YM.Push.RELAY_MARK.Span
import YM.Push.STRESS_FLUX.Ward
import YM.UVNext.COMMON_GRADE_ASSEMBLY.Current


/-!
# Converting the actual scaled PriceCoords affine jets to ordered left derivatives

`Quote` below uses the Counting/Color pins of the ordered resolution.
Price external locations at the **output** period. Pay all repeated
slots (including on a single link of a coalesced chart derivative),
with the same branch data in all derivatives. Keep the coupling-band
normalization external to these conversions. No claims of differentiability
of the sector flags; functions in this file are unmasked extensions, and
conversions are used on the appropriate germs. .
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.OrderedAffine2B

open Function Filter Lattice Wilson RG Precision Pressure Exterior Tree
open WardBin.Lies FreeResolvent FreeResolvent.Affine TestD
open AnalyticBridge.SectorAffine SelectedOrderedKernels
open Push.Uniform (bolt)
open scoped Topology ContDiff InnerProductSpace BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c : Side}

/-- The two pin alphabets in the accepted price ports are the SAME
coordinates, reindexed (no weighted/cochain basis here). -/
def pins (G : Gauge) (c : Side) : raw G c ≃ Coord G c where
  toFun w := (SelectedOrderedKernels.edge w,w.2.2)
  invFun w := hue w.1 w.2
  left_inv w := hue_edge w
  right_inv w := Prod.ext (edge_hue w.1 w.2) rfl

/-- Transparent CLM to map chart inputs without comparing Euclidean
and sup norms over the period. -/
def pricing (G : Gauge) (c : Side) : Vec G c 1 →L[ℝ] PriceCoords G c :=
  AnalyticBridge.SectorAffine.reader G c ∘L (paint G c).toContinuousLinearMap

lemma pricing_increment (V : Config G c) (u : Vec G c 1) :
    AnalyticBridge.SectorAffine.field V (pricing G c u) = increment V (paint G c u) :=
  reader_field V _

lemma pricing_at (u : Vec G c 1) (w : raw G c) : pricing G c u (pins G c w)=u w := by
  change paint G c u (SelectedOrderedKernels.edge w) w.2.2 = u w
  rw [paint_apply,hue_edge]

lemma pricing_ray (w : raw G c) : pricing G c (ray G c w) = bolt (pins G c w) := by
  funext i; obtain ⟨i,rfl⟩ := (pins G c).surjective i
  rw [pricing_at]; simp [ray,bolt,Pi.single_apply]



variable {j k : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {V : Config G c}
    {t : ℝ} {F : Config G c → E}

/-- Use this also at scale 1 for the D/Gram ports. `t` here in
applications on F0 is temp x, i.e. the *coarse* threshold. -/
def scaled (t : ℝ) (F : Config G c → E) (V : Config G c) :=
    fun u : PriceCoords G c => F (AnalyticBridge.SectorAffine.field V (t • u))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma chart_over (ht : t ≠ 0) : SelectedOrderedKernels.over F V = scaled t F V ∘ ⇑(t⁻¹ • pricing G c) := by
  funext u; change F (increment V (paint G c u))=F (AnalyticBridge.SectorAffine.field V (t • (t⁻¹ • pricing G c u)))
  rw [smul_smul,mul_inv_cancel₀ ht,one_smul,pricing_increment]

lemma chart_over_smooth (ht : t ≠ 0) (h : ContDiffAt ℝ j (scaled t F V) 0) :
    ContDiffAt ℝ j (SelectedOrderedKernels.over F V) 0 := by
  rw [chart_over ht]; exact ((map_zero (t⁻¹ • pricing G c)).symm ▸ h).comp _ (ContinuousLinearMap.contDiff _).contDiffAt

lemma chart_over_jet (w : Pins G c j) (ht : t ≠ 0) (h : ContDiffAt ℝ j (scaled t F V) 0) :
    jet (ray G c) (SelectedOrderedKernels.over F V) (List.ofFn w) 0 =
      t⁻¹ ^ j • jet bolt (scaled t F V) (List.ofFn (pins G c ∘ w)) 0 := by
  let L := t⁻¹ • pricing G c
  simp_rw [Stars.list_result]
  rw [chart_over ht,Push.Uniform.iter_lin_at (show ContDiffAt ℝ j (scaled t F V) (L 0) by rwa [map_zero]),
    map_zero, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  show iteratedFDeriv ℝ j (scaled t F V) 0 (fun i => t⁻¹ • pricing G c (ray G c (w i))) = _
  simp_rw [pricing_ray]; rw [ContinuousMultilinearMap.map_smul_univ]
  simp [Function.comp_def]

lemma price_locations (d : ℝ) (o : Site c) (w : Pins G c j) :
    (AnalyticBridge.SectorAffine.marks G c d).pay (List.ofFn (pins G c ∘ w)) o = due (native c) Prod.fst d o w := by
  rw [due, Stars.pays, Stars.pays]; rfl

lemma count_volume (G : Gauge) (c : Side) {d : ℝ} (hd : 0 < d) :
    (native c).Volume (Prod.fst ∘ SelectedOrderedKernels.edge (G:=G)) d (paramPrice G d) := by
  exact (param_volume G c hd).comp (pins G c).injective



end YM.PhysicalNext.OrderedAffine2B
