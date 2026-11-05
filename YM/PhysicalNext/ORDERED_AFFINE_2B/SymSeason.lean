import YM.AnalyticBridge.SECTOR_AFFINE_JETS.Directed
import YM.Next.MULTISOURCE.Enclosure
import YM.PhysicalNext.ORDERED_AFFINE_2B.Halos
import YM.PhysicalNext.ORDERED_AFFINE_2B.SymShort
import YM.PhysicalNext.ORDERED_AFFINE_2B.SymWhole
import YM.Progress.DIRECTED_RECIPE.Marks
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Commission
import YM.Push.STRESS_FLUX.Surface
import YM.SectorTools.ACTUAL_SCALAR_LEDGER.Cash
import YM.UVNext.FREE_STRESS_CERTIFICATE.VRank

/-!
# Family actions on scalar sector symbols

From actual SC operands. Stays in fixed census/contract hints
throughout. The law-level rolls for the actual local input arrays,
using the Gaussian from plate. All of this without claiming the Allocation
moves -- h.Compare about the actual SAME T,Υ, positive basis, forest
symmetries under actual s,b or same forest under coarse gauge. At V even
y-laws direction orientation changed. Does not describe tree gauges on
an ambient unclipped measure. These spins need independent checks if
using in a different parcel. Budget families are quantified externally
(not assuming running these proofs establishes all-step iterations).
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.OrderedAffine2B.SymSeason
open Function Filter Lattice Wilson RG Precision Pressure Exterior Tree
open AnalyticBridge AnalyticBridge.SectorAffine AnalyticBridge.ResetIncome
open Next Next.Foundations Next.SectorChange SectorNext.Vacuum Whole
open Further Further.CurvedGaussianJets Tracks Matrix MeasureTheory Set GaussianFieldAlignment
open Push.SectorMeasure Oriented SymRows SymWhole Orthogonal Tensor
open ProjectorNext.Equivariance (HasOrderAt)
open Footprint.Padded (widen)
open scoped Topology ContDiff InnerProductSpace BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f}

open SectorTools.ActualScalar (held shellMap chartMap)
local notation "Coords" => Next.SectorChange.Prices

variable {e : Plate G S} {A A' : Stores S} {F' : Forest S.ratio} {k l : S.Choices} {V : Config G c}

/-- A' is considered with new F and permuted tag. `book` held (has
type independent of F anyway); NO equivariance used for book here.
If using a rerolled book with the new geometry, can reissue e on both
sides with that book too, affine & ledger actual computations independent
of its values! NO such claim on e.color or other ingredients of total.
-/
def reshaped (e : Plate G S) (F : Forest S.ratio) (k : S.Choices) : Plate G S := {e with forest:=F,tag:=k}
structure Spin (e : Plate G S) (A A' : Stores S) (F' : Forest S.ratio) where
  coarse : Config G c→ Config G c
  flow : Continuous coarse
  flags (V : Config G c) (t : ℝ) : A'.flags=RG.flags t (coarse V) ↔ A.flags=RG.flags t V
  box : SymRows.Box e.x A A' e.forest F'
  picks : Equiv.Perm S.Choices
  town : Equiv.Perm (Site c) -- new → OLD
  proper (i j : Site c) : separation (town i) (town j) = separation i j
  stems (i : Slots S) : SymShort.loc S (box.slots i) = town (SymShort.loc S i)
  legs (i : Bond f) : Next.SectorChange.points S (box.edges i)=town '' Next.SectorChange.points S i
  permits (V : Config G c) (j : Bool) : ColorOrtho G (Bond f)
  axes (V : Config G c) : ColorOrtho G (Slots S)
  drape : LinkArray G (Frozen A e.x e.forest) → LinkArray G (Frozen A' e.x F')
  paid : MeasurePreserving drape (piHaar G (Frozen A e.x e.forest)) (piHaar G (Frozen A' e.x F'))
  compares {v C E : ℝ} : S.patch.Branches S.kernel G → e.tube.up.Bounds e.tube.high v C E → ∀ V k,
    (∀ Y, SymRows.Test box (permits V true) (axes V) V (coarse V) k (picks k) e.tube e.chip e.d Y (drape Y)) ∧
    ∀ (hx : 120≤ radiusB e.x) j, SymWhole.Route box (permits V j) hx (Whole.stack e.tube e.x A e.forest k j V)
      (Whole.stack e.tube e.x A' F' (picks k) j (coarse V))
section issue
open Channels Locations Gauges
lemma pourY (e : Plate G S) (A : Stores S) (s : Signed) (b : Site c) : MeasurePreserving (rollY (G:=G) s b e.x A e.forest)
      (piHaar G (Frozen A e.x e.forest)) (piHaar G (Frozen (Locations.book s b A) e.x (Locations.forest s b e.forest))) := by
  let j := frozen s b A e.forest e.x
  have hj := (measurePreserving_piCongrLeft (fun _=> G.probHaar) j).symm
  let g (i : Frozen (Locations.book s b A) e.x (Locations.forest s b e.forest)) (x : G.El) := if s.flip i.val.val.2 then x⁻¹ else x
  have hg (i) : MeasurePreserving (g i) G.probHaar G.probHaar := by unfold g; split; exact G.preserve_inv; exact MeasurePreserving.id _
  have hv := (measurePreserving_pi _ _ hg).comp hj; exact hv
lemma passY (e : Plate G S) (A : Stores S) (z : Site c → G.El) : MeasurePreserving (gaugeY z e.x A e.forest)
    (piHaar G (Frozen A e.x e.forest)) (piHaar G (Frozen A e.x e.forest)) := by
  let g (i : Frozen A e.x e.forest) (v : G.El) := z (S.ratio.parent i.val.val.1)*v*(z (S.ratio.parent (i.val.val.1+step i.val.val.2)))⁻¹
  have hf i : MeasurePreserving (g i) G.probHaar G.probHaar := (measurePreserving_mul_right G.probHaar _).comp (measurePreserving_mul_left G.probHaar _)
  exact measurePreserving_pi _ _ hf

def turn (e : Plate G S) (A : Stores S) (s : Signed) (b : Site c) : Spin e A (Locations.book s b A) (Locations.forest s b e.forest) where
  coarse := pull s b
  flow := continuous_pull ..
  flags := SymStencil.flagged A s b
  box := calendar e.x A e.forest s b
  picks := (S.withinChoice s b).symm
  town := StepData.sendSites s b
  proper i j := by change separation (affine s b i) (affine s b j)=_; simp [affine]
  stems := by
    rintro ⟨q,i|i⟩
    · exact SymStencil.rooting (S:=S) s b q (.inl i.1)
    exact SymStencil.rooting (S:=S) s b q (.inr i)
  legs := moves_points s b
  permits V := SymWhole.each s b V S
  axes _ := Channels.unchanged G S
  drape := rollY s b e.x A e.forest
  paid := pourY ..
  compares h he V k := ⟨fun Y=>SymRows.turn_test (V:=V) (k:=k) (T:=e.tube) e.chip e.d Y s b h he,fun hx j=> SymWhole.turn_stack e.tube k V hx s b he h j⟩

def gaugeSpin (e : Plate G S) (A : Stores S) (p : Site c → G.El) : Spin e A A e.forest where
  coarse := Lattice.gauge p
  flow := by unfold Lattice.gauge; fun_prop
  flags V t := by rw [gauge_flags]
  box := room e.x A e.forest
  picks := Equiv.refl _
  town := Equiv.refl _
  proper _ _ := rfl
  stems _ := rfl
  legs _ := by change _ = id '' _; rw [image_id]; rfl
  permits _ := SymWhole.crest S p
  axes _ := Gauges.outRotation p
  drape := gaugeY p e.x A e.forest
  paid := passY ..
  compares h he V k := ⟨fun Y=> SymRows.gauge_test (V:=V) (k:=k) (T:=e.tube) e.chip e.d Y p h he, fun hx j=> SymWhole.gauge_stack e.tube k V hx p he h j⟩
end issue

namespace Spin
variable (p : Spin e A A' F')

abbrev L := reshaped e F' (p.picks e.tag)

abbrev profile (V : Config G c) := SymWhole.heap p.box (p.permits V true)











-- footprints and anchors. use `town` on all addresses incl halo
-- partners. H tests per signed STACK rather than site jumps. No claim
-- of ledger assigning SymCost's rates by symmetry (rates don't need
-- to be registers; consumed absolute bound in both rotated charts)




end Spin
end YM.PhysicalNext.OrderedAffine2B.SymSeason
