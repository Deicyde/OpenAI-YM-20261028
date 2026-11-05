import YM.Push.LOOP_COEFFICIENT.Block.Glow
import YM.Push.LOOP_COEFFICIENT.Block.Rep
import YM.Push.LOOP_COEFFICIENT.Block.Reserve
import YM.Push.LOOP_COEFFICIENT.Block.Service
import YM.Push.LOOP_COEFFICIENT.Fine.Margin

/-!
# District-scale ingredients and flat comparison identification
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Block
open Matrix Function Filter Set Lattice Laurent Bloch RG Precision Exterior Complex Wilson Paths Continuum Fine Portal
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {L c f : Side} {σ η A Λ e μ : ℝ}
abbrev Lights (G : Gauge) (L : Side) := Profiles L (Axes G) (Axes G)
variable (T : Lights G L) (W : PathData G) (p : Clip)

def slab := induce (localVertex W p) T
def slope := induce (root G) T
def spindle := ((slope T).transpose.mul (slope T)).add (Vertex.id.smul ((((L.val:ℝ)⁻¹)^2:ℝ):ℂ))
def worm := (spindle T).inv.smul ((((L.val:ℝ)⁻¹)^2:ℝ):ℂ)
def mill := (worm T).roll.mul (slope T).transpose
def ash := ((duplicate (worm T)).pow depth).smul ((((L.val:ℝ)⁻¹)^2:ℝ):ℂ)
def studio := ((slab T W p).add ((mill T).transpose.mul (mill T))).add (ash T)

lemma spindle_rep : Rep (Tube η) (spindle T) (gauged G (L.val:ℝ)⁻¹) := (((Rep.induce T (root G)).transpose (fun _ h => tube_neg h) (fun _ hq l => rep_opposite (root_lit _ _) hq l)).mul (.induce T (root G))).add (Rep.id.smul _)
variable {W p} {H : Bed}
lemma spindle_unit (hL : Odd L.val) (h : Holds G H η e) {q : Momentum} (hq : q∈Tube η) (l : Site L) : IsUnit ((gauged G (L.val:ℝ)⁻¹).base (aliasAt q l)) := (alias_holds hL h hq l).2.unit (by have := h.lower; have := energy_pos L q l; positivity)







variable {T} in
lemma spire_grows (hL : Odd L.val) (h : Reserve W p η e σ A) (hσ : η/L.val ≤ σ) (hf : Flow T η) : Grows (slab T W p) η ∧ Grows (slope T) η ∧ Grows (spindle T) η ∧ Grows (worm T) η ∧ Grows (mill T) η ∧ Grows (ash T) η ∧ Grows (studio T W p) η := by
  obtain ⟨H,hH,-⟩ := h.floor
  have hs : Grows (slab T W p) η := Grows.of_lit (induce_lit (h.packet.toLit.mono hσ) hf)
  have h' : Grows (slope T) η := Grows.of_lit (induce_lit (root_lit ..) hf)
  have ht : Grows (spindle T) η := ((h'.transpose).mul h').add (Grows.id.smul _)
  have hw : Grows (worm T) η := (ht.inv (fun q hq => (spindle_rep T).unit hq (spindle_unit hL hH hq))).smul _
  have hm : Grows (mill T) η := (Grows.id.add (hw.upper depth)).mul h'.transpose
  have ha : Grows (ash T) η := (hw.duplicate.pow depth).smul _
  exact ⟨hs,h',ht,hw,hm,ha,(hs.add (hm.transpose.mul hm)).add ha⟩

variable (G c)
lemma regulation_symm (U : Config G f) (μ : ℝ) : (regulation μ U).transpose = regulation μ U := by simp [regulation,tail,transpose_sum, transpose_pow,dressing,ghost, transpose_nonsing_inv,transpose_mul]
variable {G c}
open scoped Matrix.Norms.Frobenius
variable {g : Ratio c f} {B : Matrix (BondKey G f) (BondKey G c) ℝ} {Y : Lights G g.count} (hY : Projects g (linksGrid G f) (linksGrid G c) (cmat B) Y)
include hY
local notation "LL" => linksGrid G c
local notation "CC" => coarseLinks G g
local notation "DD" => coarseNodes G g
local notation "μ₀" => ((g.count.val:ℝ)⁻¹)
lemma slab_models (h : W.Bounds p σ A Λ) : Models LL CC CC (fun z => cost (mainTerm p W) (vary 1 (B *ᵥ z))) (slab Y W p) := induce_models (F:=BondKey G f) (Z:=cost (mainTerm p W) ∘ vary 1) ⟨smooth_cost (U:=vary 1) (f:=fun _ => mainTerm p W) (Work.F02.mainTerm_contDiffAt h ((vary_diff.comp contDiffAt_fst).vary contDiffAt_snd)),local_synced h⟩ hY
lemma slope_models : Models LL CC DD (fun z => R_g (vary 1 (B *ᵥ z))) (slope Y) := induce_models (root_models G f) hY
lemma spindle_models : Models LL DD DD (fun z => ghost μ₀ (vary 1 (B *ᵥ z))) (spindle Y) := ((slope_models hY).transpose.mul (slope_models hY)).add (Models.identity.smul _)
lemma worm_models : Models LL DD DD (fun z => dressing μ₀ (vary 1 (B *ᵥ z))) (worm Y) := ((spindle_models hY).inv (fun _ _ hp => routed_invertible ((spindle_models hY).sync.base hp) (cmat_unit (ghost_pos _ _ (inv_pos.mpr (side_pos _)) |>.isUnit)))).smul _
lemma mill_models : Models LL DD CC (fun z => regulation μ₀ (vary 1 (B *ᵥ z)) * (R_g (vary 1 (B *ᵥ z))).transpose) (mill Y) := (worm_models hY).roll.mul (slope_models hY).transpose
lemma ash_models : Models LL CC CC (fun z => μ₀^2 • ((parallel (dressing μ₀ (vary 1 (B *ᵥ z))))^depth)) (ash Y) := ((duplicate_models (worm_models hY)).pow depth).smul _

end YM.Push.Loops.Block
