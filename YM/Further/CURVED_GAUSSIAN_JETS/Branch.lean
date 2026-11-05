import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Data.Set.Finite.List
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import YM.Further.CURVED_GAUSSIAN_JETS.Motion
import YM.Progress.STATIONARY_SCENES.SliceGap
import YM.Push.CUTOFF_PROJECTORS.Equations
/-!
# The ordered-address ledger on the fixed-L scheme of Mapping

Simultaneously on the same price on both matrices even before inserting
identity completions in the measure prefactor. Includes mixed left jets
and uniform absolute weighted hit prices, separately at the very same
argument before pairing any labels (triangle may lose a factor for a pair).
`x` in `meter` a coarse site; derivatives may use `Award.integrals` etc.
to reanchor. Read full and active via different `e` as needed (the latter
then `active_read`). Pollutants: Mapping conventions, BEFORE additional
source/center factors; tag-dependent changing decision SUPPORTS must still
be proved represented by the charged halos (choose m with room for ALL
such queries, never differentiate through a redecision); prices are number
bounds not a sector locality or stochastic cluster assembly proof. For
weights on full labels across sectors use the FULL universe in Hits with
blank masking of unused addresses. LHS in Hits a pure positive envelope
independent of actual x-sector V data, usable on finite subsets without any
log-of-zero rule. No path-count assumption on the periodized matrices.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 1024
noncomputable section
namespace YM.Further.CurvedGaussianJets.ChangeV
open Matrix Function Filter Jets Lattice Wilson RG Precision Push.Uniform  SectorNext.Vacuum  Tree  Progress.StationaryScenes
open Green (address)
open scoped Matrix.Norms.Frobenius BigOperators Classical Topology ContDiff
variable {I : Type} [Fintype I] [DecidableEq I] {G : Gauge} {c f : Side} {a : I → Site f} {V : Config G c} {s : Jets.Weights a} {A : Jets.Field G c I} {Q : Directions G c → Prop} {M : ℝ} {k : ℕ} {p : Prices}
lemma flat_streets (h : Street p s k Q A V M) {B : Table I} (he : Fits a p B) :
    Street p s k Q (fun _=>B) V (max p.mass M) ∧ Street p s k Q A V (max p.mass M) := by
  have hh := p.mass_pos.le.trans (le_max_left p.mass M)
  refine ⟨⟨he,fun l hl hd=>?_, h.room,Good.const _,hh⟩,⟨h.base,h.cash.mono le_rfl (le_max_right ..),h.room,h.good,hh⟩⟩
  rw [jet_const]; split_ifs with ht
  · subst l; exact (Weights.zero_order (Rows.slower he.entries (by linarith [p.speed_pos,p.speed_le] : p.speed≤p.width))).mono (le_max_left ..)
  exact Weights.zero hh


end YM.Further.CurvedGaussianJets.ChangeV
