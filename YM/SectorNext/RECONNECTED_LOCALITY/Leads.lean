import YM.Analysis.Polydisc
import YM.Next.FOUNDATIONS.Regular


set_option warningAsError false

/-!
# Subtracting off regular slots before mask
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Reconnect
namespace Snip

open Function Filter Wilson RG Lattice Finset Next.Foundations
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical

variable {G : Gauge} {c : Side} {P : BudgetPoint}
variable {Y : Support c} {f g : Config G c → ℝ} {o : Site c} {a b : ℝ}



lemma subtract (h : P.Regular Y f) (he : P.Regular Y g) : P.Regular Y (fun i => f i-g i) := by
  have ht U (hU : Healthy P.threshold Y U) : ContDiffAt ℝ (P.order : WithTop ℕ∞)
      ((fun i => f i-g i) ∘ increment U) 0 := (h.smooth U hU).sub (he.smooth U hU)
  exact ⟨fun U V hg => congr_arg₂ (· - ·) (h.sites _ _ hg) (he.sites _ _ hg), h.borel.sub he.borel,
    fun s U => congr_arg₂ (· - ·) (h.symmetry _ _) (he.symmetry _ _), ht,fun U hU k _ hv => left_has _ hv (ht U hU)⟩



lemma adjoin (h : P.Regular Y f) (he : P.Regular Y g) : P.Regular Y (fun i => f i+g i) := by
  have ht U (hU : Healthy P.threshold Y U) : ContDiffAt ℝ (P.order : WithTop ℕ∞)
    ((fun i => f i+g i) ∘ increment U) 0 := (h.smooth U hU).add (he.smooth U hU)
  exact ⟨fun U V hg => congr_arg₂ (· + ·) (h.sites _ _ hg) (he.sites _ _ hg), h.borel.add he.borel,
    fun s U => congr_arg₂ (· + ·) (h.symmetry _ _) (he.symmetry _ _), ht,fun U hU k _ hv => left_has _ hv (ht U hU)⟩

lemma scaled (c₀ : ℝ) (h : P.Regular Y f) : P.Regular Y (fun i => c₀*f i) := by
  have ht U (hU : Healthy P.threshold Y U) : ContDiffAt ℝ (P.order : WithTop ℕ∞)
      ((fun i => c₀*f i) ∘ increment U) 0 := (h.smooth U hU).const_smul c₀
  refine ⟨fun U V hg => congr_arg (c₀*·) (h.sites _ _ hg),measurable_const.mul h.borel,
    fun s U => congr_arg (c₀*·) (h.symmetry _ _),ht, fun U hU k _ hv => left_has _ hv (ht U hU)⟩





lemma swell (h : P.Regular Y f) {X : Support c} (hx : Y⊆X) : P.Regular X f :=
  ⟨fun u v hh => h.sites u v (agrees_mono hh (Finset.coe_subset.mpr hx)),h.borel,h.symmetry,
    fun x hh => h.smooth x (Finset.disjoint_of_subset_left hx hh),fun x hh => h.hasDerivs x (Finset.disjoint_of_subset_left hx hh)⟩





-- Needed for identity & jets at every stored address. -/
lemma all_white (G : Gauge) (P : BudgetPoint) (Y : Support c) : Healthy P.threshold Y (1 : Config G c) := by
  rw [Healthy, Finset.disjoint_left]; intro x _ hx
  obtain ⟨p,_,he⟩:=(RG.flags_spec ..).1 hx
  simp only [faceValue, square, travel, Lattice.Step.pos_read, Lattice.Step.neg_read,Pi.one_apply, inv_one,one_mul,
    G.chord_one] at he
  exact he.not_ge P.threshold_pos.le









lemma still (d : ℝ) : P.Regular Y (fun _ : Config G c => d) := by
  exact ⟨fun _ _ _ => rfl,measurable_const,fun _ _ => rfl,fun _ _ => contDiffAt_const,
    fun U _ A l he => left_has A he contDiffAt_const⟩












end Snip
end YM.SectorNext.Reconnect
