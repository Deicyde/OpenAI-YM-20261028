import YM.Further.THRESHOLD_SOURCE_RESTART.Omissions
import YM.Further.THRESHOLD_SOURCE_RESTART.Wells
/-!
# Exact pre-head attachment, including on failed masks

Move each assigned atom from its actual small mask to the reading on one
large common mask. At exactly the same time, keep the multiplier also on
failed large masks in every occupied cell. Supports contain all the old
reads and inventories. In this form an arbitrary countable assignment is
admitted; complements contribute only when blocked by some old K, without
summing over which K. The free cumulant subtraction step will be separate and
applies also to this *already corrected for alignment* K gas.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.ThresholdSourceRestart
open Function Filter Set MeasureTheory Wilson RG Lattice Marker Overlay
open Push.Corrected Prepare Width
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical

variable {I V α : Type*} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]
    {G : Gauge} {n : Side} {P : Rep G n} {o : I × V → Site n}
variable {F : Atoms P.p (Marks.all (I×V)) o G α}

namespace Dock
variable [Countable α]
variable {s p : ℝ} {M : ℕ} {a : ℝ} {w : I → ℝ} {R : Census I} {y : I→Site n}
variable (d : Dock P y R α) (H : Original P y R)


end Dock

namespace Wells
variable (W : Wells F)

def patch (i : α) : Support n := Option.elim (W.host i) (F.sites i) W.area

def slurry (i : α) (U : Config G n) := if W.host i=none ∨ Healthy P.p.threshold (W.patch i) U then 0
    else masked P.p.threshold (F.sites i) (F.H i) U

lemma poured (i : α) : F.sites i ⊆ W.patch i := by unfold patch; cases h : W.host i with
  | none => rfl
  | some a => exact W.keeps i a h

/-- Same addresses on all U. Zero for unassigned terms in this
supplement (their exponent stays as is in `orphan`). -/
def silt : Dock P o (Marks.all (I×V)) α where
  patch := W.patch
  warm i := by
    obtain ⟨x,hx⟩ := F.proper i; exact ⟨o x,W.poured i (F.pin i x hx)⟩
  contact i j := ∃ x∈W.patch i,x∈oldSites P j
  meets _ _ := id
  letter i U := Poly.send (F.tag i) (W.slurry i U)
  hot i U := by rw [Poly.part_send,if_neg (fun h => (F.proper i).ne_empty (congr_arg Subtype.val h.symm))]
  reads i := by
    have he : LocalCharge P.p o (W.patch i) (F.portion i) := (hot_mask (F.sites i) _ _ _ (F.footprint i)
      (F.gauge i) (F.borel i) (F.pin i)).widen (W.poured _)
    constructor
    · intro t U; dsimp only [slurry]; unfold Healthy; rw [gauge_flags]; split; rfl; exact he.gauge ..
    · by_cases h : W.host i=none
      · simp only [slurry,h,true_or,↓reduceIte]; exact measurable_const
      simp only [slurry,h,false_or]
      exact ((Bands.sends _).measurable).comp (Measurable.ite (healthy_closed _ _).measurableSet measurable_const (masked_measurable _ _ _ (F.borel i)))
    · intro U Y ha hv; dsimp only [slurry]; simp only [Healthy,Finset.disjoint_iff_inter_eq_empty,hv]; split
      · rfl
      exact he.reads _ _ ha hv
    intro U j hi; by_cases h : j=F.tag i
    · exact fun x hx => W.poured _ (F.pin i x (h ▸ hx))
    exact False.elim (hi (by rw [Poly.part_send,if_neg h]))



variable {U : Config G n}




variable [Countable α] {a b w κ : ℝ} {M : ℕ} (L : Original P o (Marks.all (I×V)))

omit [Countable α] in
lemma orphan_expend (h : F.Cost (fun _ => w) M a b) : W.orphan.Cost (fun _=>w) M a b := by
  obtain ⟨t,ht,H⟩ := h
  refine ⟨t,fun i => ⟨(ht _).1,fun U H => ?_⟩,H⟩
  dsimp only [orphan]; split; exact (ht _).2 _ H; simp only [Pi.zero_apply,norm_zero]; exact (ht _).1


end Wells
end YM.Further.ThresholdSourceRestart
