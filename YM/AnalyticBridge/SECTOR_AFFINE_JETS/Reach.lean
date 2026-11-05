import YM.Push.FREE_RESOLVENT.JetWindows
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Chosen

/-!
# Locality (V variable)

Numerical ranges and dependencies with x, forest, at-all-sites Stores and
k choices ALL held. No local structure on the holes assumed. Distinguish
this from locality on queries changing any of these (have to pay halo to know
seeds, flags etc), and from assuming a gap on V' that happened to agree on
a numerical stencil. The Gram itself must be compressed, not its rectangular
input truncated at the window before forming a new Gram!
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.SectorAffine

open Filter Function Set Lattice Wilson RG Precision Pressure Tree Exterior
open YM.Next.Fluctuations YM.Next.SectorChange
open YM.Next.SectorChange.Rows YM.Next.SectorChange.Wisps YM.Next.SectorChange.Schur
open YM.FreeResolvent.TestD Matrix
open scoped Topology ContDiff BigOperators InnerProductSpace Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f} {x : ℝ}

/-- Numerical locality including V-dependence at BOTH projected endpoints.
Requires no V-flag assertion. Not the full-sector-table dependence criterion. -/
structure SupportPrice {ι κ : Type} (p : ι → Site c) (q : κ → Site c)
    (D : Config G c → Matrix ι κ ℝ) (r w : ℕ) : Prop where
  inside (i j) (h : ¬ separation (p i) (q j) ≤ r) (V : Config G c) : D V i j=0
  rows (i j) {V W : Config G c} (h : AgreeNear id (p i) w V W) : D V i j=D W i j
  cols (i j) {V W : Config G c} (h : AgreeNear id (q j) w V W) : D V i j=D W i j

namespace SupportPrice
variable {ι κ : Type} {p : ι → Site c} {q : κ → Site c} {r s u w : ℕ}
    {D Q : Config G c → Matrix ι κ ℝ}













/-- Staggered windows, self entries included. -/
lemma columns [Fintype ι] [DecidableEq ι] {D : Config G c → Matrix ι ι ℝ} {W : ι → Set ι}
    (h : SupportPrice p p D r w) (hw : ∀ {i j}, j ∈ W i → separation (p i) (p j) ≤ u)
    (hv : ∀ i, i∈W i) : SupportPrice p p (fun V => per W (D V)) u (2*u+w) := by
  let Q (V : Config G c) := per W (D V)
  have hi (i j : ι) (he : ¬ separation (p i) (p j) ≤ u) (V : Config G c) : Q V i j=0 :=
    per_zero W (D V) (fun e => he ((separation_comm ..).trans_le (hw e)))
  have hh (i j : ι) (V V' : Config G c) (he : AgreeNear id (p j) (u+w) V V') : Q V i j=Q V' i j := by
    unfold Q; by_cases hx : i∈W j
    · rw [per_read _ _ (hv j) hx,per_read _ _ (hv j) hx]
      rw [show principal (D V) (W j)=principal (D V') (W j) from ?_]
      ext m n; exact h.rows m n (he.shrink (Nat.add_le_add_right (hw m.property) w))
    rw [per_zero W _ hx, per_zero W _ hx]
  refine ⟨hi,fun i j V V' he => ?_,fun i j V V' he => hh i j V V' (he.shrink (by rw [separation_self]; omega))⟩
  by_cases hu : separation (p i) (p j) ≤ u
  · exact hh i j V V' (he.shrink (by omega))
  exact (hi i j hu V).trans (hi i j hu V').symm


end SupportPrice



lemma panels_within (F : Forest S.ratio) (A : Stores S) {i j : In x A F (G:=G)}
    (h : j∈panels A F i) : separation (Wisps.front A F i) (Wisps.front A F j) ≤ radiusB x/20 := by
  apply (show meeting S x _ _ from h) _ _ _ _
  all_goals apply Set.mem_insert


end YM.AnalyticBridge.SectorAffine
