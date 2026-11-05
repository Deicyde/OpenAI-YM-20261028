import YM.AnalyticBridge.NONFLAT_COVARIANCE_LOCALITY.Inverse
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Windows

/-!
# Per-window estimates

Root windows only; actual selection is constant throughout the V variation.

No relation between
those two is asserted.

These algebraic helpers simultaneously price every
column formed from each window and the discrepancy with full-space inverse
(from `TestD.glimpse`).

`E` here is the actual outside product computed on
the same A as in D; retain its external index marks as well.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.NonflatCovarianceLocality
open Function Filter Lattice RG Wilson Pressure Tree
open Next.SectorChange Next.SectorChange.Schur
open FreeResolvent Mark TestD Window
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f : Side} {α : Type} [Fintype α] [DecidableEq α]

/-- column-based window truncation, applied to A AFTER forming actual Gram -/
def panes (W : α → Set α) (u : ℝ) (A : Matrix α α ℝ) := Schur.per W (A+u • 1)
lemma panes_zero (W : α → Set α) (A : Matrix α α ℝ) : panes W 0 A = Schur.per W A := by simp [panes]

lemma read_panes (W : α → Set α) (u : ℝ) (A : Matrix α α ℝ)
    (i j : α) (hi : i∈W i) (hj : j∈W i) : panes W u A j i =
    (Schur.principal A (W i) + u • 1)⁻¹ ⟨j,hj⟩ ⟨i,hi⟩ := by
  rw [panes,per_read W _ hi hj,Schur.principal, FreeResolvent.shift_compress _ _ _ Subtype.val_injective]
  rfl
lemma hidden_pane (W : α → Set α) (u : ℝ) (A : Matrix α α ℝ) {i j : α}
    (h : j∉W i) : panes W u A j i=0 := Schur.per_zero W _ h

-- define E with exact occurrence-wise support through pane inspections
def overruns (W : α → Set α) (u : ℝ) (A : Matrix α α ℝ) := (A+u • 1)*panes W u A-1

variable (W : α → Set α) (hw : ∀ i, i∈W i)
def study : Window.Survey (fun i => (W i : Type)) :=
  ⟨fun i => Function.Embedding.subtype (·∈W i),fun i => ⟨i,hw i⟩,fun _ => rfl⟩

lemma per_study (u : ℝ) (A : Matrix α α ℝ) : (study W hw).inspect A u=panes W u A := by
  ext i j
  by_cases hi : i∈W j
  · rw [read_panes W u A j i (hw j) hi]
    exact Pane.local_entry A u ((↑) : W j → α) Subtype.val_injective ⟨j,hw j⟩ ⟨i,hi⟩
  rw [hidden_pane W u A hi]
  exact Pane.unused A u ((↑) : W j → α) _ i (fun ⟨b,h⟩ => hi (h ▸ b.property))



omit [Fintype α] [DecidableEq α] in
lemma nearest_study (R : ℕ) (p : α → Site c) (hR : Bars W p R) :
    (study W hw).Near (native c) p (R:ℝ) := by
  intro i j hj
  change _ ≤ ((separation _ _):ℝ)
  apply Nat.cast_le.mpr
  by_contra! h
  exact hj ⟨⟨j,hR _ _ h.le⟩,rfl⟩

variable {W} {R : ℕ} {p : α → Site c} {F : Coord G c → Matrix α α ℝ}
    {s C η t V : ℝ} {x : Coord G c} {n : ℕ}

include hw in
lemma pole (P : TestD.Price s C η t 1 V 1 n)
    (H : Tagged p p n s C F x) (h : FreeResolvent.Gap (F x) η)
    (hV : (native c).Volume p t V) (u : ℝ) (hu : 0 ≤ u) :
    PolePrices u p (fun x => panes W u (F x)) n t (V*inverseFare n C η V) x := by
  have hv := purchase H h (price_shrink P)
  let T := study W hw
  have he : (fun z => panes W u (F z))=glimpse T F u :=
    funext fun z => (per_study W hw u (F z)).symm
  rw [he]
  refine ⟨glimpse_smooth hv T hu P.r0, fun l hl => ?_⟩
  have ht := glimpse_rates hv P T hu (position_move _ _ P.pos.le) hV l hl
  apply ht.mono (price_steps P).2.1
  unfold charges inverseFare; split <;> apply le_of_eq <;> ring







-- Powers of d are not conditional on a shrinking volume. For off-window with radius
-- controlled by the epoch, keep the ratio estimate explicitly in B, not `till x`.
def remits (u : ℝ) (x : ℝ) := Real.exp (-u*(radiusB x))







end YM.AnalyticBridge.NonflatCovarianceLocality
