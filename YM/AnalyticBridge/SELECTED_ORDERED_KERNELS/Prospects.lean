import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Finished
import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.SectorLie
import YM.Extra.ITERATION_NO_LOSS.Continuity
import YM.Next.MAXWELL.Det
import YM.Push.STRESS_FLUX.Ward

/-!
# Interpolation for one-site tag changes of the *finished* actual Gram

Keep the flags, seeds, panels and all other geometric data fixed. All changed
memberships over a single parent. `market_chart` gives a single row source
for the two different endpoint systems. Use Schur.windows for the actual
mixture, not inferring gap on its cloud by convexity of the two clouds (those
interpolations are different!). Uniform over all fixed window systems large
enough including the endpoint option. Post L, order, Teller and patch tests.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SelectedOrderedKernels.Selected
open Lattice Wilson RG Precision Exterior Tree Function Filter Topology Bloch Next.SectorChange Next.Fluctuations Set
  Rows YM.Pressure YM.Pressure.Stores FreeResolvent Affine TestD Lever Schur Wisps Matrix
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {n : ℕ} {σ r s C M g t : ℝ}
  {x : ℝ} {A : Stores S} {T U : Forest S.ratio} {k : S.Choices} {V : Config G c} {v : Site c}
  {H : Tube G S} {Pt : Teller G} {P : Patch}



def line (H : Tube G S) (x : ℝ) (A : Stores S) (k : S.Choices) (V : Config G c) (T U : Forest S.ratio) :=
  mixture (SelectedOrderedKernels.over (finished H x A T k) V) (SelectedOrderedKernels.over (finished H x A U k) V)

@[simp] lemma line_left (B : Vec G c 1) : line H x A k V T U (B,0) = SelectedOrderedKernels.over (finished H x A T k) V B := by
  simp [line,mixture,castLift,stir]
@[simp] lemma line_right (B : Vec G c 1) : line H x A k V T U (B,1) = SelectedOrderedKernels.over (finished H x A U k) V B := by
  simp [line,mixture,castLift,stir]





variable (h : ∀ T U : Forest S.ratio, Sharing x A T U k V (n+1) C) (hA : ∀ T : Forest S.ratio, FreeResolvent.Gap (Sector.form H x A T k V) g)
  (hS : S.patch.Branches S.kernel G) (hC : 0 ≤ C) (hM : 0 ≤ M) (hs : 0 < σ) (hW : Sheet H.up σ M)
include h hA hS hs hW


abbrev markup (C : ℝ) := 3*(C+1)
omit h hA hS hs hW in
lemma markup_nn {x : ℝ} (h : 0 ≤ x) : 0 ≤ markup x := by unfold markup; positivity

omit h hA hS hs hW in
lemma seats_price (P : Patch) (G : Gauge) (hs : 0 < s) (hC : 0 ≤ C) (hg : 0 < g) :
    Price s C g (room s C g n) 1 (Small.volumeCost G P (room s C g n)) 1 n :=
  ⟨hg,hC,hs,rfl,le_rfl,torusPay_nn _ _ (room_grid hs hC hg n).1,zero_le_one,le_rfl⟩

include hC hM


omit h hA hS hs hW hC hM
abbrev Covered (x : ℝ) (W : raw G f → Set (raw G f)) := Bars W (home S) (radiusB x / 60)

structure Prospects (S : StepData c f) (H : Tube G S) (x : ℝ) (A : Stores S) (k : S.Choices) (V : Config G c) (n : ℕ) (s M r g : ℝ) : Prop where
  ready : 120 ≤ radiusB x
  lineCost (T U : Forest S.ratio) (v : Site c) : changed S T U v → ∀ t ∈ Icc (0:ℝ) 1,
    let d := room s M r n
    Knew (park (native c) hearth d v) (native c) (home S) (guides (ray G c)) (0,t) n s M r 1 (line H x A k V T U)
  floors (T U : Forest S.ratio) (v : Site c) : changed S T U v → ∀ t ∈ Icc (0:ℝ) 1,
    ∀ W, Covered (S:=S) x W → FreeResolvent.Gap (Schur.clouded W (line H x A k V T U (0,t))) g




end YM.SelectedOrderedKernels.Selected
