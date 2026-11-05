import YM.OPE.Columns.Accounts

/-! The one-step transfer on each equal engineering grade is diagonal with the stated threshold ratio in the Wilson construction. -/
set_option autoImplicit false
noncomputable section
namespace YM.SharpGram
open Lattice RG Wilson MergeProof Bid Source Extra.Histories Labels Push.Local
open scoped Topology BigOperators
variable {G : Gauge}

/-- Does not decrease factor degree; on *equal or lower engineering* grade read-off
is exact, including both threshold normalizations (as powers of the factor degree). -/
structure ThresholdDiagonal {d : ℕ} (F : Labels.Frame G d) (T : Heading F) (f c : ℝ) : Prop where
  regular : ∃ cap : ℝ, Push.Local.Leading T.map.toLinearMap cap
  through (i j : F.Index) : (F.grades j).1 ≤ (F.grades i).1 →
    T.map (Size.axis F i) j = if j = i then (((c / f : ℝ) : ℂ)) ^ ((F.grades i).2) else 0
  factor (i j : F.Index) : (F.grades j).2 < (F.grades i).2 → T.map (Size.axis F i) j = 0

structure CalibratedStep {d : ℕ} (F : Labels.Frame G d) (H : History G)
    (W : Worth) (m : ℕ) (before after : F.Coeff → F.Coeff) : Prop where
  reaches : ∃ T : Heading F,
    ThresholdDiagonal F T (H.levels.budget (m+1)).threshold (H.levels.budget m).threshold ∧
    (∀ x : F.Coeff,
      F.coeffSize (T.map x) ≤ W.K (H.levels.clock.J (m+1)) * F.coeffSize x ∧
      F.coeffSize (T.map.symm x) ≤ W.K (H.levels.clock.J (m+1)) * F.coeffSize x) ∧
    ∀ x : F.Coeff, F.coeffSize (after x - T.leads (H.S.block m) (before x)) ≤
      barunit (H.S.block m) * F.coeffSize (F.core (before x))

structure TrueSteps (C : Family G) (W : Worth) : Prop where
  reads (d m N p : ℕ) (hr : C.ref d ≤ m) (hm : m < N) :
    CalibratedStep (C.labels.level d) C.path W m
      (fun x => ((C.factory d N p).entries (m+1) x).x) (fun x => ((C.factory d N p).entries m x).x)

lemma CalibratedStep.triangle {d m : ℕ} {F : Labels.Frame G d} {H : History G} {W : Worth}
    {x y : F.Coeff → F.Coeff} (A : CalibratedStep F H W m x y) :
    Triangle H W m x y := by
  obtain ⟨T,h,hV⟩ := A.reaches
  exact ⟨T,h.regular,hV⟩
end YM.SharpGram
