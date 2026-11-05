import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.Reconnect


/-!
# Normalized shape service

Uniform-in-field price at finite volume from the local reconstruction and
bills.

Not a small bound on relative large-field tails.

Price may grow with
volume even with the very strongly paid inputs.

Log tests only asked on V
where they're legitimate.

Priced just for the shape-control socket here, not inverse-shooting purchases.

Trial
Representations DO vary in β, holding all the activity data; the shape estimate
compares actual evaluators, not pre-mask or jet-equivalence.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.CouplingShape
open Function Filter Lattice Wilson RG PathData Push.AbsoluteSums Push.BetaTransport UVNext.CouplingReset
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {n : Side} {σ C Λ : ℝ} {P : PathData G} {p : Clip} {b : BudgetPoint}

















variable {R : ℝ→Activities G n} {u : ℝ→ℝ} (P : PathData G) (p : Clip) (b : BudgetPoint)
/-- Commit dictionary; dial independent on the correction branch, not
on the actual input family. -/
def physicalTerms (u : G.Color) (α : ℝ) (R : ℝ → Activities G n) (x _d : ℝ) := written P p b (R x) α (delta (R x) u)

def author (u : G.Color) (α : ℝ) (R : ℝ→Activities G n) : Template G n := ⟨P,p,b,physicalTerms P p b u α R⟩
variable {P p b}
lemma location {β : ℝ→ℝ} {H : ℝ → Config G n → ℝ} {α z x H₀ w κ γ : ℝ} {V : Config G n}
    (hd : P.Bounds p σ C Λ) (hg : Grace p (boost b) σ) (hv : Selector p b) (hn : 10<n.val) (hs : G.Simple)
    (u : G.Color) (hu : ‖u‖=1)
    (hr : Earnings b (R x) H₀ w) (hE : Reserve p b G H₀ σ C w α (delta (R x) u) κ γ)
    (hin : H x=received P p b (R x) z (β x) α) (hV : flags b.threshold V=∅) :
    let A:=author P p b u α R; let ε:= delta (R x) u; let f (x : ℝ) := β x+α
    scalar H x=perVac (R x) z ∧ 0 < H x 1 ∧ 0 < H x V ∧
      (∀ U, H x U / H x 1=A.shape f U x ε) ∧ (∀ a, A.residual H V f x a=(a-ε)*A.leg V) := by
  intro A ε f
  let v:=perVac (R x) z
  have hh (U) : (A.trial f x ε v).eval U= H x U := hin ▸ (transferred U hd hg hv hs hn hr u hu z (β x) α hE).symm
  have hc i : (A.terms x ε).E i 1=0 := (valid_output hd hg hv hs hn hr hE).regular.at_flat i
  have he : contrast H V x= (f x+ε)*A.leg V+A.background V+A.add V x ε := A.contrast_eq hc hV (hh 1) (hh V)
  refine ⟨A.scalar_eq hc (hh 1),?_,?_,fun U=>?_,fun a=>?_⟩
  · rw [← hh 1,Template.trial_one _ _ hc]; exact Real.exp_pos _
  · have hk : flags A.p.threshold V=∅ := hV
    rw [← hh V,A.eval_trial,Template.shape, Activities.gas_one _ _ hk,mul_one]; exact mul_pos (Real.exp_pos _) (Real.exp_pos _)
  · rw [← hh U,← hh 1,Template.trial_one _ _ hc,Template.eval_trial]; field_simp
  rw [Template.residual,he,show A.add V x a=A.add V x ε from rfl]; ring


end YM.AnalyticBridge.CouplingShape
