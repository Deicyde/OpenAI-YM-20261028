import YM.Next.RANK.Tilt
import YM.TraceExtension.Prom.Sway.Price
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Ribbon
open Function Filter RG Thirst Baler Lattice Wilson MeasureTheory Relation Corona Value Glyph Marker Perch Vac.Numbers Alarm Station Cells Spindle Atlas Edition Normal LiftMark Rise Paint MvPolynomial
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} (C : Family G) {N k p d D : ℕ}

lemma StampDuty.procureSky (h : G.Simple) (H : C.Makes) (d D : ℕ) (v : C.label d) : ∀ᶠ k in atTop, ∀ b y : ℝ, 0 ≤ b → y+b*d+saves C d ≤ -8 →
    year C D k → ∀ N (p : ℕ), k ≤ N → ∀ {Q q X} (F : StampDuty C k N p d D Q q X), ∀ t,
        Price.Solves C (Station.mag C.path.levels b k) d k N p F.T v t →
        let s:= clim C.path.levels k;let E:=b*d+saves C d;let r:= Perch.bill y s
        r * moneys C d k N p t ≤ Perch.bill (-8) s ∧ coin (F.W t) ≤ Perch.bill E s := by
  filter_upwards [Atlas.incomeSky h H v] with k hp b y hb hi hy N p hN Q q X F t hv s E r
  have h':= hp b hb N p hN F.T F.lights.span t hv
  let A:= C.path.levels;rw [fire_bill] at h'; let u:= paid C d k N p t
  change bill 1 s * u ≤ Perch.bill E s at h'
  have hh:(A.params k).columns ≤ bill 1 s:= le_trans hy (Glimmer.billed _ (show LiftMark.shade D/4≤1 by linarith only [shaded D]))
  have he : u≥0:=paid_pos ..
  refine ⟨(mul_le_mul_of_nonneg_left (le_trans (mul_le_mul_of_nonneg_right hh he) h') (show 0≤r from Real.exp_pos _|>.le)).trans ?_, (F.weight _).trans h'⟩; unfold r; rw [overlap]; exact Glimmer.billed s (by unfold E; linarith only [hi])
end YM.Next.Rank.Ribbon
