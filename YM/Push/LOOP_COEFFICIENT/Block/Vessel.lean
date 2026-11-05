import YM.Push.LOOP_COEFFICIENT.Block.Pier

/-!
# Actual rooted drift and uncentering (no pre-L trace bound on either)
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Block
open Function Matrix Set Filter Lattice Laurent RG Wilson Precision Exterior Bloch Complex Portal Fine
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {L c f : Side} {r : Ratio c f} {S : StepData c f} {p : Clip} {W : PathData G} {η C Λ : ℝ}

structure Vessel (G : Gauge) (L : Side) where
  port : Pier G L
  back : JointVertex G L
  kick : JointVertex G L
  signal : JointVertex G L

namespace Vessel
def spill (G : Gauge) (t : S.Choices) (A : Matrix (Body 1 f) (Body 1 c) ℝ) (z : Loops.Links G c) := let U := background G S A z; acceleration (Zmap t) U (first (penalty S (vary 1 z)) (Zmap t U))
structure Charts (V : Vessel G r.count) (t : S.Choices) (A : Matrix (Body 1 f) (Body 1 c) ℝ) : Prop where
  turns : ∃ χ, V.port.Serves t A χ ∧ Models (linksGrid G c) (jointGrid G r) (jointGrid G r) (fun z => (χ z)⁻¹) V.back
  kicks : Models (linksGrid G c) (jointGrid G r) (jointGrid G r) (spill G t A) V.kick
  listens : Charged (linksGrid G c) (jointGrid G r) (onAcc G t A) V.signal

def sail (V : Vessel G L) (Y : Lights G L) (W p) := (V.back.transpose.mul (V.port.fabric Y W p)).mul V.back
def onboard (V : Vessel G L) (Y : Lights G L) (W p) := (V.sail Y W p).add V.kick
def drift (V : Vessel G L) (Y : Lights G L) (W p) := (V.sail Y W p).inv.amplify V.signal
variable {t : S.Choices} {A : Matrix (Body 1 f) (Body 1 c) ℝ} {V : Vessel G r.count} {Y : Lights G r.count} (h : Charts V t A) (hY : Projects r (linksGrid G f) (linksGrid G c) (cmat (liftMatrix G A)) Y) (hW : W.Bounds p η C Λ) (hS : S.patch.Branches S.kernel G)
include h hY hW
lemma Charts.sail : Models (linksGrid G c) (jointGrid G r) (jointGrid G r) (onBase p W t A) (V.sail Y W p) := by
  obtain ⟨χ,hs,hχ⟩ := h.turns; refine ((hχ.transpose.mul (hs.adjusted W p hY hW)).mul hχ).congr (hs.hχ.det.mono fun z hz => ?_)
  have he := (χ z).mul_nonsing_inv (isUnit_iff_ne_zero.mpr (fun he => by simp [he] at hz)); dsimp only [onAdjusted]; rw [← Matrix.mul_assoc,← Matrix.mul_assoc,← transpose_mul,he,transpose_one,Matrix.one_mul, Matrix.mul_assoc,he,Matrix.mul_one]
include hS
lemma Charts.onboard : Models (linksGrid G c) (jointGrid G r) (jointGrid G r) (onVector p W t A) (V.onboard Y W p) := by
  refine ((h.sail hY hW).add h.kicks).congr ?_
  have hb := background_diff (x:= (0:Loops.Links G c)) |>.continuousAt (v:=background G S A)
  rw [ContinuousAt,background_zero] at hb; exact (hb.eventually (beam_near hS t)).mono fun z hz => vector_eq hW t _ _ hz.bonds
lemma Charts.drift (hu : ∀ q k, Matches (n:=c) q k → IsUnit ((V.sail Y W p).base q)) : Charged (linksGrid G c) (jointGrid G r) (observed p W t A) (V.drift Y W p) := by
  have hm := (h.sail hY hW).inv hu
  exact h.listens.amplify hm.smooth (onAcc_diff hS) hm.sync
end Vessel
end YM.Push.Loops.Block
