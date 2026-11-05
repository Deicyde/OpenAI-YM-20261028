import YM.Push.LOCAL_SPLITTING.CovariantKernel
import YM.Work.F05.Actions


/-!
# Direct non-PSREC step decomposition on a supplied history

Operates on actual kernel, paths and existing label supports. Contrast with
the `Output`-conditional PSREC estimate: this fallback's large finite-volume
residual estimate, though it requires far less input and can be applied to
actual pushed products etc., is NOT uniform on taking cutoffs to infinity.
Projection, gauge invariance and per-layer costs here are genuine; contraction
of the remainder and small leading perturbation are NOT obtained this way.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Local.Kernel
open Function Filter Lattice Wilson RG Source Labels MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {n : Side} {m N p d : ℕ} {F : Labels.Frame G d}

section Gauge
variable {B : BudgetPoint} {R : Rep G n} {T : SectionData F} {A : Hol G}

theorem mask_gauge {E : Type*} [Zero E] (t : ℝ) (Z : Support n) {f : Config G n → E} (h : GaugeInvariant f) : GaugeInvariant (masked t Z f) := by
  intro g U; by_cases he : Healthy t Z U
  · rw [masked_eq _ _ _ _ (by simpa [Healthy] using he),masked_eq _ _ _ _ he,h]
  rw [masked_ne _ _ _ _ (by simpa [Healthy] using he), masked_ne _ _ _ _ he]

theorem exp_invariant {σ C Λ δ v : ℝ} (h : R.Lawful σ C Λ δ v) : GaugeInvariant R.exponent := by
  intro g U
  let B := R.p; let W := R.path; let p := R.clip
  have ha {k : ℕ} (A : ℕ → Atom G k) (hA : ∀ i,(A i).Invariant) (x : Site n) : GaugeInvariant (fun U => PathData.atomSeries A B U x) := fun t V => tsum_congr fun i => by
    have he : GaugeInvariant (fun V : Config G n => (A i).unmasked V x) := by intro g U; unfold Atom.unmasked; simp only [Work.F05.slot_gauge]; exact hA i ..
    exact mask_gauge B.threshold _ he t V
  have hb (x : Face (Per n)) : GaugeInvariant (fun U : Config G n => W.baseTerm p B U x) := by
    intro g U; change W.baseTerm p B (Lattice.gauge g U) x = _; unfold PathData.baseTerm PathData.kept
    simp only [face_gauge, G.chord_conj, Work.F05.ell_gauge (W:=W) h.paths U g x, G.norm_adjoint]; congr
  have hP : GaugeInvariant (fun U : Config G n => W.principal p B R.beta U) := by
    intro g U; simp only [PathData.principal,hb _ g U,ha W.loop (fun i => (h.paths.invariant i).1) _ g U,ha W.cubic (fun i => (h.paths.invariant i).2.1) _ g U,ha W.quartic (fun i => (h.paths.invariant i).2.2) _ g U]
  have he (i) : GaugeInvariant (R.activities.regularOccurrence R.p i) := mask_gauge _ _ (h.labels.regular.smooth i).symmetry
  dsimp only [W,B,p] at hP
  simp only [Rep.exponent,PathData.inChannels,Activities.additive,Work.F05.pull_gauge_zero,hP _ _, he _ g U]

theorem insertion_gauge {P : Coefficient F n} {o : Site n} {σ C Λ δ v : ℝ} (ht : T.Sound A) (hr : R.Lawful σ C Λ δ v)
    (h : P.Format o A R) (he : GaugeInvariant R.eval) : GaugeInvariant (P.density o T R) := by
  have hm (i) : GaugeInvariant (P.maskedTerm R i) := mask_gauge _ _ (h.smooth i).symmetry
  have hK (i) : GaugeInvariant (P.marked R i) := by
    intro g V; unfold Coefficient.marked Activities.admissible; simp only [gauge_flags,h.invariant _ g V,hr.labels.forced.sym _ g V]; congr
  intro g U
  simp only [Coefficient.density, he g U, hK _ g U, exp_invariant hr g U, Coefficient.exponentialEntry, hm _ g U, mask_gauge _ _ (T.placed_invariant ht o _) g U]
end Gauge

variable {H : RG.History G} {k a : ℝ} {T : SectionData F} {A : Hol G}

theorem vacuum_actual (h : H.Selected) (hm : m ≤ N) :
    let R := H.rep N p m
    Continuous R.eval ∧ GaugeInvariant R.eval ∧ ∀ V, 0 < R.eval V := by
  induction hm using Nat.decreasingInduction with
  | self => dsimp only; rw [(h.starts ..).2]; exact ⟨bare_cont _,fun g U => bare_gauge ..,bare_pos _⟩
  | of_succ i hi ih =>
    let c := H.levels.clock.op i p
    have hc : c.patch.Branches c.kernel G := (H.levels.blocks ..).branches
    dsimp only at *; rw [(h.steps _ _ _ hi).1,← pass_full]
    have he := ((H.rep N p (i+1)).envelope (h.represents _ _ _ hi).good).integrable (prior G _)
    exact ⟨pass_continuous _ _ _ hc he, pass_gauge _ _ _ hc ih.2.1, fun _ => pass_pos _ _ _ hc _ he ih.2.2⟩




end YM.Push.Local.Kernel
