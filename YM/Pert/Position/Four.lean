import YM.Pert.Position.Frame
/-!
Unconditional determinant and normalization, through horizon 4 (nested since below four Maxwell fields are scalars). Only ordinary unmarked correlations of the constructed mean theory, along a weak sequence, and leading position equations; no all-order actual-vs-diagram match assertion.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Pert.Position
open Filter Set Function Lattice Topology Classical Maxwell Climb Spec Rigid
variable {G : Gauge} (C : Family G) {I : Extraction.Order} {S : Table C.book}
variable (b : Final C I S) (X : Scaling S)
lemma square_four (hg : G.Simple) : ∃ (n : ℕ) (Q : Conditions C.labels 4 n), square Q ∧ CleanProfiles Q := by
  obtain ⟨k,s,m,g,h,hw⟩ := square_of_frozen C.labels 4 (frozen_four C.labels hg)
  exact ⟨m,assemble C.labels 4 s m g,h,fun i=>hw i⟩

variable {C} {n : ℕ} {Q : Conditions C.labels 4 n} {φ : Ledger Q→Buffer C.labels 4}

def named (φ : Ledger Q→Buffer C.labels 4) (k : ℕ) := φ (measured Q X k)
def renormLeading (φ : Ledger Q→Buffer C.labels 4) {m} (R : Conditions C.labels 4 m) (L : Side) (i : ℕ) := chart R (finite R L i 0,φ (finite Q L i 0))
theorem continuous_jet {m} (R : Conditions C.labels 4 m) (L : Side) (i p : ℕ) : renormLeading φ R L i = readJet φ p 0 (chart R) (finite Q L i) (finite R L i) := by simp only [renormLeading,readJet,iteratedDeriv_zero,curve_zero]

structure Resident (φ : Ledger Q→Buffer C.labels 4) : Prop where
  converges : Tendsto (named X φ) atTop (𝓝 0)
  solved : ∀ᶠ k in atTop, IsUnit (motor C.labels (named X φ k)) ∧ testedMean Q X (named X φ k) k = chart Q (white Q,0)
  law : ∀ᶠ k in atTop, YM.Spin.realH b.room.kernel.spin (Free.spin_free C.labels) (adjusted X (named X φ) k)
  unit : ∀ᶠ k in atTop, adjusted X (named X φ) k ((freeTable C.labels).unit 4) = S.unit 4
  nested (d) (h : d≤3) : ∀ᶠ k in atTop, ∀ v, adjusted X (named X φ) k (toFour C.labels (by omega : d≤4) v) = b.sector.derivatives.rise (by omega : d≤4) (X.U k d v)
  leads {m} (R : Conditions C.labels 4 m) (hR : CleanProfiles R) (L : Side) (hl : 1<L.val) (p) :
     Tendsto (fun k=>testedMean R X (named X φ k) k - readJet φ p 0 (chart R) (finite Q L k) (finite R L k)) atTop (𝓝 0)

lemma residency (h : FirstExtension b X) (hg : G.Simple) (hc : CleanProfiles Q) (hl : BoardAttains Q X φ) : Resident b X φ := by
  obtain ⟨A,hA,he,hlead⟩ := hl.comparison
  let B := named X φ
  have hB : Tendsto B atTop (𝓝 0) := hl.patch.fixes ▸ hl.patch.diff.continuousAt.tendsto.comp (measured_tends Q hc X h)
  have hw : B =ᶠ[atTop] A := by
    filter_upwards [he, Filter.Tendsto.eventually ((measured_tends Q hc X h).prodMk_nhds hA) hl.patch.strict] with k he' hk
    exact (hk.mp ((chart_actual Q b.room.kernel.smooth X hc (A k) k).trans he'.2))
  refine ⟨hB,(he.and hw).mono (fun k i=>by simpa only [←i.2, show B=named X φ from rfl] using i.1), (h.fit.hsym 4).mono (fun _=>adjusted_own h _), (h.fit.units 4).mono (fun k hk=> (adjusted_unit X B k).trans hk),fun d hd => ?_, fun R hR L HL p => ?_⟩
  · filter_upwards [h.fit.rises d 4 (by omega)] with k hk v
    unfold adjusted; split_ifs <;> first | (change X.U k 4 (motor _ _ _)=_; rw [motor_small C.labels hg (by omega)]; exact hk _) | exact hk _
  apply (hlead L HL p R hR).congr'
  exact hw.mono (fun i hi=>congrArg (testedMean R X · i - _) hi.symm)

structure FourMeters : Prop where
  root : Crest X
  meter : ∃ (n : ℕ) (Q : Conditions C.labels 4 n) (φ : _), square Q ∧ CleanProfiles Q ∧ BoardAttains Q X φ ∧ Resident b X φ

theorem four_on (hg : G.Simple) (hX : FirstExtension b X) : FourMeters b X := by
  have hC := credible b X hX
  obtain ⟨n,Q,hq,hR⟩ := square_four _ hg
  obtain ⟨φ,hφ⟩ := hC.position _ _ Q hR hq
  exact ⟨hC,n,Q,φ,hq,hR,hφ,residency b X hX hg hR hφ⟩

/-- Constructs the determining tests at horizon four and compares their leading readings on the same scaling sequence. -/
theorem normalized_four (hg : G.Simple) {p : ℝ} (hp : 0<p) : ∃ C : Family G,
  C.path.levels.clock.kernel.penalty=p ∧ Extraction.Wcmain C ∧
  MergeProof.Ribbons.Materials C ∧ MergeProof.Ribbons.Plenty C ∧ ∀ f : Extraction.Order,
    ∃ (g : Extraction.Order) (S : Table C.book) (b : Final C (f.refine g) S), ∃ X : Scaling S, FirstExtension b X ∧ FourMeters b X := by
  obtain ⟨C,h0,hW,hM,hP,H⟩ := firstTarget hg hp
  refine ⟨C,h0,hW,hM,hP,fun f => ?_⟩
  obtain ⟨g,S,k,X,hX⟩ := H f
  exact ⟨g,S,k,X,hX,four_on k X hg hX⟩
end YM.Pert.Position
