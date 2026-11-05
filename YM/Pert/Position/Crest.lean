import YM.Pert.Rig.Linked
import YM.Pert.Position.Actual
/-! Leading-order comparison of continuum readings and the Wilson regulator for compact tests on separated configurations. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
namespace YM.Pert.Position
open Filter Topology Function Set Lattice Maxwell Org Climb Spec RawLabels Classical
variable {G : Gauge} {C : Family G} {I : Extraction.Order} {S : Table C.book}
variable {d t : ℕ}
variable (Q : Conditions C.labels d t)

theorem finite_leading {A : Labels.Frames G} (Q : Conditions A d t) (H : CleanProfiles Q) (L : Side) (hL : 1<L.val) : Tendsto (fun m : ℕ=> finite Q L m 0) atTop (𝓝 (white Q)) := by
  apply tendsto_pi_nhds.mpr; intro i; apply tendsto_pi_nhds.mpr; intro j
  obtain ⟨f,hf⟩ := H i
  simpa only [finite,white,← hf] using (Rig.zerothProfile d A L hL (fun k=> baring _ d (j k)) f f.continuous f.hasCompactSupport f.tsupport_subset)

private theorem jet_zero (φ : Ledger Q→Buffer C.labels d) (H : Reports (chart Q) (white Q) 0 φ) (hQ : CleanProfiles Q) (p : ℕ) (L : Side) (hL : 1<L.val) {n : ℕ} (R : Conditions C.labels d n) (hR : CleanProfiles R) :
   Tendsto (fun m=> readJet φ p 0 (chart R) (finite Q L m) (finite R L m)) atTop (𝓝 (chart R (white R,0))) := by
  simp_rw [readJet, iteratedDeriv_zero, curve_zero]
  have h := (finite_leading R hR L hL).prodMk_nhds (H.diff.continuousAt.tendsto.comp (finite_leading Q hQ L hL))
  rw [H.fixes] at h
  exact ((chart_diff R).continuous.tendsto _).comp h

variable (b : Final C I S) (X : Scaling S)
structure BoardAttains (φ : Ledger Q→ Buffer C.labels d) : Prop where
  patch : Reports (chart Q) (white Q) 0 φ
  raw (L : Side) : 1<L.val → Tendsto (fun m : ℕ=>finite Q L m 0) atTop (𝓝 (white Q))
  calibrates_pt (L : Side) (hL : 1 < L.val) (p j : ℕ) :
    ∀ᶠ m in atTop, readJet φ p j (chart Q) (finite Q L m) (finite Q L m) =
      iteratedDeriv j (fun _ : ℝ => chart Q (white Q,0)) 0
  comparison : ∃ B : ℕ→ Buffer C.labels d, Tendsto B atTop (𝓝 0) ∧ (∀ᶠ k in atTop, IsUnit (motor C.labels (B k)) ∧ testedMean Q X (B k) k = chart Q (white Q,0)) ∧
    ∀ (L : Side), 1<L.val → ∀ p : ℕ, ∀ {n} (R : Conditions C.labels d n), CleanProfiles R →
       Tendsto (fun k=>testedMean R X (B k) k - readJet φ p 0 (chart R) (finite Q L k) (finite R L k)) atTop (𝓝 0)

lemma calibrate (H : FirstExtension b X) (hQ : CleanProfiles Q) (h : square Q) : ∃ φ, BoardAttains Q X φ := by
  obtain ⟨φ,hφ⟩ := squareSolve Q h
  obtain ⟨B,hB,he,hf⟩ := actual_square Q h hQ X H
  refine ⟨φ,hφ,finite_leading Q hQ,?_,B,hB,he,?_⟩
  · intro L hL p j
    exact Reports.deletion (x := fun _ => white Q) (D := fun i m => finite Q L m i)
      hφ (finite_leading Q hQ L hL) p j
  intro L hL p n R hR; simpa only [sub_self] using (hf R hR).sub (jet_zero Q _ hφ hQ _ _ hL R hR)

structure Crest : Prop where
  raw (d t : ℕ) (Q : Conditions C.labels d t) : CleanProfiles Q → ∀ L : Side, 1<L.val →
    Tendsto (fun k=> measured Q X k - finite Q L k 0) atTop (𝓝 0)
  position (d t : ℕ) (Q : Conditions C.labels d t) : CleanProfiles Q → square Q → ∃ φ, BoardAttains Q X φ

lemma credible (H : FirstExtension b X) : Crest X := by
  refine ⟨fun d t Q hQ L hL=>?_,fun d t Q hQ h => calibrate Q b X H hQ h⟩
  simpa only [sub_self] using (measured_tends Q hQ X H).sub (finite_leading Q hQ L hL)

/-- Both the order-zero Wilson prescription match here and all the sector/stress/witness properties of `FirstExtension` hold for the same constructed mean theory. A statement in moving frames and along the displayed scaling (including engineering powers); not yet all-order or an OPE comparison. -/
theorem crestTarget (hg : G.Simple) {p : ℝ} (hp : 0<p) : ∃ C : Family G,
  C.path.levels.clock.kernel.penalty=p ∧ Extraction.Wcmain C ∧
  MergeProof.Ribbons.Materials C ∧ MergeProof.Ribbons.Plenty C ∧ ∀ f : Extraction.Order,
    ∃ (g : Extraction.Order) (S : Table C.book) (h : Final C (f.refine g) S), ∃ X : Scaling S, FirstExtension h X ∧ Crest X := by
  obtain ⟨C,h0,hW,hM,hP,H⟩ := firstTarget hg hp
  refine ⟨C,h0,hW,hM,hP,fun f => ?_⟩
  obtain ⟨g,S,k,X,hX⟩ := H f
  exact ⟨g,S,k,X,hX,credible k X hX⟩

end YM.Pert.Position
