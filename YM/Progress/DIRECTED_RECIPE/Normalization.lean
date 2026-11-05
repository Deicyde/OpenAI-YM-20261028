import YM.PCalc.Band


/-!
# Transfer supplies: scalar and flags

Density strictly positive after pushing *genuine* positive input, even before
shooting. Not assuming coupling survives the next band. Derive scalar from
exact transfer at trivial field. The unnormalized density, probability Haars,
and prediction likelihood remain those in RG.History. Also transport gauge
and signed symmetry through the actual kernel; not testing them on numerical
truncations or independently averaged channels.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Progress.DirectedRecipe
open Function Set RG Wilson Lattice MeasureTheory RG.Shoot
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius ENNReal

variable {G : Gauge} {n : Side}
section Identity
private lemma travel1 {R} [AddCommGroup R] [One R] (x : Four R) (w : Walk) :
    travel (1 : Links R G.El) x w = 1 := by
  induction w generalizing x with
  | nil => rfl
  | cons l m ih => simp [travel,ih,Step.read]
lemma face1 (x : Face (Per n)) : faceValue (1 : Config G n) x = 1 := travel1 ..





lemma no_flags {t : ℝ} (h : 0 ≤ t) : flags t (1 : Config G n) = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro x hx
  obtain ⟨a,_,ha⟩ := (flags_spec ..).mp hx
  rw [face1,G.chord_one] at ha
  exact not_lt.mpr h ha










end Identity

section Transfer
variable {c f : Side} (S : StepData c f) {a : Levels G} (β : ℝ)

/-- Even unused bond tags enter; no noise independent of *frames* chosen
in the physical site likelihood. Strict even at β=0; finite tori, don't
assert any uniform strength by this proof. -/
lemma noise_strict (V X : Config G c) : 0 < S.noise β V X :=
  Finset.prod_pos fun _ _ => mul_pos (inv_pos.mpr (S.penaltyZ_pos _)) (Real.exp_pos _)

/-- Version for arbitrary Levels (unlike `Next.Foundations.uses_kernel`, cannot assume
the particular `Axial.viable` witness was used). Same elementary argument. -/
lemma density_strict (h : S.patch.Branches S.kernel G) (U : Config G f) (V : Config G c) :
    0 < S.density β U V := by
  have hp : ∃ t, 0 < S.likelihood U t := by
    by_contra! hh
    have he : (∑ t, S.likelihood U t) ≤ 0 := Finset.sum_nonpos fun i _ => hh i
    rw [S.chosen h] at he
    norm_num at he
  obtain ⟨i,hi⟩ := hp
  exact Finset.sum_pos' (fun t _ => mul_nonneg (S.likelihood_pos U t) (noise_strict ..).le)
    ⟨i, Finset.mem_univ _, mul_pos hi (noise_strict ..)⟩

lemma push_strict (h : S.patch.Branches S.kernel G) {F : Config G f → ℝ}
    (hp : ∀ U, 0 < F U) (hi : Integrable F (prior G f)) (V : Config G c) :
    0 < S.push β F V := by
  let w := fun U => S.density β U V • F U
  have hx (U) : 0 < w U := mul_pos (density_strict S β h U V) (hp U)
  apply (integral_pos_iff_support_of_nonneg (fun U => (hx U).le)
    (StepData.push_slice (S.isKernel h _) _ _ hi)).mpr
  simp only [show Function.support w = univ from Set.eq_univ_of_forall fun x => (hx x).ne',
    measure_univ, zero_lt_one]

/-- Keep pullback on *both* sides of the push. -/
lemma push_pull {a : Levels G} {m p : ℕ} {F : Config G (a.S.side (m+1) p) → ℝ}
    (H : Integrable F (prior G (a.S.side (m+1) p))) (s : Signed) (b : Site (a.S.side m p))
    (h : ∀ U, F (pull s ((a.clock.op m p).ratio.embed b) U) = F U) :
    ∀ V : Config G (a.S.side m p), (a.clock.op m p).push β F (pull s b V) = (a.clock.op m p).push β F V := by
  intro V
  let k := a.clock.op m p
  let M := prior G (a.S.side (m+1) p)
  let T := pull s (k.ratio.embed b) (K:=G.El)
  let f := fun U => k.density β U (pull s b V) • F U
  have hf : Integrable f M := StepData.push_slice (a.transition_mass ..) _ _ H
  have hg : MeasurePreserving T M M := prior_pull ..
  have he (U) : f (T U) = k.density β U V • F U := by
    dsimp only [f]; rw [show F (T U) = _ from h U, show k.density β _ (pull s b V) = _ from
      (a.blocks m p).symmetric β U V s b]
  have HI := integral_map (μ:=M) (φ:=T) (f:=f) hg.aemeasurable (by rw [hg.map_eq]; exact hf.aestronglyMeasurable)
  simp_rw [hg.map_eq, he] at HI
  exact HI

/-- Coarse gauge from fine gauge, *including at boundary points*. -/
lemma push_orbit {a : Levels G} {m p : ℕ} {F : Config G (a.S.side (m+1) p) → ℝ}
    (H : Integrable F (prior G (a.S.side (m+1) p))) (h : GaugeInvariant F) :
    GaugeInvariant ((a.clock.op m p).push β F) := by
  intro t V
  let k := a.clock.op m p
  let M := prior G (a.S.side (m+1) p)
  let r := t ∘ k.ratio.parent
  have hr : r ∘ k.ratio.embed = t := by funext; simp [r,Ratio.embed_parent]
  let T := gauge r
  let f := fun U => k.density β U (gauge t V) • F U
  have hf : Integrable f M := StepData.push_slice (a.transition_mass ..) _ _ H
  have hg : MeasurePreserving T M M := prior_gauge _
  have he (U) : f (T U) = k.density β U V • F U := by
    dsimp only [f]; rw [show F (T U) = _ from h r U]
    nth_rw 1 [← hr]
    rw [show k.density β (T U) _ = _ from (a.blocks m p).gauge β U V r]
  have HI := integral_map (μ:=M) (φ:=T) (f:=f) hg.aemeasurable (by rw [hg.map_eq]; exact hf.aestronglyMeasurable)
  simp_rw [hg.map_eq, he] at HI
  exact HI
end Transfer
end YM.Progress.DirectedRecipe
