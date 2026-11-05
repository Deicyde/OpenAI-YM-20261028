import YM.Ac.Table
import YM.Next.MULTISOURCE.Cupful
import YM.Next.MULTISOURCE.Determined
import YM.Next.MULTISOURCE.Grass
import YM.Next.MULTISOURCE.Measure
import YM.Pressure.Seeds



/-!
# Normalized smoothness mechanism on the actual Reading steps (finite estimates!)

Normalize by the ACTUAL never-zero density at this r. Not the vacuum
Canons alone or a sector by sector normalization.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Multi.Step
open RG Lattice Wilson MeasureTheory Function Filter Finset Puff Work.G07
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {c f : Side} {S : StepData c f} {G : Gauge} {Q : Rep G f} {P : Rep G c}

abbrev uniform (P : BudgetPoint) (ℓ b : ℝ) (F : Config G c → ℂ) :=
    LeftBound P.order (fun v => ‖v‖≤ℓ) (fun _ => True) 1 b F

def clean (P : Rep G c) (F : Config G c → ℂ) (V) := (P.eval V)⁻¹ • F V
lemma cleaned (P : Rep G c) (F : Config G c → ℂ) (U) (he : 0 < P.eval U) :
    (P.eval U:ℂ)*clean P F U=F U := by simp [clean,Complex.real_smul,he.ne']

lemma smooth_price (P : Rep G c) (ok : S.patch.Branches S.kernel G) (h : Envelope Q.eval) (hp : ∀ x,0<Q.eval x)
    (he : P.eval=S.push Q.beta Q.eval) {L : ℝ} (hl : 0 ≤ L) : ∃ C : ℝ, 0≤C ∧
    ∀ (F : Config G f→ ℂ), Integrable F (prior G _) → ∀ t, (∀ U,‖F U‖≤t) →
      Continuous (clean P (S.push Q.beta F)) ∧ uniform P.p L (t*C) (clean P (S.push Q.beta F)) := by
  obtain ⟨C,H⟩ := h.cost
  let W := appraise S ok Q.eval (h.integrable _) H
  let D := curve S (G:=G) Q.beta
  have hc : ContDiff ℝ ∞ (fun i => W (D i)) := W.contDiff.comp (coated S Q.beta)
  have hW i : P.eval i=W (D (showU i)) := he ▸ kernel_push S ok Q.eval _ H i _
  have ht i : 0 < W (D i) := by
    let f (U) := outcome S U (D i) • Q.eval U
    have hf x : 0 < f x := mul_pos (hopeful S ok (D i) x (fun y => sunny ..)) (hp x)
    apply (integral_pos_iff_support_of_nonneg (fun x => (hf x).le) (show Integrable f (prior G _) from survives S ok _ _ (h.integrable _))).2
    rw [show Function.support f=Set.univ from Set.eq_univ_of_forall fun x => (hf x).ne']; simp
  let X v := (W (D v))⁻¹ • D v
  have hX : ContDiff ℝ ∞ X := (hc.inv (fun v => (ht v).ne')).smul (coated ..)
  obtain ⟨b,hb⟩ := attained X hX P.p.order hl
  refine ⟨_,hb.nonneg,fun F hF t hf => ?_⟩
  let A := appraise S ok F hF hf
  have he : clean P (S.push Q.beta F) = fun U => A (X (showU U)) := by
    funext U
    unfold X clean; rw [map_smul,hW,kernel_push S ok F hF hf]
  rw [he]
  refine ⟨A.continuous.comp (hX.continuous.comp visible),enlarged (hb.postcomp A) ?_⟩
  exact mul_le_mul_of_nonneg_right (appraisal S ok F hF hf) hb.nonneg

section
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma push_gauge (A : Levels G) (j p : ℕ) (F : Config G (A.S.side (j+1) p)→ V)
    (h : Integrable F (prior G _)) (hk : GaugeInvariant F) (β : ℝ) : GaugeInvariant ((A.clock.op j p).push β F) := by
  let S := A.clock.op j p
  intro t x; let u := t ∘ S.ratio.parent
  have he := prior_gauge u
  let i (U) := S.density β U (gauge t x) • F U
  have hp : Integrable i (prior G _) := StepData.push_slice (A.transition_mass ..) _ F h
  have hg := integral_map (μ:=prior G _) (f:=i) he.aemeasurable
    (show AEStronglyMeasurable i _ from he.map_eq.symm ▸ hp.aestronglyMeasurable)
  rw [he.map_eq] at hg
  change (∫ U,i U ∂prior G _)=_
  rw [hg]
  unfold StepData.push i
  have ht : u ∘ S.ratio.embed=t := funext fun x => by simp [u,S.ratio.embed_parent]
  refine integral_congr_ae (Eventually.of_forall fun U => ?_)
  have hp := (A.blocks j p).gauge β U x u
  change S.density _ _ (gauge (u ∘ S.ratio.embed) x)=_ at hp
  simp_rw [ht] at hp; exact congrArg₂ _ hp (hk u U)
end

lemma path_gauge (H : History G) (h : H.Selected) (N p j : ℕ) (he : j≤N) :
    GaugeInvariant (H.rep N p j).eval := by
  induction he using Nat.decreasingInduction with
  | self => rw [(h.starts N p).2]; exact fun a b => bare_gauge ..
  | of_succ i hi ih => rw [(h.steps N p i hi).1]
                       exact push_gauge _ i p _ (((H.rep N p (i+1)).envelope (h.represents N p _ hi).good).integrable _) ih _
lemma exponent_gauge (H : History G) (h : H.Selected) (N p j : ℕ) (he : j≤N) :
    GaugeInvariant (H.rep N p j).exponent := by
  let P := H.rep N p j
  have hp (x) : 0 < P.activities.gas P.p x :=
    pos_of_mul_pos_right (AxisShift.chosen_positive h he x) (Real.exp_pos _).le
  intro i U
  have hU : P.activities.gas P.p (gauge i U)=P.activities.gas P.p U := by
    apply Complex.ofReal_injective
    have hc : P.activities.Valid P.p _ _ := (h.represents N p j he).good.labels
    rw [real_book _ _ hc, real_book _ _ hc,gauge_flags]; apply sum_congr rfl; intro b hb
    exact prod_congr rfl fun k hk => (incumbent_legible P k hc.forced).symmetry i U
  apply Real.exp_injective
  apply mul_right_cancel₀ (hp U).ne'
  nth_rw 1 [← hU]; exact path_gauge H h N p j he i U
end YM.Multi.Step
