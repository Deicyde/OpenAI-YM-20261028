import YM.MultiNext.VACUUM_STABILITY.Gaussian.Purchase

set_option warningAsError false

/-!
# Through actual component integrals

Physical producers may represent even the nondiagonal score integrand under a
change of variables tending to this computation. Explicit sufficient hypotheses on the
actual integrals, including neighborhoods for the cut domain and measurable parameter maps.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Multi.Vacuum.Gauss
open RG Lattice Wilson Filter Finset Function MeasureTheory ProbabilityTheory Text Cluster Desk Component Puff
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {X Y J : Type} [MeasurableSpace J] (μ : Measure J)
  [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Crude domination on a chart, allowed to depend on entire period and finite history and
singular scale. Enough to interchange through finite order at a corner. -/
structure Crud (E : Set X) (f : J → X → Y) (p : ℕ) : Prop where
  opens : IsOpen E
  unit j x : x∈E → ContDiffAt ℝ (p:ℕ∞) (f j) x
  bound i : i ≤ p → ∃ g : J → ℝ, Integrable g μ ∧
    (∀ x ∈ E, AEStronglyMeasurable (fun j => iteratedFDeriv ℝ i (f j) x) μ) ∧
    ∀ᵐ j ∂μ, ∀ x∈E, ‖iteratedFDeriv ℝ i (f j) x‖ ≤ g j

namespace Crud
variable {E : Set X} {f : J → X → Y} {p : ℕ} {μ}

lemma starts (h : Crud μ E f p) : ∃ g : J → ℝ, Integrable g μ ∧ (∀ x∈E,AEStronglyMeasurable (fun j => f j x) μ) ∧
    ∀ᵐ j ∂μ,∀ x∈E,‖f j x‖ ≤ g j := by
  obtain ⟨g,hg,hM,hG⟩:=h.bound 0 (Nat.zero_le _)
  simp_rw [norm_iteratedFDeriv_zero] at hG
  refine ⟨g,hg,?_,hG⟩
  intro x hx
  let u := continuousMultilinearCurryFin0 ℝ X Y
  have he := u.continuous.comp_aestronglyMeasurable (hM x hx)
  simp_rw [iteratedFDeriv_zero_eq_comp, Function.comp_apply] at he
  simpa only [u,LinearIsometryEquiv.apply_symm_apply] using he

lemma crumb (h : Crud μ E f (p+1)) : Crud μ E (fun i x => fderiv ℝ (f i) x) p := by
  refine ⟨h.opens,fun j x hx => (h.unit j x hx).fderiv_right (by simp),?_⟩
  intro i hi; obtain ⟨g,hg,hM,hF⟩:=h.bound (i+1) (by omega)
  refine ⟨g,hg, fun x hx => ?_,?_⟩
  · let u := continuousMultilinearCurryRightEquiv' ℝ i X Y
    have he := u.continuous.comp_aestronglyMeasurable (hM x hx)
    simp_rw [iteratedFDeriv_succ_eq_comp_right,Function.comp_apply] at he 
    simpa only [u,LinearIsometryEquiv.apply_symm_apply] using he
  filter_upwards [hF] with j hj
  exact fun x hx => (norm_iteratedFDeriv_fderiv).trans_le (hj x hx)

lemma cooked (h : Crud μ E f p) (x) (hx : x∈E) : ContDiffAt ℝ (p:ℕ∞) (fun x => ∫ j,f j x ∂μ) x := by
  induction p generalizing x Y with
  | zero =>
    obtain ⟨g,hg,hM,hF⟩:=h.starts
    have hc : ContinuousOn (fun x => ∫ j, f j x ∂μ) E := continuousOn_of_dominated hM (fun x hx => hF.mono fun j hj => hj x hx)
      hg (Eventually.of_forall fun j x hx => (h.unit j _ hx).continuousAt.continuousWithinAt)
    exact contDiffAt_zero.2 ⟨E,h.opens.mem_nhds hx,hc⟩
  | succ p ih =>
    let F' j := fderiv ℝ (f j)
    let q x := ∫ j,F' j x ∂μ
    obtain ⟨g,hg,hM,hF⟩:=h.crumb.starts
    have hc : ContDiffAt ℝ (p:ℕ∞) q x := ih h.crumb _ hx
    have ht y (hy : y∈E) : HasFDerivAt (fun x => ∫ j, f j x ∂μ) (q y) y := by
      obtain ⟨p,hp,hP,hQ⟩:=h.starts
      have hu : E∈𝓝 y:=h.opens.mem_nhds hy
      exact hasFDerivAt_integral_of_dominated_of_fderiv_le (F':=fun x j => F' j x) hu (mem_of_superset hu fun i => hP i)
        (hp.mono' (hP _ hy) (hQ.mono fun j hx => hx _ hy)) (hM _ hy) hF hg
        (Eventually.of_forall fun j y hy => ((h.unit j _ hy).differentiableAt (by simp)).hasFDerivAt)
    simpa using (contDiffAt_succ_iff_hasFDerivAt.mpr ⟨q,⟨E,h.opens.mem_nhds hx,ht⟩,
      show ContDiffAt ℝ (p:WithTop ℕ∞) q x from hc⟩)
end Crud

-- group portion: interchange actual ordered derivatives in a neighborhood of the corner
section
variable {μ} {n : Side} {G : Gauge}

lemma movement (U : Config G n) (A : Directions G n) (s t : ℝ) : increment (increment U (t • A)) (s • A)=increment U ((s+t) • A) := by
  funext i; apply G.mat_injective
  simp only [increment,G.mat_mul,Pi.smul_apply,G.mat_lieExp,map_smul,add_smul,map_add,←mul_assoc]; congr 1
  haveI : NormedAlgebra ℚ G.Mat := .restrictScalars ℚ ℝ _
  exact (NormedSpace.exp_add_of_commute (((Commute.refl (G.colorMat (A i))).smul_left s).smul_right t)).symm

lemma Crest_turn {U : Config G n} (f : Config G n → Y) (A : Directions G n) (t : ℝ) {i : ℕ} (h : Crest i f (increment U (t • A)))
    (l : List (Directions G n)) (hh : l.length < i) : HasDerivAt (fun x : ℝ => leftDerivs f l (increment U (x • A)))
      (leftDerivs f (A::l) (increment U (t • A))) t := by
  let F (x : ℝ) := increment U (x • A)
  have ht : HasDerivAt (fun x : ℝ => leftDerivs f l (increment (F t) (x • A))) (leftDerivs f (A::l) (F t)) 0 :=
    (h.line _ hh _).hasDerivAt
  let g x : ℝ := x-t
  have hg : HasDerivAt g 1 t := (hasDerivAt_id' _).sub_const _
  have he := (show HasDerivAt _ _ (g t) from (show 0=g t by unfold g; simp) ▸ ht).scomp t hg
  simpa only [F,g, Function.comp_def,one_smul,movement,sub_add_cancel] using he

structure Implanted (μ : Measure J) (y : Config G n) (p : ℕ) (f : J → Config G n → Y) (F : Config G n → Y) where
  hood : Set (Config G n)
  openH : IsOpen hood
  inside : y ∈ hood
  agreement U : U ∈ hood → F U=∫ j,f j U ∂μ
  thermal j U : U∈hood → ContDiffAt ℝ (p:ℕ∞) (fun x => f j (increment U x)) 0
  coords : ∃ O : Set (Directions G n), 0∈O ∧ Crud μ O (fun j v => f j (increment y v)) p
  cuffs (l : List (Directions G n)) : l.length ≤ p → ∃ g : J→ℝ, Integrable g μ ∧
      (∀ U ∈ hood,AEStronglyMeasurable (fun j => leftDerivs (f j) l U) μ) ∧
      ∀ᵐ j ∂μ, ∀ U∈hood, ‖leftDerivs (f j) l U‖ ≤ g j

namespace Implanted
variable {p : ℕ} {f : J → Config G n → Y} {F : Config G n → Y} {U : Config G n}

lemma done (h : Implanted μ U p f F) (l : List (Directions G n)) (he : l.length ≤ p) (V : Config G n) (hv : V∈h.hood) :
    leftDerivs F l V = ∫ j,leftDerivs (f j) l V ∂μ := by
  induction l generalizing V with
  | nil => exact h.agreement _ hv
  | cons A l ih =>
    have hd : l.length < p := he
    let g (t : ℝ) := increment V (t • A)
    have hh : g ⁻¹' h.hood ∈ 𝓝 (0:ℝ) := swing V A (h.openH.mem_nhds hv)
    obtain ⟨v,hv',ht,hF⟩:=h.cuffs (A::l) he; obtain ⟨y,hy,hY,hZ⟩:=h.cuffs l hd.le
    have ha : g 0 ∈ h.hood := show 0∈g ⁻¹' h.hood from mem_of_mem_nhds hh
    let q (j : J) (t : ℝ) := leftDerivs (f j) l (g t)
    let z (j : J) (t : ℝ) := leftDerivs (f j) (A::l) (g t)
    have hp : ∀ (t : ℝ) (ht : t∈g ⁻¹' h.hood) (i : J), HasDerivAt (q i) (z i t) t :=
      fun t ht i => Crest_turn (f i) _ t (into p (f i) (h.thermal i (g t) ht)) l hd
    have hk := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F:=fun t i => q i t) (F':=fun t i => z i t)
      hh (mem_of_superset hh (fun t ht => hY (g t) ht)) (hy.mono' (hY _ ha) (hZ.mono fun j hj => hj _ ha))
      (ht _ ha) (hF.mono fun j hj t ht => hj (g t) ht) hv' (Eventually.of_forall fun i t ht => hp _ ht _)).2
    change deriv (fun t => leftDerivs F l (g t)) 0 = _
    have hr : ∀ᶠ t in 𝓝 0, leftDerivs F l (g t)=∫ j,q j t ∂μ := mem_of_superset hh (fun t ht => ih hd.le (g t) ht)
    have hx := (hk.congr_of_eventuallyEq hr).deriv
    simpa only [z,g,zero_smul,inc_zero] using hx

lemma edge (h : Implanted μ U p f F) : ContDiffAt ℝ (p:ℕ∞) (fun x => F (increment U x)) 0 := by
  obtain ⟨O,ho,H⟩:=h.coords
  apply (H.cooked 0 ho).congr_of_eventuallyEq
  have ht : Tendsto (increment U) (𝓝 0) (𝓝 U) := by simpa only [inc_zero] using (inc_tr U).tendsto 0
  exact ((ht.eventually (h.openH.mem_nhds h.inside))).mono fun j hj => h.agreement _ hj
end Implanted
end
end YM.Multi.Vacuum.Gauss
