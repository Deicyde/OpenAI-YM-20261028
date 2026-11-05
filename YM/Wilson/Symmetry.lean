import YM.Wilson.Law

/-!
# Invariance of the **physical measure**

Actual product Haar, one action on all probes including phases.

Includes bounded measurable as well as continuous integrands.

A chessboard statement
will be separate; symmetry by itself asserts no factorization or positivity.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Wilson

open Lattice MeasureTheory Filter Set
open scoped Matrix.Norms.Frobenius Topology ENNReal
variable {G : Gauge} {n : Side}

/-- Permutation used in the Haar computation, maps positive links to positive
orientations of their images. On e.g. a negative reflection this also shifts the
base by one negative step. -/
def sendEdge (s : Signed) (t : Site n) (e : Edge (Site n)) : Edge (Site n) :=
  (((posDir e.2).rotate s).used (affine s t e.1))

theorem sendEdge_injective (s : Signed) (t : Site n) : Function.Injective (sendEdge s t) := by
  rintro ⟨x,a⟩ ⟨y,b⟩ h
  have hs (z : Site n) (c : Axis) : (sendEdge s t (z,c)).2 = s.perm c := by
    unfold sendEdge Step.used; split <;> rfl
  have e : a=b := s.perm.injective <| by rw [← hs x a, ← hs y b, h]
  subst b
  suffices x=y by rw [this]
  apply s.act_injective
  unfold sendEdge Step.used at h
  cases he : s.flip a <;> simpa [Step.rotate, affine, posDir, he] using h

@[fun_prop] theorem continuous_pull (s : Signed) (t : Site n) :
    Continuous (pull s t (K := G.El)) := by
  apply continuous_pi
  intro e; simp only [pull, Step.read]; split <;> fun_prop

/-- Pullback is one relabelling of independent Haar links, with inversion. -/
theorem prior_pull (s : Signed) (t : Site n) :
    MeasurePreserving (pull s t (K := G.El)) (prior G n) (prior G n) := by
  let e : Equiv.Perm (Edge (Site n)) := Equiv.ofBijective (sendEdge s t) ⟨sendEdge_injective s t,
    Finite.injective_iff_surjective.mp (sendEdge_injective s t)⟩
  have he : MeasurePreserving
      (fun U : Config G n => (fun f => U (sendEdge s t f))) (prior G n) (prior G n) := by
    have hm := measurePreserving_piCongrLeft (fun _ : Edge (Site n) => G.probHaar) e.symm
    convert hm using 1 <;> first | rfl | skip
    funext U k
    change U (e k) = _
    simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]
  let q (f : Edge (Site n)) (u : G.El) := if s.flip f.2 then u⁻¹ else u
  have hq : MeasurePreserving (fun U : Config G n => (fun f => q f (U f)))
      (prior G n) (prior G n) := by
    refine measurePreserving_pi (fun _ => G.probHaar) (fun _ => G.probHaar) (f := q) ?_
    intro i
    cases hF : s.flip i.2
    · simpa only [q, hF, Bool.false_eq_true, ↓reduceIte] using! MeasurePreserving.id G.probHaar
    · simpa only [q, hF, ↓reduceIte] using G.preserve_inv
  convert hq.comp he using 1
  funext U k
  unfold pull q Step.read; dsimp only [Function.comp_apply]
  simp [sendEdge, Step.rotate, posDir]

theorem prior_gauge (t : Site n → G.El) :
    MeasurePreserving (gauge t) (prior G n) (prior G n) :=
  measurePreserving_pi (fun _ : Edge (Site n) => G.probHaar) (fun _ => G.probHaar)
    (f := fun i u => t i.1 * u * (t (i.1 + step i.2))⁻¹) fun e => G.preserve_two_sided (t e.1) (t (e.1+step e.2))⁻¹

/-- No bijectivity assumption needed here. -/
theorem law_preserved (β : ℝ) {e : Config G n → Config G n}
    (hf : MeasurePreserving e (prior G n) (prior G n)) (hw : ∀ x, energy (e x) = energy x) :
    MeasurePreserving e (law G n β) (law G n β) := by
  refine ⟨hf.measurable, ?_⟩
  apply Measure.ext; intro x hx
  rw [Measure.map_apply hf.measurable hx, law, withDensity_apply _ hx,
    withDensity_apply _ (hf.measurable hx), ← lintegral_indicator hx,
    ← lintegral_indicator (hf.measurable hx)]
  have he : (e ⁻¹' x).indicator (weight β) = (x.indicator (weight β)) ∘ e := by
    classical
    funext y
    by_cases hxy : e y ∈ x <;> simp [indicator, weight, bare, hw, hxy]
  rw [he]
  have h := lintegral_map (g := e) (μ := prior G n)
    ((weight_meas β).indicator hx) hf.measurable
  rw [hf.map_eq] at h
  exact h.symm

theorem law_pull (β : ℝ) (s : Signed) (t : Site n) :
    MeasurePreserving (pull s t (K := G.El)) (law G n β) (law G n β) :=
  law_preserved β (prior_pull s t) fun x => energy_pull x s t

theorem law_gauge (β : ℝ) (t : Site n → G.El) :
    MeasurePreserving (gauge t) (law G n β) (law G n β) :=
  law_preserved β (prior_gauge t) fun x => energy_gauge x t

theorem law_translate (β : ℝ) (t : Site n) :
    MeasurePreserving (translate t (K := G.El)) (law G n β) (law G n β) := by
  rw [show (translate t (K := G.El)) = pull 1 t from funext fun U => (pull_one t U).symm]
  exact law_pull β 1 t

theorem moment_pull (β : ℝ) (s : Signed) (t : Site n) (F : Config G n → ℂ)
    (hf : Integrable F (law G n β)) : moment β (F ∘ pull s t) = moment β F := by
  let e := pull s t (K := G.El)
  have h : MeasurePreserving e (law G n β) (law G n β) := law_pull β s t
  have hi := integral_map (μ := law G n β) (φ := e) (f := F) h.aemeasurable
    (by rw [h.map_eq]; exact hf.aestronglyMeasurable)
  rw [h.map_eq] at hi
  exact hi.symm
end YM.Wilson
