import YM.Push.FINITE_DETECTION.Pairs
import YM.Push.FINITE_DETECTION.TwoPoint


/-!
# Free rank and an actual finite tested family on the free side

Pick one joint bump for all entries at fixed d before asking for k-scale
comparison; openness at the reflected pair on true Shell. Uses only
non-coincident points and normalized compact smooth separated tests. Also
produce a generic point pair (row candidate for corrected-column arguments).
No requirement of RP of any *interacting* table here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.FiniteDetection
open Free Maxwell Kelvin Dash Extraction Function Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
variable {G : Gauge}

lemma free_criterion (F : Labels.Frames G) (d : ℕ) (v : (standard F).Ref d)
    (hv : ∀ w : (standard F).Ref d, (freeTable F).value (fun _ : Fin 2 => d) detectors ![v,w] = 0) : snap F d v = 0 := by
  let e := (F.level d).coords
  let p := e.symm v
  let q := Labels.tensor σ (Labels.realBar p)
  have h : Wick.moment G detectors ![observable G d p,observable G d q] = 0 := by
    rw [show (![observable G d p, observable G d q] : Fin 2 → WickPol G) =
        (fun i => observable G d (e.symm (![v,e q] i))) by funext i; fin_cases i <;> simp [p]]
    exact hv (e q)
  suffices observable G d p = 0 from Subtype.ext this
  by_contra he
  exact (two_detect p he).ne' (congr_arg Complex.re h)

lemma free_null (F : Labels.Frames G) (d : ℕ) : (freeTable F).null d = LinearMap.ker (snap F d) := by
  ext1 v
  constructor
  · intro h
    apply free_criterion F d v
    intro w
    let f (i : Fin 2) : (standard F).Token := ⟨d,(![v,w] : Fin 2 → (standard F).Ref d) i⟩
    exact (freeTable F).each_place (table_sym F) h detectors_in f 0 rfl
  intro h; exact (projectionExact F).mp ((show snap F d v = 0 from h).symm ▸ Submodule.zero_mem _)

/-- There are no further exterior free nulls of the actual Shell sector. -/
theorem residual_trivial (G : Gauge) (d : ℕ) : residual G d = ⊥ := by
  apply le_antisymm _ bot_le
  rintro v hv
  let F := Labels.frames G
  obtain ⟨w,rfl⟩ := full F d v
  exact (free_null F d ▸ (projectionExact F |>.mp hv) : w ∈ LinearMap.ker (snap F d))

variable {C : Family G} {d : ℕ}

def pointPair (C : Family G) (d : ℕ) (x : Points 2) : Model C d →ₗ[ℂ] Model C d →ₗ[ℂ] ℂ :=
  let M := (Standard C).classMoment (Standard C) (fun _ => d) x
  let T i (u : Fin 2 → Model C d) := M.toLinearMap u i
  have he a b c : T 0 ![a,b] c = M ![c,b] := by unfold T; rw [MultilinearMap.toLinearMap_apply]; congr 1; ext1 i; fin_cases i <;> simp
  have ht a b c : T 1 ![a,b] c = M ![a,c] := by unfold T; rw [MultilinearMap.toLinearMap_apply]; congr 1; ext1 i; fin_cases i <;> simp
  LinearMap.mk₂ ℂ (fun a b => M ![a,b])
    (fun a b u => by simpa only [he] using (T 0 ![a,u]).map_add a b)
    (fun c a u => by simpa only [he] using (T 0 ![a,u]).map_smul c a)
    (fun a u v => by simpa only [ht] using (T 1 ![a,u]).map_add u v)
    (fun c a u => by simpa only [ht] using (T 1 ![a,u]).map_smul c u)
lemma point_project {x : Points 2} (hx : x ∈ conf 2) (v w : C.label d) :
    pointPair C d x ((Standard C).project d v) ((Standard C).project d w) = (Standard C).value (fun _ => d) x ![v,w] := by
  change (Standard C).classMoment (Standard C) (fun _ : Fin 2 => d) x ![(Standard C).project d v, (Standard C).project d w] = _
  rw [← (Standard C).class_agrees (Standard C) (table_sym _) (fun _ => le_rfl) (fun _ => d) hx ![v,w]]
  congr 1; funext i; fin_cases i <;> simp
lemma point_cont (p q : Model C d) : ContinuousOn (fun x => pointPair C d x p q) (conf 2) :=
  ((Standard C).class_smooth (Standard C) (table_smooth _) (fun i : Fin 2 => ⟨d,(![p,q] : Fin 2 → Model C d) i⟩)).continuousOn

variable {ι : Type*} [Fintype ι]

def freeMatrix (β : Module.Basis ι ℂ (Model C d)) (x : Points 2) : Model C d →L[ℂ] ι → ℂ :=
  .pi fun i => LinearMap.toContinuousLinearMap ((pointPair C d x).flip (β i))

lemma free_injective (β : Module.Basis ι ℂ (Model C d)) : Injective (freeMatrix β detectors) := by
  suffices LinearMap.ker (freeMatrix β detectors).toLinearMap = ⊥ from LinearMap.ker_eq_bot.mp this
  apply le_antisymm _ bot_le; rintro p hp
  obtain ⟨v,rfl⟩ := (Standard C).onto d p
  rw [Submodule.mem_bot]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  rw [free_null]; apply free_criterion _ d v
  intro w; rw [← point_project detectors_in v w, ← β.sum_repr ((Standard C).project d w),map_sum]
  apply Finset.sum_eq_zero; intro i _; rw [map_smul]; exact (congr_arg _ (congr_fun hp i)).trans (smul_zero _)

lemma near_free (β : Module.Basis ι ℂ (Model C d)) {x} (hx : x ∈ conf 2) :
    Tendsto (freeMatrix β) (𝓝 x) (𝓝 (freeMatrix β x)) := matrix_tends β fun i => tendsto_pi_nhds.mpr fun j =>
  (point_cont (β i) (β j) |>.continuousAt ((conf_open _).mem_nhds hx))

theorem generic_free (β : Module.Basis ι ℂ (Model C d)) : ∃ x ∈ generic 2, Injective (freeMatrix β x) := by
  have he := (near_free β detectors_in).eventually (ContinuousLinearMap.isOpen_injective.mem_nhds (free_injective β))
  obtain ⟨x,hx,hq⟩ := mem_closure_iff_nhds.mp ((Measure.dense_of_ae (almostGeneric 2)) detectors) _ he
  exact ⟨x,hq,hx⟩

def freeTest (β : Module.Basis ι ℂ (Model C d)) (t : Test 2) : Model C d →L[ℂ] ι → ℂ :=
  let R := (Standard C).representative d
  have hl : Live (Standard C) := fun _ v t => t.smearing (((Standard C).smooth_read (table_smooth _) v).continuousOn)
  .pi fun i => ((pairShot t (d := d) (R (β i))).core (Standard C) hl).comp (LinearMap.toContinuousLinearMap R)
omit [Fintype ι] in
lemma freeTest_apply (β : Module.Basis ι ℂ (Model C d)) (t : Test 2) (v i) :
    freeTest β t v i = t.applyTo (fun x => pointPair C d x v (β i)) := by
  let R := (Standard C).representative d
  change t.applyTo (fun x => (Standard C).read x ((pairShot t (d := d) (R (β i))).record (d := d) (R v))) = _
  rw [pair_mem (d := d)]
  apply congr_arg t.applyTo; funext x
  change (Standard C).value (fun _ => d) x ![R v,R (β i)] = (Standard C).value (fun _ => d) x (fun j => R ((![v,β i] : Fin 2 → _) j))
  congr 1; funext j; fin_cases j <;> rfl

section Bumps
variable {n : ℕ}




end Bumps


end YM.Push.FiniteDetection
