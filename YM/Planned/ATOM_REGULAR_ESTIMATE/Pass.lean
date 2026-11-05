import YM.Next.WARD_BIN.Lies
import YM.Planned.ATOM_REGULAR_ESTIMATE.Parametric
import YM.Push.LOCAL_SPLITTING.Calculus



/-!
Ordered `U` variations in the full-branch integrals. Many observations can
share a tag/packet and local chart choice in this passage.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.AtomRegular
open Function Filter Lattice Wilson RG MeasureTheory Push.Local Next.Foundations WardBin WardBin.Lies
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical

variable {Z : Type*} [MeasurableSpace Z] {μ : Measure Z} {G : Gauge} {n k l : ℕ} {c : Side}
variable {A : Slab G c l} {V : Config G c} {K : Config G c → ℂ}

lemma journey_lift (V : Config G c) (n : ℕ) (A : Slab G c n) :
    ∃ φ : Panels n → Directions G c, φ 0 = 0 ∧ ContDiffAt ℝ ω φ 0 ∧
      journey V n A =ᶠ[𝓝 0] increment V ∘ φ := by
  suffices h : ∀ i, ContDiffAt ℝ ω (fun y => G.mat (journey V n A y i)) 0 by
    obtain ⟨φ,h1,h2,h3⟩ := Push.Local.lift_germ (journey V n A) _ h
    have ht : journey V n A 0 = V := by
      rw [journey_photon,Function.comp_apply,map_zero,chug_zero]
    exact ⟨φ,h2,h1,by rwa [ht] at h3⟩
  have hg : ∀ m : ℕ, ∀ (W : Panels n → Config G c) (X : Panels n → Slab G c m),
      (∀ i, ContDiffAt ℝ ω (fun y => G.mat (W y i)) 0) → ContDiffAt ℝ ω X 0 →
        ∀ i, ContDiffAt ℝ ω (fun y => G.mat (chug m (W y) (X y) i)) 0 := by
    intro m
    induction m with
    | zero => exact fun _ _ hi _ => hi
    | succ m ih =>
      intro W X hw hx i
      refine ih (fun y => increment (W y) (X y 0)) (fun y => Fin.tail (X y)) (fun i => ?_) ?_ i
      · simp only [increment,G.mat_mul]
        exact (G.exp_jet.contDiffAt.comp (f:=fun y => X y 0 i) _ (contDiffAt_pi.mp (contDiffAt_pi.mp hx 0) i)).mul (hw i)
      exact contDiffAt_pi.mpr fun j => contDiffAt_pi.mp hx j.succ
  exact hg n (fun _ => V) (photon n A) (fun _ => contDiffAt_const) (photon n A).contDiff.contDiffAt

variable {f : Z → Config G c → ℂ}

lemma left_integral (V : Config G c) (A : Slab G c l) (hl : l ≤ k)
    (hF : Covered μ (fun z => f z ∘ increment V) k 0)
    (h : K ∘ increment V =ᶠ[𝓝 0] fun v => ∫ z, f z (increment V v) ∂μ) :
    Chart k K V ∧ Integrable (fun z => iteratedFDeriv ℝ l (f z ∘ journey V l A) 0 cart) μ ∧
      leftDerivs K (List.ofFn A) V = ∫ z, iteratedFDeriv ℝ l (f z ∘ journey V l A) 0 cart ∂μ := by
  have hh : Chart k K V := hF.leaves h
  refine ⟨hh,?_⟩
  obtain ⟨φ,hφ,hφ',hs⟩ := journey_lift V l A
  have he : K ∘ journey V l A =ᶠ[𝓝 0] (K ∘ increment V) ∘ φ := hs.fun_comp K
  have hp : Covered μ (fun z => f z ∘ increment V) k (φ 0) := by rwa [hφ]
  obtain ⟨ht,hj⟩ := hp.test (F':=K ∘ increment V) (by rw [hφ]; exact h) (hφ'.of_le le_top) hl cart
  have H (z) : iteratedFDeriv ℝ l (f z ∘ journey V l A) 0 = iteratedFDeriv ℝ l ((f z ∘ increment V) ∘ φ) 0 :=
    ((hs.fun_comp (f z)).iteratedFDeriv (𝕜:=ℝ) l).eq_of_nhds
  simp_rw [H]
  exact ⟨ht, (Germ.ordered A ((show Germ k K V from hh).prod hl)).trans
    (((congr_arg (fun i : Tensor.T (Panels l) ℂ l => i cart) ((he.iteratedFDeriv (𝕜:=ℝ) l).eq_of_nhds)).trans hj))⟩

end YM.Planned.AtomRegular
