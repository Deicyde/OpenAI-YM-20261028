import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Exponent

/-!
# Chart purchases

Convert a single outer scalar/function cost to this Z's ordered
jets; not coordinatewise comparison with Lie derivatives. E profile
calculus pays the small *normalized* arguments before charging these
conversions. Keep ell on each rank to the stated k.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussian
open Function Filter Set Lattice RG Wilson ProjectorNext.Equivariance Next.Foundations
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Gauge} {c : Side} {x y : Config G c → E} {f : E → F}
    {D : Directions G c → Prop} {V : Config G c} {k : ℕ} {r v H : ℝ}

def Farewell (f : E → F) (x : E) (k : ℕ) (H : ℝ) := ∀ j ≤ k, ‖iteratedFDeriv ℝ j f x‖ ≤ H

lemma Farewell.after {q : E} (h : Farewell f q (k+1) H) : Farewell (fderiv ℝ f) q k H := by
  intro i hi; rw [norm_iteratedFDeriv_fderiv]; exact h _ (Nat.succ_le_succ hi)
lemma Farewell.nonneg {q : E} (h : Farewell f q k H) : 0 ≤ H := (norm_nonneg _).trans (h _ (le_refl k))
lemma Farewell.value {q : E} (h : Farewell f q k H) : ‖f q‖ ≤ H := by simpa using h 0 (Nat.zero_le k)

lemma smooth_around (hx : HasOrderAt x V k) (hf : ContDiffAt ℝ k f (x V)) : HasOrderAt (f ∘ x) V k := by
  apply hf.comp_of_eq _ hx
  · simp
  change x (increment V 0)=_; rw [Work.G07.at_zero_increment]

lemma next_one (hf : ContDiffAt ℝ ↑(k+1) f (x V)) (h : HasOrderAt x V (k+1)) (A : Directions G c) :
    leftDerivs (f ∘ x) [A] V = fderiv ℝ f (x V) (leftDerivs x [A] V) := by
  let g : ℝ → E := fun t => x (increment V (t • A))
  have ht : HasDerivAt g (leftDerivs x [A] V) 0 := left_has A (l:=[]) (by simp) h
  have hi := hf.differentiableAt (by simp)
  have he : g 0=x V := by simp [g,Work.G07.at_zero_increment]
  rw [← he] at hi ⊢
  exact (hi.hasFDerivAt.comp_hasDerivAt _ ht).deriv

lemma Charge.inspect (hf : Charge D k V r x) (h : Farewell f (x V) k H) (hs : ContDiffAt ℝ k f (x V)) :
    Ticket D k V H (climbing k r) (f ∘ x) := by
  induction k generalizing F with
  | zero =>
    refine ⟨smooth_around hf.smooth hs,h.nonneg,climbing_nonneg _ hf.nonneg,fun l hl _ => ?_⟩
    rw [Nat.le_zero,List.length_eq_zero_iff] at hl; subst l; simpa [leftDerivs] using Farewell.value h
  | succ k ih =>
    refine ⟨smooth_around hf.smooth hs,h.nonneg,climbing_nonneg _ hf.nonneg,fun l hl hi => ?_⟩
    induction l using List.reverseRecOn with
    | nil => simpa [leftDerivs] using Farewell.value h
    | append_singleton l J _ =>
      let e := fderiv ℝ f ∘ x; let g := leftDerivs x [J]
      let C (U : Config G c) := HasOrderAt x U (k+1) ∧ ContDiffAt ℝ ↑(k+1) f (x U)
      have hc : C V := ⟨hf.smooth,hs⟩
      have he (W : Config G c) (hw : C W) (A : Directions G c) : ∀ᶠ t : ℝ in nhds 0,C (increment W (t • A)) := by
        have ht := (left_has A (l:=[]) (show ([]:List (Directions G c)).length < k+1 by simp) hw.1).continuousAt
        change Tendsto (fun t : ℝ => x (increment W (t • A))) _ (nhds (x (increment W (0 • A)))) at ht
        simp_rw [zero_smul,Work.G07.at_zero_increment] at ht
        exact (recur hw.1 A).and (ht.eventually (hw.2.eventually (by simp)))
      have hj : Ticket D k V H (climbing k r) e := ih (hf.halt (Nat.le_succ k)) h.after (hs.fderiv_right (by push_cast; rfl))
      have hx := hj.bill_apply (hf.offset (hi J (by simp)))
      rw [Work.G07.left_append, along (g:=fun U => e U (g U)) hc he (fun _ hw => next_one hw.2 hw.1 J)]
      refine (hx.price l (by simpa using hl) (fun i hv => hi _ (List.mem_append_left _ hv))).trans ?_
      simp only [List.length_append,List.length_singleton,pow_succ',← climbing_succ]
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (climbing_le _ hf.nonneg) h.nonneg) (pow_nonneg (climbing_nonneg _ hf.nonneg) _)




end YM.AnalyticBridge.LocalGaussian
