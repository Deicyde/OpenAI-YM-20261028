import YM.AnalyticNext.QUARTIC_MATCH.Range

/-!
# Logarithmic-path prescription through cubic and quartic (cost-takers)

Fixed H, chosen cubic prescription retained. If specifying a cost about `Spatial`
below it means about these literal kernels on these finite periods, with `Spatial`
per *physical* link argument and all others arithmetically in that tag.

Upstream use needs `Spatial` PRODUCED on funded P with pre-L constants to get
classical recurrence (or expose only post-L limitations). This file pays them as
inputs and derives the exact path data. Two distinct exponents, Janus (all
multiples & genuine unmasked pipeline). Exposes cost paid for new atoms,
including actual path weights; not beta-weighted.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch
open Lattice RG Precision Bid Function Matrix Wilson Exterior Filter Laurent Tensor Joint BoxChain Analyzers
open Mail Residual
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {c : Side} {p : Clip} {R : PathData G}

-- overwrite when filling after the cubic recipe/exact comparison at that scale. We will require quartic coefficients zero
-- on input model R witnessing the lower jets; can arrange already blank for .debt comparisons.
def fourth (R : PathData G) (W : ℕ→Atom G 4) : PathData G := { R with quartic := W }
def third (R : PathData G) (W : ℕ→Atom G 3) : PathData G := { R with cubic := W }

theorem base_more (h : ∀ i, (R.quartic i).coeff=0) (P : Clip) (W : ℕ→Atom G 4) :
    baseAt (c:=c) P (fourth R W) = baseAt P R + impact W := by
  have hp (U : Config G c) : uncut R.quartic U=0 := by simp [Atom.unmasked,Atom.poly,h,uncut]
  have he (U : Config G c) : quadratic P (fourth R W) U = quadratic P R U := rfl
  funext x
  simp_rw [Pi.add_apply,baseAt,mainTerm,he, hp, add_zero,show (fourth R W).cubic=R.cubic from rfl,
    show (fourth R W).quartic=W from rfl, impact, Patch.average, Finset.sum_add_distrib,mul_add]



variable {τ D B : ℝ}





lemma banks_add {n : ℕ} {r F : Dir G c → ℝ} (hr : ContDiffAt ℝ ω r 0) (hf : ContDiffAt ℝ ω F 0)
    (hl : ∀ k : ℕ, k<n → iteratedFDeriv ℝ k F 0=iteratedFDeriv ℝ k r 0)
    (W : ℕ → Atom G n) (h : SumBudget (fun i => (W i).budget τ) D) (hp : 0<τ)
    (he : Tensor.coeff (impact W) n 0=Tensor.coeff (F-r) n 0) (hc : ∀ j, j<n → Tensor.coeff (impact (c:=c) W) j 0=0) :
    ∀ j : ℕ, j≤n → Precision.SameJet j F (r+impact W) := by
  have ht := impact_cont (c:=c) hp h
  intro j hi
  refine ⟨hf,hr.add ht, coeff_eq ?_⟩
  rcases lt_or_eq_of_le hi with hv|hv
  · rw [Tensor.coeff_add (hr.of_le le_top) (ht.of_le le_top),hc _ hv,add_zero,Tensor.coeff,hl _ hv]; rfl
  subst j
  rw [Tensor.coeff_add (hr.of_le le_top) (ht.of_le le_top),he,sub_eq_add_neg F,
    Tensor.coeff_add (hf.of_le le_top) (show ContDiffAt ℝ n (-r) 0 from hr.neg.of_le le_top),Tensor.neg_coeff]; abel

namespace Analyzers
variable (G : Gauge)
namespace Series

/-- At all geometries downstairs. use even from just the lower exact for
specified `d`. All orientations charged by W, and hold V-penalty IN
canonical germ. Costs of other rows to use on same `S`! -/
theorem open_four (P : Printed 3) (σ : ℝ) (he : 0 < σ) :
    ∃ δ Q : ℝ, 0<δ ∧ 0≤Q ∧ ∀ {K : Patch} {L : KernelChoices} {M : Bed} {R W : PathData G}
        {p q : Clip} {v τ C Λ D b T t : ℝ}
        (S : Analyzers.Series K L G M p W v) (hp : W.Bounds p τ C Λ) (hh : R.Bounds q t T b),
      (∀ i, (R.quartic i).coeff=0) → (∃ s B, ∀ c : Side, allowanceSide K ≤ c.val → Spatial ((S.debt hp hh 4).raw c) s B) →
      ∀ d : ℕ→Side, (∀ i, allowanceSide K ≤ (d i).val) → Tendsto (fun i => (d i).val) atTop atTop →
        (∀ i : ℕ, Spatial ((S.debt hp hh 4).raw (d i)) σ D) →
          (∀ i : ℕ, ∀ k<4, iteratedFDeriv ℝ k (S.canonical (d i)) 0=iteratedFDeriv ℝ k (baseAt q R (c:=d i)) 0) →
          ∃ A : rootArray G 3, SumBudget (fun i => (letters P A i).budget δ) (Q*D) ∧
            ∀ i j : ℕ, j≤4 → SameJet j (S.canonical (d i)) (baseAt q (fourth R (letters P A))) := by
  obtain ⟨δ,Q,hδ,hQ,H⟩:= Mail.writes G 3 P (by omega) σ he
  refine ⟨δ,Q,hδ,hQ,?_⟩
  intro K L M R W p q v τ C Λ D b T t S hp hh hN HN d hd hD ha hl
  obtain ⟨A,hA,h⟩ := H _ _ (S.debt hp hh 4) HN d hd hD
    (fun i => Residual.closed (S.choice _) S.society hp (S.solved (d i) (hd i)) (S.controller _ (hd i)) hh S.cheap
      (S.gap _ (hd i)) (hl _)) D ha
  refine ⟨A,hA,fun i j hv => ?_⟩
  rw [base_more hN]
  exact banks_add (base_smooth hh) (S.leg_value _ (hd i)) (hl _) (letters P A) hA hδ (h i).1 (h i).2 j hv


end Series
end Analyzers
end YM.AnalyticNext.QuarticMatch
