import YM.Push.CUTOFF_PROJECTORS.Equations

/-!
# Small producer facts about the finite equation receipt

The β and `Along energy` parts can be cashed without any Woke or detector
hypotheses. Include also closure operations for checking derivatives in an
actual stencil. Only local facts about finite-cutoff prerequisites, not
aiming to do the IBP/disjointness/copy estimates here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.CutoffProjectors.Packet
open Function Filter Lattice Source RG Wilson
open scoped Topology BigOperators Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {Y Y' : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Y'] [NormedSpace ℝ Y'] {f g : Config G n → Y}

theorem along (h : Continuous f) (d : Edge (Site n) → G.ColorIndex → Config G n → Y)
    (hd : ∀ e i U, HasDerivAt (fun t : ℝ => f (increment U (t • forward e i))) (d e i U) 0)
    (he : ∀ e i, Continuous (d e i)) : Along f := by
  have hh e i : d e i = derivative f e i := funext fun U => (hd e i U).deriv.symm
  exact ⟨h, fun e i U => hh e i ▸ hd e i U, fun e i => hh e i ▸ he e i⟩

theorem Along.add (hf : Along f) (hg : Along g) : Along (fun U => f U + g U) :=
  along (hf.continuous.add hg.continuous) _ (fun e i U => (hf.exact e i U).add (hg.exact e i U))
    fun e i => (hf.rate e i).add (hg.rate e i)

theorem Along.apply (hf : Along f) (L : Y →L[ℝ] Y') : Along (fun U => L (f U)) :=
  along (L.continuous.comp hf.continuous) _
    (fun e i U => L.hasFDerivAt.comp_hasDerivAt _ (hf.exact e i U)) fun e i => L.continuous.comp (hf.rate e i)

theorem Along.constant (x : Y) : Along (n:=n) (G:=G) (fun _ => x) :=
  along continuous_const (fun _ _ _ => 0) (fun _ _ _ => hasDerivAt_const ..) (fun _ _ => continuous_const)



theorem Along.sum {ι : Type*} (s : Finset ι) (u : ι → Config G n → Y) (hu : ∀ i ∈ s, Along (u i)) :
    Along (fun U => ∑ i ∈ s, u i U) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp; exact Along.constant _
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hu a (by simp)).add (ih fun i hi => hu _ (Finset.mem_insert_of_mem hi))








end YM.Push.CutoffProjectors.Packet
