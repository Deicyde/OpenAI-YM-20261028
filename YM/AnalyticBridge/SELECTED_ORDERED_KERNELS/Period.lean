import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Slots
import YM.Next.FOUNDATIONS.SU2
import YM.Push.FREE_RESOLVENT.Overlap
import YM.Push.FREE_RESOLVENT.PeriodAffine
import YM.Push.FREE_RESOLVENT.TensorPrice


/-!
# Cross-period readings of ordered Taylor coefficients (FTt precursor)

Same cover displacements of all input arguments (incl repeats); not necessarily
the same trees or group space! Do not charge one unestimated boundary entry
as if it were the corresponding projected kernel on the other torus. Reuse
the actual nonwrapping `drift`, `short_compare` prices, incl path length and
margin exponents. Active arrays in these comparisons (tag dependence on
plant retained). No passage to a phase or station.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SelectedOrderedKernels.Period
open Lattice Wilson RG Function Filter Topology WardBin.Lies Exterior Precision Tree Laurent Bloch FreeResolvent
  Affine Mark TestD View Lifted 
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {c c' f f' : Side} {j R D : ℕ} {P : Patch} {K : KernelChoices}

abbrev Specimen (G : Gauge) (j : ℕ) := Fin j → Cover × PAC G 1



def replace (p : OrderedFinpartition j) (g : Specimen G j) (u : Fin p.length → G.ColorIndex) : Specimen G p.length :=
  fun b => ((g (p.emb b ⟨0,p.partSize_pos b⟩)).1, (g (p.emb b ⟨0,p.partSize_pos b⟩)).2.1,u b)



section comparisons
variable {α β : Type*} [Fintype α] [Fintype β] {m : ℕ} {x y : Site c}
  {F : Config G c → Matrix α α ℝ} {H : Config G c' → Matrix β β ℝ} {d γ M : ℝ}
  {g : Specimen G j} {o : Site c} {o' : Site c'} {a b : α} {a' b' : β}





lemma read {p : OrderedFinpartition j} {u : Fin p.length → G.ColorIndex} (hF : Germ j F 1) (o : Site c) (a b : α) :
      iteratedFDeriv ℝ p.length (over (fun x => F x b a) 1) 0 (ray G c ∘ forge (replace p g u) o) =
        jet (ray G c) (over F 1) (List.ofFn (forge (replace p g u) o)) 0 b a := by
    rw [← Stars.list_result, ← TestD.entry _ _ (smooth_of_le (smooth_over.mpr hF) (by simp [p.length_le]))]; rfl


end comparisons

variable {τ : Type*} [Fintype τ] [DecidableEq τ] {m : ℕ}
  {h : f.val=c.val*P.L.val} {h' : f'.val=c'.val*P.L.val} {S : StepData c f} {W : PathData G} {M σ u ρ : ℝ}
  (hs : 0 < σ) (hm : 0 ≤ M) (hW : Sheet W σ M) (hu : 0 ≤ u)
include hs hm hW hu



variable (T : Forest (data h K).ratio) (U : Forest (data h' K).ratio) (k : (data h K).Choices) (k' : (data h' K).Choices)
    (p : Clip) {o : Site c} {o' : Site c'}
    {i : τ ↪ Active G T} {v : τ ↪ Active G U} {a b : τ}
    (hA : Bid.Larger (G:=G) (data h K)) (hA' : Bid.Larger (G:=G) (data h' K)) (hj : j ≤ m)
    {g : Specimen G j} {n : τ → Cover × Co P.L (PAC G 1)}
    (hf : Copies (data h K) T i o n) (he : Copies (data h' K) U v o' n)
    (hg : ∀ t, size (g t).1 ≤ lengthMark P R D) (hn : ∀ t, size (n t).1 ≤ D)
    (hp : 4*lengthMark P R D < c.val) (hq : 4*lengthMark P R D < c'.val)
    (ha : ∀ k : Active G T, k ∉ Set.range i → ρ ≤ (native c).d (theta _ T (i a)) (theta _ T k))
    (ha' : ∀ k : Active G U, k ∉ Set.range v → ρ ≤ (native c').d (theta _ U (v a)) (theta _ U k))
include hA hA' hj hf he hg hn hp hq ha ha'



-- Uses EXACT real step inputs and the extra order-independent correspondence
-- of all lower-order recolorings, proved inside. No copy theorem assumed for
-- the predictor tree field evaluation after off-flat changes.



end YM.SelectedOrderedKernels.Period
