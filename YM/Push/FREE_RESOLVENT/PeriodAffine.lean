import YM.Push.FREE_RESOLVENT.Atlas
import YM.Push.FREE_RESOLVENT.LocalTerms
import YM.Push.FREE_RESOLVENT.TrackBill

/-!
# Actual period comparison at Taylor depth

Work with the same S.Patch & kernel, PathData W and uncut precision on
both periods. Different forests allowed with same local gauge/read cells
for the entry being examined. Quantitative, no taking limits of Q
subcolumns. Choose a path-length cut *on true paths* as paid in the bigger
work boxes and the input row exponent. Then compressed cut-resolvent
jets see exactly the same arithmetic in the matching gauges and locations.
The remaining differences pay exponential margin, even for zero momentum
uses. Actual coherent Taylor tests (no hitting a tree coordinate in a
subtraction with no alignment of the projection); no covariance assertion
about arbitrary rebracketed rays or gauges. Energy u is never enlarged when
shrinking a price; still decay with two drain factors in comparisons.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FreeResolvent.Affine
open Lattice Wilson RG Matrix Laurent Bloch Exterior Precision Tree Bid Work.F03 TestD Filter Function Set
open Work.F08 Lifted Mark View
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
variable {G : Gauge} {f f' c c' n : Side} {S : StepData c f} {P : Patch} {K : KernelChoices}
variable {D m : ℕ} {o : Site c} {o' : Site c'}
variable {h : f.val=c.val*P.L.val} {h' : f'.val=c'.val*P.L.val}
variable (T : Forest (data h K).ratio) (U : Forest (data h' K).ratio)

section marks
variable {ι τ ν X Y E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma mark_change (C : Mark τ X) (H : Mark ν Y) {x y} {f : ι → τ} {g : ι → ν}
    (h : ∀ i, C.cents (f i) x=H.cents (g i) y) (l : List ι) : C.pay (l.map f) x=H.pay (l.map g) y := by
  induction l with
  | nil => rfl
  | cons t l ih => rw [List.map_cons,List.map_cons, pay,pay,h t,ih]

lemma mark_map (l : List τ) (f : τ → ν) (F : E → X) [NormedAddCommGroup X] [NormedSpace ℝ X] (v : ν → E) (x) :
    jet v F (l.map f) x=jet (v ∘ f) F l x := by
  -- dependently use lengths
  have hh : (l.map f).length=l.length := List.length_map _
  have he : ∀ (n m : ℕ) (r : Fin n → E) (s : Fin m → E) (h : n=m), (∀ i, r i=s (Fin.cast h i)) →
      iteratedFDeriv ℝ n F x r=iteratedFDeriv ℝ m F x s := by
    rintro n _ r s rfl h; rw [funext (show ∀ i,r i=s i from h)]
  exact he _ _ (v ∘ _) ((v ∘ f) ∘ l.get) hh (fun i => by simp)

lemma all_dir (l : List τ) {P : E → X} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (L : F →L[ℝ] E) (v : τ → F) (h : ContDiffAt ℝ l.length P 0) :
    jet (L ∘ v) P l 0=jet v (fun x => P (L x)) l 0 := by
  unfold jet; rw [show iteratedFDeriv ℝ l.length (fun x => P (L x)) 0 = _ from Next.Foundations.jets_linear L h]; rfl
end marks

section push
variable {τ : Type*} [Fintype τ] [DecidableEq τ]

def lever (u : τ → raw G c) : (τ → ℝ) →L[ℝ] Vec G c 1 :=
  LinearMap.toContinuousLinearMap (insertion u).mulVecLin

def forge (p : τ → Cover × PAC G 1) (o : Site c) (i : τ) := coarseAt (r:=1) o (p i).1 (p i).2



omit [DecidableEq τ] in
lemma operated (g : τ → Cover × PAC G 1) (hm : ∀ i, size (g i).1 ≤ D) (o : Site c) (o' : Site c')
    (h : 2*D < c.val) (h' : 2*D < c'.val) : alike (lever (forge g o)) (lever (forge g o')) o o' D := by
  intro v z hx i
  change (insertion (forge g o)*ᵥ v) _ = (insertion (forge g o') *ᵥ v) _
  refine Finset.sum_congr rfl fun j _ => ?_
  have he : forge g o j=coarseAt (G:=G) (r:=1) o z i ↔ forge g o' j=coarseAt o' z i := by
    constructor
    · rintro hj
      obtain ⟨h1,h2⟩ := place_inject (Equiv.refl (Co c (PAC G 1))) o D (hm j) hx h (t:=(g j).2) (u:=i) hj
      unfold forge; rw [h1,h2]
    intro hj
    obtain ⟨h1,h2⟩ := place_inject (Equiv.refl (Co c' (PAC G 1))) o' D (hm j) hx h' (t:=(g j).2) (u:=i) hj
    unfold forge; rw [h1,h2]
  change (if _ then _ else _)*v j=(if _ then _ else _)*v j
  rw [if_congr he rfl rfl]

omit [Fintype τ] [DecidableEq τ] in
lemma pins_along (g : τ → Cover × PAC G 1) {D : ℕ} (hm : ∀ i, size (g i).1 ≤ D) {x : Cover} (hx : size x ≤ D)
    (o : Site c) (o' : Site c') (h : 4*D < c.val) (h' : 4*D < c'.val) (l : List τ) (d : ℝ) :
    (marks G c d).pay (l.map (forge g o)) (addr o x) = (marks G c' d).pay (l.map (forge g o')) (addr o' x) := by
  apply mark_change; intro i
  let A := (g i).1
  have hh : size (x-A) ≤ 2*D := by
    have h1 : size A ≤ D := hm i
    rw [sub_eq_add_neg]; apply (size_add ..).trans; rw [size_neg]; omega
  have h (q : Side) (o : Site q) (he : 4*D<q.val) :
      (marks G q d).cents (forge g o i) (addr o x) = Real.exp (d*spread (x-A)) := by
    change Real.exp (d*(separation (addr o x) (addr o A):ℝ))=_
    simp only [addr,separation, add_sub_add_left_eq_sub]; rw [← map_sub, pdist,size_centers q _ hh (by omega)]; rfl
  exact (h _ o (by assumption)).trans (h _ o' h').symm
end push





section comparing
variable {τ ι : Type*} [Fintype τ] [DecidableEq τ] [Fintype ι] [DecidableEq ι]
variable {i : ι ↪ Active G T} {j : ι ↪ Active G U} {W : PathData G} {M σ u ρ : ℝ}
variable (k : (data h K).Choices) (k' : (data h' K).Choices) (hA : Larger (G:=G) (data h K)) (hA' : Larger (G:=G) (data h' K))
variable (hs : 0 < σ) (hm : 0 ≤ M) (hW : Sheet W σ M) (hu : 0 ≤ u)
include hA hA' hs hm hW hu



omit hA hA' hs hm hW hu


include hs hm hW hu


include hA hA'

end comparing
end YM.FreeResolvent.Affine
