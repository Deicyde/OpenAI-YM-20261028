import YM.Progress.STATIONARY_SCENES.Dispatch

/-!
# Spending RScene: a reduction of the CLASSICAL matching invoice

Use in the downwards generation of paths. Includes compatibility with every
period (fix one, but no tests on future periods to trigger this), every tree
and unmodified kinetic metric. Tree transfer uses F05. No claim on unmasked
jets above what we produce/use. The genuine 3 and 4 identities in the smaller
bill are likely very expensive; don't erase from `.Planned`! Top Wilson also.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Progress.StationaryScenes

open Filter Lattice RG RG.Supply Precision Bid Tree Matrix Exterior Wilson Function Bloch
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace

variable {G : Gauge} {n : Side}

section oi
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {F T : E → ℝ}


end oi

section low
open Work.F03
variable {p σ C Λ a A} {W : PathData G} {D : Bed}








end low

section use
variable {a : Levels G} {H : Horizon a} {N m : ℕ} {P : PathData G} {η : ℝ}

namespace Answer
lemma gap (R : Answer H N m P η) (p : ℕ) (F : Forest (a.clock.op m p).ratio) :
    PriceGap F (a.params (m+1)).clip P η := (R.testimony p F).2.1
lemma critical (R : Answer H N m P η) (p : ℕ) (F : Forest (a.clock.op m p).ratio) :
    Critical F (a.params (m+1)).clip P (R.station p F) := (R.testimony p F).2.2.1





abbrev classicalValue (R : Answer H N m P η) (p : ℕ) (F : Forest (a.clock.op m p).ratio)
    (t : (a.clock.op m p).Choices) (x : Dir G (a.S.side m p)) :=
  tested F t (a.params (m+1)).clip P x (R.station p F x)

lemma classical_value (R : Answer H N m P η) (p : ℕ) (F : Forest (a.clock.op m p).ratio)
    (t : (a.clock.op m p).Choices) :
    R.classicalValue p F t 0 = 0 ∧ fderiv ℝ (R.classicalValue p F t) 0 = 0 ∧
      ContDiffAt ℝ ω (R.classicalValue p F t) 0 := by
  have hv := R.critical p F
  have hk := ((R.testimony p F).1 t)
  let f := uncurry (tested F t (a.params (m+1)).clip P)
  have hx : f 0 = 0 := hk.1
  have hh : fderiv ℝ f 0 = 0 := hk.2.1
  let g := fun x => (x,R.station p F x)
  have he : g 0 = 0 := Prod.ext rfl hv.1
  have hs : ContDiffAt ℝ ω g 0 := contDiffAt_id.prodMk hv.2.1
  have hy : ContDiffAt ℝ ω f (g 0) := he.symm ▸ (hv.2.2 t).1
  change f (g 0) = 0 ∧ fderiv ℝ (f ∘ g) 0 = 0 ∧ ContDiffAt ℝ ω (f ∘ g) 0
  refine ⟨he ▸ hx, ?_, hy.comp 0 hs⟩
  rw [fderiv_comp _ (hy.differentiableAt (by simp)) (hs.differentiableAt (by simp)),he,hh,
    ContinuousLinearMap.zero_comp]





end Answer

namespace Service
variable {s : Sheet G} {D : Rolls s} {V : PostCost D} {K : MapPrices}




end Service
end use
end YM.Progress.StationaryScenes
