import YM.Extra.FREE_DETECTOR_ALGEBRA.Audience
import YM.Extra.FREE_DETECTOR_ALGEBRA.Axle

set_option warningAsError false

/-! A homogeneous real frame, not assuming the packed presentation is
orthonormal for any probe radius. -/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD
open Function Filter Set Tensor Analysis Maxwell Wick Pair Labels SphereTest Residue OPE Ward Climb MvPolynomial
open scoped Topology ContDiff BigOperators RealInnerProductSpace ComplexOrder Matrix ENNReal

variable {G : Gauge} (F : Frames G) (d : ℕ)
local notation "W" => Table.Field (freeTable F) d
local notation "γ" => writes F d

structure RStage (F : Frames G) (d : ℕ) where
  m : ℕ
  b : Module.Basis (Fin (m+1)) ℂ ((freeTable F).Field d)
  w (i : Fin (m+1)) : ℕ × ℕ
  weighs (i : Fin (m+1)) : AtWeight F (b i) (w i).1
  length (i : Fin (m+1)) : Length (writes F d (b i)) (w i).2
  real_i (i : Fin (m+1)) : (freeTable F).conj (table_spin F) d (b i)=b i
  cap (i : Fin (m+1)) : (w i).1≤d
  unit_ : b 0 = (freeTable F).unit d
  corners (i : Fin (m+1)) : ∃ j, b i=pack F j

abbrev compileW (a : Slot G) : ℕ×ℕ := (a.fst+2,1)
lemma weight_collapse (v : Slot G →₀ℕ) : Finsupp.weight compileW v=(Finsupp.weight costKey v,Finsupp.weight letterCount v) := by
  ext <;> simp [Finsupp.weight_apply,Finsupp.sum,Prod.fst_sum,Prod.snd_sum,compileW,costKey,letterCount]
lemma at_alcove (i : (F.level d).Index) :
    IsWeightedHomogeneous compileW (γ (pack F i)) ((F.level d).grades i) := by
  let B := F.level d
  have ha := (pure_grade _ _).mp (B.pure i)
  rw [pack,sourceAt,LinearMap.comp_apply,writes_project]
  change IsWeightedHomogeneous _ (observable G d (B.coords.symm (B.coords (B.basis i)))) (B.grades i)
  rw [LinearEquiv.symm_apply_apply]
  exact gradeMove bidegree compileW reduceEq (gradientReduce (fun i => (i+2,1))) _ _ ha

def recorded : RStage F d := by
  classical
  apply Classical.choice
  obtain ⟨n,b,h1,h2,h3⟩ := frameRows F d (table_spin F)
  choose f hf using h3; let w i := (F.level d).grades (f i)
  have ht (i : Fin (n+1)) : IsWeightedHomogeneous compileW (γ (b i)) (w i) := hf i ▸ at_alcove F d (f i)
  refine ⟨⟨n,b,w,fun i v hv => ?_,fun i v hv=> ?_,h2,fun i => (F.level d).bound (f i),h1,fun i=> ⟨f i,hf i⟩⟩⟩
  · exact congr_arg Prod.fst ((weight_collapse v).symm.trans (ht i hv))
  exact congr_arg Prod.snd ((weight_collapse v).symm.trans (ht i hv))

variable {F d} (B : RStage F d)


end YM.Extra.FD
