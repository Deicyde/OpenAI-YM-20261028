import YM.Next.RANK.Prepaid

/-!
# Unchanged β still supplies payable unmarked threshold representation

This exercises one constructive way two of the unmarked requirements in
`Provisions` (`fund` candles and `survivors`) **by themselves** can be obtained. Does NOT give the necessary step-W
or restored raw kernel estimate at this course; this route keeps β unchanged,
using regroupings of labels at each step. May need different restarted β
& lattices of labels for producing other gates -- their existence must still
be joint. No reinterpretation of Schedule/Path.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes
open Function MeasureTheory Filter Asymptotics Lattice Wilson RG Perch Atlas Spindle Peak Station Ac Alarm Thirst Corona Value Marker Cells Edition Finset RG.Supply Ship Bid Labels Paint
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {C : Family G} {P : Sheet G} {O : Rolls P} {D : Protection O} {W : Delays D} {F : Bar W} {B : Wait F} {d i j k m : ℕ}
variable {V : Cohesion C d} {b : ℝ} (R : RG.Levels G) (X : HaarBudget G)

def keeping (H : C.Makes) (p N k) (hi : k≤N) : Course C N p k:=
  { changeβ := fun m=> C.path.β N p m
    same := fun _ _ _ => rfl
    allow := hi
    pos := fun _ h=> Overlay.beta_positive H.wilson h }

lemma unchanged {q : ℝ} (hv : Metering V X k q) (H : C.Makes)
    (hs : ∀ j ≤ k, Station.width C.path.levels V.fixed k ≤ j → TableReady C j q (load (V.current k).era) (V.current k).era.coast.a) (hp : k≤m) p :
    let L:=keeping H p m k hp
    ∃ (A : (i:ℕ)→Rep G (C.side i p)),survivors C m k p hv.cost.pane (A k)∧∀ i (_ : Station.width C.path.levels V.fixed k ≤ i) (hL : i ≤ k), C.path.β m p i=(A i).beta∧(C.path.rep m p i).eval=(A i).eval∧ Perch.Candle L i (A i) (hL.trans hp):= by
  intro L; let a:= V.current k
  have H' i (hx : Station.width C.path.levels V.fixed k ≤ i) (h : i ≤ k) := hs i h hx
  letI (i : ℕ) : Nonempty (Rep G (C.side i p)) := ⟨C.path.rep m p i⟩
  choose! A hA using fun i hx h => parser C (h.trans hp) H (H' i hx h) p
  have ht:= (Station.wider C.path.levels V.fixed k).trans (Station.before ..)
  refine ⟨A,?_,fun i hi h'=>?_⟩; swap
  · have hY:= hA i hi h'
    have hm := lights C (h'.trans hp) (keeping H p m i (h'.trans hp)) H _ (A i) hY
    have hp' := hm.settle.tied.coupling
    refine ⟨hp',?_, ⟨⟨⟨hm.settle.tied.density,hp'⟩,hm.settle.proper⟩,hm.budget,hm.threshold⟩⟩
    exact hY.1.symm
  have hs:(V.current k).band=V.fixed:= V.sameB _
  have hpane: TableReady C k q (load a.era) a.era.coast.a:= hv.cost.pane
  exact hA k ht le_rfl

-- from paired scheduling numerical capacity

end YM.Next.Rank.Tapes
