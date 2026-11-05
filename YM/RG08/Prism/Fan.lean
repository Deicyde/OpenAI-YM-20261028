import YM.RG08.Prism.Pierce
import YM.RG08.Prism.Shore
import YM.RG08.Atlas.Furnace

/-!
# Finite frames in ledger; connecting C2.2 precision read. Actual per-ord inputs.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Prism
open Function Matrix Lattice Exterior Wilson RG Precision Stationary RG08.Line Fold Drum Bloch Laurent Finset Filter Glyph Room Camera Tack Mount
open scoped Classical Matrix ContDiff Topology BigOperators InnerProductSpace PowerSeries
variable {G:Gauge}{c f:Side}(S:StepData c f)(F:Tree.Forest S.ratio)(b v:Bed)

-- Raw keys: warrant vs phase. reimburse through Ward unscaled map.

def fir (S:StepData c f): (Lines G f 1 ⊕ Lines G c 1)≃ Epic S.patch G c:= (Equiv.sumCongr (splitCo S.ratio _) (Equiv.refl _)).trans (Equiv.prodSumDistrib _ _ _).symm
lemma fir_1 (i:Lines G f 1): fir S (Sum.inl i)=lowSlot S i:=rfl
lemma fir_2 (i:Lines G c 1): fir S (Sum.inr i)=highSlot S i:=rfl

abbrev Indoor (I J:Type):= Matrix I J ℝ
def modes{I J:Type}[Fintype J](T:Indoor I J):Strip I J:=fun i x=> (T*ᵥ x) i
lemma paced {I J:Type}[Fintype J](T:Indoor I J)(i:I): Pace (modes T i):=by unfold modes Matrix.mulVec dotProduct; exact ContDiffAt.sum fun j _=>contDiffAt_const.mul (contDiffAt_apply ℝ ℝ j _)
lemma mode_cash {I J:Type}[Fintype J](T:Indoor I J):rescaleFields (modes T)=fun i=>liftInn (median T i):=by
 funext i
 have he:(modes T i)= ∑ j:J,T i j • (fun x:Cellar J=>x j):=by funext v; rw [Finset.sum_apply];rfl
 rw [rescaleFields,he,Camera.slurry _ _ (fun j _=>show Pace ((T i j) • fun x:Cellar J=> x j) from (contDiffAt_apply ℝ ℝ j _).const_smul (T i j))]
 have ha(j:J):flask ((T i j) • fun x:Cellar J=>x j) = T i j • bump (Room.rod j):=by rw [flask_scale (contDiffAt_apply ℝ ℝ j _),lamp]
 simp_rw [ha]
 ext n:1;change tap _ _=tap _ _;rw [look];unfold tap;rw [map_sum,median,map_sum,map_sum];apply sum_congr rfl;intro j _;rw [PowerSeries.coeff_smul];rw [show (PowerSeries.coeff (n+1) (Camera.bump (Room.rod j))) = (tap (R:=Inn J) n _) from hopper ..]; simp [tap,Room.rod,liftInn,PowerSeries.coeff_C]

variable (b':Bed)(α:ℝ)(C:Castle G)
-- K agreement on leading terms, later consume Cast.starter & Crown. Use eval at any R.

def Proceed (C:Castle G)(b:Bed)(f:Side):Prop:= ∀ x:Cellar (Lines G f 1),
    MvPolynomial.eval x (tap (2:ℕ) (Aggregate.booked (C 0 0) (Mount.stick 0) f)) = (1/2:ℝ)*winB (patron G (Precision.K (b.metric.acts f))) x x -- tap namespace?
 end YM.RG08.Prism
