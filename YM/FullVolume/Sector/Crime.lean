import YM.FullVolume.Sector.Pith
/-! Force value holograph (includes unmasked Poll.dice sector emissions with flags still intact). No V derivatives or labels lost. First entropy on the same aperture. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Empire
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider Reserves Brush Metric Foramen Gate Tablet
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat PhysicalNext.Repeat.Alabaster FullVolume.Ray
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G} {W : ℝ}
variable {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W} {R : RG.Rep G f}
    {x₀ μ C:ℝ} {H : Cash W x₀ μ L Q o C T R} -- implicit v
    {v s t b δ A n B : ℝ} {j k : ℕ}
variable {F : Tree.Forest S.ratio} {i η r q u d L' A' f':ℝ} {K:ℕ} {χ:Chi}
namespace Tune
variable (U:Tune H v δ)
-- continuation of raw labels. Reimburse Sales optional once.
local notation "B₀" => radiusB x₀
local notation "Q'" => stella Q
local notation "g" => Q.goal L x₀
abbrev ports (j:Fin 3):= U.beams (Lyre.trio j) (U.lay (Lyre.trio j).2)
abbrev tipLog (i:LogIndex c f):= ∑ j:Fin 3,(U.ports j).w i
abbrev tipBag (i:ℕ):= ∑ j:Fin 3,(U.ports j).v i
abbrev receipt (p:Lyre.Signal 0)(a:ℝ):= rates (fun i=>(FullVolume.Ray.bounty (k:=2) Lyre.trio * v^2)* U.tipBag i) (fun i=>p.A*v^2*U.tipLog i) a
abbrev sheet (p:Lyre.Signal 0) (ν a:ℝ):= Mixed.costs S Q.halo (radiusB x₀) (steamP S ((Q').costs L μ R.beta x₀ ν)) (U.receipt p a)
abbrev paycheck (i:ℕ):= U.tipBag i
lemma tip_b i p: 0≤ (U.ports p).v i:= (U.ports p).fares.nonneg (.inl i)
lemma tip_l i p: 0≤ (U.ports p).w i:= (U.ports p).fares.nonneg (.inr (.inl i))
lemma pepper i : tipLog U i≤ 3* Q.goal L x₀:= (Finset.sum_le_sum (fun p (_:p∈univ)=> (U.ports p|>.fares).atom (by unfold Target.relative; linarith [Q.bound,Q.pos,Q.usable]) Q.usable.le (Sum.inr (Sum.inl i)) (exChart ..))).trans_eq (by simp)
lemma furnace (p:Lyre.Signal 0) : Sales B₀ Q.relative Q.ε (footprints T R Q.halo B₀) (U.receipt p (H.alarms*topStorm S.patch)) (units T R) (Lyre.salary p v * (3*(Q.goal L x₀)+(Q.goal L x₀))):=by
  let P:= U.ports; let k i:= (P i).opt
  have hp i: Sales B₀ Q.relative Q.ε (footprints T R Q.halo B₀) (k i) (units T R) (g):=by
    have h:=surveyed (T:=T) (U.seats _ (U.lay (Lyre.trio i).property)) Q.halo B₀
    rw [← h.1,← h.2]; exact (P i).fares
  have he:= suite_sum (v:=fun _=> g) k _ hp; rw [Finset.sum_const,nsmul_eq_mul,card_univ,Fintype.card_fin] at he; norm_cast at he
  have hf:= tribute he (show Sales B₀ Q.relative Q.ε H.birth H.opt (units T R) g from H.fares)
  let z:=FullVolume.Ray.bounty (k:=2) Lyre.trio; have hz:0≤z:=FullVolume.Ray.bounty_nn _
  have hu : z*v^2≤ Lyre.salary p v:=by change _≤ (z+p.A)*v^2+_; rw [add_mul]; linarith only [mul_nonneg p.pos (sq_nonneg v)]
  have ht:p.A*v^2 ≤ Lyre.salary p v:=by change _≤ (z+p.A)*v^2+_; rw [add_mul]; linarith only [mul_nonneg hz (sq_nonneg v)]
  have hv : 1≤ Lyre.salary p v:= le_add_of_nonneg_left (mul_nonneg (add_nonneg hz p.pos) (sq_nonneg v)); refine hf.shift (zero_le_one.trans hv) ?_ ?_
  · rintro (i|i|i); · exact mul_nonneg (mul_nonneg hz (sq_nonneg v)) (Finset.sum_nonneg fun p _=> U.tip_b i p)
    · exact mul_nonneg (mul_nonneg p.pos (sq_nonneg v)) (sum_nonneg fun p _=> U.tip_l i p)
    exact H.fares.nonneg (.inr (.inr i))
  rintro (i|i|i)
  · simp_rw [Pi.add_apply,Finset.sum_apply]; exact mul_le_mul hu (le_add_of_nonneg_right (H.fares.nonneg (.inl i))) (sum_nonneg fun p _=> U.tip_b i p) (zero_le_one.trans hv)
  · simp_rw [Pi.add_apply,Finset.sum_apply]; exact mul_le_mul ht (le_add_of_nonneg_right (H.fares.nonneg (.inr (.inl i)))) (sum_nonneg fun p _=> U.tip_l i p) (zero_le_one.trans hv)
  let x: Alphabet c f:=.inr (.inr i); apply le_trans _ (le_mul_of_one_le_left (hf.nonneg x) hv); simp_rw [Pi.add_apply,Finset.sum_apply]; exact le_add_of_nonneg_left (sum_nonneg fun i _=>hp i|>.nonneg x)
end Tune
end YM.ConnectedActivityE6.Empire
