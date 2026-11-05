import YM.AnalyticBridge.MARGINAL_MULTIPLIER_3B1D.Qualify
import YM.Next.SCHEDULE.Stadium
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Canonical


/-!
In situ Borel checks for local V jets as functions of Gaussian and Haar
bindings at fixed tags, including piecewise flag selections. Even with hard
Borel U factors: when using a pre-mask derivative must still LICENSE it.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.MarginalMultiplier3b1d
open Function Filter Set Lattice RG Wilson Next.SectorChange Pressure Pressure.Tube Pressure.Stores
  Push.SectorMeasure Precision Tree Matrix Next.SectorChange.Schur Next.SectorChange.ResidualPrice
  FiniteMatrix Gaussian  Next.Foundations Push.Local
open MeasureTheory
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {X : Type*}

section diff
private def tick (i : ℕ) := 1/((i:ℝ)+1)
private def scanD (f : Config G c → ℝ) : List (Directions G c) → Config G c → ℝ
  | [], V => f V
  | x::l,V => limUnder atTop (fun i : ℕ => (scanD f l (increment V (tick i • x)) - scanD f l V)/tick i)
lemma scanD_eq {f : Config G c → ℝ} {V : Config G c} (l : List (Directions G c)) (hf : Chart l.length f V) : scanD f l V = leftDerivs f l V := by
  induction l generalizing V with
  | nil => rfl
  | cons x l ih =>
    have he := left_has x (Nat.lt_succ_self _) hf
    have ht : Tendsto tick atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hm := (hasDerivAt_iff_tendsto_slope_zero.mp he).comp (tendsto_nhdsWithin_iff.mpr ⟨ht, Eventually.of_forall fun i h => ?_⟩)
    simp_rw [zero_add,zero_smul,Work.G07.at_zero_increment] at hm
    apply Tendsto.limUnder_eq (hm.congr' ?_)
    filter_upwards [ht.eventually (chart_near hf x)] with i hi
    simp [ih (V:=V) (hf.of_le (Nat.cast_le.mpr l.length.le_succ)),ih (V:=increment V _) (hi.of_le (Nat.cast_le.mpr l.length.le_succ)),div_eq_mul_inv,mul_comm]
    change tick i=0 at h; have he : 0 < tick i := by unfold tick; positivity
    exact he.ne' h
private lemma scanD_meas [MeasurableSpace X] {f : X → Config G c → ℝ} (hf : ∀ V, Measurable fun i => f i V) (l : List (Directions G c)) (V : Config G c) : Measurable (fun i => scanD (f i) l V) := by
  induction l generalizing V with
  | nil => exact hf V
  | cons y l ih => exact (StronglyMeasurable.limUnder (fun i : ℕ => (((ih (increment V (tick i • y))).sub (ih V)).div_const _).stronglyMeasurable)).measurable
lemma jet_param [MeasurableSpace X] {f : X → Config G c → ℝ} (hf : ∀ V, Measurable fun i => f i V) (l : List (Directions G c)) {V : Config G c} (he : ∀ i, Chart l.length (f i) V) : Measurable (fun i => leftDerivs (f i) l V) := by
  simp_rw [← fun i => scanD_eq l (he i)]; exact scanD_meas hf l V
end diff

section matrix
variable [MeasurableSpace X] {ι : Type} [Fintype ι] [DecidableEq ι] {L : X → Gaussian.Table ι}
lemma det_meas (h : ∀ i j, Measurable fun x => L x i j) : Measurable fun x => (L x).det := by
  simp_rw [Matrix.det_apply,Units.smul_def]; apply Finset.measurable_fun_sum; intro p _
  have H : Measurable fun x => ∏ i, L x (p i) i := Finset.measurable_fun_prod _ fun _ _ => h ..
  rcases Int.units_eq_one_or (Equiv.Perm.sign p) with hp|hp <;> simp [hp]; exacts [H,H]
lemma inv_meas (h : ∀ i j, Measurable fun x => L x i j) (i j : ι) : Measurable fun x => (L x)⁻¹ i j := by
  simp_rw [Matrix.inv_def,Ring.inverse_eq_inv,Matrix.smul_apply,Matrix.adjugate_apply,smul_eq_mul]
  refine (det_meas h).inv.mul (det_meas (fun i j => ?_)); simp_rw [Matrix.updateRow_apply]; split <;> first | exact measurable_const | exact h ..
end matrix

namespace Kernel
 
variable [MeasurableSpace X] {I J ρ : Type} [Fintype I] [Fintype J] [Fintype ρ] {Z : ChartRatio G}
    {q : Chi} {T : Tube G S} {R : Rep G f} {Pt : Teller G} {V : Config G c} {g x d δ w : ℝ} {F : Forest S.ratio} {A : Stores S} {k : S.Choices}
    {L : Leaf G A x F I J ρ} {P : Location f I J}

/-- Parameter Borel separately at every coarse W needed for using the jets
in a later integral. Does NOT need countably many exceptional sets over W. -/
structure Seen (h : X → Kernel G c I J ρ) : Prop where
  cov V i j : Measurable fun x => (h x).cov V i j
  gram V i j : Measurable fun x => (h x).gram V i j
  flat i j : Measurable fun x => (h x).flat i j
  mean V i : Measurable fun x => (h x).mean V i
  draw V i : Measurable fun x => (h x).draw V i
  signal V i : Measurable fun x => (h x).signal V i
  offset V i : Measurable fun x => (h x).offset V i
  holds i : Measurable fun x => (h x).holds i
variable {h : X → Kernel G c I J ρ}
namespace Seen
lemma stages (hS : Seen h) : Measurable fun x => (h x).stage g V := by
  exact (measurable_pi_lambda _ (hS.mean V)).add ((tape.measurable.comp (measurable_pi_lambda _ (hS.draw V))).const_smul g)
lemma fields (hS : Seen h) : Measurable fun x => (h x).atLinks S P g V := by
  apply measurable_pi_lambda; intro i
  unfold atLinks; split
  · rename_i he
    have ht := (measurable_pi_apply he.choose).comp (hS.stages (g:=g) (V:=V))
    exact (G.lieExp_cont.measurable.comp ht).mul_const _
  split
  · exact hS.holds ..
  exact measurable_const



lemma receipt (q : Chi) (Z : ChartRatio G) (d g p : ℝ) (hz : LocalRatio Z) (hd : 0<d) (hs : 4*d<Z.radius) (hS : Seen h) (V : Config G c) : Measurable fun x => (h x).ledger p V + (h x).correction V + (h x).chartLog q Z d g V := by
  have hlog {u : X → ℝ} (h : Measurable u) : Measurable fun x => Real.log (u x) := Real.measurable_log.comp h
  have h1 : ∀ i, Measurable fun x => logGuard q Z d ((h x).stage g V i) := fun i => (logGuard_smooth q hz hd hs).continuous.measurable.comp ((measurable_pi_apply i).comp (hS.stages (g:=g) (V:=V)))
  have hm : Measurable fun x : X => ∑ i, ((h x).offset V i * (h x).offset V i) := Finset.measurable_fun_sum _ fun i _ => (hS.offset V i).mul (hS.offset V i)
  have ht : Measurable fun x : X => ∑ i, ((h x).signal V i * (h x).draw V i) := Finset.measurable_fun_sum _ fun i _ => (hS.signal V i).mul (hS.draw V i)
  have hu (i j) := ((inv_meas (hS.cov V) i j).sub (hS.gram V i j)).mul (hS.draw V j)
  have hc := det_meas (L:=fun x => (h x).cov V) (hS.cov V)
  have he := det_meas (L:=fun x => (h x).flat) hS.flat
  have hL : Measurable fun x => (h x).ledger p V := by
    unfold ledger; exact measurable_const.add (measurable_const.mul ((hlog hc).add (hlog he)))
  have hC : Measurable fun x => (h x).correction V := by
    unfold correction dotProduct mulVec; simp_rw [dotProduct,Matrix.sub_apply]
    exact ((measurable_const.mul hm).add ht).add (measurable_const.mul (Finset.measurable_fun_sum _ fun i _ => (hS.draw V i).mul (Finset.measurable_fun_sum _ fun j _ => hu i j)))
  exact (hL.add hC).add (Finset.measurable_fun_sum _ fun i _ => h1 i)

lemma serves (q : Chi) (hZ : LocalRatio Z) (hd : 0<d) (hs : 4*d<Z.radius) (hS : Seen h) (hR : R.activities.Valid R.p δ w) (W : Config G c)
    {r : X → Finset ℕ} {s : Finset ℕ} (hr : ∀ x, r x ⊆ s) (hh : ∀ j∈s, MeasurableSet {x | j∈r x}) (o : Finset ℕ) :
    Measurable (fun x => (h x).multiplier S P R q Z d (r x) o W) := by
  let u (x : X) i := if i∈r x then (h x).light S P R i W else 0
  have he i (hi : i∈s) : Measurable fun x => u x i := Measurable.ite (hh i hi) ((hR.regular.smooth i).borel.comp hS.fields) measurable_const
  unfold multiplier expense
  have hx x : ∑ i∈r x, (h x).light S P R i W = ∑ i∈s,u x i := ((Finset.sum_congr rfl fun i hi => (if_pos hi).symm)).trans (Finset.sum_subset (hr x) (by intros; simp [*]))
  simp_rw [hx]
  exact (((doors_smooth q d).continuous.measurable.comp hS.stages).mul (Finset.measurable_fun_prod _ fun i _ => (hR.forced.meas i).comp hS.fields)).mul
    (Real.continuous_exp.measurable.comp ((hS.receipt _ _ _ _ _ hZ hd hs W).sub (Finset.measurable_fun_sum _ he)))


end Seen
variable {Y : X → LinkArray G (Frozen A x F)} {z : X → Prices G (Active A x F)}
lemma Seen.selected {s o b : Finset ℕ} (hS : Seen h) (hR : L.Reads R s o b) (q : Chi) (hz : ∀ t, L.Binds T k R.beta q d (Y t) (z t) V (h t))
    (hZ : LocalRatio Z) (hd : 0<d) (hs : 4*d<Z.radius) (hA : R.activities.Valid R.p δ w) (W : Config G c) : Measurable fun t => let U := Leaf.field T F A V k q d R.beta (Y t) (z t)
    (h t).multiplier S L.location R q Z d (Leaf.lights s R U) o W := by
  apply hS.serves q hZ hd hs hA W (fun _ => Finset.filter_subset ..) (s:=s) (fun j hj => ?_)
  simp only [Finset.mem_filter,hj,true_and, ← fun t => (hz t).health (hR.E j hj) R.p.threshold]
  exact hS.fields (healthy_closed ..).measurableSet
end Kernel
end YM.AnalyticBridge.MarginalMultiplier3b1d
