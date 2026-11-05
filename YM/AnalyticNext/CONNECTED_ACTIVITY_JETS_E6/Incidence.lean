import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Weaving
import YM.Push.ABSOLUTE_SUMS.Product


/-!
# HasSum formulas at the true weighted addresses

No volume bound claimed here. No numerators that reselect inserted k or
use optional tents from another step. Marker κ per ticket kept.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary
open Packets Coat
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {P : Teller G} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {μ x W C : ℝ} {L : Side} {I : Rep G f} {R : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable {ι κ : Type*}

lemma log_ext (H : Cash W x μ L R o C T I) : Summable H.w := by
  let F (i : LogIndex c f) : Alphabet c f := Sum.inr (Sum.inl i)
  let p := T; let s : LogIndex c f → Alphabet c f := F
  have hi : Ac.Hit (roadway T I (radiusB x) R.halo) (radiusB x) (fun j => Reserves.tariff H.opt
      (ConnectedActivityE6.lengths T I) (fun _=>0) R.ε (s j)) R.relative (R.goal L x) := by
    intro i; have hg := budget_pull s (Sum.inr_injective.comp Sum.inl_injective) (H.fares.hit i)
    exact hg
  let u (j : LogIndex c f) := Reserves.tariff H.opt (ConnectedActivityE6.lengths T I) (fun _=>0) R.ε (s j)
  have he j : H.w j ≤ u j := by
    have ht := R.usable
    have he : 0≤ ConnectedActivityE6.lengths T I (s j) := H.armed.extra _
    unfold u Reserves.tariff; exact le_mul_of_one_le_right (H.earns (s j)) (Real.one_le_exp (by positivity))
  have hw (i) : 0≤H.w i := H.earns (s i)
  have hx := AbsoluteSums.Product.everyone_ne (w:=u) (roadway T I (radiusB x) R.halo) (radiusB x)
    (fun i => (hw i).trans (he i)) (fun _ _ => exChart ..) hi
  refine hx.2.1.of_nonneg_of_le hw fun i => (he i).trans (le_mul_of_one_le_right ((hw i).trans (he i)) ?_)
  apply Real.one_le_exp; unfold Target.relative; have:= R.bound; have:= R.usable; have:=R.pos; positivity

lemma expense_series (H : Cash W x μ L R o C T I) (X : Coat T F) (h : X.x=x) (hv : X.width=o.K) (hp : X.manifest)
    (z : Air f G) :
    Summable (X.farLog I o.a R.table z) ∧ Summable (fun i : Finset (LogIndex c f) => ∏ j∈i,H.w j) ∧
      HasSum (fun i : Finset (LogIndex c f) => ∏ j∈i,X.raiseAir I o.a R.table z j) (Real.exp (∑' j,X.farLog I o.a R.table z j)) := by
  have hw := log_ext H
  let t := X.farLog I o.a R.table z
  have ht i := ((H.quotes F X h hv hp).2.1 i z)
  have he : Summable t := Summable.of_norm_bounded hw (fun i => (ht i).1)
  have hx := summable_finsetProd_of_summable_nonneg (fun i => (abs_nonneg _).trans (ht i).1) hw
  let K := fun i => X.raiseAir I o.a R.table z i
  refine ⟨he,hx,?_⟩
  have hy : Summable (fun i : Finset (LogIndex c f) => ∏ j∈i,K j) := by
    apply Summable.of_norm_bounded hx; intro i; rw [Real.norm_eq_abs,Finset.abs_prod]
    exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun i _ => (ht i).2)
  let v (i) := 1+K i
  have hg i : v i=Real.exp (t i) := by unfold v K Coat.raiseAir t; ring
  have hi : t=fun i=>Real.log (v i) := funext fun i => by rw [hg,Real.log_exp]
  change HasSum _ (Real.exp (∑' i,t i))
  rw [hi,Real.rexp_tsum_eq_tprod (fun i => hg i ▸ Real.exp_pos _) (hi ▸ he), show v=fun i => 1 + K i from rfl,tprod_one_add hy]
  exact hy.hasSum

namespace Pulse

lemma longA {B m : ℕ} {η r Q : ℝ} {A : Itinerary.Mat f G} (D : Window (along S) B) (hp : Torch η r Q)
    (h : Allow A (along S) m η r Q) (hd : scraps η r Q m B<1) (b : ℝ) (hf : Summable (fun i=> ArmA D A i*b)) :
    HasSum (fun i=>ArmA D A i*b) ((Real.log A.det-∑ i,Batch.joint A D i)*b) := by
  have hz (i : Bond f) : HasSum (fun n : ℕ => ∑ j:G.ColorIndex,lact D A (i,j) (n+1))
     ((∑ j:G.ColorIndex,coil A (i,j)) - Batch.joint A D i) := by
    rw [Batch.joint,← sum_sub_distrib]; exact hasSum_sum (fun j _ => Pulse.nofirst D A hp h (i,j) hd)
  have he : HasSum (fun n:ℕ => (∑ i: Bond f, ∑ j:G.ColorIndex,lact D A (i,j) (n+1))*b)
      ((Real.log A.det-∑ i,Batch.joint A D i)*b) := by
    rw [Pulse.clustered A hp h, Fintype.sum_prod_type,← sum_sub_distrib]
    exact (hasSum_sum fun i _ => hz i).mul_right b
  refine he.sigma_of_hasSum (fun i=>?_) hf
  rw [Finset.sum_mul]; simp_rw [← of_a D A hp h]
  convert hasSum_fintype (fun p : Bond f × Itinerary f (i+3) => ArmA D A ⟨i,p⟩ * b) using 1
  conv_rhs => rw [Fintype.sum_prod_type]
  simp_rw [Finset.sum_mul]

lemma longS {B m : ℕ} {η r Q : ℝ} {A : Itinerary.Mat f G} (D : Window (along S) B) (hp : Torch η r Q)
    (h : Allow A (along S) m η r Q) (hd : Q*distPay η r Q m B<1) (hc : PosDef (D.frameMean A))
    (b : ℝ) (hf : Summable (fun i => ArmS D A i * b)) :
    HasSum (fun i=>ArmS D A i*b) ((Real.log A.det+Real.log (D.frameMean A).det)*b) := by
  refine ((records_C D A hp h hd hc).mul_right b).sigma_of_hasSum (fun i => ?_) hf
  rw [Fintype.sum_prod_type]; simp_rw [← of_s D A]
  convert! hasSum_fintype (fun p : Bond f × Itinerary f (i+1) => ArmS D A ⟨i,p⟩ * b) using 1
  conv_rhs => rw [Fintype.sum_prod_type]
  simp_rw [Finset.sum_mul]

lemma longQ {L : Side} (X : Coat T F) {η r Q Y : ℝ}
    (h : Rotator P L η r Q Y X) (hm : Q*distPay η r Q (tubularPrice G L) X.B<1)
    (z : Air f G) (ht : Summable (X.qunique z)) :
    HasSum (X.qunique z) ((1/2:ℝ)*dotProduct z.ofLp ((X.relating⁻¹-X.plate) *ᵥ z.ofLp)) := by
  have hx := h.scale.flank X.shutter
  have he := Pulse.warp hx (show 0≤Q*distPay η r Q (tubularPrice G L) X.B from by
    apply mul_nonneg h.scale.fuel.le; exact mul_nonneg h.scale.disc (h.scale.heap _)) h.scale.weather.1.le hm
    (show X.plate*X.relating-1=X.shreds from rfl)
  let A (i : ℕ) := (-X.shreds)^(i+1)*X.plate
  let v := z.ofLp
  have ht' (i) : HasSum (fun n=> (A n *ᵥ v) i) (((X.relating⁻¹-X.plate)*ᵥ v) i) := by
    refine hasSum_sum (s:=univ) (f:=fun j n=> A n i j*v j) (fun j _=> ?_)
    exact (Pi.hasSum.mp (Pi.hasSum.mp he i) j).mul_right _
  refine (((hasSum_sum (s:=univ) (fun i _=> (ht' i).mul_left (z i))).mul_left (1/2:ℝ))).sigma_of_hasSum (fun i => ?_) ht
  rw [Fintype.sum_prod_type]
  convert! hasSum_fintype (fun p : Bond _ × Itinerary _ (i+2) => X.qunique z ⟨i,p⟩) using 1
  conv_rhs => rw [Fintype.sum_prod_type]
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; exact (X.circling j i z).symm
end Pulse
end YM.ConnectedActivityE6
