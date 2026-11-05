import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Prism.Brass

/-!
# `Prism` debits. Numbers purchase Rate orders at Wald crossing.

Always rank using ambient coverweight bound, all footprints, after-L only.
t θ in V9 Desk fixed, not adapting uniform trajectory sup. Luxembourg purchases
 spare epsilon BEFORE clocks. Does not consume frequency at a changed monitor.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Brim
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell Flux Poll Pond Silica Eider Metric Set Gaussian Tablet Quill Baffle Prism
open WardBin.Lies Push.PriceCompiler Foramen Gate
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}
variable {B B' : BudgetPoint} {Y : Support c} {K : Support f} {U : Config G c} {p j n : ℕ} {L : Side}
variable {d A t C' w M N z β W k ε J' L₀ X' : ℝ}
section stars
variable {v r b f s p q k' t g u : ℝ→ℝ}
set_option linter.unusedVariables false in
lemma absolut (hp : Rate G L d p): Rate G L d (fun x=>|p x|):= hp.compare (Eventually.of_forall fun x=>(abs_abs _).le)
lemma bell (ha : Rate G L 0 v) (hc : Rate G L 0 r): Rate G L 0 (fun x=>v x*r x) := by simpa only [zero_add] using! ha.mul hc
lemma prep (ha : Rate G L 0 v) (j : ℕ) : Rate G L 0 (fun x=> v x^j) := by simpa only [zero_mul] using! ha.pow j
lemma tide0 (j : ℕ) (ha : Rate G L 0 p) (hb : Rate G L d q) (hu : Rate G L C' u) : Rate G L (d+C') (fun x=> freight j (p x) (q x) (u x)):= by
  unfold freight; simpa only [zero_add] using! (ha.mul (hb.mul hu)).mul_right ((1+(1+1):ℝ)^j)
lemma tonic (ha : Rate G L 0 v) (hb : Rate G L 0 p) (j : ℕ): Rate G L 0 (fun x=> Prism.banner (v x) (p x) j) := by
  unfold Prism.banner token; refine Rate.mul_right ?_ _
  suffices h : ∀ s:Finset ℕ, Rate G L 0 (fun x=> ∑ i∈s, ((p x*v x)*(p x*v x)+1)^i*(p x*v x)) from h _
  intro s; induction s using Finset.induction_on with
  | empty=> simp only [Finset.sum_empty]; exact Rate.const _
  | insert i s hi ih=>
    simp_rw [Finset.sum_insert hi]; have he := bell hb ha; exact Rate.add (bell (prep ((bell he he).add (Rate.const 1)) i) he) ih

variable (n : ℕ)
lemma flecks (ha : Rate G L 0 p) (hb : Rate G L 0 q) (hv : Rate G L d v) :
    Rate G L d (fun x=> hoop (v x) (q x) (p x) n) ∧
    Rate G L d (fun x=> gear (v x) (q x) (p x) n) ∧
    Rate G L d (fun x=> sail (v x) (q x) (p x) n) ∧ Rate G L d (fun x=> Prism.beam n (p x) (q x) (v x)) := by
  have ht := tonic hb ha n; have hp:= tide0 n ha hv ht; rw [add_zero] at hp
  have hz:= (prep ha 2).mul hp; rw [zero_add] at hz
  have hx:= tide0 n ha ht hp; rw [zero_add] at hx
  refine ⟨hp,hz,?_,?_⟩
  · simpa only [zero_add,add_zero] using! (ha.mul hz).mul (prep ((Rate.const 1).add ha) n)
  have hh:= tide0 n ha hb (tide0 n ha hx hb); have hf:= tide0 n ha hv (tide0 n ha ht hb); have hr:= tide0 n ha hb (tide0 n ha ht hv); simp only [zero_add,add_zero] at hh hf hr
  exact (hh.add hf).add hr
variable (Q : Anthem n) (N : ℝ)
lemma projectionX (ha : Rate G L 0 p) (hb : Rate G L 0 q) (hv : Rate G L d v) : Rate G L d (fun x=> plumage Q (p x) (q x) (v x)) := by
  obtain ⟨-,-,hq,h⟩:=flecks n ha hb hv; exact (hq.mul_left Q.logE).add h
lemma b_power (ha : Rate G L 0 p) (hb : Rate G L 0 q) : Rate G L 0 (fun x=> Bpower Q (p x) (q x)) := by
  have hc:= Rate.const (G:=G) (L:=L) (1:ℝ)
  have hf := tide0 n ha hb hb; rw [zero_add] at hf
  have ht : Rate G L 0 (fun x=> Prism.tally0 n (p x) (q x)):= by
    unfold Prism.tally0; exact bell ((prep (hc.add ha) n).mul_left _) ((prep (hc.add (hf.add hc)) n).mul_left _)
  have he : Rate G L 0 (fun x=> reck Q (p x) (q x)):= (prep (hc.add ((hc.add ht).mul_right n)) n).mul_left _
  have hh:= tide0 n ha hb (tide0 n ha (tonic hb ha n) hb); simp only [zero_add] at hh
  exact (prep (hc.add (hc.add (he.add (hh.add hh)))) n).mul_left _

lemma blends (ha : Rate G L 0 p) (hb : Rate G L 0 q) (hv : Rate G L d v) (hk : Rate G L d k') (hd : d ≤ 0) (hr : Rate G L d (fun x=> Real.exp (-(f x)))) :
    Rate G L d (fun x=> Prism.blend Q (p x) (q x) (v x) (k' x) (f x) N) := by
  have hB:= b_power n Q ha hb
  have hs:= projectionX n Q ha hb hv
  have he : Rate G L 0 (fun x=> Prism.incomeB Q (p x) (q x)) := (bell hb hB).mul_right _
  have hx : Rate G L d (fun x=> incomeD Q (p x) (q x) (v x)) := by
    unfold incomeD tensor0; simpa only [zero_add] using! (hb.mul ((hB.mul (hs.mul_left Q.expE)).mul_right _)).mul_right ((1+(1+1):ℝ)^n)
  have hy : Rate G L 0 (fun x=> altitude Q (p x) (q x) (v x)) :=
    ((bell he (hb.mul_left _)).add (bell ((hx.weaken hd).add he) hb)).mul_right _
  have hf : Rate G L d (fun x=>ground0 Q (p x) (q x) (v x) (k' x)):= by refine Rate.add ?_ hx; unfold incomeD at hx; simpa only [add_zero] using! hk.mul he
  refine Rate.add (absolut hf) ?_
  have hh:Rate G L d (fun x=> spentP (p x) N (f x)) := by
    unfold spentP; simp_rw [Real.exp_add]; simpa only [zero_add] using! ha.mul ((hr.mul_right (Real.exp (N/2))).mul_left 2)
  simpa only [add_zero] using! hh.mul (absolut hy)
end stars
end YM.PhysicalNext.Repeat.Brim
