import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Export
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.WaltPrice

/-!
# Real ratio bills

Any post-L theta on the arm envelope. For combined determinant-exponential
expense double etc as rooted continuation charges. `fixed` for every short
look-up halo. Keep henceforward Stroke linear letters smooth at z directions
and U on any patch, and with probability constants in one Air. Ghost
exponent explicit in Funnel only.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {P : Teller G} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {η r Q Y β : ℝ} {L : Side}

lemma fixed {ι : Type*} [Fintype ι] {o : ι→ Site c} {m : ℕ} (h : Census m o) {d B : ℕ} (he : 0<B)
    (X : ι→ Support c) (hp : ∀ i, X i⊆Animals.neighbors (d*B) (o i))
    {A ε C : ℝ} (hA : 0≤A) (hC : 0≤C) : Sales B A ε X (fun _ => C) (fun _ => 0)
      (((Animals.ballCost (d*B):ℝ)*m)*(C*Real.exp (A*Animals.ballCost d))) := by
  refine ⟨fun _=>hC, fun x=>budget_finite (fun i => ?_) ?_⟩
  · unfold Reserves.tariff; split <;> positivity
  simp only [Reserves.tariff,Nat.cast_zero,mul_zero,add_zero, Real.exp_zero,mul_one,← Finset.sum_filter]
  apply le_trans (b:=∑ _j∈univ.filter fun i=> x∈X i, C*Real.exp (A*Animals.ballCost d))
  · refine sum_le_sum fun i hi => ?_; gcongr; exact (Lattice.Corona.cover_mono (hp _) B).trans (Lattice.Corona.tile _ _ _ he)
  rw [sum_const,nsmul_eq_mul]; apply mul_le_mul_of_nonneg_right _ (by positivity)
  have ht : (univ.filter fun i=>x∈X i).card ≤ Animals.ballCost (d*B)*m := by
    refine (card_le_card (show univ.filter _ ⊆ withinH o x (d*B) from fun i hi => ?_)).trans (count_near h ..)
    exact (joins ..).mpr ((Animals.neighbors_mem ..).mp (Animals.neighbors_back _ (hp i (mem_filter.mp hi).2)))
  exact_mod_cast ht

namespace Coat

/-- Common period tests. Authorize μ with contours post-L. -/
structure Tender (x W γ K C E : ℝ) (X : Coat T F) : Prop where
  time_eq : X.x=x
  width_eq : X.width=K
  cap : 0<C
  charge : 0≤E
  mean i : ‖X.μ i‖≤ C*X.t
  upper i : |(X.plate *ᵥ X.driftM+X.linearBill) i| ≤ E
  access : ShellAccess S G X.x W K γ

lemma tends_val (P : Teller G) (L : Side) (D : Patch) (hd : D.Branches P.bind G)
    (η r Q Y W γ K k : ℝ) (hθ : Torch η r Q) : ∃ C : ℝ, 0<C ∧ ∃ E : ℝ→ℝ,
    Rate G L k E ∧ ∀ᶠ x in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (F : Forest S.ratio)
      (X : Coat T F), X.x=x → X.width=K → S.patch=D → S.patch.L=L → Rotator P L η r Q Y X → X.manifest →
        ShellAccess S G x W K γ → Tender x W γ K C (|E x|) X := by
  obtain ⟨C,hC,E,h,hG⟩ := dividend P L D hd η r Q Y W γ K hθ k
  refine ⟨C,hC,E,h,hG.mono ?_⟩
  intro x hx c f S T F X he hp H HH hZ hi ht
  have hv := hx _ _ _ _ F X he hp H HH hZ hi ht
  exact ⟨he,hp,hC,abs_nonneg _,hv.2.2.1,fun i => (hv.2.2.2 _).trans (le_abs_self _),he.symm ▸ ht⟩

/-- Bounds explicit numeric across beta bands including determinant
orth weight. -/
def burst (G : Gauge) (L : Side) (x : ℝ) := Real.sqrt (2*betaF G x L)
lemma burst_h {x : ℝ} {L : Side} (h : β ≤ 2*betaF G x L) : (gStep β)⁻¹ ≤ burst G L x := by
  unfold gStep burst; rw [inv_inv]; gcongr
lemma burst_rate (G : Gauge) (L : Side) : Rate G L (1/2) (burst G L) := by
  refine (Rate.power (G:=G) (L:=L) (a:=1/2) |>.mul_left (Real.sqrt 2)).congr ?_
  filter_upwards [Delay.shift_pos G L] with x hx; unfold burst
  exact (Real.sqrt_mul (by norm_num : 0 ≤ (2:ℝ)) (betaF G x L)).trans (congr_arg _ (Real.sqrt_eq_rpow _))

/-- For Quant. -/
theorem sellers {G : Gauge} (P : Teller G) (L : Side) {W γ K η r Q C Y H k A ε : ℝ}
    (h : Torch η r Q) (m : ℕ) (hm : 4 ≤ m) (hA : 0≤A) (hp : 0<H) (hC : 0<C) {E : ℝ→ℝ}
    (he : Rate G L (k-1/2) E) : ∃ U J C₁ C₂ : ℝ → ℝ, Rate G L 0 U ∧ Rate G L k J ∧ Rate G L k C₁ ∧ Rate G L k C₂ ∧
    ∀ᶠ x in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (F : Forest S.ratio)
      (X : Coat T F), X.x=x → S.patch.L=L → Rotator P L η r Q Y X → Tender x W γ K C (|E x|) X →
    let B := X.B
    let Xq := capQ S η r Q (tubularPrice G L) B G (U x)
    Sales B A ε (receipt S B m 2) Xq Sigma.fst (C₁ x) ∧
    Sales B A ε (town S B m) (fun (_:Bond f)=>J x) (fun _=>0) (C₂ x) ∧
      ∀ β>0, β ≤ 2*betaF G x L → ∀ z : Air f G,
      (∀ p,|X.chain β z H p| ≤ Xq p) ∧
        ∀ p,|X.qfirst β z H p| ≤ J x := by
  let u := Census.tubularPrice G L
  let U x := burst G L x*Pressure.fiery G x L*muRate C H
  have hu : Rate G L 0 U := by convert (((burst_rate G L).mul Rate.flame).mul_right (muRate C H)) using 1; ring
  obtain ⟨X,hX,hg⟩ := Itinerary.out P L m 2 A ε hA hm (show (-1:ℝ)<0 by norm_num)
    (fun x => centreQ η r Q u (radiusB x) G (U x)) (fun x => etaS η r Q u (radiusB x) G)
    (show Rate G L k _ from by
      convert ((((hu.pow 2).mul_left (1/2:ℝ)).mul_right (Itinerary.flagP (G:=G)^4)).mul
        ((((h.physical G L k u).mul_left (payE η r Q u)).mul_left Q).mul_left Q)) using 1
      · ring
      rfl)
    (show Rate G L (-1) _ from by
      exact (((h.physical G L (-1) u).mul_left (payE η r Q u)).mul_left Q).mul_left (Itinerary.flagP (G:=G)))
  let b x := burst G L x* |E x|
  let J x := (Fintype.card G.ColorIndex:ℝ)*(U x*b x)
  have hj : Rate G L k J := by
    have hbr := (burst_rate G L).mul (he.compare (Eventually.of_forall fun _ => (abs_abs _).le) : Rate G L (k-1/2) (fun x => |E x|))
    convert (hu.mul hbr).mul_left (Fintype.card G.ColorIndex) using 1; ring
  let i := (L.val^4*Fintype.card Axis)
  let M x := ((Animals.ballCost ((m+1)*radiusB x):ℝ)*i)*(J x*Real.exp (A*Animals.ballCost (m+1)))
  have hx : Rate G L k M := by
    have he := Census.width_rate G L (m+1) 0; simp only [add_zero] at he
    convert (he.mul_right i).mul (hj.mul_right _) using 1; ring
  refine ⟨U,J,X,M,hu,hj,hX,hx,hg.mono ?_⟩
  intro x hG c f S T F X he hL hY hT B Xq
  subst x
  have ht := hY.scale
  have hF := hY.room.fiery
  have hk := hY.full.hQ
  have hu : 0≤ U X.x := by unfold U burst muRate; rw [← hL]; positivity
  have hb : 0 ≤ b X.x := by unfold b burst; positivity
  have his : 100 ≤ B := hY.room.sight.1
  have he := hG c f S T hL hY.room
  have hn : 0≤ Window.distPay η r Q u B := mul_nonneg ht.disc (ht.heap _)
  have ho : 0<Q := ht.fuel
  refine ⟨he (by change 0≤ centreQ _ _ _ u B G _; unfold centreQ flagP; positivity) (by
    change 0≤etaS _ _ _ u B G; unfold etaS flagP; positivity),?_,?_⟩
  · refine fixed (d:=m+1) (m:=i) (o:=atEdge S) ?_ ?_ _ ?_ ?_ ?_
    · unfold i; rw [← hL]; exact Census.perch S
    · omega
    · intro i y hy
      exact (Animals.neighbors_mem ..).mpr ((Itinerary.checking S m B i y hy).trans (by rw [add_mul,one_mul]; omega))
    · exact hA
    unfold J; positivity
  intro β hp' hh z
  have hκ : 0<H*X.t := mul_pos hp hF
  have hz : heat H C X.t β ≤ U X.x := by
    unfold U heat; apply mul_le_mul_of_nonneg_right ?_ (by unfold muRate; positivity)
    have he := burst_h (L:=L) hh
    rw [show Pressure.fiery G X.x L=X.t from hL ▸ rfl]
    exact mul_le_mul_of_nonneg_right he hF.le
  refine ⟨fun p => X.borne hY _ _ hp' hκ hu hz hT.mean,fun p => X.first_cost z hp' hκ hY hu hz hb (fun i => ?_) hT.mean p⟩
  have h := hT.upper i
  have h₀ : 0 < (gStep β)⁻¹ := inv_pos.mpr (inv_pos.mpr (Real.sqrt_pos.mpr hp'))
  unfold hatted; rw [Pi.smul_apply,smul_eq_mul,abs_mul,abs_neg, abs_of_pos h₀]
  exact mul_le_mul (burst_h hh) h (abs_nonneg _) (Real.sqrt_nonneg _)
end Coat
end YM.ConnectedActivityE6
