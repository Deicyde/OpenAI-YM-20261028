import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.ClipError
import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.Weigh
import YM.Next.SCHEDULE.Stadium
import YM.Push.PRICE_COMPILER.Builders


/-!
# Pre-reset support exponents and prices of unforced subtraction / attachments

Not testing on shortest paths. Cover-number from actual projections, even on
paths revisiting the same coarse cells. Chord relaxation compared to the true
length width; the TWO inventories of path positions cost two budgets.
`Grace` includes a condition for later compilation after this exponent reserve
is chosen. No using a smaller exponent in each subsequent `J -> J` step.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.CouplingShape
open Function Filter Lattice RG Next.Scheduling Next.Scheduling.Wages Finset Push.AbsoluteSums UVNext.PricedKernels
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff
variable {n : Side} {G : Gauge} {σ C Λ : ℝ} {P : PathData G} {p : Clip} {b : BudgetPoint}
def Grace (p : Clip) (b : BudgetPoint) (σ : ℝ) := 4 ≤ p.relaxation*σ ∧ b.supportExponent/b.B ≤ σ/4

private lemma origin_slot (z : Slot) (x : Site n) : x∈walkCuts z x := by
  have hx (w : Walk) : (0:Cover) ∈ visits 0 w := by cases w <;> simp [visits]
  exact Finset.mem_image.mpr ⟨0, Finset.mem_union_left _ (List.mem_toFinset.mpr (hx _)),by simp⟩

private lemma count_pair (P : PathData G) (p : BudgetPoint) (x : PlaqAxes) (i : ℕ × ℕ) :
    p.B * coverNumber p.B (imageOf (n:=n) P p (x,.inr i)) ≤ 5*p.B+(first P x i.1).length+(first P x i.2).length := by
  let u := first P x i.1; let v:= first P x i.2
  let M:=p.B
  let o:Site n:=0; let T:=halo M {o}
  change M*coverNumber M (T∪walkCuts u o∪walkCuts v o) ≤ 5*M+u.length+v.length
  have ht : o∈ T := halo_subset _ _ (mem_singleton_self _)
  have hl : M*coverNumber M (T ∪ walkCuts u o) ≤ M+(2*M+u.length) := by
    apply (Nat.mul_le_mul_left M (Corona.meets_sum ht (origin_slot u o) M)).trans
    rw [Nat.mul_add]
    exact Nat.add_le_add (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left M (ballPaid M o)) (walked u o M p.B_pos)
  apply (Nat.mul_le_mul_left M (Corona.meets_sum (mem_union_left (walkCuts u o) ht) (origin_slot v o) M)).trans
  rw [Nat.mul_add]; apply (Nat.add_le_add hl (walked v o M p.B_pos)).trans; omega

def stretch (σ : ℝ) (P : PathData G) (x : PlaqAxes) (i : ℕ × ℕ) := σ*↑((first P x i.1).length+(first P x i.2).length)

def sleeve (p : BudgetPoint) := Real.exp (5*p.supportExponent)

private lemma absorb_cover (x : PlaqAxes) (hg : Grace p b σ) (P : PathData G) (i : ℕ×ℕ) :
    Real.exp (b.supportExponent*coverNumber b.B (imageOf (n:=n) P b (x,.inr i))) ≤ sleeve b * Real.exp (stretch (σ/4) P x i) := by
  let M : ℝ:=b.B; have hM:0<M:= by unfold M; exact_mod_cast b.B_pos
  let u:= (first P x i.1).length; let v:= (first P x i.2).length; let N:=coverNumber b.B (imageOf (n:=n) P b (x,.inr i))
  unfold sleeve stretch
  rw [← Real.exp_add]; apply Real.exp_monotone; push_cast
  change b.supportExponent*↑N≤5*b.supportExponent+σ/4*((u:ℝ)+v)
  have ht : M*↑N≤5*M+(u:ℝ)+v := by unfold M; exact_mod_cast count_pair (n:=n) P b x i
  have hx : (N:ℝ) ≤5+((u:ℝ)+v)/M := by field_simp; linarith
  apply (mul_le_mul_of_nonneg_left hx b.exponent_pos.le).trans
  rw [mul_add,mul_comm _ (5:ℝ),show b.supportExponent*(((u:ℝ)+v)/M)=b.supportExponent/M*((u:ℝ)+v) by ring]
  exact add_le_add_right (mul_le_mul_of_nonneg_right hg.2 (by positivity)) _

private lemma room_direct (x : PlaqAxes) (P : PathData G) (i : Unit) (b : BudgetPoint) :
    Real.exp (b.supportExponent*coverNumber b.B (imageOf (n:=n) P b (x,.inl i))) ≤ sleeve b := by
  have he : (coverNumber b.B (imageOf (n:=n) P b (x,.inl i)):ℝ) ≤ 1 := by exact_mod_cast ringPaid b (0:Site n)
  exact Real.exp_monotone ((mul_le_of_le_one_right b.exponent_pos.le he).trans (le_mul_of_one_le_left b.exponent_pos.le (by norm_num)))

private lemma freight (hD : P.Bounds p σ C Λ) (hg : Grace p b σ) (c : Sequence→ℝ)
    (hp : ∀ i, 0≤c i) {D R : ℝ} (h : ∀ x i, c (x,.inl i) ≤ D) (hr : 0 ≤ R)
    (ht : ∀ x i, c (x,.inr i) ≤ |copper P x i| * R * Real.exp (stretch (σ/2) P x i)) :
    SumBudget (fun i => b.mass (imageOf (n:=n) P b i) (c i))
      (Fintype.card PlaqAxes*(sleeve b * D + (sleeve b * (weight/2*R))*(C*C))) := by
  let X:= fun i => b.mass (imageOf (n:=n) P b i) (c i)
  let T:= sleeve b*D; let S:= sleeve b*(weight/2*R)
  have hv := weight_pos
  have hh (i): 0 ≤ X i := mul_nonneg (Real.exp_pos _).le (hp _)
  have hu (x : PlaqAxes) : SumBudget (fun j => X (x,j)) (T+S*(C*C)) := by
    refine countTypes (budget_finite (fun i=> hh (x,.inl i)) ?_) ?_
    · simp only [comp_apply]; rw [Fintype.sum_unique]; unfold X BudgetPoint.mass
      exact mul_le_mul (room_direct ..) (h x _) (hp _) (Real.exp_pos _).le
    apply budget_mono (budget_scale (show 0≤S by unfold S sleeve; positivity) (budget_prod (hD.rows x) (hD.rows x))) (fun i=>hh (x,.inr i))
    intro i
    have he := mul_le_mul (absorb_cover (n:=n) x hg P i) (ht x i) (hp _) (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    refine he.trans ?_
    have hpc : |copper P x i| = weight /2 * |(P.row x i.1).1| * |(P.row x i.2).1| := by
      simp only [abs_mul,copper,earnCoeff,abs_of_pos (half_pos weight_pos)]
    let z := Real.exp (stretch (σ/4) P x i + stretch (σ/2) P x i)
    have hx : z ≤ Real.exp (σ * (first P x i.1).length)* Real.exp (σ*(first P x i.2).length) := by
      unfold z; rw [←Real.exp_add]; apply Real.exp_monotone; unfold stretch; push_cast
      nlinarith only [Nat.cast_nonneg (α:=ℝ) (first P x i.1).length,Nat.cast_nonneg (α:=ℝ) (first P x i.2).length, hD.width]
    rw [hpc]
    let t := ((sleeve b*(weight/2*R))*|(P.row x i.1).1| *|(P.row x i.2).1|)
    calc
      _ = t*z := by unfold t z; rw [Real.exp_add]; ring
      _ ≤ t*(Real.exp (σ * (first P x i.1).length)* Real.exp (σ*(first P x i.2).length)) :=
        mul_le_mul_of_nonneg_left hx (by unfold t sleeve; positivity)
      _ = _ := by unfold S t first; ring
  change SumBudget X _
  simpa only [sum_const,card_univ,nsmul_eq_mul,T,S] using countOuter hu

-- endpoints normalized fee length
private def flatM (G : Gauge) (b : BudgetPoint) := slotCost G b.power b.order 0

def payer (G : Gauge) (b : BudgetPoint) (σ : ℝ) : ℝ := flatM G b*momentCost ((b.power+1)*b.order) σ
lemma payer_nonneg (G : Gauge) (b : BudgetPoint) (σ : ℝ) : 0 ≤ payer G b σ := by
  unfold payer; apply mul_nonneg (b:=momentCost _ σ) ((zero_le_one' ℝ).trans (slot_ge ..)) (tsum_nonneg fun i => ?_)
  unfold decay; positivity
private lemma absorb_slot (G : Gauge) (b : BudgetPoint) (hσ : 0<σ) (n : ℕ) :
    slotCost G b.power b.order n ≤ payer G b σ*Real.exp (σ/4*n) := by
  let d:=(b.power+1)*b.order
  have hm: decay d (σ/4) n ≤ momentCost d σ := by
    simpa only [sum_singleton] using! (decay_summable d (σ/4) (by positivity)).sum_le_tsum {n} (fun i _ => by unfold decay; positivity)
  have hl : slotCost G b.power b.order n=flatM G b*((n:ℝ)+1)^d := by simp [d,flatM,slotCost,margin,mul_pow,pow_mul,mul_assoc]
  rw [hl,payer,mul_assoc]; apply mul_le_mul_of_nonneg_left _ ((zero_le_one' ℝ).trans (slot_ge ..))
  refine le_trans ?_ (mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le); apply le_of_eq; unfold decay
  rw [mul_assoc, ← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero, mul_one]

private def arms (b : BudgetPoint) (D R : ℝ) (C : ℝ) := Fintype.card PlaqAxes*(sleeve b*D+sleeve b*(weight/2*R)*(C*C))

def rawFee (G : Gauge) (b : BudgetPoint) (p : Clip) (σ C : ℝ) := arms b (modulus G p * spoke G b*feeWalk G 4 b.power b.order^2)
    (wireS G b * (payer G b σ)^2) C

def responseFee (G : Gauge) (b : BudgetPoint) (p : Clip) (C : ℝ) := arms b (weight*p.direct/2*wireS G b*leafPrice G b^2) (wireS G b*leafPrice G b^2) C

/-- Includes B/θ display via b. No use in any pre-L base constants without repricing. -/
def clipFee (b : BudgetPoint) (p : Clip) (C : ℝ) := arms b (weight*(p.direct/2+p.linear*2)*b.threshold) (b.threshold^2) C

private lemma wire_nonneg (G : Gauge) (b : BudgetPoint) : 0 ≤ wireS G b := by unfold wireS; positivity
lemma price_raw_pos (P : PathData G) (p : Clip) (b : BudgetPoint) (i : Sequence) : 0 ≤ priceRaw P p b i :=
  nonneg_of_mul_nonneg_left (bill_raw (n:=1) P p b i).nonneg (pow_pos b.threshold_pos 2)
lemma price_response_pos (P : PathData G) (p : Clip) (b : BudgetPoint) (i : Sequence) : 0 ≤ priceResponse P p b i :=
  nonneg_of_mul_nonneg_left (bill_response (n:=1) P p b i).nonneg (pow_pos b.threshold_pos 2)
lemma raw_reserve (hD : P.Bounds p σ C Λ) (hg : Grace p b σ) :
    SumBudget (fun i => b.mass (imageOf (n:=n) P b i) (priceRaw P p b i)) (rawFee G b p σ C) := by
  apply freight hD hg (priceRaw P p b) (price_raw_pos P p b) (fun _ _ => le_rfl) (mul_nonneg (wire_nonneg G b) (sq_nonneg _))
  intro x i
  let m := (first P x i.1).length; let u := (first P x i.2).length
  let L (n : ℕ) := slotCost G b.power b.order n; let a:= wireS G b; let K:=payer G b σ
  let c:=copper P x i
  have hA : 0≤a:=wire_nonneg ..
  have he n : 0 ≤ L n := (zero_le_one' ℝ).trans (slot_ge ..)
  change |c| * a*L m*L u ≤ _
  calc
    _ ≤ |c| * a*(K*Real.exp (σ/4*m))*(K*Real.exp (σ/4*u)) := by
      gcongr <;> first | exact he _ | positivity [payer_nonneg G b σ, show 0 ≤ K from payer_nonneg G b σ] | exact absorb_slot G b hD.width _
    _ = |c| * (a*K^2)* Real.exp (stretch (σ/4) P x i) := by unfold stretch; push_cast; rw [mul_add,Real.exp_add]; unfold m u; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_monotone (by
      unfold stretch; apply mul_le_mul_of_nonneg_right _ (by positivity); linarith only [hD.width]))
       (mul_nonneg (abs_nonneg _) (mul_nonneg hA (sq_nonneg _)))

lemma response_reserve (hD : P.Bounds p σ C Λ) (hg : Grace p b σ) :
    SumBudget (fun i => b.mass (imageOf (n:=n) P b i) (priceResponse P p b i)) (responseFee G b p C) := by
  apply freight hD hg (priceResponse P p b) (price_response_pos P p b) (fun _ _ => le_rfl) (mul_nonneg (wire_nonneg G b) (sq_nonneg _))
  intro x i; simp only [priceResponse,Sum.elim_inr,mul_assoc |copper P x i| (wireS G b)]
  apply le_mul_of_one_le_right (mul_nonneg (abs_nonneg _) (mul_nonneg (wire_nonneg ..) (sq_nonneg _)))
  apply Real.one_le_exp; unfold stretch; positivity [hD.width]

lemma price_clip_pos (P : PathData G) (p : Clip) (b : BudgetPoint) (i : Sequence) : 0 ≤ priceClip P p b i := (norm_nonneg _).trans (clip_claim P p b i (1:Wilson.Config G 1))

lemma clip_reserve (hD : P.Bounds p σ C Λ) (hg : Grace p b σ) :
    SumBudget (fun i => b.mass (imageOf (n:=n) P b i) (priceClip P p b i)) (clipFee b p C) := by
  apply freight hD hg (priceClip P p b) (price_clip_pos P p b) (fun _ _ => le_rfl) (sq_nonneg _)
  intro x i; unfold priceClip; simp only [Sum.elim_inr]; rw [mul_right_comm]
  refine mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) (mul_nonneg (abs_nonneg _) (sq_nonneg _)); unfold stretch; push_cast
  rw [←add_div,div_le_iff₀ p.radius_pos]; have hp:= hg.1
  apply le_trans (b:=(4/2:ℝ)*((first P x i.1).length+(first P x i.2).length))
  · nlinarith [Nat.cast_nonneg (α:=ℝ) (first P x i.1).length, Nat.cast_nonneg (α:=ℝ) (first P x i.2).length]
  nlinarith only [mul_le_mul_of_nonneg_right hp (show 0 ≤ ((first P x i.1).length:ℝ)+(first P x i.2).length by positivity)]
end YM.AnalyticBridge.CouplingShape
