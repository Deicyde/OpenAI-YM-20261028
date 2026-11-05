import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.PathPair
import YM.Next.SCHEDULE.Postal
import YM.Push.ABSOLUTE_SUMS.Basic


/-! # Budget organization

Enlarged exponent inside this step; not reusing estimates at the same exponent after mergers.
Includes within-one-scale conversion from anchored to hit (polynomial in B).
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.CouplingShape
open Function Filter Lattice RG Finset Push.AbsoluteSums Next.Scheduling
open scoped Topology BigOperators ContDiff
variable {n : Side} {p : BudgetPoint}
section
variable {ι κ : Type} {a b : ℝ}
lemma countOuter [Fintype ι] {f : ι × κ→ℝ} {g : ι → ℝ}
    (h : ∀ i, SumBudget (fun j => f (i,j)) (g i)) : SumBudget f (∑ i, g i) := by
  have hh (x : ι × κ) : 0 ≤ f x := (h x.1).1 _
  have he : Summable f := (summable_prod_of_nonneg hh).mpr ⟨fun i => (h i).2.1,(hasSum_fintype _).summable⟩
  refine ⟨hh,he,?_⟩; rw [he.tsum_prod,tsum_fintype]; exact sum_le_sum fun i _ => (h i).2.2

lemma countTypes {f : ι ⊕ κ→ℝ} (h : SumBudget (f ∘ Sum.inl) a) (hh : SumBudget (f ∘ Sum.inr) b) : SumBudget f (a+b) := by
  obtain ⟨m,hm⟩:= h.2.1; obtain ⟨n,hn⟩:= hh.2.1
  have he := HasSum.sum hm hn
  exact ⟨fun i => Sum.recOn i h.1 hh.1,he.summable,by rw [he.tsum_eq,← hm.tsum_eq, ← hn.tsum_eq]; exact add_le_add h.2.2 hh.2.2⟩

lemma stamped {w : Around n ι → ℝ} {a : ℝ} (h : ∀ o : Site n, ∀ s : Signed, SumBudget (fun i : ι => w (o,s,i)) a)
    (x : Site n) : SumBudget (fun i : Around n ι => if i.atPin=x then w i else 0) (Fintype.card Signed*a) := by
  let r := (Fintype.card Signed:ℝ)*a
  let f (i : Around n ι) := if i.atPin=x then w i else 0
  have hh (o : Site n) : SumBudget (fun s : Signed × ι => f (o,s)) (if o=x then r else 0) := by
    by_cases ht : o=x
    · simp only [f,Around.atPin,if_pos ht]; simpa [r] using (countOuter (f:=fun s : Signed × ι => w (o,s)) (h o))
    simp [f,Around.atPin,SumBudget,ht,summable_zero]
  simpa [r] using (countOuter hh)

/-- Price each label at its *declared* anchor. -/
def Sealed (p : BudgetPoint) (u : ι→RegularAddress n) (f : ι→ℝ) (v : ℝ) := ∀ x : Site n,
    SumBudget (fun i => if (u i).site=x then p.mass (u i).support (f i) else 0) v

lemma totalBooked {u : ι→RegularAddress n} {f : ι→ℝ} (hf : ∀ i,0≤f i) (h : Sealed p u f a) :
    SumBudget f (Fintype.card (Site n)*a) := by
  let q (x : Site n) i := if (u i).site=x then p.mass (u i).support (f i) else 0
  have hh := budget_over (Finset.univ : Finset (Site n)) q _ (fun x _ => h x)
  rw [sum_const] at hh; apply budget_loosen (budget_mono hh hf _) (by simp)
  intro i; simpa [q] using! (p.loMass (u i).support (f i) (hf i))
end

def boost (p : BudgetPoint) : BudgetPoint := { p with
    supportExponent:=p.supportExponent+2
    exponent_pos:=by positivity [p.exponent_pos] }
lemma tighter (X : Support n) {c : ℝ} (hc : 0 ≤ c) : p.mass X c ≤ (boost p).mass X c := by unfold BudgetPoint.mass boost; simp only; gcongr; linarith

lemma ballPaid (B : ℕ) (x : Site n) : coverNumber B (halo B {x}) ≤ 1 := by
  apply le_trans (b:=({x}:Support n).card) _ (by simp)
  refine Corona.list_cost _ ⟨Subset.refl _, Corona.ship_halo _ ?_⟩
  intro i hi j hj; rw [mem_singleton.mp hi, mem_singleton.mp hj]

lemma ringPaid (p : BudgetPoint) (x : Site n) : coverNumber p.B (ringlet x) ≤ 1 :=
  (Corona.cover_mono (Corona.halo_mono p.B_pos (Subset.refl _)) _).trans (ballPaid ..)

def fare (p : BudgetPoint) := (12*(p.B+1):ℝ)^(4:ℕ) * ∑' i, decay 4 1 i



/-- Cost incurred once on going from the anchored reset log to the
unnormalized Mayer attachments . No bound on overlap degree
by number of roots. -/
lemma turnToHit {ι : Type} {u : ι→ RegularAddress n} {w : ι→ℝ} {a : ℝ} (h : ∀ i, 0≤w i)
    (hh : Sealed (boost p) u w a) : Ac.Hit (fun i => (u i).support) p.B w (p.supportExponent+1) (fare p * a) := by
  classical
  let B:=p.B
  let d i:= coverNumber B (u i).support
  let Φ (r : ℕ) := r*(4*B+2)+2*B
  let q (x : Site n) i := if (u i).site=x then (boost p).mass (u i).support (w i) else 0
  let z : ℝ := 12*(B+1); have hZ : 0≤z := by unfold z; positivity
  have ha:=budget_nonneg (hh 0)
  intro x
  let F i := if x ∈ (u i).support then w i*Real.exp ((p.supportExponent+1)*d i) else 0
  have ht i : 0≤ F i := by unfold F; split; exact mul_nonneg (h i) (Real.exp_pos _).le; rfl
  have hd : SumBudget (decay 4 1) (∑' i, decay 4 1 i) := ⟨fun i => by unfold decay; positivity,decay_summable _ _ (by norm_num),le_rfl⟩
  let L := fare p * a
  have hr : L=(z^4*a) * ∑' i, decay 4 1 i := by unfold L fare z B; ring
  change SumBudget F L
  rw [hr]; apply budget_fiberwise d ht _ (budget_scale (mul_nonneg (pow_nonneg hZ 4) ha) hd)
  intro i U hU
  let s:=halo (Φ i) {x}
  have he j (hj : j∈U) : F j≤Real.exp (- (i:ℝ)) * ∑ y∈s,q y j := by
    unfold F; split
    next hx =>
      have hl : (u j).site∈s := halo_spec.mpr ⟨x,mem_singleton_self _,?hh⟩
      case hh => rw [← hU j hj]; exact Corona.extent _ _ hx (u j).anchor
      apply le_trans (b:=Real.exp (-(i:ℝ)) * q (u j).site j) _ (mul_le_mul_of_nonneg_left (single_le_sum (f:=fun y=>q y j) (fun y _ => (hh y).1 j) hl) (Real.exp_pos _).le)
      unfold q; rw [if_pos rfl]; change _ ≤ Real.exp _ * (Real.exp ((p.supportExponent+2)*d j)*_)
      rw [hU j hj,←mul_assoc,← Real.exp_add, mul_comm (w j),show -(i:ℝ)+(p.supportExponent+2)*i=(p.supportExponent+1)*i by ring]
    exact mul_nonneg (Real.exp_pos _).le (sum_nonneg fun y _ => (hh y).1 _)
  have hk : (s.card:ℝ) ≤ z^4*((i:ℝ)+1)^ (4:ℕ) := by
    have he := Corona.halo_size {x} (Φ i); rw [card_singleton, one_mul] at he
    apply (show (s.card:ℝ) ≤ (↑((Φ i+Φ i+1)^4:ℕ):ℝ) by exact_mod_cast he).trans
    rw [←mul_pow]; dsimp only [Φ,z]; push_cast; gcongr; nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) i) (Nat.cast_nonneg (α:=ℝ) B)]
  calc
    ∑ j∈U,F j ≤ ∑ j∈U,_ := sum_le_sum he
    _ = Real.exp (-(i:ℝ))*∑ y∈s,∑ j∈U,q y j := by rw [← mul_sum,sum_comm]
    _ ≤ Real.exp (-(i:ℝ))*∑ _y∈s, a := mul_le_mul_of_nonneg_left (sum_le_sum (fun y _ => budget_sum (hh y) _)) (Real.exp_pos _).le
    _ = Real.exp (-(i:ℝ))*((s.card:ℝ)*a) := by simp
    _ ≤ Real.exp (-(i:ℝ))*(z^4*((i:ℝ)+1)^ (4:ℕ)*a) := by gcongr
    _ = _ := by unfold decay; ring_nf
end YM.AnalyticBridge.CouplingShape
