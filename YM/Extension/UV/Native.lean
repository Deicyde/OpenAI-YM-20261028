import YM.Extension.UV.ActualLimit
/-! For exponentially summable rows on true displacement covers, convergence of all finite period
images plus a common positive reserve suffices for convergence before periodization. Don't infer
it from one fixed period. This isolates the actual pre-averaged quadratic path prescription.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extension.UV.Linear
open Set Function Filter Lattice Laurent Exterior Bloch Metric Precision RG Next.Free Work.F08
open scoped Topology BigOperators
variable {α β : Type*}

def weight (σ : ℝ) (x : Cover) := Real.exp (σ*size x) -- η cost from Laurent
lemma weight_pos (σ : ℝ) (x : Cover) : 0 < weight σ x := Real.exp_pos _
lemma weight_summable {σ:ℝ} (h:0<σ) : Summable (weight (-σ)) := (Width.compactPay (α:=Axis) σ h).2.1

lemma priced_row_point {C σ : ℝ} (_h:0<σ) {R:Row α β} (he:R.strip σ C) (a b) : ∀ x, ‖R a b x‖ ≤ C*weight (-σ) x:= by
  intro x
  let f := fun y=> weight σ y * ‖R a b y‖
  have he : SumBudget f C := he a b
  have ht : f x ≤ C := (he.2.1.le_tsum x (fun y hy=>he.1 y)).trans he.2.2
  unfold f weight at ht; rw [weight,neg_mul,Real.exp_neg,← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)] -- maybe lemma name different
  simpa only [mul_comm] using ht

def maskLeak {L : ℕ → Side} {C σ : ℝ} (x : Cover) (i:ℕ) (y : Cover) := if (wrap (L i) x=0+wrap (L i) y ∧ y ≠ x) then 2*C*weight σ y else 0

lemma leak_tendsto {σ:ℝ} (_h:σ<0) (x y : Cover) {L : ℕ → Side} (hL : Tendsto (fun n=>(L n).val) atTop atTop) {C:ℝ} : Tendsto (@maskLeak L C σ x · y) atTop (𝓝 0) := by
  apply Filter.EventuallyEq.tendsto
  filter_upwards [eventually_unfold L hL x, eventually_unfold L hL y] with i hx hy
  by_cases he : y=x
  · simp [maskLeak,he]
  have hn : wrap (L i) x ≠ 0+wrap (L i) y := by
    intro hw
    rw [zero_add] at hw
    exact he (hy ▸ hx ▸ congr_arg lift hw.symm)
  exact if_neg (fun e=>(hn e.1))

lemma leaks {σ C : ℝ} (h:0<σ) (hC:0 ≤ C) (x : Cover) {L : ℕ→Side} (hL:Tendsto (fun n=>(L n).val) atTop atTop) :
    Tendsto (fun i=>∑' y,@maskLeak L C (-σ) x i y) atTop (𝓝 0) := by
  have hb := (weight_summable h).mul_left (2*C)
  have hi i y : ‖@maskLeak L C (-σ) x i y‖ ≤ (2*C)*(weight (-σ) y) := by
    have := weight_pos (-σ) y
    unfold maskLeak
    split_ifs
    · rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    rw [norm_zero]
    positivity
  simpa only [tsum_zero] using (tendsto_tsum_of_dominated_convergence hb (fun y=> leak_tendsto (neg_lt_zero.mpr h) x y hL) (Eventually.of_forall hi))

lemma leak_bound_abstract {Z : Type*} (f k : Z→ℝ) {C: Z→Prop} [DecidablePred C] {D:Z→Prop} [DecidablePred D] (hcd:∀x, C x→D x) (h:∀ x,‖f x‖≤k x) (hs:Summable k)
   (G : Z→ℝ) (he:∀x,(if ¬ C x ∧ D x then k x else 0) ≤ G x) (hg:Summable G) :
  |(∑' x, ite (D x) (f x) 0)-(∑' x,ite (C x) (f x) 0)| ≤ ∑' x,G x:=by
  let d := fun x=>ite (D x) (f x) 0
  let c := fun x=>ite (C x) (f x) 0
  have hf : Summable f := hs.of_norm_bounded h
  have hd : Summable d:= (hf.indicator {i | D i}).congr (by intro x; simp [d,indicator])
  have hc : Summable c:= (hf.indicator {i | C i}).congr (by intro x; simp [c,indicator])
  have hm x : ‖d x-c x‖≤ G x := by
    dsimp only [d,c]; apply le_trans (b:=(if ¬ C x ∧ D x then k x else 0)) ?_ (he x)
    by_cases hh : C x
    · simp only [hh,hcd x hh,not_true,false_and, if_pos,if_false,sub_self,norm_zero,le_rfl]
    by_cases hx:D x
    · simp only [hh,hx,not_false_eq_true,and_self,if_pos,if_false,sub_zero]; exact h x
    simp only [hh,hx,not_false_eq_true,true_and,if_false,sub_self,norm_zero,le_rfl]
  have hsd : Summable (fun x=>‖d x-c x‖):= hg.of_nonneg_of_le (fun _=>norm_nonneg _) hm
  change |(∑' x,d x)-(∑' x,c x)| ≤ _; rw [← hd.tsum_sub hc]
  exact (norm_tsum_le_tsum_norm hsd).trans (hsd.tsum_le_tsum hm hg)

lemma leak_bound {σ C:ℝ} (h:0<σ) (hC:0≤C) {R:ℕ→Row α β} {n:ℕ} (hr:(R n).strip σ C) (a b) (x : Cover) (L : ℕ → Side) (l : ℕ) :
    |(R n).acts (L l) (0,a) (wrap (L l) x,b) -R n a b x| ≤ ∑' y, @maskLeak L C (-σ) x l y := by
  have hM := priced_row_point h hr a b
  let A x := C*weight (-σ) x
  have ha : Summable A := (weight_summable h).mul_left C
  have hs := (weight_summable h).mul_left (2*C)
  have hK : Summable (@maskLeak L C (-σ) x l) := Summable.of_nonneg_of_le (by intro i; unfold maskLeak; have := weight_pos (-σ) i; split_ifs <;> positivity) (by intro i; unfold maskLeak; split_ifs; rfl; have := weight_pos (-σ) i; positivity) hs
  change |(∑' y, (if wrap (L l) x=0+wrap (L l) y then R n a b y else 0))-R n a b x| ≤ _

  simpa only [tsum_ite_eq] using leak_bound_abstract (R n a b) A
    (C:=fun y=> y=x) (D:=fun y=>wrap (L l) x=0+wrap (L l) y) (by intro y hy; rw [hy,zero_add]) hM ha
    (@maskLeak L C (-σ) x l) (fun y=> by
       unfold maskLeak
       by_cases hh : y=x
       · simp only [hh,not_true_eq_false,false_and,and_false, ne_eq, if_false,le_refl]
       by_cases hh' : wrap (L l) x=0+wrap (L l) y
       · simp only [hh,hh',not_false_eq_true,and_self,ne_eq,if_pos,A]; nlinarith [weight_pos (-σ) y]
       simp only [hh',and_false,false_and,if_false,le_refl]) hK

end YM.Extension.UV.Linear
