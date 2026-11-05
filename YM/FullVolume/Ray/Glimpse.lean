import YM.FullVolume.Ray.Mono
/-! Polynomial after removing exponential measured at probe.
Uniformly in *value of exponent* even when coefficient hits nonlinear poles at large Negative energy. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Ray
open Filter Function Set RG ConnectedActivityE6.Blaze Planned.AtomRegular Next.Foundations Finset
open scoped Topology BigOperators NNReal ContDiff
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {R:ℝ} {k i n:ℕ}
section polynomial
lemma ahead (f:ℝ→ℝ) {v : ℝ} (hp : ContDiffAt ℝ (↑(k+1)) f v) : ContDiffAt ℝ k (deriv f) v:= (hp.fderiv_right (show (k:WithTop ℕ∞)+1 ≤ (↑(k+1):WithTop ℕ∞) from (by push_cast; exact le_rfl))).clm_apply (g:=fun _:ℝ=>1) contDiffAt_const
-- reusable lemma
lemma spiral {f : ℝ→ℝ} {a:ℝ} (p:ContDiffAt ℝ (↑(i+1)) f a) :
    iteratedDeriv (i+1) (fun t=> Real.exp (f t)) a= ∑ k ∈ range (i+1),(i.choose k : ℝ) * iteratedDeriv k (Real.exp ∘ f) a * iteratedDeriv (i-k+1) f a:= by
  have hg : deriv (Real.exp ∘ f)=ᶠ[𝓝 a] (fun t=>Real.exp (f t)*deriv f t):=by
    filter_upwards [p.eventually (by simp)] with i hi
    exact (hi.differentiableAt (by simp)).hasDerivAt.exp.deriv
  have ht : ContDiffAt ℝ i (Real.exp ∘ f) a:= p.exp.of_le (Nat.cast_le.mpr (Nat.le_succ _))
  rw [iteratedDeriv_succ']; refine ((show _ = _ from hg.iteratedDeriv_eq _)).trans ?_
  refine (iteratedDeriv_fun_mul ht (ahead f p)).trans (Finset.sum_congr rfl fun j _=> ?_); rw [iteratedDeriv_succ']
variable {p f:ℝ→ℝ} {x:ℝ}
private lemma gallop (a: ink k p) (h : ContDiffAt ℝ i f x) :
    ∃ g:ℝ→ℝ, ink (k*i) g ∧ ∀ t, iteratedDeriv i (fun y=> Real.exp (p t*f y)) x=g t*Real.exp (p t*f x):=by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    match i with
    | 0=> exact ⟨fun _=>1,ink.termC _,fun t=>by simp⟩
    | j+1=>
    classical
    let I:= Finset.range (j+1)
    have hx (i:ℕ) : ∃ g:ℝ→ℝ, i∈I → ink (k*i) g ∧∀ t,iteratedDeriv i (fun y=> Real.exp (p t*f y)) x=g t*Real.exp (p t*f x):=by
      by_cases ht:i∈I; swap; · exact ⟨0,fun hc=>(ht hc).elim⟩
      have hi:= Finset.mem_range.mp ht
      obtain ⟨g,hg,h⟩:= ih _ hi (h.of_le (Nat.cast_le.mpr hi.le)); exact ⟨g,fun _=>⟨hg,h⟩⟩
    choose g hg using hx
    let K i (t:ℝ):=(j.choose i:ℝ)*g i t*p t*iteratedDeriv (j-i+1) f x
    refine ⟨fun t=> ∑ i∈I,K i t,ink.collection _ _ (fun i hi=>?_ ),fun t=>?_⟩
    · have he:= (((hg i hi).1.scale (j.choose i:ℝ)).docket a).docket (ink.termC (k:=0) (iteratedDeriv (j-i+1) f x)); apply he.rise; rw [mul_add,add_zero,mul_one]; apply Nat.add_le_add_right; apply Nat.mul_le_mul_left; exact Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    rw [spiral (contDiffAt_const.mul h),Finset.sum_mul]; apply sum_congr rfl
    intro i hi; rw [show iteratedDeriv i (Real.exp ∘ fun x=> p t*f x) x=_ from (hg i hi).2 t, iteratedDeriv_const_mul _ (n:=j-i+1) (h.of_le (by
      apply Nat.cast_le.mpr; have he:= mem_range.mp hi; omega))]; unfold K; ring
lemma measured {V Γ:E →ℝ} {x:E} {u:ℝ→ℝ} (h : ink k p) (hv:ContDiffAt ℝ i V x) (hh:ContDiffAt ℝ i Γ x) (y:E) : ∃ g:ℝ→ℝ, ink (k*i) g ∧ ∀ t,
     marked i (fun x=> V x * u t * Real.exp (p t * Γ x)) x y = g t*(u t*Real.exp (p t* Γ x)):=by
  classical let F t:= Real.exp ∘ (fun a=>p t* (Γ ∘ tintM x y) a)
  let G' := Γ ∘ tintM x y; let E':= V ∘ tintM x y; let I:= Finset.range (i+1)
  have ht (j:ℕ): ContDiffAt ℝ (↑(i-j)) G' 0:= sheen (hh.of_le (Nat.cast_le.mpr (Nat.sub_le ..))) _
  choose g hg hQ using fun j:ℕ=> gallop h (ht j)
  let f j t:= (i.choose j:ℝ)*iteratedDeriv j E' 0 * g j t
  refine ⟨fun t=> ∑ j∈I, f j t,ink.collection I _ (fun j _=>((hg j).scale _).rise (Nat.mul_le_mul_left _ (Nat.sub_le ..))),fun t=>?_⟩
  unfold marked
  have he:= sheen hh y
  change iteratedDeriv i (fun v=> E' v * u t * F t v) 0=_
  have hr:ContDiffAt ℝ i (F t) 0:=(show ContDiffAt ℝ i (fun z=>p t*G' z) 0 from contDiffAt_const.mul he).exp
  dsimp only; rw [iteratedDeriv_fun_mul (f:=fun i=> E' i * u t) ((sheen hv y).mul contDiffAt_const) hr,sum_mul]
  apply sum_congr rfl; intro j hj; have hs: Nat.cast j ≤ (↑i:WithTop ℕ∞):= by apply Nat.cast_le.mpr; have he:=mem_range.mp hj; omega
  rw [show iteratedDeriv j (fun i=> E' i * u t) 0 = u t * iteratedDeriv j E' 0 from (by simp_rw [mul_comm (E' _)]; exact iteratedDeriv_const_mul _ ((sheen hv y).of_le hs)), show iteratedDeriv (i-j) (F t) 0=_ from hQ j t, show G' 0=Γ x from by simp [G', tintM]]
  unfold f; ring
end polynomial
end YM.FullVolume.Ray
