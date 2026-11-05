import YM.WilsonBulk.Web.Volume

/-!
# Pointwise limits and period test.

Here for arbitrary supplied finite widths (not using any widening),
positive thickness pays absolute summation over all legs. Rank ≥1 for
uniformity across volume. Does NOT pass to or use a limit in cutoff yet.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet
open scoped Topology Classical ENNReal BigOperators
open Function Equiv Lattice Laurent Filter Pert.Bulk
variable {σ θ p q : ℝ} {α : Type} {n k : ℕ} {c : Side}
variable {u v : Text α n} [Fintype α]
variable {D : ℕ → Side} (hd : Tendsto (fun i=> (D i).val) atTop atTop)

lemma expo_one (hσ : 0<σ) (x : Market α) : Summable fun y:Market α=> Real.exp (-σ*(lawn α).cost x y) := by
  let e : Cover≃ Cover:= Equiv.trans (Equiv.neg _) (Equiv.addRight x.1)
  have hh : Summable fun y => Real.exp (-σ* Laurent.size (e y)) := (Equiv.summable_iff e).mpr (Width.compactPay σ hσ).2.1
  change Summable (fun y => _); apply Summable.congr (summable_mul_of_summable_norm hh.norm (show Summable (fun (_ : α)=>‖(1:ℝ)‖) from Summable.of_finite))
  intro y; rw [mul_one]; change Real.exp (-σ*length (e y.1))=_
  rw [show e y.1=x.1-y.1 by change -y.1+x.1=_; abel]; rfl
lemma expo_all (hσ : 0<σ) (x : Market α) (n : ℕ) : Summable fun v:Legs (Market α) n=> Real.exp (-σ*run (lawn α) x v) := by
  induction n with
  | zero => exact Summable.of_finite
  | succ n ih =>
    apply (Equiv.summable_iff (hitchEquiv (Market α) n)).mp
    apply ((summable_mul_of_summable_norm (expo_one hσ x).norm ih.norm)).congr (fun z=>?_)
    change _ = Real.exp (-σ*run _ x (hitch z.1 z.2)); rw [run_some,mul_add,Real.exp_add]

omit [Fintype α] in
lemma item_bound (h : Within (lawn α) σ p u) (i : Fin n) (v : Legs (Market α) n) :
    ‖u v‖ ≤ p * Real.exp (-σ*run (lawn α) (v i) v) := by
  rw [neg_mul,Real.exp_neg,← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
  simpa only [Real.norm_eq_abs] using within_entry' h i v

-- fixed printed coefficient bounds independent of period
omit [Fintype α] in
lemma printed_bound {u : Text α n} {V : Page (Bloch.Co c α) n} (ha : Within (lawn α) σ p u) (hp : 0≤σ) (h : Orates (small c α) u V) (hn : n≠0)
    (v : Legs (Bloch.Co c α) n) : |V v| ≤ p := by
  let i : Fin n:=⟨0,by omega⟩
  obtain ⟨x,hx⟩:= small_onto c α (v i)
  rw [h i x v hx.symm, page_tsum]
  let F (y : Legs (Market α) n) := if y i=x ∧ small c α ∘ y=v then u y else 0
  have he y : ‖F y‖ ≤ fee (lawn α) σ u i x y := by
    dsimp only [F,fee]; by_cases hx : y i=x; swap; · simp only [hx,false_and,↓reduceIte,norm_zero,le_refl]
    rw [if_pos hx]; split
    · exact (Real.norm_eq_abs _).le.trans (le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (mul_nonneg hp (run_nonneg ..))))
    simp only [norm_zero]; positivity
  have HH := ((within_budget ha.1).1 ha i x)
  have hs := (Summable.of_norm_bounded HH.2.1 he).norm
  have hi : |∑' y,F y| ≤ p := (norm_tsum_le_tsum_norm hs).trans ((hs.tsum_le_tsum he HH.2.1).trans HH.2.2)
  convert! hi using 2 with z -- Dec Eq
  exact tsum_congr (fun i=> by unfold F; congr!)

include hd
lemma wrap_event (v : Cover) : ∀ᶠ i in atTop,lift (wrap (D i) v)=v := by
  simp_rw [lift_eq_iff,true_and] -- equality self
  apply eventually_all.mpr
  intro j; filter_upwards [hd.eventually (eventually_ge_atTop (2*(v j).natAbs+1))] with i hi
  omega
omit [Fintype α] in
lemma small_eq_event (x y : Market α) : ∀ᶠ i in atTop,small (D i) α x=small (D i) α y → x=y := by
  filter_upwards [wrap_event hd x.1,wrap_event hd y.1] with i hs ht he
  have h := congr_arg Prod.fst he
  exact Prod.ext (hs.symm.trans ((congr_arg lift h).trans ht)) (by have hz:= congr_arg Prod.snd he; exact hz)
lemma printed_limit {K : ℕ→ Text α n} {V : ∀ i:ℕ,Page (Bloch.Co (D i) α) n}
    (ha : ∀ᶠ i in atTop, Within (lawn α) σ p (K i)) (he : 0 < σ) (hv : ∀ᶠ i in atTop, Orates (small (D i) α) (K i) (V i))
    (h : Tendsto K atTop (𝓝 u)) (hn : n≠0) (x : Legs (Market α) n) : Tendsto (fun i=> V i (small (D i) α ∘ x)) atTop (𝓝 (u x)) := by
  let j : Fin n:=⟨0,by omega⟩
  let f := fun (i:ℕ) y=> if y j=x j ∧ small (D i) α ∘ y=small (D i) α ∘ x then K i y else 0
  let g := fun y=> if y=x then u x else 0
  have ht : ∀ y : Legs (Market α) n,Tendsto (fun i=> f i y) atTop (𝓝 (g y)) := by
    intro y; by_cases hh : y=x; · subst y; simpa only [f,g,and_self,↓reduceIte] using tendsto_pi_nhds.mp h x
    apply (show Tendsto (fun _ : ℕ=> g y) atTop (𝓝 (g y)) from tendsto_const_nhds).congr'
    have hD : ∀ᶠ a in atTop, ∀ b:Fin n, small (D a) α (x b)=small (D a) α (y b) → x b=y b := eventually_all.mpr fun i=>small_eq_event hd (x i) (y i)
    filter_upwards [hD] with a ha
    have hr : small (D a) α ∘ y ≠ small (D a) α ∘ x := fun e=> hh (funext fun i=> (ha i (congr_fun e.symm i)).symm)
    simp [f,g,hr,hh]
  have hp : 0≤p := by obtain ⟨i,hi⟩:= ha.exists; exact hi.1
  let k := fun v=> p * Real.exp (-σ*run (lawn α) (x j) (v:Legs (Market α) n))
  have hk : ∀ᶠ i in atTop,∀ v, ‖f i v‖ ≤ k v := by
    filter_upwards [ha] with i hi v; dsimp only [f]; split
    next e=>
      unfold k; rw [← e.1]; exact item_bound hi j v
    rw [norm_zero]; unfold k; positivity
  have heq : u x = ∑' z,g z := by rw [tsum_eq_single x]; simp [g]; intro b h; simp [g,h]
  rw [heq]; refine (tendsto_tsum_of_dominated_convergence ((expo_all he (x j) n).mul_left p) ht hk).congr' (hv.mono (fun i hi=>?_))
  dsimp only; rw [hi j (x j) (small (D i) α ∘ x) rfl]
  convert! (page_tsum (small (D i) α) j (x j) (K i) (small (D i) α ∘ x)).symm using 1
  exact tsum_congr (fun y=> by unfold f; congr!)
end YM.WilsonBulk.Sheet
