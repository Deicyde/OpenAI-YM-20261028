import YM.Bid.Drops
import YM.Next.FREE_KERNELS.Lifts
import YM.Ovens.Coffee
import YM.UVNext.PRICED_KERNELS.Annuity
import YM.Work.C06


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Pre-L rooted probe/tree invoices (real periodic)

No multiplying by number of frame outcomes or translations. Formula read
on actual physical sites even arbitrary sizes on issued clock. `fixRoot` and
`probe` of Station frame & conditional derivative take averages of complete
route integrals. Pay at the *scaled* rate here O(1/L) in fine site units.
True cost of these LINEAR rows and of given forest hiker. Includes support
per-anchor and later reverse asks (where produced, charge L^4 etc). Sym
labels & phase matching require other work. Compare . The clamped same-level rows in nonlinear tasks at a rate in
native fine units instead must be costed separately.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.PricedKernels
open Filter Set Function Lattice RG Precision Pressure Bloch Laurent Matrix Exterior Tree
open Next.Free
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side}

lemma oneStep_le (x : Site f) (b : Step) : separation x (x+b.vec) ≤ 1 := by
  rw [separation_comm,separation,add_comm,add_sub_cancel_right,Step.vec]; split
  · rw [pdist_neg]; exact pdist_step _
  exact pdist_step _

/-- Keep sign and corner shifts of `used`. -/
lemma walk_receipt (t : ℝ) (ht : 0 ≤ t) (v : form 1 f) (y : Site f)
    (he : ∀ i : Body 1 f, |v i| ≤ gained t y i.1) (x : Site f) (w : Walk) :
    |integralLink x w v| ≤ (w.length:ℝ) * Real.exp (t*((separation y x:ℝ)+w.length)) := by
  induction w generalizing x with
  | nil => simp [integralLink,linkSum]
  | cons b w ih =>
    let e := b.used x; let u := (e.1,coord e.2)
    have h (i j : Site f) (h : separation i j ≤ 1) : (separation y j:ℝ) ≤ (separation y i:ℝ)+1 := by
      exact_mod_cast ((separation_triangle y i j).trans (Nat.add_le_add_left h _) : separation y j ≤ separation y i+1)
    have hL := h _ _ (oneStep_le x b)
    have hU : (separation y e.1:ℝ) ≤ (separation y x:ℝ)+1 := by
      apply h; unfold e Step.used; split
      next hb => simpa [Step.vec,hb, sub_eq_add_neg] using oneStep_le x b
      simp
    let A := Real.exp (t*((separation y x:ℝ)+(w.length+1:ℝ)))
    change |(if b.neg then -v u else v u)+integralLink (x+b.vec) w v| ≤ _
    have hh : |if b.neg then -v u else v u| = |v u| := by split_ifs <;> simp
    have hv : |v u| ≤ A := (he u).trans (Real.exp_monotone (mul_le_mul_of_nonneg_left
      (le_trans hU (by linarith only [Nat.cast_nonneg (α:=ℝ) w.length])) ht))
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    have hw := ih (x+b.vec)
    change _ ≤ (w.length+1:ℝ)*A
    refine (abs_add_le ..).trans ?_
    rw [hh]; refine (add_le_add hv (hw.trans (mul_le_mul_of_nonneg_left (Real.exp_monotone
      (mul_le_mul_of_nonneg_left ?_ ht)) (Nat.cast_nonneg _)))).trans_eq (show A + (w.length:ℝ)*A = _ by ring)
    linarith only [hL]

-- bounds in radius, following UV_STRESS.Insides proof idea
lemma effort (P : Patch) (x y : P.Points) (i : Lattice.Order) :
    (route x.val y.val i).length ≤ 8*P.radius := by
  have he j : (straight j (y.val j-x.val j)).length ≤ 2*P.radius := by
    have h₁ := (box_test.mp x.property).1 j; have h₂ := (box_test.mp x.property).2 j
    have h₃ := (box_test.mp y.property).1 j; have h₄ := (box_test.mp y.property).2 j
    rw [straight,List.length_replicate]; omega
  have hv (w : List Axis) : (axisRoute x.val y.val w).length ≤ w.length*(2*P.radius) := by
    induction w with
    | nil => simp [axisRoute]
    | cons j w h =>
      rw [show axisRoute x.val y.val (j::w)=_ ++ axisRoute x.val y.val w from rfl,List.length_append]
      exact (Nat.add_le_add (he j) h).trans (by simp only [List.length_cons, add_mul,one_mul]; omega)
  exact (hv (allAxes i)).trans (by simp [allAxes]; omega)

lemma start_effort (S : StepData c f) (i : Site c) (x : S.patch.Points) :
    separation (S.ratio.embed i) (atPoint S i x) ≤ 4*S.patch.radius := by
  rw [separation_comm,separation,Precision.atPoint, add_sub_cancel_right]
  apply (within_size ..).trans
  unfold size
  have h k : (x.val k).natAbs ≤ S.patch.radius := by
    have h₁ := (box_test.mp x.property).1 k; have h₂ := (box_test.mp x.property).2 k; omega
  exact (Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => h k).trans (by simp [Axis])

section patch
variable (S : StepData c f) (s : ℝ) (hs : 0 ≤ s)

abbrev tollFine (S : StepData c f) (s : ℝ) := s / S.patch.L.val

def stepC (J : ℕ) (s : ℝ) := (8:ℝ)*((J:ℝ)+3)*Real.exp (s*(12*((J:ℝ)+3)))

lemma stepC_pos (J : ℕ) (s : ℝ) : 0 < stepC J s := by unfold stepC; positivity

include hs
lemma through_patch (v : form 1 f) (x : Site c) (he : ∀ i : Body 1 f, |v i| ≤ gained (tollFine S s) (S.ratio.embed x) i.1)
    (b : S.patch.Points) (w : Walk) (hL : w.length ≤ 8*S.patch.radius) :
    |integralLink (atPoint S x b) w v| ≤ (S.patch.L.val:ℝ)*stepC S.patch.J s := by
  let L := (S.patch.L.val:ℝ); let j:ℝ := S.patch.J
  let t := tollFine S s; have h : 0<L := side_pos _
  have hh := walk_receipt t (div_nonneg hs h.le) v (S.ratio.embed x) he (atPoint S x b) w
  let X := ((8:ℕ)*S.patch.radius:ℕ)
  have hX : (w.length:ℝ) ≤ (X:ℝ) := Nat.cast_le.mpr hL
  have ht : (separation (S.ratio.embed x) (atPoint S x b):ℝ) ≤ ((4*S.patch.radius:ℕ):ℝ) := Nat.cast_le.mpr (start_effort ..)
  refine hh.trans ((mul_le_mul hX (Real.exp_monotone (b:=t*(((4*S.patch.radius:ℕ):ℝ)+(X:ℝ)))
      (mul_le_mul_of_nonneg_left (add_le_add ht hX) (div_nonneg hs h.le))) (Real.exp_pos _).le (by positivity)).trans_eq ?_)
  unfold X Patch.radius t tollFine stepC
  push_cast
  rw [show s/(S.patch.L.val:ℝ) * (4*(((S.patch.J :ℝ)+3)* (S.patch.L.val:ℝ)) + 8*(((S.patch.J:ℝ)+3)* (S.patch.L.val:ℝ))) = s*(12*((S.patch.J:ℝ)+3)) by field_simp; ring] -- assoc
  ring

lemma tau_cost (x : Body 0 c) (v : form 1 f) (he : ∀ i,|v i| ≤ gained (tollFine S s) (S.ratio.embed x.1) i.1) (b : S.patch.Points) :
    |tau S x.1 b v| ≤ (S.patch.L.val:ℝ)*stepC S.patch.J s := by
  have ht (d : S.patch.Points) (k : Lattice.Order) := through_patch S s hs v x.1 he b (route b.val d.val k) (effort _ b d k)
  let p := S.patch.L.val; let F := (p:ℝ)*stepC S.patch.J s
  have h₁ : 0 < (Fintype.card S.patch.Points:ℝ) := by exact_mod_cast Fintype.card_pos
  have h₂ : 0 < (Fintype.card Lattice.Order:ℝ) := by exact_mod_cast Fintype.card_pos
  have hM (d : S.patch.Points) : |(Fintype.card Lattice.Order:ℝ)⁻¹ * ∑ k : Lattice.Order, integralLink (atPoint S x.1 b) (route b.val d.val k) v| ≤ F := by
    rw [abs_mul,abs_of_pos (inv_pos.mpr h₂)]
    refine (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_nonneg.mpr h₂.le)).trans ?_
    refine (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k (_ : k∈Finset.univ) => ht d k) (inv_nonneg.mpr h₂.le)).trans_eq ?_
    simp only [Finset.sum_const, Finset.card_univ,nsmul_eq_mul, inv_mul_cancel_left₀ h₂.ne']; rfl
  unfold tau; simp only [LinearMap.neg_apply,LinearMap.smul_apply,LinearMap.sum_apply,smul_eq_mul,abs_neg]
  rw [abs_mul,abs_of_pos (inv_pos.mpr h₁)]
  refine (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_nonneg.mpr h₁.le)).trans ?_
  refine (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k (_ : k∈Finset.univ) => hM k) (inv_nonneg.mpr h₁.le)).trans_eq ?_
  simp only [Finset.sum_const, Finset.card_univ,nsmul_eq_mul, inv_mul_cancel_left₀ h₁.ne']; rfl

lemma fix_price : Annuity (parent S.ratio _) (site f _) (fixRoot S) (tollFine S s)
    (S.patch.L.val * (2*stepC S.patch.J s)) := by
  apply Annuity.earned; intro i v hv
  rw [fixRoot, LinearMap.toMatrix'_mulVec]; change |_ - ((∑ _, _ ) : form 1 f →ₗ[ℝ] ℝ) v| ≤ _ -- simplify
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  have ht b := tau_cost S s hs i v hv b
  refine (abs_sub ..).trans ?_
  refine (add_le_add (ht _) ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (g:=fun b => S.patch.weight b *
    ((S.patch.L.val:ℝ)*stepC S.patch.J s)) (fun b _ => ?_)))).trans_eq ?_
  · rw [abs_mul, abs_of_nonneg (S.patch.weight_nonneg _)]
    exact mul_le_mul_of_nonneg_left (ht _) (S.patch.weight_nonneg _)
  rw [← Finset.sum_mul,S.patch.weight_sum]; ring


end patch
end YM.UVNext.PricedKernels
