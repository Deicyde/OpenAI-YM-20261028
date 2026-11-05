import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Words


/-!
# Intersection costing: ordered jets at a single evaluation point

The flags do not promise good inputs on open neighborhoods. Use REAL left
jet bounds of *unmasked/extended* functions. No smooth-all-orders or global
uniform smoothness assumption.

When paying for a product of many factors we must avoid a constant (even
order-dependent) loss on **each undifferentiated factor**. `Ticket` and
`Charge` distinguish the order-loss radius from the amplitude. Thus putting
weights `(pay, r)` even on factors possibly evaluated at the *same*
Gaussian variable, the pointwise rank-`j` bill on their product uses
`(sum of r's)^j` (not a combinatorial bound growing exponentially in
the cardinality at all derivative orders). Integration and the payment of
order losses (including when directions originate elsewhere) separate.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussian
open Function Filter Lattice Wilson RG Next.Foundations ProjectorNext.Equivariance
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius ContDiff

section Words
variable {G : Gauge} {n : Side} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {k j : ℕ} {U : Config G n} {f g : Config G n → E}

/-- For recentering identities in repeated derivatives. -/
theorem along {H : Config G n → Prop} (hi : H U) (hf : ∀ V, H V → ∀ A : Directions G n,
    ∀ᶠ t : ℝ in 𝓝 0, H (increment V (t • A))) (he : ∀ V : Config G n, H V → f V = g V)
    (l : List (Directions G n)) : leftDerivs f l U = leftDerivs g l U := by
  induction l generalizing U with
  | nil => exact he U hi
  | cons x l ih =>
    change deriv _ _ = deriv _ _
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [hf U hi x] with i hh
    exact ih hh

theorem increment_germ (V : Config G n) : Tendsto (increment V) (𝓝 0) (𝓝 V) := by
  have h : Tendsto (increment V) (𝓝 0) (𝓝 (increment V 0)) := by
    refine (show Continuous (increment V) from ?_).tendsto _
    unfold increment; fun_prop
  rwa [Work.G07.at_zero_increment] at h

theorem per_step (V : Config G n) (A : Directions G n) :
    Tendsto (fun t : ℝ => increment V (t • A)) (𝓝 0) (𝓝 V) := by
  apply (increment_germ V).comp (f := fun t : ℝ => t • A) ?_
  simpa using! (show Continuous (fun t : ℝ => t • A) by fun_prop).tendsto (0 : ℝ)

theorem identical (h : f =ᶠ[𝓝 U] g) (l : List (Directions G n)) :
    leftDerivs f l U = leftDerivs g l U := by
  refine along (H:=fun U => f =ᶠ[𝓝 U] g) h ?_ (fun V he => he.eq_of_nhds) l
  exact fun V he A => (per_step V A).eventually (eventually_eventually_nhds.mpr he)

theorem recur (h : HasOrderAt f U k) (A : Directions G n) :
    ∀ᶠ t : ℝ in 𝓝 0, HasOrderAt f (increment U (t • A)) k := h.nearby false A

lemma last_shift (A : Directions G n) (h : HasOrderAt f U (k+1)) :
    HasOrderAt (leftDerivs f [A]) U k :=
  leftDerivs_chart _ _ ((show 1+k=k+1 from Nat.add_comm ..) ▸ h)

lemma add_parts (hf : HasOrderAt f U k) (hg : HasOrderAt g U k) {l : List (Directions G n)}
    (hl : l.length ≤ k) : leftDerivs (f+g) l U = leftDerivs f l U + leftDerivs g l U := by
  induction l generalizing U with
  | nil => rfl
  | cons A l ih =>
    have hh : l.length < k := hl
    refine (((left_has A hh hf).add (left_has A hh hg)).congr_of_eventuallyEq (f₁:=fun t =>
      leftDerivs (f+g) l (increment U (t • A))) ?_).deriv
    filter_upwards [recur hf A, recur hg A] with t hu hv
    exact ih hu hv hh.le

lemma linear_parts (L : E →L[ℝ] F) (hf : HasOrderAt f U k) {l : List (Directions G n)}
    (hl : l.length ≤ k) : leftDerivs (fun x => L (f x)) l U = L (leftDerivs f l U) := by
  induction l generalizing U with
  | nil => rfl
  | cons A l ih =>
    have hh : l.length < k := hl
    refine Filter.EventuallyEq.deriv_eq ?_ |>.trans (L.hasFDerivAt.comp_hasDerivAt 0 (left_has A hh hf)).deriv
    filter_upwards [recur hf A] with t hu
    exact ih hu hh.le

lemma sub_parts (hf : HasOrderAt f U k) (hg : HasOrderAt g U k) {l : List (Directions G n)}
    (hl : l.length ≤ k) : leftDerivs (f-g) l U = leftDerivs f l U - leftDerivs g l U := by
  rw [sub_eq_add_neg, add_parts hf (g := -g) ?_ hl]
  · rw [sub_eq_add_neg]
    congr 1
    let L := -ContinuousLinearMap.id ℝ E
    have hz : -g = fun x => L (g x) := rfl
    rw [hz]; exact linear_parts L hg hl
  exact (show ContDiffAt ℝ k _ _ from hg).neg

/-- A transfer budget, in native left derivative directions, with exponent
order separated. `U` is the *only* evaluation being quantitatively priced.
When integrating, in particular use this on a **common** U for every factor. -/
structure Ticket (D : Directions G n → Prop) (k : ℕ) (U : Config G n) (w r : ℝ) (f : Config G n → E) : Prop where
  smooth : HasOrderAt f U k
  price_nonneg : 0 ≤ w
  radius_nonneg : 0 ≤ r
  price (l : List (Directions G n)) : l.length ≤ k → (∀ i∈l, D i) → ‖leftDerivs f l U‖ ≤ w*r^l.length

namespace Ticket
variable {D : Directions G n → Prop} {w d v r s : ℝ}

lemma legal (h : Ticket D k U w r f) (A : Directions G n) {l} (hl : List.length l < k) :
    HasDerivAt (fun t : ℝ => leftDerivs f l (increment U (t • A))) (leftDerivs f (A::l) U) 0 :=
  left_has A hl h.smooth

lemma base (h : Ticket D k U w r f) : ‖f U‖ ≤ w := by simpa [leftDerivs] using h.price [] (by simp) (by simp)

lemma agree (h : Ticket D k U w r f) (he : f =ᶠ[𝓝 U] g) : Ticket D k U w r g := by
  refine ⟨(show ContDiffAt ℝ k _ _ from h.smooth).congr_of_eventuallyEq ((increment_germ U).eventually he.symm), h.price_nonneg, h.radius_nonneg, fun l hl hD => ?_⟩
  rw [← identical he]; exact h.price l hl hD

lemma truncate (h : Ticket D k U w r f) (hl : j ≤ k) : Ticket D j U w r f :=
  ⟨h.smooth.fewer hl,h.price_nonneg,h.radius_nonneg,fun l hm hD => h.price l (hm.trans hl) hD⟩

lemma mono (h : Ticket D k U w r f) (hl : w ≤ v) (hm : r ≤ s) : Ticket D k U v s f := by
  refine ⟨h.smooth,h.price_nonneg.trans hl,h.radius_nonneg.trans hm, fun l hx hD => ?_⟩
  exact (h.price l hx hD).trans (mul_le_mul hl (pow_le_pow_left₀ h.radius_nonneg hm _) (pow_nonneg h.radius_nonneg _) (h.price_nonneg.trans hl))

lemma taper (h : Ticket D (k+1) U w r f) {A : Directions G n} (hv : D A) :
    Ticket D k U (w*r) r (leftDerivs f [A]) := by
  refine ⟨last_shift A h.smooth,mul_nonneg h.price_nonneg h.radius_nonneg,h.radius_nonneg,fun l hl H => ?_⟩
  rw [← Work.G07.left_append]
  refine (h.price (l++[A]) (by simpa) ?_).trans_eq ?_
  · intro i hi
    rcases List.mem_append.mp hi with hi|hi
    · exact H _ hi
    rwa [List.mem_singleton.mp hi]
  simp only [List.length_append,List.length_singleton,pow_succ]; ring

lemma pure (hr : 0 ≤ r) (x : E) : Ticket D k U ‖x‖ r (fun _ => x) := by
  refine ⟨contDiffAt_const,norm_nonneg _,hr,fun l _ _ => ?_⟩
  rw [Work.G07.left_const]; split
  next h => simp [h]
  next => rw [norm_zero]; exact mul_nonneg (norm_nonneg _) (pow_nonneg hr _)

lemma linear (h : Ticket D k U w r f) (L : E →L[ℝ] F) :
    Ticket D k U (‖L‖*w) r (fun x => L (f x)) := by
  refine ⟨L.contDiff.contDiffAt.comp _ h.smooth,mul_nonneg (norm_nonneg _) h.price_nonneg,h.radius_nonneg,fun l hl he => ?_⟩
  rw [linear_parts L h.smooth hl,mul_assoc]
  exact L.le_opNorm _ |>.trans (mul_le_mul_of_nonneg_left (h.price l hl he) (norm_nonneg _))

lemma add (hf : Ticket D k U w r f) (hg : Ticket D k U v r g) : Ticket D k U (w+v) r (f+g) := by
  refine ⟨(show ContDiffAt ℝ k _ _ from hf.smooth).add (show ContDiffAt ℝ k _ _ from hg.smooth), add_nonneg hf.price_nonneg hg.price_nonneg, hf.radius_nonneg,fun l hl H => ?_⟩
  rw [add_parts hf.smooth hg.smooth hl, add_mul]; exact (norm_add_le ..).trans (add_le_add (hf.price _ hl H) (hg.price _ hl H))

lemma sub (hf : Ticket D k U w r f) (hg : Ticket D k U v r g) : Ticket D k U (w+v) r (f-g) := by
  refine ⟨(show ContDiffAt ℝ k _ _ from hf.smooth).sub (show ContDiffAt ℝ k _ _ from hg.smooth), add_nonneg hf.price_nonneg hg.price_nonneg, hf.radius_nonneg,fun l hl H => ?_⟩
  rw [sub_parts hf.smooth hg.smooth hl, add_mul]; exact (norm_sub_le ..).trans (add_le_add (hf.price _ hl H) (hg.price _ hl H))

/-- Includes the empty bill (need `hr` then). -/
lemma sum {ι : Type*} {I : Finset ι} {w : ι → ℝ} {f : ι → Config G n → E} (hr : 0 ≤ r)
    (h : ∀ i∈I, Ticket D k U (w i) r (f i)) : Ticket D k U (∑ i∈I, w i) r (∑ i∈I, f i) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    simpa using! (pure (k:=k) (U:=U) (D:=D) hr (0:E))
  | insert i I hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi]
    exact (h i (by simp)).add (ih fun j hj => h j (by simp [hj]))

section Apply
variable {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    {y : Config G n → A →L[ℝ] B} {x : Config G n → A}

lemma apply_part (hx : HasOrderAt x U (k+1)) (hy : HasOrderAt y U (k+1)) (z : Directions G n) :
    leftDerivs (fun q => (y q) (x q)) [z] U = leftDerivs y [z] U (x U) + y U (leftDerivs x [z] U) := by
  change deriv _ 0 = _
  simpa only [zero_smul,Work.G07.at_zero_increment] using!
    ((left_has z (l:=[]) (Nat.zero_lt_succ _) hy).clm_apply (left_has z (l:=[]) (Nat.zero_lt_succ _) hx)).deriv

lemma bill_apply (hy : Ticket D k U w r y) (hx : Ticket D k U v s x) :
    Ticket D k U (w*v) (r+s) (fun q => y q (x q)) := by
  induction k generalizing y w x v with
  | zero =>
    refine ⟨ContDiffAt.clm_apply hy.smooth hx.smooth,mul_nonneg hy.price_nonneg hx.price_nonneg,
      add_nonneg hy.radius_nonneg hx.radius_nonneg, fun l hl H => ?_⟩
    rw [Nat.le_zero,List.length_eq_zero_iff] at hl
    subst l; rw [List.length_nil,pow_zero,mul_one]
    exact ((y U).le_opNorm _).trans (mul_le_mul hy.base hx.base (norm_nonneg _) hy.price_nonneg)
  | succ k ih =>
    refine ⟨ContDiffAt.clm_apply hy.smooth hx.smooth,mul_nonneg hy.price_nonneg hx.price_nonneg,
      add_nonneg hy.radius_nonneg hx.radius_nonneg, fun l hl H => ?_⟩
    induction l using List.reverseRecOn with
    | nil => rw [List.length_nil,pow_zero,mul_one]
             exact ((y U).le_opNorm _).trans (mul_le_mul hy.base hx.base (norm_nonneg _) hy.price_nonneg)
    | append_singleton l i _ =>
      rw [List.length_append,List.length_singleton,Nat.add_le_add_iff_right] at hl
      let a V := leftDerivs y [i] V (x V)
      let b V := y V (leftDerivs x [i] V)
      have ha := ih (hy.taper (H i (by simp))) (hx.truncate (Nat.le_succ k))
      have hb := ih (hy.truncate (Nat.le_succ k)) (hx.taper (H i (by simp)))
      rw [Work.G07.left_append, along (f:=leftDerivs (fun q => y q (x q)) [i])
        (g:=a + b) (H:=fun U => HasOrderAt x U (k+1) ∧ HasOrderAt y U (k+1)) ⟨hx.smooth,hy.smooth⟩
        (fun V hv A => (recur hv.1 A).and (recur hv.2 A)) (fun V hv => apply_part hv.1 hv.2 i)]
      refine ((ha.add hb).price l hl (fun i hi => H _ (List.mem_append_left _ hi))).trans_eq ?_
      simp only [List.length_append,List.length_singleton,pow_succ]; ring
end Apply

section Algebra
variable {K : Type*} [NormedRing K] [NormedAlgebra ℝ K]

lemma mul {x y : Config G n → K} (hx : Ticket D k U w r x) (hy : Ticket D k U v s y) :
    Ticket D k U (w*v) (r+s) (x*y) := by
  apply ((hx.linear (ContinuousLinearMap.mul ℝ K)).bill_apply hy).mono _ le_rfl
  apply mul_le_mul_of_nonneg_right _ hy.price_nonneg
  exact mul_le_of_le_one_left hx.price_nonneg (ContinuousLinearMap.opNorm_mul_le ..)

lemma pair_shift {x x' y y' : Config G n → K} {p q : ℝ}
    (h : Ticket D k U w r x) (hp : Ticket D k U p r (x-x'))
    (h' : Ticket D k U v s y') (hq : Ticket D k U q s (y-y')) :
    Ticket D k U (w*q+p*v) (r+s) (x*y - x'*y') := by
  rw [show x*y - x'*y' = x*(y-y')+(x-x')*y' by rw [mul_sub,sub_mul]; abel]
  exact (h.mul hq).add (hp.mul h')
end Algebra

lemma stack {ι : Type*} {I : Finset ι} {r w : ι → ℝ} {f : ι → Config G n → ℝ}
    (h : ∀ i∈I, Ticket D k U (w i) (r i) (f i)) : Ticket D k U (∏ i∈I, w i) (∑ i∈I, r i) (∏ i∈I, f i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp only [Finset.prod_empty,Finset.sum_empty]; simpa using! (pure (U:=U) (k:=k) (D:=D) le_rfl (1:ℝ))
  | insert i I hi ih =>
    rw [Finset.prod_insert hi,Finset.prod_insert hi,Finset.sum_insert hi]
    exact (h i (by simp)).mul (ih fun j hj => h j (by simp [hj]))


end Ticket
end Words
end YM.AnalyticBridge.LocalGaussian
