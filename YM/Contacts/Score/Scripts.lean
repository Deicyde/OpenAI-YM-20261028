import YM.Contacts.Score.Tape
import YM.Contacts.Normal.Pieces

/-! # Commit exact optical instructions; independence and localization -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Normal
open Function Filter Set Metric MeasureTheory Submodule Ordered
open scoped Topology BigOperators Classical ContDiff TensorProduct InnerProductSpace
variable {E A B I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]
variable {R S T : Optical E → Prop} {K L : Submodule ℝ E}
variable {p q : Optical E}
inductive Mark (R : Optical E → Prop) : Score E A → Prop
| atom {p : Optical E} (g : E→ A) (h : R p) : Mark R (g ⊗ₜ[ℂ] p)
| zero : Mark R 0
| plus {a b} (h : Mark R a)(hh : Mark R b) : Mark R (a+b)
namespace Mark
variable {a b : Score E A}
omit [FiniteDimensional ℝ E]
lemma switch (h : Mark R a) (hp : ∀r,R r→ S r): Mark S a := by
   induction h with
   | atom g h => exact .atom g (hp _ h)
   | zero=> exact .zero
   | plus _ _ hx hy=> exact hx.plus hy
lemma inst (h : R p) : Mark R (instructionScore E A p):= .atom _ h
lemma minus (h : Mark R a) : Mark R (-a) := by
   induction h with
   | atom g h => rw [← TensorProduct.neg_tmul]; exact .atom _ h
   | zero => rw [neg_zero]; exact .zero
   | plus _ _ hx hy=> rw [neg_add]; exact hx.plus hy
lemma sum {s: Finset I} {f : I→ Score E A} (h : ∀i∈s,Mark R (f i)) : Mark R (∑ i∈s,f i) := by
   induction s using Finset.induction_on with
   | empty=> rw [Finset.sum_empty]; exact .zero
   | insert i s hi ih=> rw [Finset.sum_insert hi]; exact (h i (by simp)).plus (ih (fun j hj=> h _ (Finset.mem_insert_of_mem hj)))
lemma prod (h : Mark R a)(hx : Mark S b) (hc : ∀ ⦃p q⦄,R p→S q→ T (p*q)) : Mark T (a*b) := by
   induction h with
   | atom g h =>
     induction hx with
     | atom f he => rw [Algebra.TensorProduct.tmul_mul_tmul]; exact .atom _ (hc h he)
     | zero => rw [mul_zero]; exact .zero
     | plus _ _ hx hy=> rw [mul_add]; exact hx.plus hy
   | zero=> rw [zero_mul]; exact .zero
   | plus _ _ hx hy=> rw [add_mul]; exact hx.plus hy
lemma agree (h : Mark R a) (hx : Mark S b)(hc : ∀ ⦃p q⦄, R p→ S q→ Commute p q) : Commute a b:= by
   induction h with
   | atom g h=>
     induction hx with
     | atom f he => exact Commute.tmul (Commute.all g f) (hc h he)
     | zero => exact Commute.zero_right _
     | plus _ _ hx hy=> exact hx.add_right hy
   | zero => exact Commute.zero_left _
   | plus _ _ hx hy=> exact hx.add_left hy
lemma transformed (h : Mark R a) (f : E→ A →ₗ[ℂ] B) : Mark R (reshape f a) := by
   induction h with
   | atom g h=> rw [reshape_tape]; exact .atom _ h
   | zero=> rw [map_zero]; exact .zero
   | plus _ _ hx hy=> rw [map_add]; exact hx.plus hy
lemma relabel (h : Mark R a)(f : A →ₐ[ℂ] B) : Mark R (retag E f a):= transformed h _
end Mark

/-- just for commuting: all the numbers and shapes will be filled at the geometry later -/
inductive Uses (K : Submodule ℝ E) : Optical E → Prop
| taylor (L : Submodule ℝ E) (h : L≤K) (s : ℝ)(i : ℕ): Uses K (taylor L s i)
| times {p q : Optical E} : Uses K p → Uses K q → Uses K (p*q)
| id : Uses K 1

lemma Uses.widen (h : Uses K p)(hh : K≤L): Uses L p:= by
   induction h with
   | taylor M h t i=> exact .taylor _ (h.trans hh) t i
   | times _ _ hx hy=> exact hx.times hy
   | id => exact .id
lemma Uses.independent (h : Uses K p)(hh : Uses L q)(he : K≤Lᗮ): Commute p q := by
   induction h with
   | taylor M h t i=>
     induction hh with
     | taylor J hh u j=> exact (commute_taylor J M ((h.trans he).trans (orthogonal_le hh)) u t j i).symm
     | times _ _ hx hy=> exact hx.mul_right hy
     | id => exact Commute.one_right _
   | times _ _ hx hy=> exact hx.mul_left hy
   | id => exact Commute.one_left _

/-- Instruction which uses only germs at a specified (transformed) point. -/
def Germ (p : Optical E) (h : E→ E) := ∀ x, ∀ f g : SmoothTests E, f.val =ᶠ[𝓝 (h x)] g.val → (p f).val =ᶠ[𝓝 x] (p g).val
lemma focal (s : ℝ)(i : ℕ) : Germ (taylor K s i) (slide K 0) := fun _ _ _ h=> taylor_germ K h
omit [FiniteDimensional ℝ E] in
lemma Germ.identity : Germ (1:Optical E) id:= fun _ _ _ h=> h
omit [FiniteDimensional ℝ E] in
lemma Germ.times {f g : E→ E}(h : Germ p f)(he : Germ q g) : Germ (p*q) (g ∘ f):= fun x _ _ hx=> h _ _ _ (he (f x) _ _ hx)
lemma Germ.right (hf : Uses K p) (h : Germ q (slide K 0)) : Germ (p*q) (slide K 0) := by
  induction hf generalizing q with
  | id=> rw [one_mul]; exact h
  | taylor L he s i=>
    have he' : (slide K 0) ∘ (slide L 0)= (slide K 0) := by
       funext x; simp only [Function.comp_apply]; rw [slide_zero L,map_sub]
       rw [slip_mem K 0 (he (L.starProjection_apply_mem x)),zero_smul,sub_zero]
    exact he' ▸ Germ.times (focal s i) h
  | times _ _ hp hq=> rw [mul_assoc]; exact hp (hq h)

-- Restricting evaluations before taking final integrals.
lemma all_off {f : SmoothTests E} (h : ∀ x∈Kᗮ, x∉ tsupport f.val) {a : Score E A} (he : Mark (fun p=> Germ p (slide K 0)) a) : a * instructionScore E A (mask f)=0 := by
  induction he with
  | zero=> rw [zero_mul]
  | @atom p g hv=> rw [instructionScore,Algebra.TensorProduct.tmul_mul_tmul]; have hp : p * mask f=0:= by
                     apply LinearMap.ext; intro u; apply Subtype.ext; funext x; have he:= notMem_tsupport_iff_eventuallyEq.mp (h _ (show slide K 0 x∈ Kᗮ by rw [slide_zero]; exact sub_starProjection_mem_orthogonal x)); have ht:= hv x (mask f u) 0 (by filter_upwards [he] with x hx; exact mul_eq_zero_of_left hx _)|>.eq_of_nhds; rw [map_zero] at ht; exact ht
                   rw [hp,TensorProduct.tmul_zero]
  | plus _ _ hx hy=> rw [add_mul,hx,hy,add_zero]
lemma Mark.chain [DecidableEq I] (p : Finset I) (f:I→Score E A) (hc:(p:Set I).Pairwise fun i j=> Commute (f i) (f j)) (h:∀i∈p,Mark (Uses K) (f i)): Mark (Uses K) (Ordered.product p f):= by
   rw [Ordered.actual p f hc]; exact Finset.noncommProd_induction p f hc (Mark (Uses K)) (fun _ _ hx hy=> hx.prod hy (fun _ _ x y=>x.times y)) (Mark.inst (A:=A) Uses.id) h
end YM.Contacts.Normal
