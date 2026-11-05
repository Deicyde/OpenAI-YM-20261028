import YM.Euclid.Pairing
import YM.Extraction.Banks

/-!
# Exact finite representation of doubled test

Handle exceptional lattice weights at the seam (right-closed fundamental domain).
Track transform acts on both links & curvature label tensor.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extraction.Banks
open Function Set MeasureTheory Filter Lattice Wilson Cells Table.Pairing WithLp
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexOrder
variable {G : Gauge} (C : Family G) {a : Axis} {N p : ℕ}

lemma reflectedK {K : Cut (C.side N p)} (P : Site (C.side N p)) (H : C.Makes) (v : C.book.Token)
    (ht : C.ref v.1 ≤ N) (u) : C.seen (C.book.reflectedToken K.pos v) (K.reflect P) u = star (C.seen v P (K.pullC G u)) :=
  (C.rotated H ht (star v.2) K.flip P K.slide u).trans (C.reality H ht v.2 P (K.pullC G u))

lemma backwards (Q V : Table.PastTest C.book a) (K : Cut (C.side N p)) :
    ∃ e : (Fin Q.n → Site (C.side N p)) × (Fin V.n → Site (C.side N p)) ≃ (Fin (Q.n+V.n) → Site (C.side N p)),
      ∀ (r), e r=Fin.append (K.reflect ∘ r.1) r.2 := by
  classical
  let S := Site (C.side N p)
  let f := fun r : (Fin Q.n→S)×(Fin V.n→S) => Fin.append (K.reflect ∘ r.1) r.2
  have hp : Bijective f := by
    constructor
    · rintro ⟨x,y⟩ ⟨s,t⟩ h
      refine Prod.ext ?_ ?_
      · ext1 i; apply (show Involutive K.reflect from K.twice).injective; simpa [f] using congr_fun h (Fin.castAdd _ i)
      ext1 i; simpa [f] using congr_fun h (Fin.natAdd Q.n i)
    intro y; exact ⟨(K.reflect ∘ y ∘ Fin.castAdd V.n, y ∘ Fin.natAdd Q.n), by
      funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [f]⟩
  exact ⟨Equiv.ofBijective f hp, fun _ => rfl⟩

private lemma native_tie (N p) (a : Axis) (o : Site (C.side N p)) :
    let t := C.S.place o a
    let u := C.S.place ((plane C N p a).reflect o) a
    u = -t ∨ t=C.S.radius p ∧ u=t := by
  intro t u
  let P := plane C N p a
  let d := lift o a
  let e := lift (P.reflect o) a
  have he : (↑e:Per (C.side N p))= -(d:Per _) := by
    change wrap _ (lift (P.reflect o)) P.pos= -(wrap _ (lift o) P.pos)
    rw [wrap_lift,wrap_lift,Cut.reflect_here]; simp [P,plane,Kind.shift]
  have hz := lift_centers o a; have hv := lift_centers (P.reflect o) a
  let n := (C.side N p).val
  change - (n:ℤ)<2* d ∧ 2*d ≤ n at hz
  change - (n:ℤ)<2* e ∧ 2*e ≤ n at hv
  rcases eq_or_ne e (-d) with h'|h'
  · left; change C.S.a N * (e : ℝ) = -(C.S.a N*(d:ℝ)); rw [h',Int.cast_neg,mul_neg]
  right
  rw [← Int.cast_neg] at he
  obtain ⟨k,H⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub ..).mp he
  change -d - e = n*k at H
  have ht : d+e=n := by
    rcases lt_trichotomy k 0 with g|g|g
    · have hp := show (n:ℤ)*k ≤ -n from by nlinarith [show k ≤ -1 from Int.le_sub_one_of_lt g,show (0:ℤ)≤n from Nat.cast_nonneg _]
      omega
    · subst k; omega
    have hp : (n:ℤ) ≤ (n:ℤ)*k := by nlinarith [show (1:ℤ) ≤ k from g,show (0:ℤ) ≤ n from Nat.cast_nonneg _]
    omega
  change C.S.a N*(d:ℝ)=_ ∧ C.S.a N*(e:ℝ)=C.S.a N*(d:ℝ)
  unfold Schedule.radius; rw [← C.S.span_side N p]; constructor
  · rw [show ((↑(C.S.side N p).val):ℝ)=2*(d:ℝ) from by exact_mod_cast (show (n:ℤ)=2*d by omega)]
    ring
  rw [show e=d by omega]

lemma tester (N p) (Q V : Table.PastTest C.book a) (x : Fin Q.n → Site (C.side N p)) (y : Fin V.n → Site (C.side N p))
    (he : supported C Q p) :
    withOther Q V (Order.cells C N p (Fin.append ((plane C N p a).reflect ∘ x) y)) = star (weightValue C Q N p x) * weightValue C V N p y := by
  let P := plane C N p a
  let A := Order.cells C N p (Fin.append (P.reflect ∘ x) y)
  change star (Q.f (earlier a A))*V.f (after A)=star (Q.f _)*V.f _
  congr 1
  · let p1 := earlier (n := Q.n) a A
    let p0 := Order.cells C N p x
    suffices h : Q.f p1=Q.f p0 from congr_arg star h
    have hh i : p1 i a= -(C.S.place (P.reflect (x i)) a) := by
      simp only [p1,earlier,A,Order.cells,points_apply,Fin.append_left,Function.comp_apply]
      simp [ride]
    have hs i b (h:b≠a) : p1 i b=p0 i b := by
      simp [p0,p1,earlier,A,Order.cells,ride,h]; change _ * ↑(lift (P.reflect _) b) = C.S.a _ * _
      congr 1; congr 1
      unfold lift; rw [Cut.reflect_there P _ h]
    by_cases h : p1=p0; rw [h]
    have hg : ∃ i, p1 i a≠p0 i a := by by_contra! hp; apply h; ext i b; by_cases h:b=a <;> simp [hs,h,hp]
    obtain ⟨i,hi⟩ := hg
    have hk : p0 i a = C.S.radius p ∧ p1 i a = - C.S.radius p := by
      rw [hh] at *
      rcases native_tie C N p a (x i) with h|h
      · exact False.elim (hi (h ▸ neg_neg ..)) -- orientation
      change C.S.place (x i) a=_ ∧ _
      exact ⟨h.1,congr_arg Neg.neg (h.2.trans h.1)⟩
    rw [show Q.f p1=0 from by_contra fun w => hk.2.symm.not_lt (he (subset_closure w) i a).1,
      show Q.f p0=0 from by_contra fun w => hk.1.not_lt (he (subset_closure w) i a).2]
  congr 1; ext1 i; simp [A,Order.cells,after]

lemma int_ (Q V : Table.PastTest C.book a) (N p x y) : Integrable (fun U => star (base C Q N p x ((plane C N p a).pullC G U))*base C V N p y U) (law G _ (C.beta N p)) :=
  continuous_integrable _ (((elementary C Q x).comp (continuous_pull (Signed.mirror a) _)).star.mul (elementary C V y))

lemma at_cut (Q V : Table.PastTest C.book a) (hq : C.sufficient N Q.v) (he : supported C Q p) (h : C.Makes) :
    Order.smears C N p (tied Q.v V.v a) (withOther Q V) = form (C.beta N p) (plane C N p a) (stem C V N p) (stem C Q N p) := by
  let s := plane C N p a
  let f := tied Q.v V.v a
  obtain ⟨e,hv⟩ := backwards C Q V (plane C N p a)
  unfold Order.smears; rw [← Equiv.sum_comp e, Finset.mul_sum,Fintype.sum_prod_type]
  unfold form moment stem
  -- star sum and group
  have HI x y : Integrable (fun U => base C V N p y U * star (base C Q N p x ((plane C N p a).pullC G U))) (law G (C.side N p) (C.beta N p)) := by
    simpa only [mul_comm (base C V N _ _ _)] using int_ C Q V N p x y
  simp_rw [star_sum, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => HI j i)]
  simp_rw [integral_finsetSum Finset.univ (fun i _ => HI _ _)]
  rw [Finset.sum_comm] -- on first; y then x
  apply Finset.sum_congr rfl; intro y _; apply Finset.sum_congr rfl; intro x _
  rw [hv, tester C N p Q V x y he,C.num]
  simp only [← integral_const_mul]; apply integral_congr_ae; filter_upwards with U
  simp only [base, Fin.prod_univ_add, Function.comp_apply,tied,Fin.append_left,Fin.append_right]
  have hh i := reflectedK C (x i) h (Q.v i) (K := plane C N p a) (hq i) U
  change ∀ i, C.seen (C.book.reflectedToken a (Q.v i)) _ U = _ at hh
  simp_rw [hh]
  simp only [star_prod, star_mul', star_pow, Complex.star_def,Complex.conj_ofReal, Nat.mul_add,pow_add]; ring
end YM.Extraction.Banks
