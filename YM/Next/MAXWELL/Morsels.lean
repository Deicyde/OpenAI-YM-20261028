import YM.Next.MAXWELL.Flavor
import YM.Next.MAXWELL.Shelves

/-!
# Highest single contraction, as a Wick derivation

Color equivariant on the actual observables. Filtration drop when
a mixed-leg tester uses a partner in the strict interior jet shelf.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis MeasureTheory Wick
open MvPolynomial hiding monomial
open scoped ContDiff Topology BigOperators InnerProductSpace ComplexOrder
variable {G : Gauge} {j k l n w d : ℕ}

abbrev keyAt (j : ℕ) (a : Fin (legDim G j)) := (⟨j,a⟩ : Slot G)

lemma erase_var (i : Slot G) (p : WickPol G) (h : pderiv i p = 0) : i ∉ p.vars := by
  classical
  intro hi; obtain ⟨s,hs,hK⟩ := (mem_vars_iff_mem_support i).1 hi
  let u := s-Finsupp.single i 1
  have hu : u+Finsupp.single i 1=s := tsub_add_cancel_of_le (single_le hK)
  have ht := coeff_pderiv (i:=i) p u
  rw [hu,h,MvPolynomial.coeff_zero] at ht
  exact mul_ne_zero (MvPolynomial.mem_support_iff.mp hs) (by exact_mod_cast Nat.succ_ne_zero (u i)) ht.symm
lemma shelf_var {p : WickPol G} (hp : p ∈ shelf G j) (i : Slot G) : pderiv i p ∈ shelf G j := by
  classical
  rw [shelf_support]; intro u hx b hb
  rw [coeff_pderiv] at hx
  apply shelf_support.mp hp (u+Finsupp.single i 1) (fun h => hx (by rw [h,zero_mul])) b
  simp [Finsupp.support_add_eq_union,hb]

/-- Nibble p precisely in one order j. B leg at x relative to p. -/
def singleBite (j : ℕ) (B : Probe G k) (x : E4) : Derivation ℂ (WickPol G) (WickPol G) :=
  ∑ a : Fin (legDim G j), (↑(legKernel B (coordinateLeg (keyAt j a)) x):ℂ) • pderiv (keyAt j a)

lemma bite_eval (j : ℕ) (B : Probe G k) (x : E4) (p : WickPol G) : singleBite j B x p=
    ∑ a : Fin (legDim G j), (↑(legKernel B (coordinateLeg (keyAt j a)) x):ℂ) • pderiv (keyAt j a) p :=
  derivation_sum_apply ..

lemma bite_letter (j : ℕ) (B : Probe G k) (x : E4) (i : Slot G) : singleBite j B x (X i) = if i.1=j then C (legKernel B (coordinateLeg i) x : ℂ) else 0 := by
  rw [bite_eval]; rcases i with ⟨l,a⟩; dsimp only
  split_ifs with h
  · subst l; rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ _)]
    · rw [pderiv_X_self, ← C_mul', mul_one]
    intro i _ hi; rw [pderiv_X_of_ne (by simp [Ne.symm hi]), smul_zero]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [pderiv_X_of_ne (by intro w; exact h (congr_arg Sigma.fst w)),smul_zero]
lemma bite_symbol (B : Probe G k) {x : E4} (hx : x ≠ 0) (p : Probe G j) : singleBite j B x (symbol j p)=C (legKernel B p x : ℂ) := by
  rw [← show eat B x 0 (symbol j p)= C (legKernel B p x : ℂ) from (eat_symbol B p hx).trans (by rw [K,sub_zero])]
  unfold symbol; simp_rw [map_sum,C_mul',Derivation.map_smul]
  apply Finset.sum_congr rfl; intro i _
  rw [bite_letter,if_pos rfl,eat,mkDerivation_X,K,sub_zero]
lemma bite_off (B : Probe G k) (x : E4) (p : Probe G l) (h : l≠j) : singleBite j B x (symbol l p)=0 := by
  unfold symbol; rw [map_sum]; apply Finset.sum_eq_zero; intro i _
  rw [C_mul',Derivation.map_smul,bite_letter,if_neg h,smul_zero]
lemma all_bite (p : Probe G j) (x y : E4) (q : WickPol G) (h : q∈shelf G k) : eat p x y q=∑ i∈Finset.range (k+1),singleBite i p (x-y) q := by
  classical
  rw [← derivation_sum_apply]
  let A : Derivation ℂ (WickPol G) (WickPol G) := ∑ i∈Finset.range (k+1),singleBite i p (x-y)
  change eat p x y q=A q; rw [← sub_eq_zero, ← Derivation.sub_apply]; apply MvPolynomial.derivation_eq_zero_of_forall_mem_vars
  intro i hi
  have ht : i.fst ≤ k := MvPolynomial.mem_supported.mp (show q∈Rack G k from h) hi
  unfold A; rw [Derivation.sub_apply,sub_eq_zero,derivation_sum_apply,Finset.sum_eq_single_of_mem i.fst (by simp; omega),bite_letter,if_pos rfl]; exact mkDerivation_X ..
  intro j _ hh; rw [bite_letter,if_neg hh.symm]
lemma upper_shelf {p : WickPol G} (hp : p∈shelf G d) (q : Probe G k) (x : E4) : singleBite j q x p∈ shelf G d := by
  rw [bite_eval]; exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (shelf_var hp _)


def circulate (j : ℕ) (p : Flavor k) (q : Flavor l) (x : E4) : Derivation ℂ (WickPol G) (WickPol G) :=
    ∑ c : G.ColorIndex, bit q c • singleBite j (flavor k c p) x
lemma circulate_eval (j : ℕ) (p : Flavor k) (q : Flavor l) (x : E4) (A : WickPol G) : circulate j p q x A=
    ∑ c : G.ColorIndex, bit q c * singleBite j (flavor k c p) x A := derivation_sum_apply ..

lemma circulates_one (c : G.ColorIndex) (p : Flavor k) (q : Flavor l) (r : Flavor j) (i : G.ColorIndex) {x : E4} (hx : x ≠ 0) :
    circulate j p q x (bit r i)=(fare c p r x:ℂ) • bit q i := by
  rw [circulate_eval]; simp_rw [bit,bite_symbol _ hx, any_ink c p r _ _ hx]
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)];
  · rw [if_pos rfl,one_mul,mul_comm,C_mul']
  intro a _ ha; rw [if_neg ha]; simp
lemma circulates_off (p : Flavor k) (q : Flavor l) (r : Flavor n) (i : G.ColorIndex) (x : E4) (he : n ≠ j) :
    circulate j p q x (bit r i)=0 := by
  rw [circulate_eval]; refine Finset.sum_eq_zero fun i _ => ?_; change bit q _ * singleBite _ _ x (symbol _ _)=0; rw [bite_off _ _ _ he, mul_zero]

lemma hue_orbit (u : G.El) (p : Flavor k) (i : G.ColorIndex) : pigment u (bit p i) =
    ∑ c : G.ColorIndex, (↑(G.adjoint u (unitColor G c) i):ℂ) • bit p c := by
  apply equalPol; intro A
  rw [bit_tint p]; simp_rw [map_sum,map_smul]; unfold line
  conv_lhs => rw [← color_sum (G:=G) (available (A k) p),map_sum]
  simp only [WithLp.ofLp_sum,Finset.sum_apply,map_smul,PiLp.smul_apply,bit,symbol_test,
    Complex.ofReal_sum,smul_eq_mul, Complex.ofReal_mul]; exact Finset.sum_congr rfl fun i _ => mul_comm ..

lemma orbit_runs (u : G.El) (p : Flavor k) (q : Flavor l) {x : E4} (hx : x≠0) (A : WickPol G) :
    pigment u (circulate j p q x A)=circulate j p q x (pigment u A) := by
  let R : Derivation ℂ (WickPol G) (WickPol G) := circulate j p q x
  have he {n} (r : Flavor n) (i : G.ColorIndex) : pigment u (circulate j p q x (bit r i))=circulate j p q x (pigment u (bit r i)) := by
    rw [hue_orbit]; simp only [map_sum,Derivation.map_smul]; by_cases hv:n=j
    · subst n; simp_rw [circulates_one i p q r _ hx,map_smul,hue_orbit,Finset.smul_sum]; exact Finset.sum_congr rfl fun a _ => smul_comm ..
    simp_rw [circulates_off p q r _ _ hv,map_zero, smul_zero, Finset.sum_const_zero]
  induction A using MvPolynomial.induction_on with
  | C a => rw [algHom_C, derivation_C, map_zero]; exact (derivation_C ..).symm
  | add p q hp hq => rw [map_add,map_add,map_add,map_add,hp,hq]
  | mul_X A i ih =>
    have ht : pigment u (circulate j p q x (X i)) = circulate j p q x (pigment u (X i)) := by
      rw [← symbol_coordinate,divide]; simp_rw [map_sum,he]
    rw [map_mul (pigment u),Derivation.leibniz,Derivation.leibniz]; simp only [smul_eq_mul, map_add,map_mul, ht,ih]
lemma circulates_lower (j : ℕ) (p : Flavor k) (q : Flavor l) {x : E4} (hx : x ≠ 0) (hh : l<j) (A : WickPol G) (ha : A∈ shellSector G (w+1)) :
    circulate j p q x A∈shellSector G w := by
  classical
  rw [sector] at ha ⊢
  refine ⟨?_,fun u => by rw [orbit_runs _ _ _ hx,ha.2 u]⟩
  rw [circulate_eval]; refine Submodule.sum_mem _ fun i _ => ?_
  rw [bite_eval,Finset.mul_sum]; apply Submodule.sum_mem; intro s _
  rw [mul_smul_comm]; apply Submodule.smul_mem
  let u := keyAt j s
  let r := pderiv u A
  let t : Probe G l := flavor l i q
  unfold bit symbol; rw [Finset.sum_mul]; refine Submodule.sum_mem _ fun a _ => ?_
  rw [mul_assoc,C_mul']; apply Submodule.smul_mem
  let v := keyAt (G:=G) l a
  have h : A∈lowerCap G (w+1) := ha.1
  rw [lowerCap, MvPolynomial.mem_restrictSupport_iff] at h
  change X v*r∈_
  rw [lowerCap,MvPolynomial.mem_restrictSupport_iff]; intro m hm
  rw [Finset.mem_coe,MvPolynomial.mem_support_iff] at hm
  by_cases H : v∈m.support
  · let d := m-Finsupp.single v 1
    have hA : d+Finsupp.single v 1=m := tsub_add_cancel_of_le (single_le H)
    have hx := coeff_pderiv (i:=u) A d
    change MvPolynomial.coeff d r=_ at hx
    have ht : r.coeff d ≠ 0 := fun hu => hm (by rw [← hA,add_comm,MvPolynomial.coeff_X_mul,hu])
    have hb : degree (d+Finsupp.single u 1) ≤ w+1 := h (MvPolynomial.mem_support_iff.mpr (show _ from fun hb => ht (by rw [hx,hb,zero_mul])))
    change degree m ≤ _
    rw [← hA,weight_next]; rw [weight_next] at hb; change degree d+j+2 ≤ _ at hb; change degree d+l+2 ≤ w; omega
  exfalso
  apply hm; rw [MvPolynomial.coeff_X_mul', if_neg ?_]
  exact H
end YM.Maxwell.Free
