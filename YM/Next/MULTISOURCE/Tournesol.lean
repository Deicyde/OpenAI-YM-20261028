import YM.Next.MULTISOURCE.Seat
import YM.Next.MULTISOURCE.Tea

/-!
# Approximants at the input side, including unguarded amplitudes at finite volume
-/
set_option autoImplicit false
noncomputable section
namespace YM.Multi.Desk
open RG Wilson Lattice MeasureTheory Marker Finset Filter MvPolynomial
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {I : Type*} [Fintype I] [DecidableEq I] {G : Gauge} {n : Side}
variable (P : Rep G n) {C E σ Λ w : ℝ} (H : P.Lawful σ C Λ E w)
    (D : I → Pulse G n)

def fill (D : I → Pulse G n) (U : Config G n) := staves fun i => (D i).1 U
def steep (D : I → Pulse G n) (U : Config G n) (x : Pack n) := staves fun i => (D i).2 x U

def cup (N : ℕ) (U : Config G n) := vapor N (fill D U) * chip P U (steep D U)
lemma filled (N : ℕ) : Reservoir.listed (cup P D N) := by
  refine listed_mul (listed_sum _ _ (fun i => listed_smul _ (listed_pow ?_ _))) ?_
  · apply listed_sum; intro i; exact listed_smul _ (listed_fix (MvPolynomial.X _))
  simp_rw [chip,Pack.clears,sum_filter]
  refine listed_mul (listed_C _) (listed_sum _ _ (fun i => listed_if _ (listed_prod _ _ (fun j => ?_))))
  exact listed_add (listed_C _) (listed_sum _ _ (fun _ => listed_smul _ (listed_fix _)))

lemma cup_print (R : Census I) (x : R.Mode) (N : ℕ) (he : Fintype.card I ≤ N) :
    (fun U => coeff (power x.val) (cup P D N U))=jet P R D x := by
  funext U; simp_rw [← print_coeff R]
  dsimp only [cup]; rw [patch P U (steep D U) (fill D U) R he (staves_zero R _)]
  simp_rw [fill,steep, staves_print]
  rfl

section
omit P D [Fintype I] [DecidableEq I]
variable {J X : Type*} [MeasurableSpace X] {A B : X → ℂ}
lemma revenue (h : Envelope A) : Tint Set.univ A := ⟨_, fun x _ => h.cost.choose_spec x⟩
lemma parcel (V : Finset J) (F : J→ X→ℂ) (h : ∀ i, Envelope (F i)) : Envelope fun x => ∏ i∈V,F i x :=
  { meas := Finset.measurable_fun_prod _ (fun i _ => (h i).meas)
    cost := ⟨_,fun x => (tint_prod V F fun i => revenue (h i)).choose_spec x (Set.mem_univ _)⟩ }
lemma envelope_ite (p : X → Prop) [DecidablePred p] (h : MeasurableSet {x | p x}) (he : Envelope A) :
    Envelope (fun x => if p x then A x else 0) := ⟨he.meas.ite h measurable_const, _,fun x =>
      (tint_ite (revenue he) p).choose_spec x (Set.mem_univ _)⟩
lemma tempered (N : ℕ) (h : Envelope A) : Envelope fun x => Desk.powers N (A x) := by
  have hp (i : ℕ) : Envelope fun x => A x^i := by
    induction i with
    | zero => simp only [pow_zero]; exact Leaf.atom _
    | succ i ih => simp only [pow_succ]; exact Leaf.multiply ih h
  refine Leaf.amounts _ _ fun j => ?_
  simp_rw [div_eq_mul_inv]; exact Leaf.multiply (hp _) (Leaf.atom _)
end

include H
lemma holders : Envelope fun U : Config G n => (Real.exp (P.exponent U):ℂ) := by
  obtain ⟨hm,B,hB⟩ := (P.exponentEnv H).exp
  exact ⟨Complex.continuous_ofReal.measurable.comp hm,B, fun x => by rw [Complex.norm_real]; exact hB x⟩
lemma holders_K (q : Pack n) : Envelope fun U => incumbent P U q := by
  obtain ⟨p,hp,hP⟩ := Activities.K_total H.labels.boundK
  refine ⟨(incumbent_legible P q H.labels.forced).borel, _, fun x => collects_bound P p (fun i => (P.activities.K i x:ℂ)) hp (fun i => ?_) q⟩
  rw [Complex.norm_real]; exact (hP i).2 x

variable (h : ∀ i, Envelope (D i).1 ∧ ∀ j, Envelope ((D i).2 j))
include h

omit H [DecidableEq I] in
lemma pour_w (z : I → ℂ) : Envelope fun U => eval z (fill D U) := by
  simp_rw [fill, staves_eval]; exact Leaf.amounts _ _ (fun i => Leaf.multiply (Leaf.atom _) ((h i).1))
omit [DecidableEq I] in
lemma brew_w (z : I → ℂ) : Envelope fun U => baseJoint P U (fun i => eval z (steep D U i)) := by
  simp_rw [baseJoint,Pack.clears,Finset.sum_filter]; refine Leaf.multiply (holders P H) (Leaf.amounts _ _ fun i => ?_)
  refine envelope_ite _ ?_ (parcel _ _ (fun j => ?_))
  · simpa only [Pack.clears,Finset.mem_filter,Finset.mem_univ,true_and] using Pack.neighborhood (G:=G) i P.p.threshold
  simp_rw [steep,staves_eval]; exact Leaf.combine (holders_K P H j) (Leaf.amounts _ _ (fun i => Leaf.multiply (Leaf.atom _) ((h i).2 _)))
omit [DecidableEq I] in
lemma cup_pass (N : ℕ) (z : I→ℂ) : Integrable (fun x => eval z (cup P D N x)) (prior G _) := by
  simp_rw [cup,map_mul,chip_eval, vapor_eval]; obtain ⟨hm,C,hC⟩ := Leaf.multiply (tempered (N+1) (pour_w D h z)) (brew_w P H D h z)
  exact Integrable.of_bound hm.aestronglyMeasurable C (Eventually.of_forall hC)
omit [DecidableEq I] in
lemma signal_cast (z : I→ℂ) : Integrable (perturbs P D z) (prior G _) := by
  let p := fun U => eval z (fill D U)
  have hp : Envelope (fun U => Complex.exp (p U)) :=
    ⟨Complex.continuous_exp.measurable.comp ((pour_w D h z).meas),_,fun x => (colors (revenue (pour_w D h z))).choose_spec
      x (Set.mem_univ _)⟩
  obtain ⟨hm,B,hB⟩ := Leaf.multiply hp (brew_w P H D h z)
  have he := Integrable.of_bound (μ:=prior G n) hm.aestronglyMeasurable B (Eventually.of_forall hB)
  simp only [p, fill, steep, staves_eval] at he
  exact he

omit [DecidableEq I] in
lemma palette (r : ℝ) : TendstoUniformlyOn (fun N (x : (I→ℂ) × Config G n) => eval x.1 (cup P D N x.2))
    (fun x => perturbs P D x.1 x.2) atTop (Set.prod (boxes r) Set.univ) := by
  let V := Set.prod (boxes (I:=I) r) (Set.univ (α:=Config G n))
  have he (A : I → Config G n → ℂ) (he : ∀ i, Envelope (A i)) : Tint V fun x => ∑ i,x.1 i*A i x.2 := by
    refine tint_sum _ _ fun i => tint_mul ⟨r,fun x hx => ?_⟩ ⟨_,fun x _ => (he i).cost.choose_spec x.2⟩
    exact hx.1 i
  let F (x : (I→ℂ) × Config G n) := ∑ i,x.1 i*(D i).1 x.2
  let X (x : (I→ℂ) × Config G n) := baseJoint P x.2 (fun i => ∑ j,x.1 j*(D j).2 i x.2)
  have hf : Tint V F := he _ (fun i => (h i).1)
  simp_rw [cup,map_mul,chip_eval,vapor_eval,fill,steep,staves_eval]
  refine uniform_mul (colors hf) (show Tint V X from ?_) (condensate hf (painting V F)) (painting _ _)
  simp_rw [X,baseJoint,Pack.clears, Finset.sum_filter]
  refine tint_mul ⟨_,fun x _ => (holders P H).cost.choose_spec x.2⟩ (tint_sum _ _ (fun i => tint_ite (tint_prod _ _ ?_) _))
  intro j; exact tint_add ⟨_,fun x _ => (holders_K P H j).cost.choose_spec x.2⟩ (he _ fun i => (h i).2 _)
end YM.Multi.Desk
