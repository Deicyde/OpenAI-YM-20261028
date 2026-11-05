import YM.Extra.MULTISOURCE_BOUNDS.Forest
import YM.Extra.MULTISOURCE_BOUNDS.Repeated
import YM.Next.EXTRACTION.Basis
import YM.Next.EXTRACTION.Mixture

/-!
# Estimates through all derivatives for the marked overlap logarithm terms

Coefficientwise, prior to any changes of inventory/indicators,
restoring exclusions, or further merging/extraction. Same native markers,
w for each name (can include physical rescalings), repeated tuples. The
positive magnitude is estimated even for an insertion on a root chosen from
the *other* factors of that product. Assert no formal-to-analytic log identity
or branch choice here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Multi.LogTerms
open Function Filter Lattice RG Source Wilson Overlay Marker Labels MeasureTheory Finset Mayer Repeated Germs
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {V α : Type*} {n : Side} {G : Gauge}

def nameSet (t : α → Finset V) (u : Tuple α) := univ.biUnion fun j => t (u.2 j)

def legal (t : α → Finset V) (u : Tuple α) := (↑(univ : Finset (Fin (u.1+1))) : Set (Fin (u.1+1))).PairwiseDisjoint (fun j => t (u.2 j))

def coefficient (X : α → Support n) (u : Tuple α) := ursell (overlap X u.2)

def current (t : α → Finset V) (X : α → Support n) (F : α → Config G n → ℂ) (u : Tuple α) :=
    if legal t u then (↑(coefficient X u / (u.1+1).factorial):ℂ) • (fun U => ∏ j,F (u.2 j) U) else 0

def duty (w : V → ℝ) (t : Finset V) := ∏ i∈t,w i

def book (power order : ℕ) := (exp_absorbs ((power+1)*order) 1 zero_lt_one).choose

/-- Allow the constant, translation price polynomial in B and derivative
order k,P; reserve just two extra exponent units in the overlap price. -/
theorem estimates (P : BudgetPoint) : let C := book P.power P.order
    1 ≤ C ∧
    ∀ (F : α → Config G n → ℂ) (X : α → Support n) (y : α → Site n) (e : α → ℝ)
    (names : α → Finset V) (w : V → ℝ) (a b γ : ℝ), 0 ≤ b → 0 ≤ a → 0 ≤ γ →
    8*((P.B+P.B+1:ℕ):ℝ)^4*γ ≤ 1 → (∀ v,0≤w v) → (∀ i,y i∈ X i ∧ P.Regular (X i) (F i) ∧ P.supBounds (y i) (X i) (F i) (e i)) →
    let f := fun i => duty w (names i)*e i
    Rooted names X P.B (a+2) f b → Ac.Hit X P.B f (a+2) γ →
    ∃ g : Tuple α → ℝ, (∀ i,0 ≤ g i ∧ P.Regular (numbered X i) (current names X F i) ∧
      ∀ p∈numbered X i, P.supBounds p (numbered X i) (current names X F i) (g i)) ∧
      Rooted (nameSet names) (numbered X) P.B a (fun i => duty w (nameSet names i)*g i) (pay P * C * (2*b)) ∧
      Ac.Hit (numbered X) P.B (fun i => duty w (nameSet names i)*g i) a (pay P*C*(2*γ)) := by
  intro C; obtain ⟨hC,h⟩ := (exp_absorbs ((P.power+1)*P.order) 1 zero_lt_one).choose_spec
  change 1 ≤ C at hC
  refine ⟨hC,?_⟩; intro F X y e names w a b γ hb ha hγ hc hw hF f hr ht
  let H (u : Tuple α) := overlap X u.2
  let W (u : Tuple α) := ∑ i,coverNumber P.B (X (u.2 i))
  let k := (P.power+1)*P.order
  let g (u : Tuple α) := if legal names u then |coefficient X u|/(u.1+1).factorial *
    (pay P * (1+(W u:ℝ))^k * ∏ i,e (u.2 i)) else 0
  have hp : 0 ≤ pay P := by unfold pay; positivity
  have hg (u : Tuple α) : 0 ≤ g u := by
    have he := prod_nonneg (fun i (_:i∈univ) => (hF (u.2 i)).2.2.1)
    unfold g; split <;> positivity
  have hU (u : Tuple α) : P.Regular (numbered X u) (fun U => ∏ j, F (u.2 j) U) := smoothProd _ fun i _ => (hF (u.2 i)).2.1
  have he u := Next.Foundations.regular_smul (↑(coefficient X u/(u.1+1).factorial) : ℂ) (hU u)
  refine ⟨g,fun u => ⟨hg u,?_,fun p hh => ?_⟩,?_⟩
  · unfold current; split
    · exact he u
    simpa using Next.Foundations.regular_smul 0 (he u)
  · by_cases hl : legal names u ∧ coefficient X u ≠ 0
    · have hs : Ac.Spark (fun i => X (u.2 i)) univ := ⟨univ_nonempty,fun i _ j _ => (by
        induction (SimpleGraph.reachable_iff_reflTransGen _ _).mp (Mayer.ursell_ne _ hl.2 i j) with
        | refl => exact .refl
        | tail _ hh IH => exact (IH (mem_univ _)).tail ⟨mem_univ _,mem_univ _,hh.2⟩)⟩
      have H := reanchored _ p (fun i _ => (hF _).2.1) (fun i _ => (hF _).2.2) hs (fun i _ => (hF _).1) hh
      simpa only [current,g,if_pos hl.1,occurrences,k,W,Complex.norm_real,Real.norm_eq_abs,abs_div,
        abs_of_nonneg (show 0≤((u.1+1).factorial:ℝ) by positivity),numbered] using
        Next.Foundations.bound_smul (↑(coefficient X u / (u.1+1).factorial):ℂ) H
    obtain hl|hl := not_and_or.mp hl
    · simp only [g,current,if_neg hl]; exact supBounds_zero ..
    replace hl := not_ne_iff.mp hl
    simp only [g,current,hl,abs_zero,zero_div,zero_mul, Complex.ofReal_zero,zero_smul,ite_self]; exact supBounds_zero ..
  let v i := Real.exp (coverNumber P.B (X i))*f i
  have hf i : 0 ≤ f i := mul_nonneg (prod_nonneg fun i _ => hw i) (hF i).2.2.1
  have hv i : 0 ≤ v i := mul_nonneg (Real.exp_pos _).le (hf i)
  let G := fun u => worth v (fun u => |coefficient X u|) u
  have hT : Ac.Hit X P.B v (a+1) γ := by
    intro x; convert ht x using 2; split_ifs
    next => rw [show a+(2:ℝ)=a+1+1 by ring, add_mul (a+1), one_mul,Real.exp_add]; unfold v; ring
    rfl
  have hh u : duty w (nameSet names u)*g u ≤ pay P * C * G u := by
    unfold g; split <;> rename_i hl
    · rw [duty,nameSet,prod_biUnion hl]
      have he := h (W u); rw [one_mul, show (W u:ℝ)=∑ i,(coverNumber P.B (X (u.2 i)):ℝ) from Nat.cast_sum ..,Real.exp_sum] at he
      unfold W; push_cast
      calc
        _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hp)
          (prod_nonneg fun i (_:i∈univ) => (hF (u.2 i)).2.2.1))
          (show 0≤ |coefficient X u|/((u.1+1).factorial:ℝ) by positivity))
          (show 0≤ ∏ i,∏ x∈names (u.2 i),w x from prod_nonneg fun _ _ => prod_nonneg fun x _ => hw x)
        _ = _ := by unfold G worth v f duty C book; simp_rw [prod_mul_distrib]; ring
    have hG : 0 ≤ G u := mul_nonneg (by positivity) (prod_nonneg fun _ _ => hv _)
    rw [mul_zero]; positivity
  have H (p : α→Prop) (b : ℝ) (hb : 0 ≤ b) (he : SumBudget (fun i => if p i then
      Real.exp ((a+2)*coverNumber P.B (X i))*f i else 0) b) : SumBudget (fun u : Tuple α => if ∃ i,p (u.2 i) then
      Real.exp (a*coverNumber P.B (numbered X u))*(duty w (nameSet names u)*g u) else 0) (pay P*C*(2*b)) := by
    have hr (u : Tuple α) := abs_nonneg (coefficient X u)
    have hx := repeated X P.B v (fun u => |coefficient X u|) p b γ a hb hγ hc ha hv (fun u => ⟨hr u, tree_estimate (H u)⟩) hT
      (by convert he using 2; split_ifs <;> simp only [v,
          show a+(2:ℝ)=a+1+1 by ring,add_mul,one_mul,Real.exp_add, mul_assoc])
    refine Budget.mono (Budget.scale hx (mul_nonneg hp (zero_le_one.trans hC))) (fun u => ?_) (fun u => ?_) le_rfl
    · split
      · exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (prod_nonneg fun _ _ => hw _) (hg _))
      exact le_rfl
    split_ifs <;> first | exact (mul_le_mul_of_nonneg_left (hh u) (Real.exp_pos _).le).trans_eq (by unfold G; ring) | simp
  constructor <;> intro x
  · simpa only [nameSet,mem_biUnion,mem_univ,true_and] using! H (x∈names ·) _ hb (by convert! hr x using 2; split_ifs <;> rfl)
  simpa only [numbered,mem_biUnion,mem_univ,true_and,mul_comm (Real.exp _)] using! H (x∈X ·) _ hγ (by simpa only [mul_comm (Real.exp _)] using ht x)

end YM.Extra.Multi.LogTerms
