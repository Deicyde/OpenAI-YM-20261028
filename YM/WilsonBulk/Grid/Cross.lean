import YM.Pert.Bulk.Keys
import YM.WilsonBulk.Grid.Dual
import YM.Work.F08.Mixed

/-!
# Cross composition with blind rows

When projecting away a relevant or marginal coefficient, cancellation of discrete moments at rank
*r* lets us retain an exponential-width budget and gain powers of L. Needed EVEN as stages change,
so allow different widths at the two ends. Width paid relative to the ROOT.

Pre-length estimate; on the lengthy row evaluation can request at any positive widths with just
the explicit compatibility below. No constant from integrating an interacting kernel and no real
volume in any contraction bound. Half old coefficient width is spent in absorbing polynomial
of ANY lifted old distance. Intermediate-width requests and sufficient `J` must be taken on the
context's fixed demand list first. Counts types once, not intermediate period cardinalities.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
open Lattice Laurent Filter Function Bloch
open Push.AbsoluteSums RG Finset Work.F08 Precision
open MultiNext.SignedSource.Newt MultiNext.SignedSource
open Pert.Bulk
open scoped Topology BigOperators Classical

variable {L : Side} {α β γ : Type}

lemma small_carry (x : Site L) (a : Cover) : span (carry x a) ≤ 8 + span a / L.val := by
  have hL : (0:ℝ)< L.val := by positivity
  have hp := (div_le_iff₀ hL).1 (length_lift L x)
  have hq := (div_le_iff₀ hL).1 (length_lift L (arrives x a))
  have hz : L.val * span (carry x a) ≤ (span (lift x) + span a) + span (lift (arrives x a)) := calc
    _ = span (L.val • carry x a) := (length_nsmul (carry x a) _).symm
    _ = span (lift x+a+ -lift (arrives x a)) := by rw [carry_spec x a]; congr 1; abel
    _ ≤ _ := (span_add _ _).trans (add_le_add (span_add _ _) (span_neg _).le)
  suffices span (carry x a) ≤ ((8:ℝ)*L.val+span a)/L.val by
    rwa [add_div, mul_div_cancel_right₀ (8:ℝ) hL.ne'] at this
  refine (le_div_iff₀ hL).2 ?_
  change span _ ≤ _ at hp hq
  nlinarith only [hp,hq,hz]

lemma jump_rent_spec (x : Site L) (a : Cover) : Stationary.rent L (lift x+a) = carry x a :=
  (@Stationary.rent_raw L (carry x a) (lift x+a) (arrives x a) (carry_spec x a)).2

lemma read_offset (T : Cross L α β) (x : Site L) (a y : Cover) (i j) :
    install T (lift x+a,i) (y,j) = T (arrives x a,i) j (y-carry x a) := by
  simp only [install, jump_rent_spec, arrives]

section testing
variable (r : Site L) (T : Cross L α β) (i : α) (j : β) (s : Finset Cover) (g : Cover → ℝ)
def priceTest (a : Cover) := ∑ y∈s, install T (lift r + a,i) (y,j) * g y
lemma test_step (h : Odd L.val) (b : Axis) :
    Newt.jump (priceTest r T i j s g) b = priceTest r (forwardC L T b) i j s g := by
  funext x; dsimp only [Newt.jump, priceTest]
  rw [←sum_sub_distrib]; simp_rw [← (install_step h b T), foot, sub_mul, ← add_assoc]

lemma advance_singleton (l : List Axis) (b : Axis) :
    advanceC L T (l ++ [b]) = advanceC L (forwardC L T b) l := by induction l with
  | nil => rfl
  | cons x l H => rw [List.cons_append]; simp only [advanceC]; rw [H]

lemma test_advance (h : Odd L.val) (l : List Axis) :
    Newt.iterate (priceTest r T i j s g) l = priceTest r (advanceC L T l.reverse) i j s g := by
  induction l generalizing T with
  | nil => rfl
  | cons b l ih => rw [Newt.iterate,test_step _ _ _ _ _ _ h, ih, List.reverse_cons,advance_singleton]

variable {r i j T s g} {A σ : ℝ}
lemma crest (hs : 0 ≤ σ) (hg : ∀ z∈s, ‖g z‖ ≤ Real.exp (σ*span z)) (y : Cover) (hy : y∈s)
    (v : Cover) :
    ‖g y‖ ≤ Real.exp (σ*(8 + span v/L.val))*Real.exp (σ*span (y-carry r v)) := by
  rw [← Real.exp_add, ← mul_add]
  apply (hg _ hy).trans; apply Real.exp_monotone; apply mul_le_mul_of_nonneg_left _ hs
  calc _ = span (carry r v + (y-carry r v)) := by rw [add_sub_cancel]
       _ ≤ _ := (span_add _ _).trans (add_le_add_left (small_carry ..) _)

lemma cheap (hs : 0 ≤ σ) (hg : ∀ z∈s, ‖g z‖ ≤ Real.exp (σ*span z))
    (h : T.strip σ A) (v : Cover) :
    ‖priceTest r T i j s g v‖ ≤ Real.exp (σ*(8 + span v/L.val)) * A := by
  unfold priceTest; apply (norm_sum_le ..).trans
  let f (x) := x-carry r v; have hf : Injective f := fun _ _ h => sub_left_inj.mp h
  let k := Real.exp (σ*(8+span v / L.val))
  let p (x : Cover) := k * (Real.exp (σ*span (f x))*‖T (arrives r v,i) j (f x)‖)
  have he y (hy:y∈s) : ‖install T (lift r + v,i) (y,j) * g y‖ ≤ p y := by
    rw [read_offset,norm_mul]; exact (mul_le_mul_of_nonneg_left (crest hs hg _ hy v) (norm_nonneg _)).trans_eq (by unfold p f k; ring)
  exact (sum_le_sum he).trans (budget_sum (budget_scale (Real.exp_pos _).le
      (show SumBudget (fun x => Real.exp (σ*span (f x))*‖T (arrives r v,i) j (f x)‖) A from budget_pull f hf (h (arrives r v,i) j))) s)

lemma remainder_core (hL : Odd L.val) {d : ℕ}
    (hs : 0 ≤ σ) (hA : 0≤ A) (hg : ∀ z∈s, ‖g z‖ ≤ Real.exp (σ*span z))
    (h : ∀ l : List Axis, l.length = d → (advanceC L T l).strip σ A) (v : Cover) :
    ‖Newt.tail d (priceTest r T i j s g) v‖ ≤
      (Real.exp (σ*(8 + span v/L.val)) * A) * (1+span v)^d := by
  refine Newt.localized d (by positivity) (span v) (fun l hl x hx => ?_) v le_rfl
  rw [test_advance _ _ _ _ _ _ hL l]
  exact (cheap hs hg (h _ (by simpa using hl)) x).trans (by gcongr)

-- use with both widths chosen before making L sufficiently large
def outlay (θ σ : ℝ) (d : ℕ) := momentWeight (θ/2) d * Real.exp (8*σ)
lemma outlay_nonneg (θ σ : ℝ) {d : ℕ} (h : 0 ≤ θ) : 0 ≤ outlay θ σ d :=
  mul_nonneg (momentWeight_nonneg (by positivity) d) (Real.exp_pos _).le
lemma test_remainder {θ : ℝ} (ht : 0 < θ) (hL : Odd L.val) {d : ℕ}
    (hs : 0 ≤ σ) (hA : 0 ≤ A) (hc : σ / L.val ≤ θ/2)
    (hg : ∀ z∈s, ‖g z‖ ≤ Real.exp (σ*span z))
    (h : ∀ l : List Axis, l.length = d → (advanceC L T l).strip σ A) (v : Cover) :
    ‖Newt.tail d (priceTest r T i j s g) v‖ ≤ outlay θ σ d * A * Real.exp (θ*span v) := by
  refine (remainder_core hL hs hA hg h v).trans ?_
  have he : σ * (8+span v / L.val) ≤ 8*σ + θ/2 * span v := by
    calc _ = 8*σ + (σ/L.val)*span v := by ring
         _ ≤ _ := by gcongr
  have hh := momentWeight_nonneg (by linarith : 0≤ θ/2) d
  have hP := test_budget (d:=d) v (by positivity : 0< θ/2)
  refine (mul_le_mul (mul_le_mul_of_nonneg_right (Real.exp_monotone he) hA)
    hP (by positivity) (by positivity)).trans_eq ?_
  rw [Real.exp_add, show θ*span v=θ/2 *span v + θ/2*span v by ring, Real.exp_add]; unfold outlay momentWeight; ring

end testing
end YM.WilsonBulk
