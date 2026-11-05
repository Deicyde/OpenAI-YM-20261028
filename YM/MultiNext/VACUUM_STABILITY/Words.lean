import YM.MultiNext.VACUUM_STABILITY.Sums

set_option warningAsError false

/-!
# A word ledger for hard-core logarithms

Repeats are actual words before summation. Concatenate for powers and power series, paying
absolute at EVERY evaluation needed, including the edge of the request domain. No interpretation
of a jet as a density. No termwise differentiation of a conditionally summable series.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Multi.Vacuum
open RG Lattice Wilson Filter Finset Function MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {I : Type}

structure Syllable (I : Type) where
  letters : List I
  amp : ℂ

namespace Syllable
variable (w : Syllable I)

def eval (u : I → ℂ) := w.amp * (w.letters.map u).prod

def weight (f : I → ℝ) := ‖w.amp‖ * (w.letters.map f).prod

lemma weight_nonneg {f : I → ℝ} (hf : ∀ i, 0 ≤ f i) : 0 ≤ w.weight f := by
  obtain ⟨l,x⟩ := w; induction l with
  | nil => exact mul_nonneg (norm_nonneg _) zero_le_one
  | cons a l ih =>
    rw [show (Syllable.mk (a::l) x).weight f = f a * (Syllable.mk l x).weight f from mul_left_comm ..]
    exact mul_nonneg (hf a) ih

lemma eval_bound {u : I → ℂ} {f : I → ℝ} (hu : ∀ i, ‖u i‖ ≤ f i) : ‖w.eval u‖ ≤ w.weight f := by
  obtain ⟨l,x⟩ := w; induction l with
  | nil => simp [eval,weight]
  | cons a l ih =>
    rw [show (Syllable.mk (a::l) x).eval u = u a * (Syllable.mk l x).eval u from mul_left_comm .., norm_mul,
      show (Syllable.mk _ _).weight f = f a * (Syllable.mk l x).weight f from mul_left_comm ..]
    exact mul_le_mul (hu a) ih (norm_nonneg _) ((norm_nonneg _).trans (hu a))

def join (s : Syllable I) := Syllable.mk (w.letters ++ s.letters) (w.amp*s.amp)

def scale (z : ℂ) := { w with amp := z*w.amp }

lemma join_eval (s : Syllable I) (u : I → ℂ) : (w.join s).eval u = w.eval u * s.eval u := by
  simp only [join,eval,List.map_append,List.prod_append]; ring

lemma join_weight (s : Syllable I) (f : I → ℝ) : (w.join s).weight f = w.weight f * s.weight f := by
  simp only [join,weight,List.map_append,List.prod_append,norm_mul]; ring

lemma scale_eval (z : ℂ) (u : I → ℂ) : (w.scale z).eval u = z*w.eval u := mul_assoc ..

lemma scale_weight (z : ℂ) (f : I → ℝ) : (w.scale z).weight f = ‖z‖*w.weight f := by
  rw [scale,weight,norm_mul]; exact mul_assoc ..
end Syllable

/-- Countably many labelled words. One output tape for any evaluation. -/
structure Text (I : Type) where
  address : Type
  [counts : Countable address]
  line : address → Syllable I

instance (T : Text I) : Countable T.address := T.counts

namespace Text
variable (T : Text I)

def lineSum (u : I → ℂ) := ∑' j, (T.line j).eval u

def Fund (f : I → ℝ) (g : ℝ) : Prop := SumBudget (fun j => (T.line j).weight f) g

lemma sum_bound {u : I → ℂ} {f : I → ℝ} (hu : ∀ i, ‖u i‖ ≤ f i) {c : ℝ} (h : T.Fund f c) :
    SumBudget (fun j => ‖(T.line j).eval u‖) c := Absolute.compare h (fun _ => norm_nonneg _)
        fun i => (T.line i).eval_bound hu

lemma evaluated {u : I → ℂ} {f : I → ℝ} (hu : ∀ i, ‖u i‖ ≤ f i) {c : ℝ} (h : T.Fund f c) :
    ‖T.lineSum u‖ ≤ c := (norm_tsum_le_tsum_norm (T.sum_bound hu h).2.1).trans (T.sum_bound hu h).2.2

def blank : Text I := { address := Empty, line := Empty.elim }

def atom (i : I) : Text I := { address := Unit, line := fun _ => ⟨[i],1⟩ }

lemma atom_fund (i : I) {f : I → ℝ} (hf : ∀ i, 0 ≤ f i) : (atom i).Fund f (f i) := by
  unfold Fund; simp only [atom,Syllable.weight,norm_one,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul]
  exact Absolute.singleton _ (hf i)

lemma atom_sum (i : I) (u : I → ℂ) : (atom i).lineSum u = u i := by simp [atom,lineSum,Syllable.eval]







def bind {J : Type} [Countable J] (T : J → Text I) : Text I :=
    { address := Σ i, (T i).address, line := fun j => (T j.1).line j.2 }

lemma bind_fund {J : Type} [Countable J] (T : J → Text I) {f : I → ℝ} {g : J → ℝ} {p : ℝ}
    (hP : SumBudget g p) (h : ∀ i, (T i).Fund f (g i)) : (bind T).Fund f p := Absolute.bundles hP h

lemma bind_sum {J : Type} [Countable J] (T : J → Text I) {f : I → ℝ} {c : ℝ}
    (h : (bind T).Fund f c) {u : I → ℂ} (hu : ∀ i, ‖u i‖ ≤ f i) :
    (bind T).lineSum u = ∑' i, (T i).lineSum u := ((bind T).sum_bound hu h).2.1.of_norm.tsum_sigma

def pair (V : Text I) : Text I :=
    { address := T.address × V.address, line := fun j => (T.line j.1).join (V.line j.2) }

lemma pair_fund (V : Text I) {f : I → ℝ} {c d : ℝ} (h : T.Fund f c) (hh : V.Fund f d) :
    (T.pair V).Fund f (c*d) := by simpa only [Fund,pair,Syllable.join_weight] using Absolute.cross h hh

lemma pair_sum (V : Text I) {f : I → ℝ} {c d : ℝ} (h : T.Fund f c) (hh : V.Fund f d)
    {u : I → ℂ} (hu : ∀ i, ‖u i‖ ≤ f i) : (T.pair V).lineSum u = T.lineSum u * V.lineSum u := by
  simp only [lineSum,pair,Syllable.join_eval]
  exact (tsum_mul_tsum_of_summable_norm (T.sum_bound hu h).2.1 (V.sum_bound hu hh).2.1).symm

def scale (z : ℂ) : Text I := { address := T.address, line := fun j => (T.line j).scale z }

lemma scale_fund (z : ℂ) {f : I → ℝ} {c : ℝ} (h : T.Fund f c) : (T.scale z).Fund f (‖z‖*c) := by
  simpa only [Fund,scale,Syllable.scale_weight] using permit_mul h (norm_nonneg z)

lemma scale_sum (z : ℂ) (u : I → ℂ) : (T.scale z).lineSum u = z*T.lineSum u := by
  simp_rw [lineSum,scale,Syllable.scale_eval,tsum_mul_left]

def copies (T : Text I) : ℕ → Text I
  | 0 => { address := Unit, line := fun _ => ⟨[],1⟩ }
  | k+1 => (T.copies k).pair T

lemma copies_fund (k : ℕ) {f : I → ℝ} {c : ℝ} (h : T.Fund f c) : (T.copies k).Fund f (c^k) := by
  induction k with
  | zero => simpa only [Fund,copies,Syllable.weight,List.map_nil,List.prod_nil,norm_one,mul_one,pow_zero] using
      Absolute.singleton 1 zero_le_one
  | succ k hi => rw [copies,pow_succ]; exact pair_fund _ _ hi h

lemma copies_sum (k : ℕ) {f : I → ℝ} {c : ℝ} (h : T.Fund f c) {u : I → ℂ} (hu : ∀ i, ‖u i‖ ≤ f i) :
    (T.copies k).lineSum u = (T.lineSum u)^k := by
  induction k with
  | zero => simp [copies,lineSum,Syllable.eval]
  | succ k ih => rw [copies,pow_succ,pair_sum _ _ (T.copies_fund _ h) h hu,ih]

/-- Output word list for exponentiation; labels include arbitrary repeats before summing. -/

def expanding : Text I := bind fun n : ℕ => (T.copies n).scale ((n.factorial:ℂ)⁻¹)

lemma expanding_fund {f : I → ℝ} {c : ℝ} (h : T.Fund f c) :
    T.expanding.Fund f (Real.exp c) := by
  refine bind_fund _ (Absolute.rexp _ (Absolute.bound_nonneg h)) fun i => ?_
  simpa only [norm_inv,Complex.norm_natCast] using (T.copies i).scale_fund ((i.factorial:ℂ)⁻¹) (T.copies_fund i h)

lemma expanding_sum {f : I → ℝ} {c : ℝ} (h : T.Fund f c) {u : I → ℂ} (hu : ∀ i, ‖u i‖ ≤ f i) :
    T.expanding.lineSum u = Complex.exp (T.lineSum u) := by
  unfold expanding; rw [bind_sum _ (T.expanding_fund h) hu]; simp_rw [scale_sum,copies_sum T _ h hu]
  exact (Absolute.cexp _).tsum_eq

private def price (n : ℕ) := (-1:ℂ)^(n+2)/(↑(n+1:ℕ):ℂ)

private lemma price_le (n : ℕ) : ‖price n‖ ≤ 1 := by
  unfold price; rw [norm_div,norm_pow,norm_neg,norm_one,one_pow,Complex.norm_natCast,div_le_one₀] <;>
    exact_mod_cast (by omega)

/-- log(1+.). Taylor powers *with repetitions*. Small absolute input. -/

def pressed : Text I := bind fun n : ℕ => (T.copies (n+1)).scale (price n)

lemma press_fund {f : I → ℝ} {c : ℝ} (h : T.Fund f c) (he : c ≤ 1/2) :
    T.pressed.Fund f (2*c) := by
  have hh := Absolute.bound_nonneg h
  refine bind_fund _ (Absolute.geometric hh he) fun i => ?_
  exact Absolute.loosen ((T.copies _).scale_fund (price i) (T.copies_fund _ h))
    (mul_le_of_le_one_left (pow_nonneg hh _) (price_le _))

lemma press_sum {f : I → ℝ} {c : ℝ} (h : T.Fund f c) (he : c ≤ 1/2) {u : I → ℂ} (hu : ∀ i, ‖u i‖ ≤ f i) :
    Complex.exp (T.pressed.lineSum u) = 1+T.lineSum u := by
  have hx : ‖T.lineSum u‖ < 1 := lt_of_le_of_lt ((T.evaluated hu h).trans he) (by norm_num)
  unfold pressed; rw [bind_sum _ (T.press_fund h he) hu]; simp_rw [scale_sum,copies_sum T _ h hu]
  unfold price; rw [(Absolute.clog hx).tsum_eq]; apply Complex.exp_log; intro hn
  have hh : T.lineSum u = -1 := eq_neg_of_add_eq_zero_right hn
  rw [hh,norm_neg,norm_one] at hx; exact lt_irrefl _ hx
end Text

end YM.Multi.Vacuum
