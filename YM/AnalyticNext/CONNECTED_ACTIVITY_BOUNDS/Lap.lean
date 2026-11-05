import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Birthday

/-!
# Label multiplicity in determinant and density ratios I

Address path algebra. A path does not forget (e.g. quota-share on)
repeated visits. Group colors in the value of ONE label; this can be
used also with tolls after gauge change. Σ of these grouped paths yields
the ordinary real matrix expression. Proof using only counting: no spectral
genericity, no nonempty global index hypothesis. `G.ColorIndex` will be
finite but the sizes for `Y` links could diverge with period.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Laps
open Matrix Finset MeasureTheory
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {Y n X : Type*} [Fintype Y] [DecidableEq Y] [Fintype n] [DecidableEq n]

abbrev Tile (Y n : Type*) := Matrix (Y × n) (Y × n) ℝ

def sectionOf (A : Tile Y n) (i j : Y) : Matrix n n ℝ := Matrix.of fun a b => A (i,a) (j,b)

omit [DecidableEq Y] [DecidableEq n] in
lemma section_mul (A B : Tile Y n) (i j : Y) :
    sectionOf (A*B) i j = ∑ k, sectionOf A i k * sectionOf B k j := by
  ext a b; rw [Matrix.sum_apply]
  change (A*B) (i,a) (j,b)=_
  rw [Matrix.mul_apply,Fintype.sum_prod_type]; rfl

omit [DecidableEq Y] [DecidableEq n] in
lemma section_trace (A : Tile Y n) : trace A = ∑ i, trace (sectionOf A i i) := by
  unfold Matrix.trace; rw [Fintype.sum_prod_type]; rfl

/-- Chain after i, terminal jump to j via C. -/
def routeF (A C : Tile Y n) : (k : ℕ) → Y → (Fin k → Y) → Y → Matrix n n ℝ
  | 0,i,_,j => sectionOf C i j
  | k+1,i,s,j => sectionOf A i (s 0) * routeF A C k (s 0) (Fin.tail s) j





/-- The ENDPOINT Z data also uses physical colors. -/
def amount (A : Matrix n n ℝ) (z : Y × n → ℝ) (i j : Y) :=
    dotProduct (fun k => z (i,k)) (A *ᵥ fun k => z (j,k))

omit [DecidableEq Y] [DecidableEq n] in
lemma sections (A : Tile Y n) (z : Y × n → ℝ) :
    dotProduct z (A *ᵥ z) = ∑ i, ∑ j, amount (sectionOf A i j) z i j := by
  unfold dotProduct; rw [Fintype.sum_prod_type]; refine Finset.sum_congr rfl fun i _ => ?_
  unfold amount dotProduct; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun k _ => ?_
  unfold Matrix.mulVec dotProduct; rw [Fintype.sum_prod_type,Finset.mul_sum]; rfl

omit [Fintype Y] [DecidableEq Y] [DecidableEq n] in
lemma amount_finset (D : X → Matrix n n ℝ) (s : Finset X) (z : Y × n → ℝ) (i j : Y) :
    amount (∑ p∈s,D p) z i j = ∑ p∈s, amount (D p) z i j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [sum_empty,amount, Matrix.zero_mulVec,dotProduct_zero]
  | insert b s hb ih =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb,amount, Matrix.add_mulVec,dotProduct_add]; exact congr_arg _ ih



section bounds
variable (z : Y × n → ℝ)

-- endpoint bills

def readers (i j : Y) : Finset (Y × n) := {i,j} ×ˢ univ

omit [Fintype Y] [DecidableEq n] in
lemma readers_bound (i j : Y) : (readers (n:=n) i j).card ≤ 2 * Fintype.card n := by
  unfold readers; rw [Finset.card_product, Finset.card_univ]
  refine Nat.mul_le_mul_right _ ?_
  by_cases H : i=j <;> simp [H]

omit [Fintype Y] [DecidableEq n] in
lemma spends (i j : Y) (p q : n) :
    |z (i,p)| * |z (j,q)| ≤ (∑ d ∈ readers i j, z d ^ 2) := by
  have h a m (hm : a∈readers (n:=n) i j) (he : a=m) : z m ^ 2 ≤ ∑ k ∈ readers i j,z k ^ 2 := by
    subst m; exact Finset.single_le_sum (fun d (_:d∈readers i j) => sq_nonneg (z d)) hm
  have hx : _ ≤ _ := h (i,p) _ (by simp [readers]) rfl
  have hz : _ ≤ _ := h (j,q) _ (by simp [readers]) rfl
  nlinarith only [hx,hz,sq_abs (z (i,p)),sq_abs (z (j,q)),sq_nonneg (|z (i,p)| - |z (j,q)|)]

omit [Fintype Y] [DecidableEq n] in
lemma amount_bound (A : Matrix n n ℝ) (i j : Y) (C : ℝ) (hC : 0 ≤ C) (he : ∀ a b, |A a b| ≤ C) :
    |amount A z i j| ≤ ((Fintype.card n:ℝ)^2 * C)*(∑ d ∈ readers i j,z d ^ 2) := by
  let V := ∑ d∈ readers i j,z d ^ 2
  unfold amount Matrix.mulVec; simp only [dotProduct, Finset.mul_sum]
  calc
    _ ≤ ∑ a : n, ∑ b : n, |z (i,a)*(A a b*z (j,b))| := (Finset.abs_sum_le_sum_abs ..).trans
      (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs ..)
    _ ≤ ∑ _a : n, ∑ _b : n, C*V := by
      refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
      simp only [abs_mul]; rw [mul_left_comm]; exact mul_le_mul (he a b) (spends z i j a b)
        (by positivity) hC
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, V, ← Finset.mul_sum]; ring

omit [DecidableEq Y] [Fintype Y] [DecidableEq n] in
lemma route_entry (A C : Tile Y n) (k : ℕ) (i : Y) (s : Fin k→ Y) (j : Y) {B D : ℝ}
    (hA : ∀ i j, |A i j| ≤ B) (hC : ∀ i j, |C i j| ≤ D)
    (hb : 0≤ B) (a b : n) : |routeF A C k i s j a b| ≤ (Fintype.card n*B)^k * D := by
  induction k generalizing i a with
  | zero => simpa [routeF,sectionOf] using hC (i,a) (j,b)
  | succ k ih =>
    rw [routeF,Matrix.mul_apply]
    apply (Finset.abs_sum_le_sum_abs ..).trans
    calc
      _ ≤ ∑ _m : n,B*((Fintype.card n*B)^k*D) := by
        refine Finset.sum_le_sum fun m _ => ?_
        rw [abs_mul]; exact mul_le_mul (hA (i,a) (s 0,m)) (ih ..) (abs_nonneg _) hb
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,pow_succ]; ring

omit [DecidableEq Y] [Fintype Y] [DecidableEq n] in
lemma route_cap (A C : Tile Y n) (k : ℕ) (i : Y) (s : Fin k → Y) {B D : ℝ}
    (hA : ∀ i j, |A i j| ≤ B) (hC : ∀ i j, |C i j| ≤ D) (hb : 0≤ B) :
    |trace (routeF A C k i s i)| ≤ Fintype.card n * ((Fintype.card n*B)^k * D) := by
  unfold Matrix.trace
  apply (Finset.abs_sum_le_sum_abs ..).trans
  calc
    _ ≤ ∑ _i : n, (Fintype.card n*B)^k * D := Finset.sum_le_sum fun j _ => route_entry A C k i s i hA hC hb j j
    _ = _ := by simp
end bounds

section cont
variable {v : X → Tile Y n} {u : X → Tile Y n} [TopologicalSpace X] {s : Set X}

omit [Fintype n] [DecidableEq n] [Fintype Y] [DecidableEq Y] in
lemma continuous_section (i j : Y) : Continuous fun x : Tile Y n => sectionOf x i j := by
  refine continuous_matrix fun a b => ?_
  unfold sectionOf; fun_prop

omit [DecidableEq n] [Fintype Y] [DecidableEq Y] in
lemma route_continuous (h : ContinuousOn v s) (he : ContinuousOn u s)
    {k : ℕ} (i j : Y) (l : Fin k → Y) : ContinuousOn (fun x => routeF (v x) (u x) k i l j) s := by
  induction k generalizing i with
  | zero => simp_rw [routeF]; exact (continuous_section ..).comp_continuousOn he
  | succ k ih => simp_rw [routeF]; exact ((continuous_section ..).comp_continuousOn h).mul (ih _ _)
end cont
end YM.AnalyticNext.ConnectedActivity.Laps
