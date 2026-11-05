import YM.Push.FREE_RESOLVENT.JetWindows

/-!
# Simultaneous Taylor tensor sum envelopes

For FTt interpretation use **star through root** length in torus
max-distance, even when the other endpoint positions coincide. This charges
all the positions (multiplicity & true orientation) and can pay a connected
tree test with it, not requiring finding a minimizer. These estimates are
before trace/cumulant sums; for especially the single-tag term all external
indices are summed with no period factor! Calls can use smaller rates than
these prices.
-/

set_option autoImplicit false
noncomputable section
namespace YM.FreeResolvent
open Matrix TestD Mark  Filter Function Set
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
variable {ι κ τ E G X : Type*} {n : ℕ}

namespace Stars
variable (D : Cost X)

def rays (x : X) (m : Fin n → X) := ∑ i, D.d x (m i)
lemma rays_nn (x : X) (m : Fin n → X) : 0 ≤ rays D x m := Finset.sum_nonneg fun _ _ => D.nonneg ..
lemma rays_visit (x y : X) (m : Fin n → X) : rays D x m ≤ n*D.d x y+rays D y m := calc
  _ ≤ ∑ i, (D.d x y+D.d y (m i)) := Finset.sum_le_sum fun i _ => D.triangle ..
  _ = _ := by simp [rays,Finset.sum_add_distrib]

def costs (x i j : X) (m : Fin n → X) := D.d x i+D.d x j + rays D x m
lemma costs_nn (x i j : X) (m : Fin n → X) : 0 ≤ costs D x i j m := add_nonneg (add_nonneg (D.nonneg ..) (D.nonneg ..)) (rays_nn ..)
lemma pivots (x i j : X) (m : Fin n → X) : costs D x i j m ≤ (n+2:ℕ)*D.d x i + costs D i i j m := by
  unfold costs; rw [D.self,zero_add]; push_cast
  linarith only [D.triangle x i j,rays_visit D x i m]
lemma pays (o : X) (s : ℝ) (p : τ → X) (l : Fin n → τ) :
    (positions D p s).pay (List.ofFn l) o = Real.exp (s*rays D o (p ∘ l)) := by
  have hh (l : List τ) : (positions D p s).pay l o=Real.exp (s*(l.map (fun i => D.d o (p i))).sum) := by
    induction l with
    | nil => simp [pay]
    | cons i l ih => simp only [pay, ih,List.map_cons,List.sum_cons,mul_add,Real.exp_add]; rfl
  rw [hh,List.map_ofFn, List.sum_ofFn]; rfl

variable {D}
variable {a : ι → X} {b : κ → X} {p : τ → X} {γ d M V : ℝ}

-- scalar envelope of tensor gated by W predicate. Use to get stars
-- for any endpoint and costs with interior lookup by charging hit.
structure NearStar [Fintype ι] [Fintype κ] [Fintype τ] (n : ℕ) (D : Cost X) (a : ι → X) (b : κ → X)
    (p : τ → X) (x : X) (W : ι → κ → (Fin n → τ) → Bool) (γ M : ℝ) (F : ι → κ → (Fin n → τ) → ℝ) : Prop where
  limit : ∑ i, ∑ j, ∑ k : Fin n → τ, (if W i j k then Real.exp (γ*costs D x (a i) (b j) (p ∘ k))*|F i j k| else 0) ≤ M

variable [Fintype ι] [Fintype κ] [Fintype τ]
lemma sum_pivot {x : X} {W} {F} (hm : 0 ≤ M) (he : 2*γ ≤ d) (hV : 0 ≤ V)
    (h : ∀ i j k, W i j k=true → Real.exp (d*costs D x (a i) (b j) (p ∘ (k:Fin n → τ)))*|F i j k| ≤ M)
    (hv : D.Volume a γ V) (hw : D.Volume b γ V) (hh : D.Volume p γ V) :
    NearStar n D a b p x W γ ((V*V*V^n)*M) F := by
  classical
  let f := fun i => D.weight (-γ) x (a i)
  let g := fun j => D.weight (-γ) x (b j)
  let t := fun k => D.weight (-γ) x (p k)
  have h1 (i j k) : (if W i j k then Real.exp (γ*costs D x (a i) (b j) (p ∘ k))*|F i j k| else 0) ≤
      ((f i*g j)*∏ l, t (k l))*M := by
    split <;> rename_i H
    · let Q := costs D x (a i) (b j) (p ∘ k)
      have hp : (f i*g j)*∏ l, t (k l) = Real.exp (-γ*Q) := by
        unfold Q costs rays f g t Cost.weight; rw [mul_add, mul_add (-γ), Real.exp_add, Real.exp_add, Finset.mul_sum, Real.exp_sum]; rfl
      rw [hp]
      have hc : γ*Q ≤ -γ*Q+d*Q := by linarith only [mul_le_mul_of_nonneg_right he (costs_nn D x (a i) (b j) (p ∘ k))]
      apply le_trans _ (mul_le_mul_of_nonneg_left (h i j k H) (Real.exp_pos _).le)
      rw [← mul_assoc, ← Real.exp_add]; exact mul_le_mul_of_nonneg_right (Real.exp_monotone hc) (abs_nonneg _)
    exact mul_nonneg (mul_nonneg (mul_nonneg (D.weight_nn ..) (D.weight_nn ..)) (Finset.prod_nonneg fun l _ => D.weight_nn ..)) hm
  constructor; apply le_trans (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => h1 i j k)
  simp_rw [← Finset.sum_mul, ← Finset.mul_sum]; rw [← Fintype.prod_sum (fun _ : Fin n => t)]
  apply mul_le_mul_of_nonneg_right _ hm
  simp only [Finset.prod_const, Finset.card_univ,Fintype.card_fin]
  have he : 0 ≤ ∑ i, f i := Finset.sum_nonneg fun _ _ => D.weight_nn ..
  have ht : 0 ≤ ∑ i, t i := Finset.sum_nonneg fun _ _ => D.weight_nn ..
  simp_rw [← Finset.sum_mul, ← Finset.mul_sum, ← Finset.sum_mul]
  exact mul_le_mul (mul_le_mul (hv.bound x) (hw.bound x) (Finset.sum_nonneg fun i _ => D.weight_nn ..) hV)
    (pow_le_pow_left₀ ht (hh.bound x) _) (pow_nonneg ht _) (mul_self_nonneg _)

omit [Fintype ι] [Fintype κ] [Fintype τ] in
lemma visit_support {x : X} {m : Fin n → τ} {i : ι} {j : κ}
    (h : x=a i ∨ x=b j ∨ ∃ k, x=p (m k)) :
    D.d x (a i) ≤ costs D (a i) (a i) (b j) (p ∘ m) := by
  rcases h with (rfl|rfl|⟨k,rfl⟩)
  · rw [D.self]; exact costs_nn ..
  · unfold costs; rw [D.comm (b j),D.self,zero_add]; exact le_add_of_nonneg_right (rays_nn ..)
  have he : D.d (a i) (p (m k)) ≤ rays D (a i) (p ∘ m) := Finset.single_le_sum
    (f:=fun l => D.d (a i) (p (m l))) (fun l _ => D.nonneg ..) (Finset.mem_univ k)
  rw [D.comm _ (a i)]; exact he.trans (le_add_of_nonneg_left (add_nonneg (D.nonneg ..) (D.nonneg ..)))

-- weaker than anchor-index testing? actually aggregate also when any coincident
-- anchors at same positions, costs valid for all.
def crowd (n : ℕ) (M V : ℝ) := V*V*V^n*M

lemma sums_no_mark {x : X} {W} {F} (hg : 0 ≤ γ) (hm : 0 ≤ M) (he : 2*(n+3:ℕ)*γ ≤ d) (hV : 0 ≤ V)
    (h : ∀ i j k, Real.exp (d*costs D (a i) (a i) (b j) (p ∘ (k:Fin n → τ)))*|F i j k| ≤ M)
    (hW : ∀ i j k, W i j k=true → x=a i ∨ x=b j ∨ ∃ m : Fin n, x=p (k m))
    (hv : D.Volume a γ V) (hw : D.Volume b γ V) (hh : D.Volume p γ V) :
    NearStar n D a b p x W γ (crowd n M V) F := by
  apply sum_pivot hm (d:=2*γ) le_rfl hV _ hv hw hh
  intro i j k hK
  have hL : costs D x (a i) (b j) (p ∘ k) ≤ (n+3:ℕ)*costs D (a i) (a i) (b j) (p ∘ k) :=
    le_trans (pivots ..) ((add_le_add_left (mul_le_mul_of_nonneg_left
      (visit_support (hW i j k hK)) (by positivity)) _).trans_eq (by push_cast; ring))
  apply le_trans _ (h i j k)
  apply mul_le_mul_of_nonneg_right (Real.exp_monotone _) (abs_nonneg _)
  refine (mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ 2*γ)).trans ?_
  rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (by rwa [mul_right_comm (2:ℝ) γ]) (costs_nn ..)

lemma sums_tagged {x : X} {F} (hg : 0 ≤ γ) (hm : 0 ≤ M) (he : 2*(n+3:ℕ)*γ ≤ d) (hV : 0 ≤ V)
    (h : ∀ i j k, (D.weight d (a i) x * Real.exp (d*costs D (a i) (a i) (b j) (p ∘ (k:Fin n → τ)))) * |F i j k| ≤ M)
    (hv : D.Volume a γ V) (hw : D.Volume b γ V) (hh : D.Volume p γ V) :
    NearStar n D a b p x (fun _ _ _ => true) γ (crowd n M V) F := by
  apply sum_pivot hm (d:=2*γ) le_rfl hV _ hv hw hh
  intro i j k hK
  apply le_trans _ (h i j k); rw [Cost.weight_symm, Cost.weight, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_right (Real.exp_monotone _) (abs_nonneg _)
  apply le_trans (mul_le_mul_of_nonneg_left (pivots ..) (mul_nonneg (by norm_num) hg))
  rw [mul_add, ← mul_assoc]; refine add_le_add ?_ ?_
  · apply mul_le_mul_of_nonneg_right _ (D.nonneg ..); rw [mul_right_comm]; apply le_trans _ he; gcongr; simp
  apply mul_le_mul_of_nonneg_right _ (costs_nn ..); apply le_trans _ he; push_cast
  nlinarith [show (0:ℝ)≤ (n:ℝ) by positivity]

variable [NormedAddCommGroup E] [NormedSpace ℝ E]
omit [Fintype τ] in
lemma list_result [NormedAddCommGroup G] [NormedSpace ℝ G]
    (v : τ → E) (z : Fin n → τ) (F : E → G) (x) :
    jet v F (List.ofFn z) x = iteratedFDeriv ℝ n F x (v ∘ z) := by
  have he : ∀ (n m : ℕ) (u : Fin n → E) (w : Fin m → E) (h : n=m),
      (∀ i, u i=w (Fin.cast h i)) → iteratedFDeriv ℝ n F x u = iteratedFDeriv ℝ m F x w := by rintro n _ u w rfl h; rw [funext h]; rfl
  exact he _ _ (v ∘ _) (v ∘ _) List.length_ofFn (fun i => by simp; rfl)




end Stars
end YM.FreeResolvent
