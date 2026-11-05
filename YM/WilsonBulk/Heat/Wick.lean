import YM.WilsonBulk.Heat.Cooking

/-!
# Full Wick convention at flat

Define Gaussian on all `Formula`; `timeRead` gives the polynomial heat/Wick
solution for arbitrary covariance, not projected IR kernel, with optional
wrap lines. `wick` means translation-preserving (no `X` mean subtracted);
eval at a mean uses that formula directly. No division by orbit volumes in
the normalized expectation. Real-algebra derivation supplies IBP rules.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet
open scoped Topology Classical ENNReal BigOperators
open Function Filter Finset
open MvPolynomial (X C pderiv)
variable {α : Type} [Fintype α] (G : Page α 2) {n : ℕ}

-- nilpotence certificate finite polynomial degree at fixed input
abbrev breadth (x : α→₀ℕ) := x.sum fun _ n=> n
omit [Fintype α] in
lemma successor_breadth (i : α) (x : α→₀ℕ) : breadth (x+ Finsupp.single i 1) = breadth x+1 := by simp [breadth,Finsupp.sum_add_index']
omit [Fintype α] in
lemma decreases (f : Formula α) (i : α) : (pderiv i f).totalDegree ≤ f.totalDegree-1 := by
  apply Finset.sup_le; intro x hx
  have h : x+ Finsupp.single i 1 ∈ f.support := by
    rw [MvPolynomial.mem_support_iff] at hx ⊢; intro he; exact hx (by rw [MvPolynomial.coeff_pderiv,he,zero_mul])
  have ht : breadth x+1≤ f.totalDegree := (successor_breadth i x).ge.trans (MvPolynomial.le_totalDegree h)
  change breadth x ≤ _; omega
omit [Fintype α] in
lemma sum_cap {ι : Type} (p : ι→ Formula α) {s : Finset ι} (h : ∀ i∈s,(p i).totalDegree ≤ n) : (∑ i∈s,p i).totalDegree ≤ n := by
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih => rw [sum_insert hi]; exact (MvPolynomial.totalDegree_add ..).trans (max_le (h i (mem_insert_self ..)) (ih fun j hj=> h j (mem_insert_of_mem hj)))
lemma lap_decreases (f : Formula α) : (laplace G f).totalDegree ≤ f.totalDegree-1 := by
  rw [laplace_eval]; refine sum_cap _ fun x _=>sum_cap _ fun y _=>?_
  exact (MvPolynomial.totalDegree_smul_le _ _).trans ((decreases _ y).trans ((Nat.sub_le ..).trans (decreases f x)))
lemma lap_flat {f : Formula α} (h : f.totalDegree=0) : laplace G f=0 := by rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h]; simp [laplace_eval]
lemma lap_finite {f : Formula α} (h : f.totalDegree < n) : ((laplace G)^n) f=0 := by
  induction n generalizing f with
  | zero => omega
  | succ n ih =>
     rw [pow_succ]; change ((laplace G)^n) ((laplace G) f)=_
     by_cases hz : f.totalDegree=0; · rw [lap_flat _ hz,map_zero]
     exact ih (by have he:= lap_decreases G f; omega)

-- Multiplier action requires endomorphism power syntax
abbrev ray (n : ℕ) (f : Formula α) := ((laplace G)^n) f
abbrev rayc (n : ℕ) (f : Formula α) := ((n.factorial : ℝ)⁻¹) • ray G n f
def timeRead (f : Formula α) : KTime α := ∑ n∈range (f.totalDegree+1), Polynomial.monomial n (rayc G n f)
lemma rayc_eq (f : Formula α) (n : ℕ) : (timeRead G f).coeff n=rayc G n f := by
  unfold timeRead; simp_rw [Polynomial.finsetSum_coeff,Polynomial.coeff_monomial]; rw [sum_eq_single n]; swap
  · intro b hb he; simp [he]
  swap
  · intro hv; rw [show rayc G n f=0 from by unfold rayc ray; rw [lap_finite G (by rw [mem_range] at hv; omega),smul_zero]]; simp
  simp
@[simp] lemma rayc_zero (f : Formula α) : rayc G 0 f=f := by simp [rayc,ray]
lemma rayc_next (f : Formula α) (n : ℕ) : ((n+1:ℕ):ℝ) • rayc G (n+1) f=laplace G (rayc G n f) := by
  rw [rayc,rayc,map_smul]; unfold ray; rw [smul_smul,pow_succ']
  change (_:ℝ) • (laplace G (((laplace G)^n) f)) = _
  congr 1; rw [Nat.factorial_succ]; push_cast; field_simp

variable {f : Formula α} {p q : KTime α}
def Wields (f : Formula α) (p : KTime α) : Prop := p.coeff 0=f ∧ sundial α p=lapTime G p
lemma ray_thin (f : Formula α) : Wields G f (timeRead G f) := ⟨by rw [rayc_eq,rayc_zero],by ext1 n; rw [lapTime_price, sun_price]; simp_rw [rayc_eq]; exact rayc_next ..⟩
lemma Wields.unique (hp : Wields G f p) (hq : Wields G f q) : p=q := by
  ext1 n; induction n with
  | zero => exact hp.1.trans hq.1.symm
  | succ n ih=>
    refine smul_right_injective _ (show ((n+1:ℕ):ℝ)≠ 0 by positivity) ?_
    dsimp only; rw [← sun_price,← sun_price,hp.2,hq.2,lapTime_price,lapTime_price,ih]
lemma Wields.is (hp : Wields G f p) : p=timeRead G f := hp.unique G (ray_thin ..)
def timer (G : Page α 2) : Formula α →ₗ[ℝ] KTime α where
  toFun:= timeRead G
  map_add' r s:= by ext1 x; simp only [Polynomial.coeff_add,rayc_eq,rayc,ray,map_add,smul_add]
  map_smul' r s:= by ext1 x; simp only [Polynomial.coeff_smul,rayc_eq,rayc,ray,map_smul]; exact smul_comm ..

lemma timer_ray (f : Formula α) : timer G f=timeRead G f := rfl
lemma timer_C (c : ℝ) : timer G (C c)= Polynomial.C (MvPolynomial.C c) := by
  rw [timer_ray]
  symm; refine Wields.is G ⟨by simp,?_⟩; ext1 i; rw [lapTime_price, sun_price,laplace_eval];simp only [Polynomial.coeff_C]; split_ifs <;> first| contradiction| omega| simp

omit [Fintype α] in
def reader (x : Formula α) : KTime α →ₐ[ℝ] Formula α := (Polynomial.aeval x).restrictScalars ℝ
omit [Fintype α] in
lemma reader_actual (p : KTime α) (x : Formula α) : reader x p= Polynomial.eval x p := have hz:= Polynomial.coe_aeval_eq_eval x; congr_fun hz p

def wick (G : Page α 2) : Formula α →ₗ[ℝ] Formula α := (reader (1:Formula α)).toLinearMap.comp (timer G)
lemma wick_read (f : Formula α) : wick G f=Polynomial.eval 1 (timeRead G f) := reader_actual _ _
lemma wick_scalar (c : ℝ) : wick G (C c)=C c := by rw [wick_read,← timer_ray,timer_C, Polynomial.eval_C]
lemma wick_one : wick G 1=1 := (congr_arg (wick G) (map_one (MvPolynomial.C (σ:=α) (R:=ℝ)))).symm.trans ((wick_scalar G 1).trans (map_one _))
end YM.WilsonBulk.Sheet
