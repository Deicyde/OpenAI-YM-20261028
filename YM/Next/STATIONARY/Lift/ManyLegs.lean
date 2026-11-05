import YM.Next.STATIONARY.Lift.Koszul

set_option autoImplicit false
/-!
# Eliminate/restore one group of Laurent variables
-/
noncomputable section
namespace YM.Stationary
open Function Lattice RG Exterior Bloch Laurent Filter Finset Asymptotics
open Matrix (transpose mulVec)
open scoped Matrix Topology ContDiff BigOperators
set_option linter.unusedSectionVars false

abbrev Keys (t : ℕ) := Fin t × Axis
abbrev Space (t : ℕ) := Phase (Keys t)
abbrev Run (t : ℕ) := Fin t → TypeFace 1

variable {t : ℕ}

def strand (i : Fin t) : Axis ↪ Keys t := ⟨fun b => (i,b), fun _ _ h => congr_arg Prod.snd h⟩
def stick (t : ℕ) := strand (0 : Fin (t+1))
def missing {M : Type} [AddCommGroup M] (p : Keys t → M) : Axis → M := -∑ i : Fin t, p ∘ strand i
def clipVars {M : Type} (p : Keys (t+1) → M) : Keys t → M := fun i => p (i.1.succ,i.2)
def extendVar {M : Type} (p : Keys t → M) (v : Axis → M) : Keys (t+1) → M := uncurry (Fin.cons v (curry p))
def bypass {M : Type} [AddCommGroup M] (p : Keys (t+1) → M) := extendVar (clipVars p) (missing p)
@[simp] lemma extends_zero {M : Type} (p : Keys t → M) (v) (i) : extendVar p v (0,i)=v i := rfl
@[simp] lemma extends_other {M : Type} (p : Keys t → M) (v) (j i) : extendVar p v (Fin.succ j,i)=p (j,i) := by
  simp [extendVar,uncurry,Function.curry]
lemma extends_back {M : Type} (p : Keys (t+1) → M) : extendVar (clipVars p) (fun i => p (0,i))=p := by
  ext1 ⟨i,j⟩; refine Fin.cases ?_ (fun i => ?_) i <;> simp [clipVars]
lemma extends_drop {M : Type} (p : Keys t → M) v : clipVars (extendVar p v)=p := by
  ext1 ⟨i,j⟩; simp [clipVars]
lemma miss_extend {M : Type} [AddCommGroup M] (p : Keys t → M) v : missing (extendVar p v)=-v+missing p := by
  unfold missing
  rw [Fin.sum_univ_succ,neg_add]
  congr! 1

lemma bypass_bypass {M : Type} [AddCommGroup M] (p : Keys (t+1) → M) : bypass (bypass p)=p := by
  have he := extends_back p
  simp only [bypass,extends_drop,miss_extend]
  trans extendVar (clipVars p) (fun i => p (0,i))
  · congr 1; rw [show missing p=_ from (congr_arg (fun y : Keys (t+1) → M => missing y) he).symm,miss_extend]; abel
  exact he
lemma miss_bypass {M : Type} [AddCommGroup M] (p : Keys (t+1) → M) : missing (bypass p) = p ∘ stick _ :=
    funext fun i => (congr_fun (bypass_bypass p) (0,i))

lemma miss_phase {p : Corn (Keys t)} : missing (axes p)=axes (missing p) := by
  ext1 a; simp [axes,missing,Finset.sum_apply]
lemma bypass_phase (p : Corn (Keys (t+1))) : bypass (axes p)=axes (bypass p) := by
  ext1 ⟨i,j⟩; refine Fin.cases ?_ (fun i => ?_) i <;> simp only [bypass,axes,extends_zero,extends_other, clipVars]
  exact congr_fun miss_phase _
lemma scale_bypass (p : Corn (Keys (t+1))) (s : ℝ) : bypass (s • p)=s • bypass p := by
  ext1 ⟨i,j⟩; refine Fin.cases ?_ (fun i => ?_) i <;> simp [bypass,clipVars, missing, Finset.sum_apply,Finset.mul_sum,Function.comp_def]

def slim (t : ℕ) (a : ℝ) := a / (t+2)
lemma slim_pos (t : ℕ) {σ : ℝ} (h : 0 < σ) : 0 < slim t σ := by unfold slim; positivity
lemma slim_le (t : ℕ) {σ : ℝ} (h : 0 < σ) : slim t σ ≤ σ := div_le_self h.le (by norm_cast; omega)

lemma miss_strip {σ : ℝ} {p : Space (t+1)} (hp : 0 < σ) (hv : p∈strip (slim t σ)) : missing p ∈ strip σ := by
  intro i
  simp only [missing, Pi.neg_apply,Finset.sum_apply,Complex.neg_im,Complex.im_sum,abs_neg]
  apply (Finset.abs_sum_le_sum_abs _ _).trans_lt
  calc
    _ ≤ ∑ j : Fin (t+1), slim t σ := sum_le_sum fun j _ => (hv (j,i)).le
    _ < σ := by simp [slim]; rw [← mul_div_assoc,div_lt_iff₀ (by positivity)]; nlinarith
lemma firm_shear {σ A : ℝ} {f : Space (t+1) → ℂ} (hf : Firm σ A f) : Firm (slim t σ) A (f ∘ bypass) := by
  have he := hf.width_pos
  refine hf.comp _ ?_ (slim_pos t he) (fun p hp i => ?_) (fun p x => ⟨bypass x,?_⟩)
  · refine differentiable_pi.mpr (fun i => ?_)
    rcases i with ⟨i,j⟩; refine Fin.cases ?_ (fun i => ?_) i <;> simp only [bypass,missing,clipVars,extends_zero,extends_other,Finset.sum_apply,Pi.neg_apply,Function.comp_def] <;> fun_prop
  · rcases i with ⟨i,j⟩; refine Fin.cases ?_ (fun i => ?_) i <;> simp only [bypass,extends_zero,extends_other,clipVars]
    · exact miss_strip he hp j
    exact (hp _).trans_le (slim_le t he)
  ext1 ⟨i,j⟩; refine Fin.cases ?_ (fun i => ?_) i <;>
    simp [bypass,clipVars,missing,reciprocal,Function.comp_def,Finset.sum_apply,Finset.mul_sum,sum_add_distrib]
  abel

lemma firm_drop {σ A : ℝ} {f : Space t → ℂ} (hf : Firm σ A f) : Firm σ A (f ∘ clipVars) := by
  refine hf.comp _ ?_ hf.width_pos (fun p hp i => hp _) fun p x => ⟨clipVars x,rfl⟩
  rw [differentiable_pi]; intro i; unfold clipVars; fun_prop

lemma firm_extend {σ A : ℝ} {f : Space (t+1) → ℂ} (hf : Firm σ A f) : Firm σ A (fun i => f (extendVar i 0)) := by
  refine hf.comp (fun p => extendVar p 0) ?_ hf.width_pos (fun p hp i => ?_) (fun p x => ⟨extendVar x 0,?_⟩)
  · refine differentiable_pi.mpr (fun i => ?_)
    rcases i with ⟨i,j⟩; refine Fin.cases ?_ (fun i => ?_) i <;> simp only [extends_zero,extends_other] <;> fun_prop
  · rcases i with ⟨i,j⟩; refine Fin.cases ?_ (fun i => ?_) i <;> simp only [extends_zero,extends_other]
    · simp [hf.width_pos]
    exact hp (i,j)
  ext1 ⟨i,j⟩; refine Fin.cases ?_ (fun i => ?_) i <;> simp [reciprocal]

lemma jet_bypass {s : ℕ} {f : Space (t+1) → ℂ} (h : Rays s (f ∘ axes)) : Rays s ((f ∘ bypass) ∘ axes) := by
  intro p
  simpa only [Function.comp_apply,bypass_phase,scale_bypass] using h (bypass p)

section bills
variable {α ξ : Type} [Fintype α] [Fintype ξ] [DecidableEq α]
    {σ A : ℝ} {r : ℕ}

lemma base_cob (m : Axis ↪ α) (i : TypeFace r) (j : TypeFace (r+1)) (p : Phase α) : (symbol r (projected m p)) j i = ∑ k : Axis, divZ (m k) p * left ℂ r k j i := by rw [symbol,wedge, Matrix.sum_apply]; rfl

def billCon (σ : ℝ) (r : ℕ) := (Fintype.card (TypeFace (r+1)) : ℝ) * (4 * (Real.exp σ+1))
lemma billCon_nonneg (σ : ℝ) (r : ℕ) : 0 ≤ billCon σ r := by unfold billCon; positivity
lemma norm_left (k : Axis) (a : TypeFace (r+1)) (b : TypeFace r) : ‖left ℂ r k a b‖ ≤ 1 := by
  unfold left; dsimp only [Matrix.of_apply]; split_ifs <;> simp [parity]

lemma strip_symbol (m : Axis ↪ α) (h : 0<σ) (a : TypeFace (r+1)) (b : TypeFace r) : Firm σ (4*(Real.exp σ+1)) (fun p => symbol r (projected m p) a b) := by
  simp_rw [base_cob]
  have he (k : Axis) := (divMode (m k) h).mul (Firm.const h (left ℂ r k a b))
  have hy := Firm.sum (σ:=σ) univ _ (fun _ : Axis => Real.exp σ+1) h (fun i _ =>
    (he i).mono h le_rfl (mul_le_of_le_one_right (by positivity) (norm_left _ _ _)))
  simpa [mul_add] using hy

lemma ray_symbol (m : Axis ↪ α) (a : TypeFace (r+1)) (b : TypeFace r) : Rays 1 (fun p => symbol r (projected m (axes p)) a b) := by
  apply (rays_at_zero ((strip_symbol m (σ:=1) one_pos a b).analytic_real 0)).2
  simp [Function.comp,base_cob,divZ]

lemma pay_cob (m : Axis ↪ α) (h : 0<σ) {f : SheetLeg α ξ (r+1)} (H : CostWall σ A f) : CostWall σ (A*billCon σ r) (cob r (projected m) f) := by
  intro i x; unfold cob Matrix.mulVec dotProduct
  have he (j : TypeFace (r+1)) := (strip_symbol m h j i).mul (H j x)
  have hy := Firm.sum (σ:=σ) univ _ _ h (fun i _ => he i)
  convert hy using 1
  · unfold billCon; simp; ring
  rfl
lemma jets_cob {m : Phase α → Momentum} (hm : ∀ (a : TypeFace (r+1)) (b : TypeFace r), Rays 1 (fun p => symbol r (m (axes p)) a b)) {f : SheetLeg α ξ (r+1)} {s : ℕ} (h : JetWall s f) : JetWall (s+1) (cob r m f) := by
  intro i x p; unfold cob Matrix.mulVec dotProduct
  apply Asymptotics.IsBigO.sum; intro j _
  simp_rw [Matrix.transpose_apply]
  rw [add_comm s]
  exact Rays.mul (hm j i) (h j x) p

lemma wall_cob (m : Phase α → Momentum) {U} {f : SheetLeg α ξ (r+1)} (h : wall U f) : wall U (cob r m f) := by
  intro p a
  have hh : cob r m f (axes p) a = ∑ i : TypeFace (r+1), symbol r (m (axes p)) i a • f (axes p) i := by
    funext x; rw [Finset.sum_apply]; rfl
  rw [hh]; exact (U p).sum_mem fun i _ => (U p).smul_mem _ (h p i)
end bills
end YM.Stationary
end

/-!
# Dependent-leg tools

`seal` is contraction with the first still independent leg. Use `open_end`
only when allowed to forget this constraint, then fix its commutator
with a curl along the same end. Everything before periodization.
-/
noncomputable section
namespace YM.Stationary
open Function Lattice RG Exterior Bloch Laurent Filter Finset Asymptotics
open Matrix (transpose mulVec)
open scoped Matrix Topology ContDiff BigOperators
variable {t r : ℕ} {σ A : ℝ}

def locus {α : Type} (m : Fin t × Axis ↪ α) (p : Phase α) : Submodule ℂ (Run t → ℂ) where
    carrier := {w | ∀ (i : Fin t) (b : Run t),
      ∑ j : TypeFace 1, symbol 0 (projected ((strand i).trans m) p) j vac * w (update b i j) = 0}
    add_mem' := fun {a b} ha hb i k => by simp only [Pi.add_apply, mul_add,Finset.sum_add_distrib]; rw [ha,hb,add_zero]
    smul_mem' := fun x _ ha i k => by
      simp only [Pi.smul_apply,smul_eq_mul]; simp_rw [mul_left_comm _ x]; rw [← Finset.mul_sum,ha,mul_zero]
    zero_mem' := fun i b => by simp

def locus0 (p : Corn (Keys t)) := locus (Embedding.refl (Keys t)) (axes p)

abbrev SpanAt (t r : ℕ) := SheetLeg (Keys t) (Run t) r

section remove
-- forget the requirement of closure in *first* independent index

def lineTail {t : ℕ} (p : Corn (Keys (t+1))) : Submodule ℂ (Run (t+1) → ℂ) where
    carrier := {w | ∀ a : TypeFace 1,(fun b : Run t => w (Fin.cons a b))∈locus0 (clipVars p)}
    zero_mem' := fun _ => (locus0 (clipVars p)).zero_mem
    smul_mem' := fun x _ H a => (locus0 _).smul_mem x (H a)
    add_mem' := fun {_ _} H h a => (locus0 _).add_mem (H a) (h a)

lemma var_uniform {ξ : Type} [Fintype ξ] {U : Corn (Keys (t+1)) → Submodule ℂ (ξ → ℂ)}
    (h : ∀ p q, clipVars p=clipVars q → U p=U q) : Uniforms ξ _ (stick t) U := by
  intro p q ht; apply h; funext ⟨i,a⟩; apply ht
  rintro ⟨v,hv⟩; exact (Fin.succ_ne_zero i) (congr_arg Prod.fst hv.symm)
lemma line_uniform : Uniforms _ _ (stick t) lineTail := var_uniform (fun p q he => by
  ext f; change (∀ a : TypeFace 1, _ ∈ locus0 (clipVars p)) ↔ ∀ a : TypeFace 1, _ ∈ locus0 (clipVars q)
  rw [he])

lemma seal_tail (p : Corn (Keys (t+1))) (f : Run (t+1) → ℂ) : f ∈ locus0 p ↔
    f∈lineTail p ∧ ∀ b : Run t, ∑ j : TypeFace 1, symbol 0 (projected (stick t) (axes p)) j vac * f (Fin.cons j b) = 0 := by
  have ht (W : Run (t+1) → ℂ) : W∈ locus0 p ↔ _ := show W∈ locus0 p ↔
    ∀ (i : Fin (t+1)) (b : Run (t+1)), ∑ j : TypeFace 1, symbol 0 (projected (strand i) (axes p)) j vac * W (update b i j)=0 from Iff.rfl
  have he (i : Fin t) : axes (clipVars p) ∘ (strand i).trans (Embedding.refl _) = axes p ∘ strand i.succ := rfl
  rw [ht]; constructor
  · intro H
    refine ⟨fun q k a => ?_, fun b => ?_⟩
    · change ∑ j : TypeFace 1, symbol 0 (axes (clipVars p) ∘ _) j vac * f (Fin.cons q (update a k j)) = _
      have h₁ := H k.succ (Fin.cons q a)
      rw [he]; simp_rw [← Fin.cons_update] at h₁; exact h₁
    have h₁ := H 0 (Fin.cons (coord 0) b)
    simpa only [stick,Fin.update_cons_zero] using h₁
  rintro ⟨H,h⟩ i b
  rw [← Fin.cons_self_tail b]
  refine Fin.cases ?_ (fun k => ?_) i
  · simp only [Fin.update_cons_zero]; exact h _
  simp_rw [← Fin.cons_update]
  exact H _ k _

-- borrowing active coordinate (shear)
def payEnd (t : ℕ) (σ : ℝ) := taxWall (Keys (t+1)) (slim t σ)
def endWidth (t : ℕ) (σ : ℝ) := slim t (slim t σ / 4)
lemma payEnd_nonneg (h : 0 < σ) (t : ℕ) : 0 ≤ payEnd t σ := (taxWall_pos (slim_pos t h)).le
lemma end_paid (h : 0 < σ) (t : ℕ) : 0 < endWidth t σ ∧ endWidth t σ ≤ σ := by
  have hh := slim_pos t h
  have he : 0 < slim t σ / 4 := by positivity
  exact ⟨slim_pos _ he,(slim_le t he).trans ((show slim t σ / 4 ≤ slim t σ by linarith).trans (slim_le t h))⟩

def swab {ξ : Type} (f : SheetLeg (Keys (t+1)) ξ r) : SheetLeg (Keys (t+1)) ξ r := f ∘ bypass
lemma shear_cob {ξ : Type} (f : SheetLeg (Keys (t+1)) ξ (r+1)) : cob r (projected (stick t)) (swab f)=swab (cob r missing f) := by
  ext1 p; funext a b
  simp only [swab,Function.comp_apply, cob,miss_bypass]; rfl
lemma swab_twice {ξ : Type} (f : SheetLeg (Keys (t+1)) ξ r) : swab (swab f)=f := by ext1 p; simp [swab,bypass_bypass]
lemma swab_cost {ξ : Type} [Fintype ξ] {f : SheetLeg (Keys (t+1)) ξ r} (h : CostWall σ A f) : CostWall (slim t σ) A (swab f) := fun i x => firm_shear (h i x)
lemma swab_jets {ξ : Type} {f : SheetLeg (Keys (t+1)) ξ r} {s : ℕ} (h : JetWall s f) : JetWall s (swab f) := fun i x => jet_bypass (f:=fun p => f p i x) (h i x)
lemma swab_wall {ξ : Type} [Fintype ξ] {U : Corn (Keys (t+1)) → Submodule ℂ (ξ → ℂ)}
    (h : Uniforms _ _ (stick t) U) {f : SheetLeg (Keys (t+1)) ξ r} (hf : wall U f) : wall U (swab f) := by
  intro p a
  have he : U p = U (bypass p) := h p (bypass p) (by
    intro z hn; rcases z with ⟨j,i⟩
    revert hn; refine Fin.cases ?_ (fun j => ?_) j
    · exact fun hn => False.elim (hn ⟨i,rfl⟩)
    intro _; simp [bypass,clipVars])
  rw [he]; unfold swab; simp only [Function.comp_apply,bypass_phase]; exact hf _ _

/-- Single dependent leg, assuming wall already independent of first
momentum. Degree zero requires input void at the harmonic of *that leg*. -/
lemma open_end {ξ : Type} [Fintype ξ] (f : SheetLeg (Keys (t+1)) ξ r) (hσ : 0<σ) (ha : 0 ≤ A)
    (hf : CostWall σ A f) {U} (hU : Uniforms ξ _ (stick t) U) (h : wall U f) (hu : Cycles missing r f)
    (hp : r≠0 ∨ ∀ p : Corn (Keys (t+1)), missing p=0 → f (axes p)=0)
    {s : ℕ} (hj : JetWall s f) : ∃ B : SheetLeg (Keys (t+1)) ξ (r+1), CostWall (endWidth t σ) (A*payEnd t σ) B ∧
        JetWall (s-1) B ∧ wall U B ∧ ∀ p : Corn (Keys (t+1)), f (axes p)=cob r missing B (axes p) := by
  have hv : Cycles (projected (stick t)) r (swab f) := by
    cases r with
    | zero => trivial
    | succ r =>
      intro p
      rw [shear_cob, swab, Function.comp_apply,bypass_phase]; exact hu _
  obtain ⟨X,hx,ht,hy,hQ⟩ := wall_lift (stick t) (slim_pos t hσ) ha (swab f) (swab_cost hf) hv (hp.imp_right (fun H p hs => by
    rw [swab,Function.comp_apply,bypass_phase]; exact H _ ((miss_bypass p).trans hs))) (swab_jets hj) hU (swab_wall hU h)
  refine ⟨swab X, swab_cost hx,swab_jets ht,swab_wall hU hy,fun p => ?_⟩
  have H := hQ (bypass p)
  have he : cob r (projected (stick t)) X = swab (cob r missing (swab X)) := by simpa only [swab_twice] using shear_cob (swab X)
  simpa only [← bypass_phase,he,swab,bypass_bypass,Function.comp_apply] using H

-- pull one contraction past the lost variable with smaller width
lemma seal_missing {ξ : Type} [Fintype ξ] {f : SheetLeg (Keys (t+1)) ξ (r+1)} (hσ : 0<σ)
    (h : CostWall σ A f) : CostWall (slim t (slim t σ)) (A*billCon (slim t σ) r) (cob r missing f) := by
  have hh := pay_cob (stick t) (slim_pos t hσ) (swab_cost h)
  rw [shear_cob] at hh; simpa only [swab_twice] using swab_cost hh
lemma miss_jet {ξ : Type} [Fintype ξ] {f : SheetLeg (Keys (t+1)) ξ (r+1)} {s} (h : JetWall s f) : JetWall (s+1) (cob r missing f) := by
  have hh := jets_cob (m:=projected (stick t)) (ray_symbol _) (swab_jets h)
  rw [shear_cob] at hh; simpa only [swab_twice] using swab_jets hh

-- Contraction in the first independent leg, suppressing its degree-zero slot.
def headPress (f : SpanAt (t+1) r) : SheetLeg (Keys (t+1)) (Run t) r := fun p a b =>
    ∑ j : TypeFace 1, symbol 0 (projected (stick t) p) j vac * f p a (Fin.cons j b)

lemma press_cob (f : SpanAt (t+1) (r+1)) : headPress (cob r missing f)=cob r missing (headPress f) := by
  funext p a b
  simp only [headPress,cob,Matrix.mulVec,dotProduct,mul_sum]
  rw [sum_comm]; exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => mul_left_comm ..
lemma press_sub (f g : SpanAt (t+1) r) : headPress (f-g)=headPress f-headPress g := by
  funext p a b; simp [headPress,mul_sub,sum_sub_distrib]
lemma press_wall {f : SpanAt (t+1) r} (h : wall lineTail f) : wall (fun p => locus0 (clipVars p)) (headPress f) := by
  intro p b; dsimp only
  rw [show headPress f (axes p) b=∑ j : TypeFace 1, symbol 0 (projected (stick t) (axes p)) j vac • fun v => f (axes p) b (Fin.cons j v) by
    funext v; rw [Finset.sum_apply]; rfl]; exact (locus0 _).sum_mem fun i _ => (locus0 _).smul_mem _ (h p b i)
lemma press_cost {f : SpanAt (t+1) r} (hσ : 0 < σ) (h : CostWall σ A f) : CostWall σ (A*billCon σ 0) (headPress f) := by
  intro i x
  let g : SheetLeg (Keys (t+1)) Unit 1 := fun p j _ => f p i (Fin.cons j x)
  exact pay_cob (stick t) hσ (f:=g) (fun a _ => h i _) vac ()

end remove
end YM.Stationary
end

/-!
# Last momentum is not independent

Dimension shift for the multileg Ward lift (E approx lines 2300--2364).
Carry the earlier closure wall. Costs all per-index constants times input,
no unknown widths invoked along the same-step path.
-/
noncomputable section
namespace YM.Stationary
open Function Lattice RG Exterior Bloch Laurent Filter Finset Asymptotics
open Matrix (transpose mulVec)
open scoped Matrix Topology ContDiff BigOperators
variable {t r : ℕ} {σ A : ℝ}

-- degree-zero right inverse for `headPress`
lemma press_lift {s : ℕ} (f : SheetLeg (Keys (t+1)) (Run t) r) (hσ : 0 < σ) (ha : 0 ≤ A)
    (hf : CostWall σ A f) (hj : JetWall s f) (hW : wall (fun p => locus0 (clipVars p)) f)
    (hv : ∀ p : Corn (Keys (t+1)), p ∘ stick t = 0 → f (axes p)=0) :
    ∃ V : SpanAt (t+1) r, CostWall (σ/4) (A*taxWall (Keys (t+1)) σ) V ∧ JetWall (s-1) V ∧
      wall lineTail V ∧ ∀ p : Corn (Keys (t+1)), headPress V (axes p)=f (axes p) := by
  let T p := locus0 (clipVars p) (t:=t)
  have H : Uniforms (Run t) _ (stick t) T := var_uniform (fun p q he => by unfold T; rw [he])
  choose X HX HY HH He using fun i : TypeFace r =>
    wall_lift (stick t) hσ ha (fun p (_ : TypeFace 0) => f p i) (fun _ b => hf i b) (by trivial) (Or.inr (fun p he => by rw [hv p he]; rfl))
      (s:=s) (fun _ b => hj i b) H (fun p _ => hW p i)
  let V (p : Phase (Keys (t+1))) (a : TypeFace r) (b : Run (t+1)) := X a p (b 0) (Fin.tail b)
  refine ⟨V,fun i x => HX i _ _,fun i x => HY i _ _,fun p i a => ?_,fun p => ?_⟩
  · change (fun b => X i (axes p) _ _)∈ _
    simpa only [Fin.tail_cons,Fin.cons_zero] using HH i p a
  funext i x
  simp only [headPress,V,Fin.tail_cons,Fin.cons_zero]
  exact congr_fun (congr_fun (He i p).symm vac) x

lemma jet_nil {α ξ : Type} [Fintype α] {f : SheetLeg α ξ r} (h : CostWall σ A f) : JetWall 0 f :=
    fun i x => rays_zero ((h i x).analytic_real 0)


/-- Dimension shift, uniform (constants needn't be explicit). -/
theorem dimensionShift (t r : ℕ) (h : r+1+2*t>4) (σ : ℝ) (hs : 0 < σ) :
    ∃ δ C, 0 < δ ∧ δ≤σ ∧ 0≤C ∧ ∀ (A : ℝ) (u : SpanAt t (r+1)),
      0 ≤ A → CostWall σ A u → Cycles missing (r+1) u → wall locus0 u →
      ∃ v : SpanAt t (r+2), CostWall δ (A*C) v ∧ wall locus0 v ∧
        ∀ p : Corn (Keys t), cob (r+1) missing v (axes p)=u (axes p) := by
  induction t generalizing r σ with
  | zero =>
    refine ⟨σ,0,hs,le_rfl,le_rfl,fun _ u ha hu he hh => ⟨0, ?_, fun i j => (locus0 i).zero_mem, fun i => ?_⟩⟩
    · intro i x; simpa only [mul_zero,Pi.zero_apply] using Firm.zero (α:=_) hs
    funext j
    have hm := Finset.card_le_univ j.val
    rw [j.property] at hm; simp at hm; omega
  | succ t ih =>
    let τ := endWidth t σ
    let τ' := endWidth t τ
    obtain ⟨hs',hs₁⟩ : 0<τ ∧ τ≤σ := end_paid hs t
    obtain ⟨hk',hs₂⟩ : 0<τ' ∧ τ'≤τ := end_paid hs' t
    obtain ⟨w,C,hw,He,Hc,H⟩ := ih (r+2) (by omega) τ' hk'
    let γ := slim t (slim t w)
    let α := slim t (slim t (γ/4))
    have hg : 0<γ := slim_pos _ (slim_pos _ hw)
    have hG : γ ≤ w := (slim_le _ (slim_pos _ hw)).trans (slim_le _ hw)
    have h₁ : 0<γ/4 := by positivity
    have ht : 0 < α := slim_pos _ (slim_pos _ h₁)
    have hl : α ≤ τ := (slim_le _ (slim_pos _ h₁)).trans ((slim_le _ h₁).trans ((show γ/4 ≤ γ by linarith).trans (hG.trans (He.trans hs₂))))
    let b := payEnd t σ * billCon τ 0
    let c := b * payEnd t τ
    let d := c*C*billCon (slim t w) (r+3)
    let B := (c+d)*taxWall (Keys (t+1)) γ
    have hb : 0 ≤ b := mul_nonneg (payEnd_nonneg hs _) (billCon_nonneg ..)
    have hc : 0 ≤ c := mul_nonneg hb (payEnd_nonneg hs' _)
    have hd : 0 ≤ d := mul_nonneg (mul_nonneg hc Hc) (billCon_nonneg ..)
    have hB : 0 ≤ B := mul_nonneg (add_nonneg hc hd) (taxWall_pos hg).le
    refine ⟨α,payEnd t σ+B*billCon (slim t (γ/4)) (r+2),ht,hl.trans hs₁,
      add_nonneg (payEnd_nonneg hs _) (mul_nonneg hB (billCon_nonneg ..)), fun A u ha hh hy hu => ?_⟩
    obtain ⟨X,HX,_,HT,Hj⟩ := open_end u hs ha hh line_uniform
      (fun i j => ((seal_tail i _).1 (hu i j)).1) hy (Or.inl (by omega)) (jet_nil hh)
    let V := headPress X
    let T : Corn (Keys (t+1)) → Submodule ℂ (Run t → ℂ) := fun p => locus0 (clipVars p)
    have U : Uniforms (Run t) _ (stick t) T := var_uniform fun _ _ he => by unfold T; rw [he]
    have hV : CostWall τ (A*b) V := by unfold b; rw [← mul_assoc]; exact press_cost hs' HX
    have hv : Cycles missing (r+2) V := by
      intro p
      unfold V; rw [← press_cob]
      funext a x; unfold headPress; rw [← Hj]
      exact ((seal_tail p _).1 (hu p a)).2 x
    obtain ⟨Y,HY,_,HW,Hy⟩ := open_end V hs' (mul_nonneg ha hb) hV U
      (press_wall HT) hv (Or.inl (by omega)) (jet_nil hV)
    have hconv (p : Corn (Keys t)) : axes (extendVar p 0) = extendVar (axes p) 0 := by
      ext1 ⟨i,j⟩; refine Fin.cases ?_ (fun i => ?_) i <;> simp [axes]
    let Z : SpanAt t (r+3) := fun p => Y (extendVar p 0)
    have HZ : CostWall τ' (A*c) Z := by unfold c; rw [← mul_assoc]; exact fun i x => firm_extend (HY i x)
    have hz (p : Corn (Keys t)) : cob (r+2) missing Z (axes p)=0 := by
      have he : V (axes (extendVar p 0))=0 := by
        funext i x; simp only [V,headPress]
        rw [show projected (stick t) (axes (extendVar p 0))=0 from funext fun j => by simp [projected,axes,stick,strand]]
        simp [symbol,q,wedge]
      have he := (Hy (extendVar p 0)).symm.trans he
      funext a x
      have hh := congr_fun (congr_fun he a) x
      simp only [hconv, cob,miss_extend,neg_zero,zero_add] at hh
      exact hh
    obtain ⟨W,hW,Wh,Wp⟩ := H (A*c) Z (mul_nonneg ha hc) HZ hz (by
      intro p a; have hi := HW (extendVar p 0) a; rw [hconv] at hi; unfold T at hi; rw [extends_drop] at hi; exact hi)
    let W' : SheetLeg (Keys (t+1)) (Run t) (r+4) := fun p => W (clipVars p)
    have HW' : wall T W' := fun p i => Wh (clipVars p) i
    have hw' := seal_missing (ξ:=Run t) (f:=W') hw (A:=(A*c)*C) (fun i x => firm_drop (hW i x))
    let L := Y - cob (r+3) missing W'
    have Hp : CostWall γ (A*(c+d)) L := by
      have hA : CostWall γ (A*c) Y := by
        unfold c; rw [← mul_assoc]
        exact HY.mono hg (hG.trans He) le_rfl
      have hE : A*d=((A*c)*C)*billCon (slim t w) (r+3) := by unfold d; ring
      rw [mul_add,hE]; exact hA.sub hw'
    obtain ⟨F,hF,_,Hf,hf⟩ := press_lift L hg (mul_nonneg ha (add_nonneg hc hd)) Hp (jet_nil Hp)
      (fun p i => (T p).sub_mem (HW p i) (wall_cob missing HW' p i)) (by
        intro p hs
        let q := clipVars p
        have he : p=extendVar q 0 := by
          conv_rhs => rw [← hs]
          exact (extends_back p).symm
        rw [he,hconv]
        funext i x
        simp only [L,Pi.sub_apply,cob,W',extends_drop,miss_extend,neg_zero,zero_add]
        exact sub_eq_zero.mpr (congr_fun (congr_fun (Wp q).symm i) x))
    let S := X-cob (r+2) missing F
    refine ⟨S,?_,fun p i => ?_, fun p => ?_⟩
    · rw [mul_add, ← mul_assoc]
      unfold S
      exact (HX.mono ht hl le_rfl).sub (seal_missing h₁ (by unfold B; rw [← mul_assoc]; exact hF))
    · apply (seal_tail p _).2
      refine ⟨(lineTail p).sub_mem (HT p i) (wall_cob missing Hf p i),?_⟩
      intro v
      change headPress S (axes p) i v=0
      rw [show headPress S = V-cob (r+2) missing (headPress F) by rw [show S=X-_ from rfl,press_sub,press_cob]]
      change V (axes p) i v - cob _ _ _ _ _ _ = _
      have hm : cob (r+2) missing L = cob (r+2) missing Y := by unfold L; rw [cob_sub,cob_zero,sub_zero]
      apply sub_eq_zero.mpr
      rw [Hy, ← hm]
      unfold cob; rw [hf]
    unfold S; rw [cob_sub,cob_zero,sub_zero,Hj]
end YM.Stationary
end

/-! # Independent-leg steps and genuine multileg kernel lift -/
noncomputable section
namespace YM.Stationary
open Function Lattice RG Exterior Bloch Laurent Filter Finset Asymptotics
open Matrix (transpose mulVec)
open scoped Matrix Topology ContDiff BigOperators
variable {t n : ℕ} {σ A : ℝ}

abbrev CurRun (t : ℕ) := Fin t → TypeFace 2

/-- potential kernel of a *scalar action* at its leading (n-wave) term,
before polarization or pulling channels. -/
def fromCurl {n : ℕ} (p : Fin n → Momentum) (F : CurRun n → ℂ) : Run n → ℂ := fun v =>
    ∑ b : CurRun n, (∏ i, symbol 1 (p i) (b i) (v i)) * F b

lemma fromCurl_cons (p : Fin (t+1) → Momentum) (F : CurRun (t+1) → ℂ) (v : Run (t+1)) :
    fromCurl p F v = ∑ b : TypeFace 2, symbol 1 (p 0) b (v 0) *
        fromCurl (Fin.tail p) (fun y => F (Fin.cons b y)) (Fin.tail v) := by
  unfold fromCurl
  let E : TypeFace 2 × CurRun t ≃ CurRun (t+1) := Fin.consEquiv (fun _ : Fin (t+1) => TypeFace 2)
  rw [← E.sum_comp,Fintype.sum_prod_type]
  apply sum_congr rfl; intro j _
  rw [mul_sum]; apply sum_congr rfl; intro k _
  rw [Fin.prod_univ_succ, mul_assoc]
  simp only [show E (j,k)=Fin.cons j k from rfl,Fin.cons_zero,Fin.cons_succ]; rfl

section partials
variable {α : Type} [Fintype α] [DecidableEq α]

def strands (m : Keys n ↪ α) (p : Phase α) (i : Fin n) : Momentum := projected ((strand i).trans m) p
private def recede (m : Keys (n+1) ↪ α) : Keys n ↪ α where
    toFun p := m (p.1.succ,p.2)
    inj' p q h := by have hh := m.injective h; simpa only [Prod.mk.injEq, Fin.succ_inj,Prod.ext_iff] using hh

omit [Fintype α] [DecidableEq α] in
private lemma recedes (m : Keys (t+1) ↪ α) : Uniforms _ _ ((stick t).trans m)
    (fun p : Corn α => locus (recede m) (axes p)) := by
  intro p q H
  have he (i : Fin t) : strands (recede m) (axes p) i=strands (recede m) (axes q) i := by
    funext a
    change (p (m (i.succ,a)):ℂ) = ((q (m (i.succ,a)):ℝ):ℂ); congr 1
    apply H
    rintro ⟨b,hb⟩; have hi : (0,b)=(i.succ,a) := m.injective hb; exact (Fin.succ_ne_zero i) (congr_arg Prod.fst hi).symm
  ext w
  change (∀ i (b : Run t), ∑ j : TypeFace 1, symbol 0 (strands _ (axes p) i) j vac * w (update b i j)=0) ↔
    ∀ i (b : Run t), ∑ j : TypeFace 1, symbol 0 (strands _ (axes q) i) j vac * w (update b i j)=0
  simp_rw [he]

lemma independent (t : ℕ) (σ : ℝ) (hσ : 0 < σ) (m : Keys t ↪ α) :
    ∃ τ K, 0 < τ ∧ τ≤σ ∧ 0 ≤ K ∧ ∀ (A : ℝ) (s : ℕ) (f : Run t → Phase α → ℂ), 0 ≤ A →
        (∀ i, Firm σ A (f i)) → (∀ i, Rays s (f i ∘ axes)) →
        (∀ p : Corn α,(fun i => f i (axes p))∈locus m (axes p)) →
        ∃ g : CurRun t → Phase α → ℂ, (∀ i, Firm τ (A*K) (g i)) ∧ (∀ i, Rays (s-t) (g i ∘ axes)) ∧
          ∀ p : Corn α,(fromCurl (strands m (axes p)) (fun i => g i (axes p)))=fun i => f i (axes p) := by
  induction t generalizing σ with
  | zero =>
    refine ⟨σ,1,hσ,le_rfl,zero_le_one,fun A s f ha hf hw he => ?_⟩
    refine ⟨fun _ => f default,fun _ => by rw [mul_one]; exact hf _,fun _ => hw _,fun p => funext fun i => ?_⟩
    simp [fromCurl,show i=default from Subsingleton.elim ..]
  | succ t ih =>
    obtain ⟨τ,K,ht,hb,hM,H⟩ := ih (σ/4) (by positivity) (recede m)
    refine ⟨τ,taxWall α σ*K,ht,hb.trans (by linarith),mul_nonneg (taxWall_pos hσ).le hM,fun A s f ha hf hj h => ?_⟩
    let F (p : Phase α) (a : TypeFace 1) (x : Run t) := f (Fin.cons a x) p
    let i := (stick t).trans m
    have hx : Cycles (projected i) 1 F := by
      intro p
      funext b x; rw [vac_only b]
      have he : ∑ y : TypeFace 1, symbol 0 (strands _ (axes p) 0) y vac * f (update (Fin.cons (coord 0) x) 0 y) (axes p)=0 := h p 0 _
      simp only [Fin.update_cons_zero] at he; exact he
    have hw : wall (fun p => locus (recede m) (axes p)) F := by
      intro p a j b
      have he : ∑ y : TypeFace 1, symbol 0 (strands m (axes p) j.succ) y vac * f (update (Fin.cons a b) j.succ y) (axes p)=0 := h p _ _
      simp_rw [← Fin.cons_update] at he
      exact he
    obtain ⟨G,hG,Gh,hV,Gp⟩ := wall_lift i hσ ha F (fun i j => hf _) hx (Or.inl (by norm_num))
      (fun i j => hj _) (recedes m) hw
    choose U hU HJ he using fun a => H (A*taxWall α σ) (s-1) (fun b p => G p a b) (mul_nonneg ha (taxWall_pos hσ).le)
      (hG a) (Gh a) (fun p => hV p a)
    let g (b : CurRun (t+1)) : Phase α → ℂ := U (b 0) (Fin.tail b)
    refine ⟨g,fun i => ?_,fun i => ?_,fun p => funext fun b => ?_⟩
    · rw [← mul_assoc]; exact hU _ _
    · rw [show s-(t+1)=s-1-t by omega]; exact HJ _ _
    rw [fromCurl_cons]; simp only [g,Fin.tail_cons,Fin.cons_zero]
    rw [show Fin.tail (strands m (axes p))=strands (recede m) (axes p) from rfl]; simp_rw [he]
    change cob 1 (projected i) G (axes p) (b 0) (Fin.tail b)=_
    rw [← Gp]; simp [F, Fin.cons_self_tail]
end partials

/-! Dependent rank larger cases. Combined route uses dependency first at
slot **zero**. -/
def plotted (p : Space t) : Fin (t+1) → Momentum := Fin.cons (missing p) (fun i => projected (strand i) p)

def Contractible (f : Run (t+1) → Space t → ℂ) : Prop :=
    ∀ p : Corn (Keys t), ∀ i b, ∑ j : TypeFace 1, symbol 0 (plotted (axes p) i) j vac * f (update b i j) (axes p) = 0

def clauses (f : Run (t+1) → Space t → ℂ) : SpanAt t 1 := fun p a b => f (Fin.cons a b) p

lemma Contractible.loci {f : Run (t+1) → Space t → ℂ} (h : Contractible f) :
    Cycles missing 1 (clauses f) ∧ wall locus0 (clauses f) := by
  constructor
  · intro p; funext i b
    have he := h p 0 (Fin.cons (coord 0) b); simp only [Fin.update_cons_zero] at he; rw [vac_only i]; exact he
  intro p a i b
  have he := h p i.succ (Fin.cons a b)
  simp_rw [← Fin.cons_update] at he
  simp only [plotted,Fin.cons_succ] at he
  exact he

/-- Arity at least three. Vane data furnished on the derivatives of a
single real score, with the first momentum always minus the sum of the rest. -/
theorem allleg (t : ℕ) (ht : 2 ≤ t) (σ : ℝ) (hs : 0 < σ) : ∃ η K, 0 < η ∧ η≤σ ∧ 0 ≤ K ∧
    ∀ (A : ℝ) (f : Run (t+1) → Space t → ℂ), 0 ≤ A → (∀ i, Firm σ A (f i)) → Contractible f →
      ∃ g : CurRun (t+1) → Space t → ℂ, (∀ i, Firm η (A*K) (g i)) ∧
        ∀ (p : Corn (Keys t)) b, fromCurl (plotted (axes p)) (fun i => g i (axes p)) b=f b (axes p) := by
  obtain ⟨w,C,hW,hΩ,hC,H⟩ := dimensionShift t 0 (by omega) σ hs
  obtain ⟨x,k,hx,hγ,hk,G⟩ := independent t w hW (Embedding.refl (Keys t))
  refine ⟨x,C*k,hx,hγ.trans hΩ,mul_nonneg hC hk,fun A f ha hf hu => ?_⟩
  obtain ⟨V,hV,hv,Hv⟩ := H A (clauses f) ha (fun i b => hf _) hu.loci.1 hu.loci.2
  choose W hw hh hw' using fun i => G (A*C) 0 (fun b p => V p i b) (mul_nonneg ha hC)
    (hV i) (fun b => rays_zero ((hV i b).analytic_real _)) (fun p => hv p i)
  refine ⟨fun b => W (b 0) (Fin.tail b), fun i => ?_, fun p b => ?_⟩
  · rw [← mul_assoc]; exact hw _ _
  rw [fromCurl_cons]
  simp only [Fin.cons_zero,Fin.tail_cons,plotted]
  rw [show (fun i => projected (strand i) (axes p)) = strands (Embedding.refl (Keys t)) (axes p) from rfl]
  simp_rw [hw']; change cob 1 missing V (axes p) _ _=_
  rw [Hv]; simp [clauses]
end YM.Stationary
end

/-!
# Exact momentum and retained order in the loop-row lift

In the two-slot case don't invoke dimension shift (the bottom ambiguity matters).
Use one further lift, and use the given vanishing order for a degree-zero step.
-/
noncomputable section
namespace YM.Stationary
open Function Lattice RG Exterior Bloch Laurent Filter Finset Asymptotics
open Matrix (transpose mulVec)
open scoped Matrix Topology ContDiff BigOperators
variable {t r s : ℕ} {σ A : ℝ}

lemma press_jet {f : SpanAt (t+1) r} (h : JetWall s f) : JetWall (s+1) (headPress f) := by
  intro i x
  let g : SheetLeg (Keys (t+1)) Unit 1 := fun p j _ => f p i (Fin.cons j x)
  exact jets_cob (f:=g) (ray_symbol (stick t)) (s:=s) (fun a _ => h i _) vac ()

theorem bothleg (σ : ℝ) (hs : 0 < σ) : ∃ η K, 0 < η ∧ η≤σ ∧ 0 ≤ K ∧
    ∀ A s (f : Run 2 → Space 1 → ℂ), 0 ≤ A → (∀ i, Firm σ A (f i)) → Contractible (t:=1) f →
      (∀ i, Rays (s+2) (f i ∘ axes)) →
      ∃ g : CurRun 2 → Space 1 → ℂ, (∀ i, Firm η (A*K) (g i)) ∧
        (∀ i, Rays s (g i ∘ axes)) ∧ ∀ (p : Corn (Keys 1)) b,
          fromCurl (plotted (axes p)) (fun i => g i (axes p)) b=f b (axes p) := by
  let τ := endWidth 0 σ
  let w := endWidth 0 τ
  obtain ⟨ht,hT⟩ : 0 < τ ∧ τ ≤ σ := end_paid hs 0
  obtain ⟨hw,hW⟩ : 0 < w ∧ w ≤ τ := end_paid ht 0
  let μ := slim 0 (slim 0 (w/4))
  have hi : 0 < w/4 := by positivity
  have hm : 0 < μ := slim_pos _ (slim_pos _ hi)
  have hl : μ ≤ τ := (slim_le 0 (slim_pos _ hi)).trans ((slim_le _ hi).trans (by linarith))
  let b := payEnd 0 σ
  let c := b * billCon τ 0
  let d := c * payEnd 0 τ
  let e := d * taxWall (Keys 1) w
  let B := b + e * billCon (slim 0 (w/4)) 2
  have hb : 0 ≤ b := payEnd_nonneg hs _
  have hc : 0 ≤ c := mul_nonneg hb (billCon_nonneg ..)
  have hd : 0 ≤ d := mul_nonneg hc (payEnd_nonneg ht _)
  have he : 0 ≤ e := mul_nonneg hd (taxWall_pos hw).le
  have hB : 0 ≤ B := add_nonneg hb (mul_nonneg he (billCon_nonneg ..))
  obtain ⟨u,k,hk,hΩ,hK,H⟩ := independent 1 μ hm (Embedding.refl (Keys 1))
  refine ⟨u,B*k,hk,hΩ.trans (hl.trans hT),mul_nonneg hB hK,fun A s f ha hh hu hy => ?_⟩
  obtain ⟨X,HX,Hj,Hw,Ht⟩ := open_end (clauses (t:=1) f) hs ha (fun i b => hh _) line_uniform
    (fun i j => ((seal_tail i _).1 (hu.loci.2 i j)).1) hu.loci.1 (Or.inl (by norm_num)) (s:=s+2) (fun i b => hy _)
  have hv : Cycles missing 2 (headPress X) := by
    intro p; rw [← press_cob]
    funext a x; unfold headPress; rw [← Ht]
    exact ((seal_tail p _).1 (hu.loci.2 p a)).2 x
  let T : Corn (Keys 1) → Submodule ℂ (Run 0 → ℂ) := fun p => locus0 (clipVars p)
  have hU : Uniforms (Run 0) _ (stick 0) T := var_uniform fun _ _ he => by unfold T; rw [he]
  have hJ : JetWall (s+2) (headPress X) := press_jet Hj
  obtain ⟨Y,hY,yJ,Hy,Hs⟩ := open_end (headPress X) ht
    (mul_nonneg ha hc) (by unfold c; rw [← mul_assoc]; exact press_cost ht HX) hU (press_wall Hw) hv
    (Or.inl (by norm_num)) hJ
  have h₁ : JetWall (s+1) Y := yJ
  obtain ⟨D,hD,Hd,HD,hp⟩ := press_lift Y hw
    (mul_nonneg ha hd) (by unfold d; rw [← mul_assoc]; exact hY) h₁ Hy (by
      intro p hr
      have hh : p=0 := funext fun ⟨i,k⟩ => by
        rw [show i=0 from @Subsingleton.elim (Fin 1) _ _ _]; exact congr_fun hr k
      subst p; funext i x
      exact (rays_at_zero ((hY i x).analytic_real _)).1 ((h₁ i x).weaker (Nat.succ_le_succ s.zero_le)))
  let V := X-cob 2 missing D
  have Vp p : cob 1 missing V (axes p) = clauses f (axes p) := by unfold V; rw [cob_sub,cob_zero,sub_zero, Ht]
  have hV : CostWall μ (A*B) V := by
    unfold B; rw [mul_add, ← mul_assoc]; exact (HX.mono hm hl le_rfl).sub
      (seal_missing hi (show CostWall (w/4) (A*e) D by unfold e; rw [← mul_assoc]; exact hD))
  have Vj : JetWall (s+1) V := fun i x => (Hj i x).sub (miss_jet Hd i x)
  have Hv : wall locus0 V := by
    intro p a; apply (seal_tail p _).2; refine ⟨(lineTail p).sub_mem (Hw p a) (wall_cob missing HD p a),fun i => ?_⟩
    change headPress V (axes p) a i=0
    rw [show V=X-_ from rfl, press_sub,press_cob]
    simp only [Pi.sub_apply]; apply sub_eq_zero.mpr
    rw [Hs]; unfold cob; rw [hp]
  choose W hZ hq hw' using fun i => H (A*B) (s+1) (fun b p => V p i b) (mul_nonneg ha hB)
    (hV i) (Vj i) (fun p => Hv p i)
  refine ⟨fun b => W (b 0) (Fin.tail b), fun i => ?_,fun i => hq _ _,fun p i => ?_⟩
  · rw [← mul_assoc]; exact hZ _ _
  rw [fromCurl_cons]
  simp only [Fin.cons_zero,Fin.tail_cons,plotted]
  rw [show (fun i => projected (strand i) (axes p)) = strands (Embedding.refl (Keys 1)) (axes p) from rfl]
  simp_rw [hw']; change cob 1 missing V (axes p) _ _=_
  rw [Vp]; simp [clauses]
end YM.Stationary
end
