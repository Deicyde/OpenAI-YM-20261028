import YM.Analysis.Polydisc
import YM.Cells.Corrected
import YM.Next.RANK.Gaussian
import YM.Next.RANK.Value
import YM.Pressure.Seeds

/-!
# Real Taylor tests on forward lattice

Literal unit-cell integration of `takeCurl` at positive face coords. `curl`
links read along positive open intervals; top differences of order j give exact
homogeneous jet, higher orders zero. Closure from Stokes. This avoids claiming a
sampling (not integrated) correction satisfies d. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.CellsInt
open Maxwell Tensor Labels Lattice MeasureTheory Filter Set Function
open scoped Topology BigOperators ContDiff Classical

variable {G : Gauge} {i j k : ℕ}
variable {V W : Type*}

def next [AddCommGroup V] (i : Axis) (f : E4 → V) : E4 → V := fun x => f (x+basis i)- f x

section
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

def east (i : Axis) (f : E4 → V) (x : E4) := ∫ t : ℝ in 0..1,f (x+t • basis i)
omit [CompleteSpace V] in
lemma east_smooth (i : Axis) {f : E4 → V} (h : Continuous f) : Continuous (east i f) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous _ continuous_const; unfold Function.uncurry; fun_prop
lemma east_const (i : Axis) (v : V) : east i (fun _ => v) = fun _ => v := by ext1 x; simp [east]
omit [NormedSpace ℝ V] [CompleteSpace V] in
lemma east_int (i : Axis) (x) {f : E4 → V} (h : Continuous f) : IntervalIntegrable (fun t : ℝ => f (x+t • basis i)) volume 0 1 := Continuous.intervalIntegrable (by fun_prop) _ _
omit [CompleteSpace V] in
lemma east_add (i : Axis) {f g : E4 → V} (h : Continuous f) (hp : Continuous g) : east i (f+g)=east i f+east i g := funext fun x => intervalIntegral.integral_add (east_int i x h) (east_int i x hp)
omit [CompleteSpace V] in
lemma east_sub (i : Axis) {f g : E4 → V} (h : Continuous f) (hp : Continuous g) : east i (f-g) = east i f-east i g := funext fun x => intervalIntegral.integral_sub (east_int i x h) (east_int i x hp)
omit [CompleteSpace V] in
lemma east_scale (a : ℝ) (i : Axis) (f : E4 → V) : east i (a • f)=a • east i f := funext fun x => intervalIntegral.integral_smul a (fun t => f (x+t • basis i))
omit [CompleteSpace V] in
lemma next_east (i a : Axis) {f : E4 → V} (h : Continuous f) : next i (east a f) = east a (next i f) := by
  have he : next i f=(fun x => f (x+basis i))-f := rfl
  rw [he,east_sub a (by fun_prop) h]; apply funext; intro x
  simp only [east,next,Pi.sub_apply, add_right_comm x (basis i)]
omit [CompleteSpace V] in
lemma exchange (i j : Axis) (f : E4 → V) (h : Continuous f) : east i (east j f)=east j (east i f) := by
  funext x; simp only [east, intervalIntegral.integral_of_le zero_le_one]
  let F (p : ℝ) (q : ℝ) := f (x+p • basis i+q • basis j)
  have hx : Continuous (uncurry F) := by unfold Function.uncurry F; fun_prop
  have hi : Integrable (uncurry F) (((volume : Measure ℝ).restrict (Ioc 0 1)).prod (volume.restrict (Ioc 0 1))) := by
    rw [Measure.prod_restrict]
    exact (hx.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set (show Ioc _ _ ×ˢ Ioc _ _ ⊆ Icc _ _ ×ˢ Icc _ _ from Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have he := integral_integral_swap hi
  dsimp only [F] at he; rw [he]; simp only [add_right_comm x (_ • basis i)]

lemma lights (f : E4 → V) (h : ContDiff ℝ 1 f) (i : Axis) : east i (grad i f)=next i f := by
  have ht : Continuous (grad i f) := (h.continuous_fderiv one_ne_zero).clm_apply continuous_const
  ext1 x; unfold next
  let g (t : ℝ) := x+t • basis i
  have hg (r : ℝ) : HasDerivAt g (basis i) r := by
    simpa only [one_smul, id_eq,Pi.smul_apply,zero_smul] using (hasDerivAt_id r).smul_const (basis i)|>.const_add x
  have hInt : east i (grad i f) x=f (g 1)-f (g 0) := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => ((h.differentiable one_ne_zero (g r)).hasFDerivAt.comp_hasDerivAt r (hg r))) (east_int _ _ ht)
  rw [hInt]; simp [g]
end

def mapZ (z : Cover) : E4 := WithLp.toLp 2 (fun i => (z i:ℝ))
lemma mapZ_step (z : Cover) (i : Axis) : mapZ (z+step i) = mapZ z+basis i := by ext1 k; simp [mapZ]

section
variable [AddCommGroup V]

def stepValue (f : Cover → V) (i : Axis) : Cover → V := fun z => f (z+step i)-f z
lemma sends (f : E4 → V) (i : Axis) : stepValue (f ∘ mapZ) i=(next i f) ∘ mapZ := by ext1 z; simp [stepValue,next,mapZ_step]

def jumps : (n : ℕ) → (Fin n → Axis) → (Cover → V) → (Cover → V)
  | 0, _,f => f
  | n+1,l,f => jumps n (Fin.tail l) (stepValue f (l 0))
lemma steps (n : ℕ) (i : Axis) (t : Fin n → Axis) (f : Cover → V) : jumps (n+1) (Fin.cons i t) f=jumps n t (stepValue f i) := by rw [jumps]; simp only [Fin.tail_cons, Fin.cons_zero]
lemma hop (i j : Axis) (f : Cover→V) : stepValue (stepValue f i) j = stepValue (stepValue f j) i := by funext x; simp only [stepValue]; rw [add_right_comm x (step i)]; abel
lemma hopped (n : ℕ) (k : Axis) (t : Fin n → Axis) (f : Cover→V) : jumps n t (stepValue f k)=stepValue (jumps n t f) k := by
  induction n generalizing f with
  | zero => rfl
  | succ n h => rw [jumps,hop,jumps,h]
lemma jumps_sub (n : ℕ) (t) (x y : Cover→V) : jumps n t (x-y)=jumps n t x-jumps n t y := by
  induction n generalizing x y with
  | zero => rfl
  | succ n h =>
    have he i : stepValue (x-y) i= stepValue x i-stepValue y i := by funext z; simp only [stepValue,Pi.sub_apply]; abel
    rw [jumps,he,h,jumps,jumps]
end

section
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

def strides : (n : ℕ) → (Fin n → Axis) → (E4 → V) → (E4 → V)
  | 0, _,f => f
  | n+1,l,f => strides n (Fin.tail l) (next (l 0) f)
omit [NormedSpace ℝ V] [CompleteSpace V] in
lemma steps_east {n : ℕ} (t : Fin n → Axis) (f : E4 → V) : jumps n t (f ∘ mapZ)=(strides n t f) ∘ mapZ := by
  induction n generalizing f with
  | zero => rfl
  | succ n h => rw [jumps, strides,sends,h]
omit [CompleteSpace V] in
lemma strides_smul (n : ℕ) (t : Fin n→Axis) (f : E4 → V) (a : ℝ) : strides n t (a • f) = a • strides n t f := by
  induction n generalizing f with
  | zero => rfl
  | succ n h => rw [strides, strides,show next _ (a • f)= a • next _ f from funext (fun x => (smul_sub a (f (_+_)) _).symm),h]

omit [CompleteSpace V] in
lemma strides_east (n : ℕ) (t) (i : Axis) (f : E4 → V) (h : Continuous f) : strides n t (east i f)=east i (strides n t f) := by
  induction n generalizing f with
  | zero => rfl
  | succ n H => rw [strides,next_east _ _ h,strides,H]; unfold next; fun_prop

lemma head {n : ℕ} (A : T E4 V n) (h : Sym A) (t : Fin n → Axis) : strides n t (diagonal A)=fun _ => (n.factorial:ℝ) • A (YM.basis ∘ t) := by
  induction n with
  | zero =>
    funext x; rw [strides, Nat.factorial_zero, Nat.cast_one,one_smul]
    exact congr_arg A (Subsingleton.elim ..)
  | succ n H =>
    let i:=t 0; let B:= A.curryLeft (YM.basis i)
    have he : next i (diagonal A) = east i (((n+1:ℕ):ℝ) • (diagonal B)) := by
      rw [← lights _ (diag_smooth A 1) i]
      exact congr_arg (east i) (funext (fun x => by
        change fderiv ℝ (diagonal A) x _ = _; rw [differential_diagonal A h]; rw [← Nat.cast_smul_eq_nsmul ℝ]; rfl))
    have hh : Continuous (diagonal B) := (diag_smooth B 1).continuous
    rw [strides, he, strides_east _ _ i _ (hh.const_smul _),strides_smul, H _ (freeze_sym A h _), east_scale,east_const]
    have hv : A (basis ∘ t)=B (basis ∘ Fin.tail t) := congr_arg A (by
      ext s; refine Fin.cases ?_ (fun k => ?_) s <;> rfl)
    funext x; simp only [hv,Pi.smul_apply,smul_smul,Nat.factorial_succ,Nat.cast_mul]; rfl
end

-- Now actual Key slot integration.

def foil {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (A : TwoJet V i) (a b : Axis) := east a (east b (diagonal (A a b))) ∘ mapZ
def test (A : Taylor G i) (a b : Axis) : Cover→G.Color := foil (takeCurl A) a b

def trail (A : Taylor G i) (a : Axis) := east a (A.value a) ∘ mapZ
lemma cigar (A : Taylor G i) (a b : Axis) : test A a b = stepValue (trail A b) a - stepValue (trail A a) b := by
  have h i (m : WithTop ℕ∞) : ContDiff ℝ m (A.value i) := diag_smooth ..
  have he i j : Continuous (grad j (A.value i)) := ((h i 1).continuous_fderiv one_ne_zero).clm_apply continuous_const
  unfold test foil trail; rw [takeCurl_diag,east_sub b (he ..) (he ..),east_sub a (east_smooth _ (he ..)) (east_smooth _ (he ..)), exchange a b _ (he b a),
    lights (A.value a) (h a 1) b, lights (A.value b) (h b 1) a, sends, sends, next_east _ _ (h a 1).continuous,next_east _ _ (h b 1).continuous]; rfl
lemma test_top (A : Taylor G i) (v : Fin i → Axis) (a b : Axis) (z) : jumps i v (test A a b) z=
    (i.factorial:ℝ) • takeCurl A a b (basis ∘ v) := by
  have he := (diag_smooth (takeCurl A a b) 1).continuous
  unfold test foil; rw [steps_east,strides_east _ _ _ _ (east_smooth b he),strides_east _ _ _ _ he,head _ ((closedCurl A).coeffSym a b),east_const,east_const]; rfl
lemma stencil (A : Taylor G i) (a b c : Axis) :
    stepValue (test A b c) a+stepValue (test A c a) b+stepValue (test A a b) c=0 := by
  have he (a) (x y : Cover→G.Color) : stepValue (x-y) a=stepValue x a-stepValue y a := by funext x;simp only [stepValue,Pi.sub_apply];abel
  simp only [cigar,he]; rw [hop b a,hop c a,hop c b]; abel
end YM.Next.Rank.CellsInt
