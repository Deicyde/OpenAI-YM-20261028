import YM.AnalyticNext.CUBIC_MATCH.Lift.Turns

set_option warningAsError false

/-!
# The augmentation step in dependent-leg lifting

Evaluate y variables at Laurent identity, here including every coefficient,
with x closure retained. Contracting on the third leg requires changing
stencils across that operation. Unweighted truncations do not give the
needed algebra.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CubicMatch.Lift
open Filter Function Lattice RG Precision Work.F08 Laurent Bloch Exterior Next.Free
open scoped Topology BigOperators

variable {r s t n : ℕ} {η C D θ : ℝ}

abbrev Two (r s : ℕ) := TypeFace r → Line Cover ℝ s

def paceTwo (η C : ℝ) (A : Two r s) := ∀ i : TypeFace r, Price1 η C (A i)

def omitY (A : Three ℝ r 0 s) : Two r s := fun a b x => ∑' y : Cover, A a vac b (x,y)

def zeroY (A : Two r s) : Three ℝ r 0 s := fun a _ b x => if x.2=0 then A a b x.1 else 0

def lowX (A : Two (r+1) s) : Two r s := fun a b => bite step (fun i => A i b) a

def back (a : Axis) : Cover := -step a
def lowZ (A : Two r (s+1)) : Two r s := fun a => bite back (A a)
lemma shift_comm (A : Two (r+1) (s+1)) : lowZ (lowX A)=lowX (lowZ A) := by
  funext i j; exact (bite_comm _ _ A i j).symm

def omitFee (η : ℝ) := share η
lemma omit_price {A : Three ℝ r 0 s} (hη : 0<η) (H : Pace η C A) : paceTwo η (omitFee η*C) (omitY A) := by
  intro a b x
  have ht : Decay size η (C*wanes η (size x)) (fun y => A a vac b (x,y)) := line_slice (H a vac) x b
  have hc := wanes_summable hη; have hsum := ht.summable_norm hc
  refine (norm_tsum_le_tsum_norm hsum).trans ((hsum.tsum_le_tsum ht (hc.mul_left _)).trans_eq ?_)
  unfold omitFee share; rw [tsum_mul_left]; ring
lemma zero_price {A : Two r s} (h : paceTwo η C A) : Pace η C (zeroY A) := by
  rintro a j b ⟨x,y⟩
  change ‖(if y=0 then _ else _)‖ ≤ C * wanes η _
  split
  · rename_i hy; subst y; rw [show length2 (x,0)=size x by simp [length2,size]]; exact h a b x
  rw [norm_zero]; exact mul_nonneg (h a b|>.cash) (wanes_pos ..).le

private lemma summable_slice {w : Couple → ℝ} (h : Decay length2 η C w) (hη : 0 < η) (x : Cover) (c : Couple) :
    Summable fun y : Cover => w ((x,y)-c) := by
  rcases c with ⟨l,r⟩
  have hh : Summable w := (h.summable_norm (summable_two hη)).of_norm
  change Summable fun y : Cover => w (x-l,y-r)
  simp_rw [sub_eq_add_neg]; exact (Equiv.addRight (-r)).summable_iff.mpr (hh.prod_factor (x+-l))

lemma contracted_slice {A : Line Couple ℝ (r+1)} (h : LineRate η C A) (v : Axis → Couple) (he : 0<η)
    (a : TypeFace r) (x : Cover) :
    (∑' y, bite v A a (x,y))=bite (Prod.fst ∘ v) (fun i x => ∑' y : Cover,A i (x,y)) a x := by
  have hb (j : TypeFace (r+1)) : Summable (fun y : Cover => A j (x,y)) := by simpa using summable_slice (h j) he x 0
  unfold bite; simp only [smul_eq_mul]
  have hp (j : TypeFace (r+1)) (w : Axis) := summable_slice (h j) he x (v w)
  rw [Summable.tsum_finsetSum]; swap
  · intro j _; apply summable_sum; intro w _; exact ((hp _ w).sub (hb j)).mul_left _
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Summable.tsum_finsetSum]; swap
  · intro i _; exact ((hp j i).sub (hb j)).mul_left _
  refine Finset.sum_congr rfl (fun u _ => ?_)
  have hh : (∑' y : Cover, A j ((x,y)-v u))=∑' y, A j (x-(v u).1,y) := by
    let f (y : Cover) := A j (x-(v u).1,y)
    have hz := (Equiv.addRight (-(v u).2)).tsum_eq f
    change (∑' y, A j (x-(v u).1,y-(v u).2))=_
    simp_rw [sub_eq_add_neg]; simpa [f,sub_eq_add_neg] using! hz
  rw [tsum_mul_left, (hp j u).tsum_sub (hb j),hh]; rfl
lemma omit_x {A : Three ℝ (r+1) 0 s} (hη : 0<η) (h : Pace η C A) : omitY (δx A)=lowX (omitY A) := by
  funext a b x; exact contracted_slice (A:=fun i => A i vac b) (fun i => h i vac b) aheadX hη a x
lemma omit_z {A : Three ℝ r 0 (s+1)} (hη : 0<η) (h : Pace η C A) : omitY (δz A)=lowZ (omitY A) := by
  funext a b x; exact contracted_slice (A:=A a vac) (h a vac) behind hη b x
lemma omit_y {A : Three ℝ r 1 t} (hη : 0<η) (h : Pace η C A) : omitY (δy A)=0 := by
  funext a b x
  change ∑' y, bite aheadY (fun i => A a i b) vac (x,y)=_
  rw [contracted_slice (A:=fun i => A a i b) (fun i => h a i b) _ hη]; simp [bite,aheadY]
lemma omit_add {A B : Three ℝ r 0 s} (hη : 0<η) (h : Pace η C A)
    (hθ : 0<θ) (g : Pace θ D B) : omitY (A-B)=omitY A-omitY B := by
  funext i j x; exact ((line_slice (h i vac) x j|>.summable_norm (wanes_summable hη)).of_norm).tsum_sub
    (line_slice (g i vac) x j|>.summable_norm (wanes_summable hθ)).of_norm
@[simp] lemma omit_silence : omitY (0:Three ℝ r 0 s)=0 := by funext i j a; simp [omitY]
@[simp] lemma zeroY_silence : zeroY (0:Two r s)=0 := by funext i j a x; simp [zeroY]
lemma omit_zero (A : Two r s) : omitY (zeroY A)=A := by funext a b x; simp [omitY,zeroY]
lemma zero_x (A : Two (r+1) s) : δx (zeroY A)=zeroY (lowX A) := by
  funext a b c x; rcases x with ⟨x,y⟩; by_cases h : y=0 <;> simp only
    [δx,zeroY,lowX,bite,aheadX,Prod.mk_sub_mk,sub_zero,h,if_true,if_false,sub_self,smul_zero,Finset.sum_const_zero]

/-- Negative displacement corresponds to inversion of the one
axis group's Laurent variables (all four axes of the group). -/
def mir (A : Array1 r) : Array1 r := fun a x => A a (-x)
@[simp] lemma mir_back (A : Array1 r) : mir (mir A)=A := by funext a x; simp [mir]
lemma mir_price {A : Array1 r} (h : Price1 η C A) : Price1 η C (mir A) := by
  intro i j; specialize h i (-j); rw [size_neg] at h; exact h
lemma mir_bite (A : Array1 (r+1)) : mir (bite back A)=boundary r (mir A) := by
  funext a x; unfold mir bite back boundary
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_; simp [smul_eq_mul,sub_eq_add_neg,add_comm]

def rear (A : Two r (s+1)) : Two r (s+2) := fun i => mir (Lifted (mir (A i)))
lemma rear_price (r s) (hη : 0<η) : ∃ θ F : ℝ, 0<θ ∧ 0<F ∧ ∀ C ≥ 0, ∀ A : Two r (s+1),
    paceTwo η C A → paceTwo θ (F*C) (rear A) := by
  obtain ⟨θ,F,hθ,hF,H⟩ := preRise (r:=s) hη
  exact ⟨θ,F,hθ,hF,fun C he A h i => mir_price (H _ _ he (mir_price (h i)))⟩
lemma rear_cross {A : Two r (s+1)} (hη : 0<η) (h : paceTwo η C A) (he : lowZ A=0) : lowZ (rear A)=A := by
  funext i
  change bite back (mir (Lifted (mir _)))=A i
  rw [← mir_back (bite _ _),mir_bite,mir_back, single_lift ((mir_price (h i)).whole hη),mir_back]
  rw [← mir_bite, show bite back (A i)=0 from congr_fun he i]; rfl
lemma ceiling {A : Two r 4} (hη : 0<η) (h : paceTwo η C A) (he : lowZ A=0) : A=0 := by
  letI : IsEmpty (TypeFace 5) := ⟨fun i => by have hi := Finset.card_le_univ i.val; rw [i.property] at hi; simp [Axis] at hi⟩
  rw [← rear_cross (s:=3) hη h he]
  funext i j x; change (∑ a : TypeFace 5, ∑ b : Axis, left ℝ 4 b a j • ((rear A) i a (x-back b)-(rear A) i a x))=0
  exact Finset.sum_of_isEmpty _
lemma low_price {A : Two (r+1) s} (hη : 0<η) (h : paceTwo η C A) :
    paceTwo η (omitFee η*(stepFee η aheadX r*C)) (lowX A) := by
  rw [← omit_zero A,← omit_x hη (zero_price h)]
  exact omit_price hη ((zero_price h).x hη.le)
lemma rear_keeps {A : Two (r+1) 3} (hη : 0<η) (h : paceTwo η C A) (hv : 0≤C) (he : lowZ A=0)
    (hb : lowX A=0) : lowX (rear A)=0 := by
  obtain ⟨θ,F,hθ,-,H⟩ := rear_price (r+1) 2 hη
  have hh : lowZ (lowX (rear (s:=2) A))=0 := by rw [shift_comm, rear_cross hη h he,hb]
  exact ceiling hθ (low_price hθ (H _ hv A h)) hh

/-- Use the zero-value primitive in the evaluated-at-one condition, with
price and preservation of x closure. -/
def restore (A : Three ℝ r 0 s) : Three ℝ r 1 s := fun i j a => runY fromZero (fun b => A i b a) j
lemma restore_cross {A : Three ℝ r 0 s} (hη : 0<η) (h : Pace η C A) (he : omitY A=0) : δy (restore A)=A := by
  funext i j a x; rcases x with ⟨x,y⟩; let M := fun (k : TypeFace 0) v => A i k a (x,v)
  have hm := vacuum_lift (A:=M) ((line_slice (A:=fun k => A i k a) (fun k => h i k a) x).whole hη)
    (congr_fun (congr_fun (congr_fun he i) a) x)
  rw [δy, pure_y]
  exact congr_fun (congr_fun hm j) y
lemma restore_keep {A : Three ℝ (r+1) 0 s} (hη : 0<η) (h : Pace η C A) (he : δx A=0) : δx (restore A)=0 := by
  funext i j a x
  let T := fun (b : TypeFace (r+1)) (j : TypeFace 0) => A b j a
  have hx (b) : LineRate _ _ (T b) := fun u => h b u a
  change bite aheadX (fun b => runY fromZero (T b) j) i x=_
  rw [empty_single.untouched (A:=T) hη hx]; have ht : (fun k : TypeFace 0 => bite aheadX (fun b => T b k) i)=0 :=
    funext fun k => congr_fun (congr_fun (congr_fun he i) k) a
  rw [ht]; change fromZero 0 _ _=0; rw [empty_single.zero_value]; rfl
lemma restore_price (r s) (hη : 0<η) : ∃ θ D : ℝ, 0<θ ∧ 0<D ∧ ∀ C ≥0, ∀ A : Three ℝ r 0 s, Pace η C A →
    Pace θ (D*C) (restore A) := by
  obtain ⟨θ,D,hθ,hD,H⟩ := line_cost empty_single hη
  exact ⟨θ,D,hθ,hD,fun C hp A h i j a => H (fun b => A i b a) _ hp (fun k => h i k a) j⟩
end YM.CubicMatch.Lift
