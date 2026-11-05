import YM.AnalyticNext.CUBIC_MATCH.Lift.Boundary
import YM.AnalyticNext.CUBIC_MATCH.Lift.Stocks

set_option warningAsError false

/-!
# Same prescription in one independent group or sheared while retaining x closures

Right inverse statements are on COVER cycles. Here we do not mix an analytic
adjoint convention with numerical Hermitian. The shear brings a dependent
boundary to a literal forward `+` dual-stencil translation. Costs among
input and output both on the real coefficient norm. These operators can
leave terms unsymmetrized; don't infer a kernel symmetry from price alone.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CubicMatch.Lift
open Filter Function Lattice RG Precision Work.F08 Laurent Bloch Exterior Next.Free
open scoped Topology BigOperators

variable {r s t n : ℕ} {η C F θ : ℝ}

def runY (U : Array1 r → Array1 s) (A : Line Couple ℝ r) : Line Couple ℝ s := fun i p =>
    U (fun j y => A j (p.1,y)) i p.2

def flipped (A : Line Couple ℝ r) : Line Couple ℝ r := fun i p => A i p.swap

def LineRate (η C : ℝ) (A : Line Couple ℝ r) := ∀ i, Decay length2 η C (A i)


lemma line_slice {A : Line Couple ℝ r} (h : LineRate η C A) (x : Cover) :
    Price1 η (C*wanes η (size x)) (fun j y => A j (x,y)) := fun i y => by
  have hh := h i (x,y); change _ ≤ C*wanes η (size x+size y) at hh
  rw [wanes_splits,← mul_assoc] at hh; exact hh
lemma line_flip {A : Line Couple ℝ r} (h : LineRate η C A) : LineRate η C (flipped A) := by
  rintro i ⟨x,y⟩; exact (h i (y,x)).trans_eq (by rw [show length2 (y,x)=length2 (x,y) from Nat.add_comm ..])
lemma line_cost {U : Array1 r → Array1 s} (h : Single r s U) (hη : 0<η) :
    ∃ θ F : ℝ, 0<θ ∧ 0<F ∧ ∀ A : Line Couple ℝ r, ∀ C ≥ 0, LineRate η C A → LineRate θ (F*C) (runY U A) := by
  obtain ⟨θ,F,hθ,hF,H⟩ := h.price η hη
  let σ := min η θ; have ht : 0<σ := lt_min hη hθ
  refine ⟨σ,F,ht,hF,fun A C hC h => ?_⟩
  rintro i ⟨x,y⟩
  have he := (H _ _ (mul_nonneg hC (wanes_pos ..).le) (line_slice h x)) i
  change _ ≤ (F*C)*wanes σ (size x+size y)
  rw [wanes_splits,← mul_assoc]
  apply he.mono (min_le_right ..) ?_ (mul_nonneg (mul_nonneg hF.le hC) (wanes_pos ..).le) y
  rw [← mul_assoc]; refine mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) (mul_nonneg hF.le hC)
  apply mul_le_mul_of_nonneg_right (neg_le_neg (min_le_left ..)); positivity

namespace Single
variable {U : Array1 r → Array1 s} (h : Single r s U)
include h
lemma zero_value : U 0=0 := by
  simpa only [zero_smul] using (h.smul (0:Array1 r) 0 (show Whole (emptyPrefix 0) from barren_whole))
lemma grant_sub {A B : Array1 r} (he : Whole (emptyPrefix A)) (hp : Whole (emptyPrefix B)) : U (A-B)=U A-U B := by
  have hh (T : Array1 r) : -T=(-1:ℝ) • T := by rw [neg_one_smul]
  rw [sub_eq_add_neg,hh,h.add _ _ he (hp.weight (-1)),h.smul _ _ hp,neg_one_smul,sub_eq_add_neg]
omit h in
lemma prefixes {ι : Type*} (R : ι → Array1 r) (k : Finset ι) (p : ∀ i ∈ k, Whole (emptyPrefix (R i))) : Whole (emptyPrefix (∑ i∈k,R i)) := by
  classical
  induction k using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact barren_whole
  | @insert a l hi ih =>
    have he := (Finset.forall_mem_insert _ _ _).mp p
    have hh := he.1.plus (ih he.2)
    rw [plus_rows] at hh; rw [Finset.sum_insert hi]; exact hh
lemma grant_sum {ι : Type*} (R : ι → Array1 r) (k : Finset ι) (p : ∀ i ∈ k, Whole (emptyPrefix (R i))) :
    U (∑ i∈k,R i)=∑ i∈k,U (R i) := by
  classical
  induction k using Finset.induction_on with
  | empty => simp [h.zero_value]
  | @insert a l hi ih =>
    have he := (Finset.forall_mem_insert _ _ _).mp p
    rw [Finset.sum_insert hi, Finset.sum_insert hi, h.add _ _ he.1 (prefixes _ _ he.2),ih he.2]

/-- Lift acts pointwise in the other group. Thus closure is preserved there
*while* doing this, even though division in the active group loses control
of its own contraction (needs cycles) and width. -/
lemma untouched {A : TypeFace (t+1) → Line Couple ℝ r} (hη : 0<η) (hA : ∀ i, LineRate η C (A i))
    (i : TypeFace t) (k : TypeFace s) :
    bite aheadX (fun b => runY U (A b) k) i = runY U (fun a => bite aheadX (fun b => A b a) i) k := by
  funext ⟨x,y⟩
  let f (x : Cover) (k : TypeFace (t+1)) := fun (a : TypeFace r) (v : Cover) => A k a (x,v)
  have H x k : Whole (emptyPrefix (f x k)) := (line_slice (hA k) x).whole hη
  let S (b : TypeFace (t+1)) (a : Axis) := left ℝ t a b i • (f (x-step a) b-f x b)
  have hp (b c) : Whole (emptyPrefix (S b c)) := ((H _ _).minus (H _ _)).weight _
  unfold bite runY
  dsimp only
  rw [show (fun (j : TypeFace r) (y : Cover) => ∑ c : TypeFace (t+1), ∑ a : Axis, Exterior.left ℝ t a c i •
    (A c j ((x,y)-aheadX a)-A c j (x,y))) = ∑ c : TypeFace (t+1), ∑ a : Axis, S c a from ?eq]
  rw [h.grant_sum _ _ (fun i _ => prefixes _ _ (fun k _ => hp i k)),Finset.sum_apply,Finset.sum_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [h.grant_sum _ _ (fun j _ => hp b j),Finset.sum_apply,Finset.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  have he : U (S b a) = left ℝ t a b i • (U (f (x-step a) b)-U (f x b)) :=
    (h.smul _ _ ((H (x-step a) b).minus (H x b))).trans (congr_arg (left ℝ t a b i • ·) (h.grant_sub (H (x-step a) b) (H x b)))
  rw [he]
  simp only [aheadX, Prod.snd_sub,Prod.fst_sub,sub_zero]; rfl
  case eq =>
    funext j y
    simp only [S,aheadX, Finset.sum_apply,Pi.smul_apply,Pi.sub_apply,f]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    simp only [Prod.mk_sub_mk,sub_zero]
end Single

lemma pure_y (A : Line Couple ℝ (r+1)) (x y : Cover) (i : TypeFace r) :
    bite aheadY A i (x,y)=boundary r (fun b z => A b (x,z)) i y := by
  unfold bite aheadY boundary; simp only [Prod.mk_sub_mk,sub_zero,smul_eq_mul]

lemma pure_dynamic {A : Line Couple ℝ (r+1)} (h : LineRate η C A) (hη : 0<η)
    (hp : bite aheadY A=0) : bite aheadY (runY Lifted A)=A := by
  funext i p; rcases p with ⟨x,y⟩
  have ht : boundary r (fun b z => A b (x,z))=0 := by
    funext b z; rw [← pure_y, hp]; rfl
  have he := single_lift ((line_slice h x).whole hη) ht
  rw [pure_y]; exact congr_fun (congr_fun he i) y

lemma pure_closed {A : Line Couple ℝ (r+2)} (h : LineRate η C A) (hη : 0<η) :
    bite aheadY (bite aheadY A)=0 := by
  funext i p; rcases p with ⟨x,y⟩
  let K : Array1 (r+2) := fun b z => A b (x,z)
  have hp : Whole (emptyPrefix K) := (line_slice h x).whole hη
  have hh : emptyPrefix (boundary r (boundary (r+1) K))=0 := by
    have ht := hp.prod (Whole.boundary (r+1))
    rw [boundary_rows,boundary_rows]
    apply bank_injective (ht.prod (Whole.boundary r)).safe barren_whole.safe; intro c
    rw [ht.acts (Whole.boundary _) _, hp.acts (Whole.boundary _) _, Matrix.mul_assoc,
      show ((cobound (r+1)).acts c * (cobound r).acts c) = 0 from closed r c,Matrix.mul_zero,barren_acts]
  rw [pure_y]; simp_rw [pure_y]
  exact congr_fun (congr_fun (congr_fun hh ()) i) y

/-- Involutive. Exponents sheared, no complex argument conventions. -/
def shear : Couple ≃+ Couple :=
    { toFun := fun x => (x.1-x.2,-x.2)
      invFun := fun x => (x.1-x.2,-x.2)
      map_add' := fun ⟨x,y⟩ ⟨a,b⟩ => by dsimp; ext1 <;> dsimp <;> abel
      left_inv := fun ⟨a,b⟩ => by simp
      right_inv := fun ⟨a,b⟩ => by simp }

def sheared (A : Line Couple ℝ r) : Line Couple ℝ r := fun i x => A i (shear x)

@[simp] lemma shear_involutive (A : Line Couple ℝ r) : sheared (sheared A)=A := by
  funext i x; exact congr_arg _ (shear.left_inv x)
lemma shear_zero : sheared (0:Line Couple ℝ r)=0 := by rfl
lemma shear_cost {A : Line Couple ℝ r} (h : LineRate η C A) (hη : 0≤η) : LineRate (η/2) C (sheared A) := by
  rintro i ⟨x,y⟩
  have he : size x ≤ size (x-y)+size y := by simpa only [sub_add_cancel] using size_add (x-y) y
  specialize h i
  refine (h (shear (x,y))).trans (mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) h.cash)
  change -(η)*(length2 (x-y,-y) : ℝ) ≤ _
  have hv : (size x:ℝ) ≤ size (x-y)+(size y:ℝ) := by exact_mod_cast he
  unfold length2
  rw [size_neg]; push_cast
  nlinarith [Nat.cast_nonneg (α:=ℝ) (size (x-y))]

lemma shear_cross (A : Line Couple ℝ (r+1)) : bite aheadY (sheared A)=sheared (bite behind A) := by
  funext i x
  have he (i : Axis) : shear (aheadY i)=behind i := by simp [shear,aheadY,behind]
  change bite aheadY (fun i => A i ∘ (shear:Couple → Couple)) i x=_
  simp_rw [permute, he]; rfl
lemma shear_keep (A : Line Couple ℝ (r+1)) : bite aheadX (sheared A)=sheared (bite aheadX A) := by
  funext i x
  have he (i : Axis) : shear (aheadX i)=aheadX i := by simp [shear,aheadX]
  change bite aheadX (fun i => A i ∘ (shear:Couple → Couple)) i x=_
  simp_rw [permute,he]; rfl

/-- First primitive in dependent momentum with no closures except the
one at x. -/
def gainZ (A : Three ℝ r s (n+1)) : Three ℝ r s (n+2) :=
    fun i j => sheared (runY Lifted (sheared (A i j)))

lemma gainZ_cost (r s n) (hη : 0<η) : ∃ θ F : ℝ, 0<θ ∧ 0<F ∧ ∀ C ≥ 0,
    ∀ A : Three ℝ r s (n+1), Pace η C A → Pace θ (F*C) (gainZ A) := by
  obtain ⟨θ,F,hθ,hF,H⟩ := line_cost (lifted_single n) (half_pos hη)
  exact ⟨θ/2,F,half_pos hθ,hF,fun C hC A hp i j => shear_cost (H _ C hC (shear_cost (hp i j) hη.le)) hθ.le⟩
lemma gainZ_cross {A : Three ℝ r s (n+1)} (hp : Pace η C A) (hη : 0<η) (hA : δz A=0) :
    δz (gainZ A)=A := by
  funext i j
  have h : LineRate _ _ _ := shear_cost (hp i j) hη.le
  have hh : bite aheadY (sheared (A i j))=0 := by
    rw [shear_cross,show bite behind (A i j)=0 from congr_fun (congr_fun hA i) j,shear_zero]
  have he := pure_dynamic h (half_pos hη) hh
  change bite behind (sheared _)=_
  calc
    _ = sheared (bite aheadY (runY Lifted (sheared (A i j)))) := by
          conv_rhs => rw [← shear_involutive (runY Lifted (sheared (A i j))),shear_cross,shear_involutive]
    _ = _ := by rw [he,shear_involutive]

lemma gainZ_kept {A : Three ℝ (t+1) s (n+1)} (h : Pace η C A) (hη : 0<η) (he : δx A=0) :
    δx (gainZ A)=0 := by
  funext i j k x
  let M (b : TypeFace (t+1)) := sheared (A b j)
  have hh b := shear_cost (h b j) hη.le
  let Q := fun a : TypeFace (n+1) => bite aheadX (fun b => M b a) i
  have hM : Q=0 := by
    funext a y
    have ht := shear_keep (fun b => A b j a)
    change bite aheadX (sheared (fun b => A b j a)) i y=0
    rw [ht]; exact congr_fun (congr_fun (congr_fun (congr_fun he i) j) a) (shear y)
  have ht : bite aheadX (fun b => runY Lifted (M b) k) i=0 := by
    rw [(lifted_single n).untouched (A:=M) (half_pos hη) hh]
    change runY Lifted Q k=0; rw [hM]
    funext p
    change Lifted (0:Array1 (n+1)) k p.2=0; rw [(lifted_single n).zero_value]; rfl
  change bite aheadX (sheared (fun b => runY Lifted (M b) k)) i x=_
  rw [shear_keep,sheared,ht]; rfl

lemma zz {A : Three ℝ r s (t+2)} (h : Pace η C A) (hη : 0<η) : δz (δz A)=0 := by
  funext i j
  change bite behind (bite behind (A i j))=0
  have he := pure_closed (shear_cost (h i j) hη.le) (half_pos hη)
  rw [shear_cross,shear_cross] at he
  rw [← shear_involutive (bite _ _),he,shear_zero]

lemma bite_ind {A : Line Couple ℝ (n+1)} : bite aheadY (flipped A)=flipped (bite aheadX A) := by
  funext i x; have he := permute A AddEquiv.prodComm aheadY i x
  change bite aheadY _ _ _=bite (fun j => (aheadY j).swap) A i x.swap at he
  rw [show (fun j => (aheadY j).swap)=aheadX from funext fun _ => rfl] at he; exact he
lemma bite_dep {A : Line Couple ℝ (n+1)} : bite aheadX (flipped A)=flipped (bite aheadY A) := by
  have he := congr_arg flipped (bite_ind (A:=flipped A)); exact he.symm

def gainX (A : Three ℝ (r+1) s t) : Three ℝ (r+2) s t := fun i j b =>
    flipped (runY Lifted (flipped (fun a => A a j b))) i
lemma gainX_cost (r s t) (hη : 0<η) : ∃ θ F : ℝ, 0<θ ∧ 0<F ∧ ∀ C ≥ 0, ∀ A : Three ℝ (r+1) s t,
    Pace η C A → Pace θ (F*C) (gainX A) := by
  obtain ⟨θ,F,hp,hF,H⟩ := line_cost (lifted_single r) hη
  exact ⟨θ,F,hp,hF,fun C hC A p i j b => line_flip (H _ C hC (line_flip (A:=fun i => A i j b) (fun i => p i j b))) i⟩
lemma gainX_cross {A : Three ℝ (r+1) s t} (h : Pace η C A) (hη : 0<η) (hh : δx A=0) :
    δx (gainX A)=A := by
  funext i j a
  let M := fun i : TypeFace (r+1) => A i j a
  have hx : bite aheadX M=0 := funext fun b => congr_fun (congr_fun (congr_fun hh b) j) a
  change bite aheadX (flipped (runY Lifted (flipped M))) _ = _
  rw [bite_dep, pure_dynamic (line_flip (A:=M) (fun b => h b j a)) hη (by rw [bite_ind,hx]; rfl)]; rfl
lemma gainX_kept {A : Three ℝ (r+1) (s+1) t} (h : Pace η C A) (hη : 0<η) (hh : δy A=0) :
    δy (gainX A)=0 := by
  funext i j a x
  let M := fun b : TypeFace (s+1) => flipped (fun i => A i b a)
  have he : ∀ b, LineRate _ _ (M b) := fun b => line_flip (fun i => h i b a)
  let Q := fun i : TypeFace (r+1) => bite aheadX (fun b => M b i) j
  have hx : Q=0 := by
    funext v w
    change bite aheadX (flipped (fun b => A v b a)) j w=_
    rw [bite_dep]; exact congr_fun (congr_fun (congr_fun (congr_fun hh v) j) a) w.swap
  change bite aheadY (flipped (fun b => runY Lifted (M b) i)) j x=_
  rw [bite_ind]; unfold flipped; rw [(lifted_single r).untouched (A:=M) hη he]
  change runY Lifted Q _ _=0; rw [hx]
  change Lifted (0:Array1 (r+1)) _ _=0; rw [(lifted_single r).zero_value]; rfl

def gainY (A : Three ℝ r (s+1) t) : Three ℝ r (s+2) t := fun i j a => runY Lifted (fun k => A i k a) j
lemma gainY_cost (r s t) (hη : 0<η) : ∃ θ F : ℝ, 0<θ ∧ 0<F ∧ ∀ C ≥ 0, ∀ A : Three ℝ r (s+1) t,
    Pace η C A → Pace θ (F*C) (gainY A) := by
  obtain ⟨θ,F,hp,hF,H⟩ := line_cost (lifted_single s) hη
  exact ⟨θ,F,hp,hF,fun C hC A p i j b => H (fun j => A i j b) C hC (fun k => p i k b) j⟩
lemma gainY_cross {A : Three ℝ r (s+1) t} (h : Pace η C A) (hη : 0<η) (he : δy A=0) :
    δy (gainY A)=A := by
  funext i j a; exact congr_fun (pure_dynamic (A:=fun b => A i b a) (fun k => h i k a) hη
    (funext fun b => congr_fun (congr_fun (congr_fun he i) b) a)) j
end YM.CubicMatch.Lift
