import YM.AnalyticNext.CUBIC_MATCH.Lift.Count

set_option warningAsError false

/-!
# Separate and dependent contractions, on the cover coefficients

Real, vector-valued. Forward primal difference corresponds to `x-step`
as below on the stored dual coefficient. Can even translate by a vector
in a joint cover space, so last momentum here need not be independent.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CubicMatch.Lift

open Filter Function Lattice RG Precision  Laurent Bloch Exterior Matrix
open scoped Topology BigOperators

variable {E D : Type*} [AddCommGroup E] [Module ℝ E]
variable [AddCommGroup D]
variable {ι : Type*} {r s t : ℕ}

abbrev Line (D E : Type*) (r : ℕ) := TypeFace r → D → E

def bite (w : Axis → D) (A : Line D E (r+1)) (b : TypeFace r) (x : D) :=
    ∑ k : TypeFace (r+1), ∑ i : Axis, left ℝ r i k b • (A k (x-w i)-A k x)

lemma bite_add (w : Axis → D) (A B : Line D E (r+1)) : bite w (A+B)=bite w A+bite w B := by
  funext i x; simp only [bite, Pi.add_apply]
  simp_rw [add_sub_add_comm,smul_add,Finset.sum_add_distrib]
lemma bite_sub (w : Axis → D) (A B : Line D E (r+1)) : bite w (A-B)=bite w A-bite w B := by
  funext i x; simp only [bite, Pi.sub_apply]
  have e (b : TypeFace (r+1)) (z : Axis) :
      A b (x-w z)-B b (x-w z)-(A b x-B b x)=(A b (x-w z)-A b x)-(B b (x-w z)-B b x) := by abel_nf
  simp_rw [e,smul_sub,Finset.sum_sub_distrib]

lemma bite_zero (w : Axis → D) : bite w (0 : Line D E (r+1))=0 := by funext i x; simp [bite]
lemma bite_sum (w : Axis → D) (A : ι → Line D E (r+1)) (q : Finset ι) :
    bite w (∑ i∈q,A i)=∑ i∈q,bite w (A i) := by
  classical
  induction q using Finset.induction_on with
  | empty => rw [Finset.sum_empty,Finset.sum_empty,bite_zero]
  | @insert a q h ih => rw [Finset.sum_insert h, Finset.sum_insert h,bite_add, ih]
lemma bite_map {M : Type*} [AddCommGroup M] [Module ℝ M] (w : Axis → D)
    (A : Line D E (r+1)) (L : E →ₗ[ℝ] M) (i : TypeFace r) (x : D) :
    L (bite w A i x)=bite w (fun j x => L (A j x)) i x := by simp only [bite,map_sum,map_sub,map_smul]

lemma bite_comm (w v : Axis → D) (A : TypeFace (r+1) → Line D E (s+1)) (i j : _) :
    bite w (fun a => bite v (A a) j) i=bite v (fun a => bite w (fun b => A b a) i) j := by
  funext x
  have he (z : D → E) (a b : Axis) : z (x-w a-v b) - z (x-w a)-(z (x-v b)-z x)=
      z (x-v b-w a)-z (x-v b) - (z (x-w a)-z x) := by rw [sub_right_comm x]; abel_nf
  unfold bite
  simp only [← Finset.sum_sub_distrib, Finset.smul_sum, ← smul_sub]
  calc
    _ = ∑ a : TypeFace (r+1), ∑ b : TypeFace (s+1), ∑ c : Axis, ∑ d : Axis,
        left ℝ r c a i • left ℝ s d b j •
          (A a b (x-w c-v d)-A a b (x-w c)-(A a b (x-v d)-A a b x)) := by
            refine Finset.sum_congr rfl fun a _ => ?_; rw [Finset.sum_comm]
    _ = _ := by
      rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun a _ => ?_
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
      rw [he,smul_comm]



abbrev Three (E : Type*) (r s t : ℕ) := TypeFace r → TypeFace s → TypeFace t → Couple → E

def aheadX (s : Axis) : Couple := (step s,0)
def aheadY (s : Axis) : Couple := (0,step s)
def behind (s : Axis) : Couple := (-step s,-step s)

def δx (A : Three E (r+1) s t) : Three E r s t := fun i j a => bite aheadX (fun b => A b j a) i
def δy (A : Three E r (s+1) t) : Three E r s t := fun i j a => bite aheadY (fun b => A i b a) j
def δz (A : Three E r s (t+1)) : Three E r s t := fun i j a => bite behind (A i j) a

lemma xy (A : Three E (r+1) (s+1) t) : δx (δy A) = δy (δx A) := by
  funext i j a; exact bite_comm _ _ (fun u v => A u v a) _ _
lemma yz (A : Three E r (s+1) (t+1)) : δy (δz A)=δz (δy A) := by
  funext i j a; exact bite_comm _ _ (A i) _ _
lemma xz (A : Three E (r+1) s (t+1)) : δx (δz A)=δz (δx A) := by
  funext i j a; exact bite_comm _ _ (fun u => A u j) _ _
lemma δz_sub (A B : Three E r s (t+1)) : δz (A-B)=δz A-δz B := by
  funext i j; exact bite_sub _ _ _
lemma δz_zero : δz (0:Three E r s (t+1))=0 := by funext i j; exact bite_zero behind
lemma δx_sub (A B : Three E (r+1) s t) : δx (A-B)=δx A-δx B := by
  funext i j a; exact congr_fun (bite_sub _ (fun b => A b j a) (fun b => B b j a)) i
lemma δy_sub (A B : Three E r (s+1) t) : δy (A-B)=δy A-δy B := by
  funext i j a; exact congr_fun (bite_sub _ (fun b => A i b a) (fun b => B i b a)) j

lemma δy_zero : δy (0:Three E r (s+1) t)=0 := by funext i j a; exact congr_fun (bite_zero (r:=s) _) j
lemma δx_sum (A : ι → Three E (r+1) s t) (q : Finset ι) : δx (∑ i∈q,A i)=∑ i∈q,δx (A i) := by
  funext i j a x; simp only [δx,bite,Finset.sum_apply,← Finset.sum_sub_distrib, Finset.smul_sum]
  conv_lhs => arg 2; intro b; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
lemma δy_sum (A : ι → Three E r (s+1) t) (q : Finset ι) : δy (∑ i∈q,A i)=∑ i∈q,δy (A i) := by
  funext i j a x; simp only [δy,bite,Finset.sum_apply,← Finset.sum_sub_distrib, Finset.smul_sum]
  conv_lhs => arg 2; intro b; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
lemma δz_sum (A : ι → Three E r s (t+1)) (q : Finset ι) : δz (∑ i∈q,A i)=∑ i∈q,δz (A i) := by
  funext i j; simp only [Finset.sum_apply]
  change bite behind ((∑ k∈q,A k) i j) = ∑ k∈q,bite behind (A k i j)
  simp only [Finset.sum_apply,bite_sum]

/-- All three shifts need commute only on different legs. -/
lemma permute {C : Type*} [AddCommGroup C] (A : Line D E (r+1)) (e : C ≃+ D) (v : Axis → C)
    (i : TypeFace r) (x : C) :
    bite v (fun i => A i ∘ e) i x=bite (fun j => e (v j)) A i (e x) := by
  simp only [bite, Function.comp_apply,map_sub]
end YM.CubicMatch.Lift

namespace YM.CubicMatch.Lift
open Filter Function Lattice RG Precision  Laurent Bloch Exterior Matrix
open scoped Topology BigOperators

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {r s t : ℕ} {η θ C D : ℝ}

def Pace (η C : ℝ) (A : Three E r s t) := ∀ a b c, Decay length2 η C (A a b c)

def stepFee (η : ℝ) (s : Axis → Couple) (r : ℕ) :=
  Fintype.card (TypeFace (r+1)) * (∑ i, (Real.exp (η*length2 (s i))+1))

lemma stepFee_nonneg (η : ℝ) (w : Axis → Couple) (r : ℕ) : 0 ≤ stepFee η w r := by unfold stepFee; positivity

lemma location_price (hη : 0 ≤ η) (w : Axis → Couple) {A : Line Couple E (r+1)}
    (h : ∀ k, Decay length2 η C (A k)) (i : TypeFace r) :
    Decay length2 η (stepFee η w r*C) (bite w A i) := by
  unfold bite
  have he (k s) : Decay length2 η ((Real.exp (η*length2 (w s))+1)*C) (fun x => left ℝ r s k i • (A k (x-w s)-A k x)) := by
    have hb s : Decay length2 η (Real.exp (η*length2 (w s))*C) (fun x => A k (x-w s)) :=
      fun x => (h k (x-w s)).trans ((mul_le_mul_of_nonneg_left (sub_decay hη x (w s)) (h k|>.cash)).trans_eq
        (by ring))
    apply Decay.enlarge ((Decay.minus (hb s) (h k)).scaled (left ℝ r s k i))
    have hN := (h k).cash
    have hh : |left ℝ r s k i| ≤ 1 := by unfold Exterior.left; rw [Matrix.of_apply]; split_ifs <;> simp [parity]
    exact (mul_le_of_le_one_left (by positivity) hh).trans (by rw [add_mul, one_mul])
  refine (Decay.fin (fun k (_ : k∈Finset.univ) => Decay.fin (fun s (_ : s∈Finset.univ) => he k s))).enlarge ?_
  simp_rw [← Finset.sum_mul]; rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; unfold stepFee; rw [mul_assoc]

variable {A B : Three E r s t}
omit [NormedSpace ℝ E] in
lemma Pace.mono (h : Pace η C A) (he : θ ≤ η) (hv : C ≤ D) (hh : 0 ≤ D) : Pace θ D A := fun i j a =>
  (h i j a).mono he hv hh
omit [NormedSpace ℝ E] in
lemma Pace.sub (h : Pace η C A) (g : Pace η D B) : Pace η (C+D) (A-B) := fun i j a =>
  (h i j a).minus (g i j a)
lemma Pace.x {A : Three E (r+1) s t} (h : Pace η C A) (hη : 0 ≤ η) :
    Pace η (stepFee η aheadX r*C) (δx A) := fun i j a => location_price hη aheadX (fun k => h k j a) i
lemma Pace.y {A : Three E r (s+1) t} (h : Pace η C A) (hη : 0 ≤ η) :
    Pace η (stepFee η aheadY s*C) (δy A) := fun i j a => location_price hη aheadY (fun k => h i k a) j
lemma Pace.z {A : Three E r s (t+1)} (h : Pace η C A) (hη : 0 ≤ η) :
    Pace η (stepFee η behind t*C) (δz A) := fun i j a => location_price hη behind (h i j) a
end YM.CubicMatch.Lift
