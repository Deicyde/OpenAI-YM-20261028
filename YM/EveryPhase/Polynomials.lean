import YM.EveryPhase.Barycenter

/-!
# Finite word polynomials on the common invariant domain
-/
set_option autoImplicit false
noncomputable section
namespace YM.EveryPhase
open Function Set Filter Spec Boundary Probe OS Next.BOUNDARY Mink
open scoped Topology NNReal InnerProductSpace BigOperators

variable {G : Gauge} {C : Family G} {S : Table C.book}

abbrev SumOfWords (T : Table C.book) := List (ℂ × Sentence T)

def monomial (V : Fields S) : Sentence S → V.domain →ₗ[ℂ] V.domain
  | [] => LinearMap.id
  | i::v => (V.field i.1 i.2).comp (monomial V v)

lemma append_op (V : Fields S) (v w : Sentence S) : monomial V (v++w)=(monomial V v).comp (monomial V w) := by
  induction v with
  | nil => simp [monomial]
  | cons i v ih => rw [List.cons_append, monomial, ih]; rfl

lemma evaluate_word (V : Fields S) (b : Sentence S) : monomial V b V.omega=V.evaluates b := by
  induction b with
  | nil => rfl
  | cons i a ih => simp only [monomial,LinearMap.comp_apply,ih]; rfl

lemma star_monomial (V : Fields S) (J : StarOp S) (h : V.sharpPair J) (x y : V.domain) (p : Sentence S) :
    inner ℂ ((monomial V p x).val) y.val=inner ℂ x.val ((monomial V (Sentence.rev J p) y).val) := by
  induction p generalizing y with
  | nil => rfl
  | cons i p IH =>
    have he : Sentence.rev J (i::p)=Sentence.rev J p ++ [Letter.op J i] := by simp [Sentence.rev]
    rw [he, append_op,LinearMap.comp_apply, monomial,LinearMap.comp_apply,h, IH]; rfl

def operator (V : Fields S) : SumOfWords S → V.domain →ₗ[ℂ] V.domain
  | [] => 0
  | p::w => p.1 • monomial V p.2 + operator V w

def reverseP (J : StarOp S) (v : SumOfWords S) : SumOfWords S := v.map fun p => (star p.1, Sentence.rev J p.2)

theorem star_operator (V : Fields S) (J : StarOp S) (h : V.sharpPair J) (x y : V.domain)
    (p : SumOfWords S) : inner ℂ (operator V p x).val y.val=inner ℂ x.val (operator V (reverseP J p) y).val := by
  induction p with
  | nil => simp [operator, reverseP]
  | cons i p ih =>
    change _=inner ℂ _ (operator V ((star i.1,Sentence.rev J i.2)::(reverseP J p)) y).val
    rw [operator,operator]; simp only [LinearMap.add_apply,
      LinearMap.smul_apply,Submodule.coe_add, Submodule.coe_smul_of_tower,inner_add_left,
      inner_add_right, inner_smul_left, inner_smul_right, ih, star_monomial V J h]; rfl

def acted (K : Spins S) (p : Poincare) (A : SumOfWords S) := A.map fun i => (i.1,K.po p i.2)
def stands (V : Fields S) (A : SumOfWords S) : V.H := (operator V A V.omega).val

lemma stands_cons (V : Fields S) (i) (A : SumOfWords S) :
    stands V (i::A)=i.1 • V.vector i.2 + stands V A := by
  unfold stands
  rw [operator, LinearMap.add_apply,LinearMap.smul_apply,evaluate_word]; rfl

variable {W : Surface S} {R : S.Rotation} {s : S.RealSpin} {X : Wightman S}

lemma cov_operator_vac (H : FieldCore W R s X) (p : Poincare) (A : SumOfWords S) :
    stands X.operators (acted X.spin p A) = X.action.V p (stands X.operators A) := by
  induction A with
  | nil => simp [acted, stands, operator]
  | cons i A ih =>
    change stands X.operators (_ :: acted X.spin p A)=_
    rw [stands_cons,stands_cons,map_add,map_smul,H.covariant,ih]

lemma star_moved (H : FieldCore W R s X) (V : DiffPlan S) (hs : S.Symmetric) (hp : V.Inclusions S)
    (p : Poincare) (A : SumOfWords S) : reverseP X.J (acted X.spin p A)=acted X.spin p (reverseP X.J A) := by
  have hh (i : Sentence S) : Sentence.rev X.J (X.spin.po p i)=X.spin.po p (Sentence.rev X.J i) := by
    unfold Sentence.rev Spins.po; rw [List.map_reverse,List.map_map,List.map_map]; congr 2
    ext1 q; exact Letter.rewrites hs hp H.induced X.spin H.letters q p
  unfold reverseP acted
  rw [List.map_map,List.map_map]; congr 1; ext1 i; exact Prod.ext rfl (hh i.2)

section support
variable (A B : SumOfWords S)

def boundedWord (v : Sentence S) : Prop := ∀ i ∈ v, HasCompactSupport ⇑i.2

def finite (A : SumOfWords S) : Prop := ∀ v∈A, boundedWord v.2

def spacelikeWords (A B : SumOfWords S) := ∀ i ∈ A, ∀ j ∈ B, ∀ x ∈ i.2, ∀ y ∈ j.2, Fields.causal x.2 y.2

private lemma mon_comm (V : Fields S) (h : V.commutes) {a b : Sentence S}
    (he : ∀ i ∈ a, ∀ j ∈ b, Fields.causal i.2 j.2) (x : V.domain) :
    monomial V a (monomial V b x)=monomial V b (monomial V a x) := by
  induction a generalizing x with
  | nil => rfl
  | cons i a ih =>
    have single_comm (b : Sentence S) (p : ∀ j∈b, Fields.causal i.2 j.2) (x : V.domain) :
        V.field i.1 i.2 (monomial V b x)=monomial V b (V.field i.1 i.2 x) := by
      induction b generalizing x with
      | nil => rfl
      | cons j b ihb =>
        simp only [monomial,LinearMap.comp_apply]; rw [h i.1 j.1 i.2 j.2 (p j (by simp))]
        rw [ihb (fun k hk => p k (List.mem_cons_of_mem _ hk))]
    simp only [monomial,LinearMap.comp_apply]
    rw [ih (fun k hk => he k (List.mem_cons_of_mem _ hk))]
    exact single_comm b (he i (by simp)) _

theorem op_comm {A B : SumOfWords S} (V : Fields S) (h : V.commutes) (hp : spacelikeWords A B)
    (x : V.domain) : operator V A (operator V B x)=operator V B (operator V A x) := by
  induction A generalizing x with
  | nil => simp [operator]
  | cons i A ih =>
    have he (B : SumOfWords S) (p : ∀ j∈B, ∀ v∈i.2, ∀ w∈j.2, Fields.causal v.2 w.2) :
        monomial V i.2 (operator V B x)=operator V B (monomial V i.2 x) := by
      induction B with
      | nil => simp [operator]
      | cons j B ihb =>
        simp only [operator, LinearMap.add_apply,LinearMap.smul_apply,map_add,map_smul]
        rw [mon_comm V h (p _ (by simp)), ihb (fun k hk => p k (List.mem_cons_of_mem _ hk))]
    simp only [operator,LinearMap.add_apply,LinearMap.smul_apply,map_add,map_smul]
    rw [ih (fun k hk => hp k (List.mem_cons_of_mem _ hk)), he B (hp i (by simp))]

lemma transl_support {x y : E4} (f : Test4) (h : y ∈ tsupport (Joint.push (Poincare.translation x) f)) :
    y-x∈ tsupport f := by
  let v := (· - x : E4 → E4)
  let G := Joint.push (Poincare.translation x) f
  have he : MapsTo v (support G) (support f) := by
    intro s hs; change f _ ≠ 0; change Joint.push _ _ s ≠ 0 at hs
    simpa [Poincare.backwards,Poincare.translation] using hs
  exact he.closure (by unfold v; fun_prop) h

private lemma compact_bounds {f : Test4} (h : HasCompactSupport ⇑f) :
    ∀ᶠ R : ℝ in atTop, ∀ x ∈ tsupport f, |time x| ≤ R ∧ ‖spatial x‖ ≤ R := by
  obtain ⟨a,hA⟩ := (h.image (show Continuous (fun x => |time x|) from by fun_prop)).bddAbove
  obtain ⟨b,hB⟩ := (h.image (show Continuous (fun x => ‖spatial x‖) from by fun_prop)).bddAbove
  filter_upwards [eventually_ge_atTop a,eventually_ge_atTop b] with r ha hb
  exact fun i hi => ⟨(hA (mem_image_of_mem _ hi)).trans ha,(hB (mem_image_of_mem _ hi)).trans hb⟩

private lemma bounded_scope (A : SumOfWords S) (hA : finite A) :
    ∀ᶠ R : ℝ in atTop, ∀ i∈A, ∀ j∈i.2, ∀ x∈tsupport ⇑j.2, |time x| ≤ R ∧ ‖spatial x‖ ≤ R := by
  classical
  have hp i (hi : i ∈ A) : ∀ᶠ R : ℝ in atTop, ∀ j∈i.2, ∀ x∈tsupport ⇑j.2, |time x| ≤ R ∧ ‖spatial x‖ ≤ R := by
    simpa only [← List.mem_toFinset] using
      (eventually_all_finset i.2.toFinset).mpr (fun j hj => compact_bounds (hA i hi j (by simpa using hj)))
  simpa only [← List.mem_toFinset] using
    (eventually_all_finset A.toFinset).mpr (fun i hi => hp i (by simpa using hi))

lemma distant (A B : SumOfWords S) (hA : finite A) (hB : finite B) (K : Spins S) :
    ∃ R : ℝ, ∀ t : ℝ, |t| ≤ 1 → ∀ x : Space3, R < ‖x‖ →
      spacelikeWords A (acted K (Poincare.translation (position x t)) B) := by
  obtain ⟨r,hr,hR⟩ := ((bounded_scope A hA).and (bounded_scope B hB)).exists
  refine ⟨4*r+1, fun t ht x hx i hi j hj f hf g hg a ha b hb => ?_⟩
  obtain ⟨j,hJ,rfl⟩ := List.mem_map.mp hj
  obtain ⟨g,hG,rfl⟩ := List.mem_map.mp hg
  obtain ⟨hv,hu⟩ := hR j hJ g hG _ (transl_support g.2 hb)
  obtain ⟨hp,hq⟩ := hr _ hi _ hf _ ha
  rw [lateral]
  have he : ‖x‖ ≤ ‖spatial (a-b)‖ + ‖spatial a‖ + ‖spatial (b-position x t)‖ := calc
    _ = ‖-spatial (a-b) + spatial a - spatial (b-position x t)‖ := by simp [sub_eq_add_neg]
    _ ≤ _ := le_trans (norm_sub_le _ _) (add_le_add_left (by simpa using norm_add_le (-spatial (a-b)) (spatial a)) _)
  simp only [sub_eq_add_neg,clock_add,clock_neg,time_position] at hv he hu ⊢
  rw [abs_le] at hv hp ht; rw [abs_lt]; constructor <;> linarith

lemma fin_reverse (J : StarOp S) {A : SumOfWords S} (hA : finite A) : finite (reverseP J A) := by
  intro i hi j hj
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hi
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hj)
  exact (hA v hv x hx).comp_left (show star (0:ℂ)=0 from star_zero ℂ)
end support

open MeasureTheory Measure

def delta (X : Wightman S) (A : SumOfWords S) (p : E4) :=
    charFun (X.momentum.diagonal (stands X.operators A)) p -
      charFun (X.momentum.diagonal (stands X.operators (reverseP X.J A))) (-p)

theorem comm_expect (H : FieldCore W R s X) (P : DiffPlan S) (hs : S.Symmetric) (hp : P.Inclusions S)
    (A : SumOfWords S) (p : E4) :
    let V := X.operators
    let T := acted X.spin (Poincare.translation p) A
    delta X A p = inner ℂ V.vacuum (operator V (reverseP X.J A) (operator V T V.omega)).val -
        inner ℂ V.vacuum (operator V T (operator V (reverseP X.J A) V.omega)).val := by
  unfold delta; rw [H.spectral,H.spectral]; congr 1
  · exact
      have he := cov_operator_vac H (Poincare.translation p) A
      calc
        _ = inner ℂ (stands X.operators A) (stands X.operators (acted X.spin (Poincare.translation p) A)) :=
          congrArg _ he.symm
        _ = _ := star_operator _ _ H.adj X.operators.omega _ A
  let U := X.action.V (Poincare.translation p)
  let x := stands X.operators (reverseP X.J A)
  let Z := acted X.spin (Poincare.translation p) A
  let V := X.operators
  have ht : reverseP X.J (reverseP X.J Z)=Z := by
    have hz := Boundary.invol hs hp H.induced
    unfold reverseP; rw [List.map_map, List.map_congr_left (g:=id)]
    · simp
    intro _ _; simp only [Function.comp_apply,star_star,Sentence.rev_rev _ hz,id_eq]
  have hw : stands V (reverseP X.J Z) = U x := by
    rw [show reverseP X.J Z= _ from star_moved H P hs hp _ _]; exact cov_operator_vac H _ _
  have hu : U (X.action.orbit.translation (-p) x)=x := by
    change X.action.orbit.translation p (X.action.orbit.translation (-p) x) = _
    rw [← ContinuousLinearMap.comp_apply,X.action.orbit.sends,add_neg_cancel,X.action.orbit.origin]; rfl
  calc
    _ = inner ℂ (U x) (U (X.action.orbit.translation (-p) x)) := (X.action.flavor _ _ _).symm
    _ = inner ℂ (stands V (reverseP X.J Z)) x := by rw [hw, hu]
    _ = inner ℂ V.vacuum (operator V (reverseP X.J (reverseP X.J Z)) (operator V (reverseP X.J A) V.omega)).val :=
        star_operator V _ H.adj _ _ _
    _ = _ := by rw [ht]
end YM.EveryPhase
