import YM.Contacts.Expressions

/-! # Action on field polynomials

Push positions and fields together. Totalization commutes with the action.
Supports remain *locations* of the transformed fields, no extra points used in an expanded
polynomial (even though this internal basis is not declared covariant).
-/

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts
open Function Filter Set MeasureTheory Table OPE MultipleContact.Script
open scoped Classical Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {L : Register G} {S : Table L} {P : DiffPlan S}
variable {I : Type} [Fintype I]

section Algebra
variable {A B : Type}
def supportedAt (Y : Set E4) : Subalgebra ℂ (Expression P) :=
  Algebra.adjoin ℂ { f | ∃ x∈Y, ∃ i : Mode P, f = unitLetter x i }
lemma unit_supportedAt (Y : Set E4) (i : Mode P) {x : E4} (h : x∈Y) : unitLetter x i ∈ supportedAt Y :=
  Algebra.subset_adjoin (show ∃ x'∈Y, ∃ i' : Mode P, unitLetter x i=unitLetter x' i' from ⟨x,h,i,rfl⟩)

def images (f : A → Grammar B) : Multiplicative (Multiset A) →* Grammar B where
  toFun m := (m.toAdd.map f).prod
  map_one' := rfl
  map_mul' x y := by change ((x.toAdd+y.toAdd).map f).prod= _; rw [Multiset.map_add,Multiset.prod_add]
def substitute (f : A → Grammar B) : Grammar A →ₐ[ℂ] Grammar B := AddMonoidAlgebra.lift _ _ _ (images f)
lemma substitute_stamp (f : A → Grammar B) (x : A) : substitute f (stamp x) = f x := by
  unfold substitute stamp; rw [AddMonoidAlgebra.lift_single, one_smul]; exact Multiset.prod_singleton _

def subConj (f : A → Grammar B) : Grammar A →+* Grammar B :=
  AddMonoidAlgebra.liftNCRingHom ((algebraMap ℂ _).comp (starRingEnd ℂ)) (images f)
    (fun _ _ => Commute.all ..)
lemma subConj_single (f : A → Grammar B) (m : Multiset A) (c : ℂ) :
    subConj f (AddMonoidAlgebra.single m c) = star c • (images f) (.ofAdd m) := by
  rw [subConj, AddMonoidAlgebra.liftNCRingHom_single, Algebra.smul_def]; rfl
lemma subConj_stamp (f : A → Grammar B) (x : A) : subConj f (stamp x) = f x := by
  rw [stamp,subConj_single,star_one,one_smul]; exact Multiset.prod_singleton _
lemma subConj_smul (f : A → Grammar B) (c : ℂ) (x : Grammar A) :
    subConj f (c • x) = star c • subConj f x := by
  rw [Algebra.smul_def,map_mul]; change subConj f (AddMonoidAlgebra.single 0 c)* _ = _
  rw [subConj_single, show Multiplicative.ofAdd (0:Multiset A)=1 from rfl,map_one,smul_mul_assoc,one_mul]
end Algebra

variable (D : Prescription P) (R : S.Rotation) {ρ : S.RealSpin} (hR : R.Laws P ρ)

private lemma insert_as (x : E4) (i : Mode P) : unitLetter x i = stamp (x,i) := rfl
lemma insert_supportedAt (Y : Set E4) {x : E4} (hx : x∈Y) {d : ℕ} (v : S.Field d) :
    insertField D x d v ∈ supportedAt Y := by
  rw [insert_formula]; exact (supportedAt Y).sum_mem fun i _ => (supportedAt Y).smul_mem (unit_supportedAt Y i hx) _

def shiftExpr (v : E4) : Expression P →ₐ[ℂ] Expression P :=
  substitute fun i : E4 × Mode P => unitLetter (i.1+v) i.2
lemma shift_unit (v x : E4) (i : Mode P) : shiftExpr v (unitLetter x i)=unitLetter (x+v) i := substitute_stamp ..
lemma shift_field (v x : E4) (d : ℕ) (f : S.Field d) : shiftExpr v (insertField D x d f)= insertField D (x+v) d f := by
  simp_rw [insert_formula,map_sum,map_smul,shift_unit]
lemma shift_add (v w : E4) (e : Expression P) : shiftExpr w (shiftExpr v e)= shiftExpr (v+w) e := by
  induction e using expression_induction with
  | hm n x p =>
    change shiftExpr w (shiftExpr v (∏ i, unitLetter (x i) (p i))) = shiftExpr _ (∏ i,unitLetter (x i) (p i))
    simp_rw [map_prod,shift_unit,add_assoc]
  | ha _ _ hx hy => simp only [map_add,hx,hy]
  | hs _ _ ha => simp only [map_smul,ha]
lemma shift_zero (e : Expression P) : shiftExpr (0:E4) e=e := by
  induction e using expression_induction with
  | hm n x p =>
    change shiftExpr _ (∏ i, unitLetter (x i) (p i))= ∏ i,unitLetter (x i) (p i); simp_rw [map_prod, shift_unit,add_zero]
  | ha _ _ hx hy => simp only [map_add,hx,hy]
  | hs _ _ ha => simp only [map_smul,ha]

/-- Kill monomials involving locations outside this set. Used **only in totalizations**, identity in applications on valid geometry. -/
def keep (U : Set E4) : Expression P →ₐ[ℂ] Expression P :=
  substitute fun i : E4 × Mode P => if i.1∈U then unitLetter i.1 i.2 else 0
lemma keep_unit (U : Set E4) (x : E4) (i : Mode P) : keep U (unitLetter x i) = if x∈U then unitLetter x i else 0 := substitute_stamp ..
lemma keep_field (U : Set E4) (x : E4) (d : ℕ) (f : S.Field d) : keep U (insertField D x d f) = if x∈U then insertField D x d f else 0 := by
  by_cases hx : x∈U <;> simp [hx,insert_formula,map_sum,keep_unit]
lemma keep_supportedAt (Y U : Set E4) (hy : Y ⊆ U) (e : Expression P) (he : e∈ supportedAt Y) : keep U e=e := by
  unfold supportedAt at he; induction he using Algebra.adjoin_induction with
  | mem x hx => obtain ⟨x,hx,i,rfl⟩ := hx; exact (keep_unit ..).trans (if_pos (hy hx))
  | algebraMap z => exact (keep (P:=P) U).commutes _
  | add x y _ _ hx hy => rw [map_add,hx,hy]
  | mul x y _ _ hx hy => rw [map_mul,hx,hy]

-- generalized rule for filtered changes
lemma acts_on_fields (a : Expression P →ₐ[ℂ] Expression P) (x y : E4) (d : ℕ)
    (t : S.Field d→ₗ[ℂ] S.Field d) (hD : D.Coherent)
    (hu : ∀ i∈bands P d, a (unitLetter x i) = insertField D y d (t (D.loaded i d)))
    (f : S.Field d) : a (insertField D x d f)=insertField D y d (t f) := by
  rw [← (hD d).rebuilds f]; simp only [map_sum]; exact Finset.sum_congr rfl fun i hi=>by
    rw [map_smul,map_smul,map_smul,map_smul,insert_loaded D hD hi,hu i hi]

def turnExpr (g : Ortho) : Expression P →ₐ[ℂ] Expression P := substitute fun p : E4 × Mode P =>
  insertField D (Ortho.move g p.1) p.2.1 (R.act p.2.1 g (D.needle p.2))
lemma turn_unit (g : Ortho) (x : E4) (i : Mode P) : turnExpr D R g (unitLetter x i)=
    insertField D (Ortho.move g x) i.1 (R.act i.1 g (D.needle i)) := substitute_stamp ..

variable (hS : S.Symmetric) (hP : P.Inclusions S) (hO : P.Orientation ρ) (hD : D.Coherent)
include hS hP hD hR
lemma turn_field (g : Ortho) (x : E4) (d : ℕ) (f : S.Field d) : turnExpr D R g (insertField D x d f)=
    insertField D (Ortho.move g x) d (R.act d g f) := by
  apply acts_on_fields D _ _ _ _ (R.act d g).toLinearMap hD (fun i hi=>?_)
  rw [turn_unit, LinearEquiv.coe_toLinearMap, D.cost i hi,hR.filtered, insert_rise D hD hS hP]
lemma turn_word (g : Ortho) (x : I → E4) (v : I → S.Tag) : turnExpr D R g (fieldWord D x v)= fieldWord D
    (Ortho.move g ∘ x) (R.label g ∘ v) := by unfold fieldWord; rw [map_prod]; exact Finset.prod_congr rfl fun i _=> turn_field D R hR hS hP hD _ _ _ _
lemma turn_mul (g k : Ortho) (e : Expression P) : turnExpr D R g (turnExpr D R k e)= turnExpr D R (g*k) e := by
  induction e using expression_induction with
  | hm n x p =>
    change turnExpr D R g (turnExpr D R k (∏ i,unitLetter (x i) (p i))) = turnExpr _ _ _ (∏ i,unitLetter (x i) (p i))
    simp_rw [map_prod,turn_unit,turn_field D R hR hS hP hD, Ortho.move_mul,hR.group]
  | ha x y hx hy => simp only [map_add,hx,hy]
  | hs r a ha => simp only [map_smul,ha]
lemma turn_one (e : Expression P) : turnExpr D R 1 e=e := by
  induction e using expression_induction with
  | hm n x p =>
    change turnExpr _ _ _ (∏ i,unitLetter (x i) (p i)) = ∏ i,unitLetter (x i) (p i)
    simp_rw [map_prod,turn_unit,Ortho.move_one,hR.fixes, insert_needle D hD hS hP]
  | ha x y hx hy => simp only [map_add,hx,hy]
  | hs r a ha => simp only [map_smul,ha]
omit hD hS hP hR in
lemma turn_shift (g : Ortho) (v : E4) (e : Expression P) :
    turnExpr D R g (shiftExpr v e)= shiftExpr (Ortho.move g v) (turnExpr D R g e) := by
  induction e using expression_induction with
  | hm n x p =>
    change turnExpr _ _ g (shiftExpr v (∏ i,unitLetter (x i) (p i)))= shiftExpr _ (turnExpr _ _ g (∏ i,unitLetter (x i) (p i)))
    simp_rw [map_prod,shift_unit,turn_unit,shift_field D,← Ortho.motion_at,map_add]
  | ha x y hx hy => simp only [map_add,hx,hy]
  | hs r a ha => simp only [map_smul,ha]
omit hD hS hP hR in
lemma turn_keep (U V : Set E4) (g : Ortho) (h : ∀ x, x∈U ↔ Ortho.move g x∈V) (e : Expression P) :
    turnExpr D R g (keep U e) = keep V (turnExpr D R g e) := by
  induction e using expression_induction with
  | hm n x p =>
    change turnExpr _ _ _ (keep U (∏ i,unitLetter (x i) (p i)))= keep V (turnExpr _ _ _ (∏ i,unitLetter (x i) (p i)))
    simp only [map_prod]; exact Finset.prod_congr rfl fun i _=>by by_cases he : x i∈U <;> simp [keep_unit,turn_unit,keep_field,h (x i)|>.symm,he]
  | ha x y hx hy => simp only [map_add,hx,hy]
  | hs r a ha => simp only [map_smul,ha]

omit hR hP hS hD
def realExpr (ρ : S.RealSpin) : Expression P →+* Expression P := subConj fun p : E4 × Mode P=>
  insertField D p.1 p.2.1 (S.conj ρ p.2.1 (D.needle p.2))
lemma real_unit (ρ : S.RealSpin) (x : E4) (i : Mode P) : realExpr D ρ (unitLetter x i)=
    insertField D x i.1 (S.conj ρ i.1 (D.needle i)) := subConj_stamp ..
lemma real_coeff (ρ : S.RealSpin) (c : ℂ) (x : Expression P) : realExpr D ρ (c • x)= star c • realExpr D ρ x := subConj_smul ..
lemma real_shift (ρ : S.RealSpin) (v : E4) (e : Expression P) :
    realExpr D ρ (shiftExpr v e)= shiftExpr v (realExpr D ρ e) := by
  induction e using expression_induction with
  | hm n x p =>
    change realExpr D ρ (shiftExpr v (∏ i,unitLetter (x i) (p i)))= shiftExpr v (realExpr _ _ (∏ i,unitLetter (x i) (p i)))
    simp_rw [map_prod,shift_unit,real_unit,shift_field]
  | ha x y hx hy => simp only [map_add,hx,hy]
  | hs r a ha => simp only [real_coeff,map_smul, ha] -- rw twice?
lemma real_keep (ρ : S.RealSpin) (U : Set E4) (e : Expression P) :
    realExpr D ρ (keep U e)= keep U (realExpr D ρ e) := by
  induction e using expression_induction with
  | hm n x p =>
    change realExpr _ _ (keep U (∏ i,unitLetter (x i) (p i)))= keep U (realExpr _ _ (∏ i,unitLetter (x i) (p i)))
    simp only [map_prod]; exact Finset.prod_congr rfl fun i _=>by by_cases he : x i∈U <;> simp [keep_unit,real_unit,keep_field,he]
  | ha x y hx hy => simp only [map_add,hx,hy]
  | hs r a ha => simp only [map_smul,real_coeff,ha]
include hS hP hO hD
lemma real_field (x : E4) (d : ℕ) (f : S.Field d) : realExpr D ρ (insertField D x d f)=
    insertField D x d (S.conj ρ d f) := by
  rw [← (hD d).rebuilds f]; simp only [map_sum]; exact Finset.sum_congr rfl fun i hi=>by
    rw [map_smul, real_coeff, map_smulₛₗ, map_smul, insert_loaded D hD hi, real_unit, D.cost i hi, hO.realInc, insert_rise D hD hS hP]; rfl
lemma real_twice (e : Expression P) : realExpr D ρ (realExpr D ρ e)= e := by
  induction e using expression_induction with
  | hm n x p =>
    change realExpr D ρ (realExpr D ρ (∏ i,unitLetter (x i) (p i)))= ∏ i,unitLetter (x i) (p i)
    simp_rw [map_prod,real_unit,real_field D hS hP hO hD, S.reflect_star,insert_needle D hD hS hP]
  | ha x y hx hy => simp only [map_add,hx,hy]
  | hs r a ha => simp only [real_coeff,ha,star_star]
include hR
lemma real_turn (g : Ortho) (e : Expression P) :
    realExpr D ρ (turnExpr D R g e)= turnExpr D R g (realExpr D ρ e) := by
  induction e using expression_induction with
  | hm n x p =>
    change realExpr _ _ (turnExpr _ _ _ (∏ i,unitLetter (x i) (p i)))= turnExpr _ _ _ (realExpr _ _ (∏ i,unitLetter (x i) (p i)))
    simp_rw [map_prod, real_unit, turn_unit,turn_field D R hR hS hP hD,real_field D hS hP hO hD,hR.real]
  | ha x y hx hy => simp only [map_add,hx,hy]
  | hs r a ha => simp only [map_smul,real_coeff,ha]

-- Reading symmetries for any phase/system of F respecting this filtration
variable (T : Table L) (hH : T.Hierarchy) (hh : T.respects S) (ht : P.Inclusions T)
omit hR hO
lemma word_needle (x : I → E4) (p : I → Mode P) :
    fieldWord D x (fun i=> ⟨(p i).1,D.needle (p i)⟩)= letterWord x p := by
  change (∏ i, insertField D (x i) _ _)= ∏ i, unitLetter (x i) (p i); simp_rw [insert_needle D hD hS hP]
include hR
include hH hh ht
lemma turn_read (h : R.Oriented T) (g : Ortho) (e : Expression P) :
    readExpr D T (turnExpr D R g e)= readExpr D T e := by
  induction e using expression_induction with
  | hm n x p =>
    rw [← word_needle D hS hP hD,turn_word D R hR hS hP hD]
    let y:=points x; let v : Fin n → S.Tag:= fun i=>⟨(p i).fst,D.needle (p i)⟩
    have hs := read_fields D hD T hH.laws.toSymmetric hh ht (Points.move g y) (R.label g ∘ v)
    change readExpr D T (fieldWord _ _ _) = readExpr D T (fieldWord D y.ofLp v)
    change readExpr D T (fieldWord D (Ortho.move g ∘ x) (R.label g ∘ v)) = _ at hs
    rw [hs, read_fields D hD T hH.laws.toSymmetric hh ht]
    by_cases he : y∈conf n
    · rw [if_pos he, if_pos (Points.move_in g he), h _ _ _ he]
    rw [if_neg he,if_neg]; exact fun h' => he (fun _ _ hh => (show Injective (Ortho.move g ∘ x) from h') (congr_arg (Ortho.move g) hh))
  | ha _ _ hx hy => simp only [map_add,hx,hy]
  | hs r x hx => simp only [map_smul,hx]
omit hh ht hR hP hS hD
lemma shift_read (v : E4) (e : Expression P) : readExpr D T (shiftExpr v e)=readExpr D T e := by
  induction e using expression_induction with
  | hm n x p =>
    rw [show shiftExpr v (letterWord x p)=letterWord (fun i=>x i+v) p from ?_, read_letters D T hH.laws.toSymmetric,read_letters D T hH.laws.toSymmetric]
    · unfold totalObserve; by_cases hx : Injective x
      · rw [if_pos hx, if_pos (show Injective (fun i=> x i+v) from fun i j H=> hx (add_right_cancel H))]; exact observe_carry T hH.translations _ hx _
      rw [if_neg hx, if_neg]; exact fun h=> hx (fun _ _ hh=> (show Injective (fun i=> x i+v) from h) (congr_arg (·+v) hh))
    change shiftExpr _ (∏ i,unitLetter (x i) (p i))=∏ i,unitLetter (x i+v) (p i); simp_rw [map_prod,shift_unit]
  | ha x y hx hy => simp only [map_add,hx,hy]
  | hs r a ha => simp only [map_smul,ha]
include hh ht hO hS hP hD
lemma real_read (e : Expression P) :
    readExpr D T (realExpr D ρ e)= star (readExpr D T e) := by
  induction e using expression_induction with
  | hm n x p =>
    let v := D.letter ∘ p
    rw [← letter_to_token D hS hP hD]
    have hf : realExpr D ρ (tokenWord D x v)= tokenWord D x (L.conjugate ∘ v) := by
      unfold tokenWord; rw [map_prod]; refine Finset.prod_congr rfl fun i _=>?_
      change realExpr D ρ (insertField D (x i) _ (S.project (v i).1 (v i).2)) = _
      rw [real_field D hS hP hO hD, S.conj_project]; rfl
    change readExpr D T (realExpr _ _ (tokenWord _ x v))= _; rw [hf]
    simp_rw [read_word D hD T hH.laws.toSymmetric hh ht]
    unfold totalObserve; split
    next hx => exact (named_fin T hH.laws.toSymmetric (L.conjugate ∘ v) (x:=points x) hx).trans ((hH.spin.real hx _).trans (congr_arg star (named_fin T hH.laws.toSymmetric v (x:=points x) hx).symm))
    simp
  | ha x y hx hy => simp only [map_add,hx,hy,star_add]
  | hs r a ha => simp only [real_coeff,map_smul,ha,star_smul]
end YM.Contacts
