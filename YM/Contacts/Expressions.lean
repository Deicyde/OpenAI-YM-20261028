import YM.OPE.Splitting.Observe
import YM.MultipleContact.Multi.Script

/-!
# Polynomials with filtrations imposed already

Products **inside** this algebra are formal. We use it to make literal
linear operations at each node of a forest, including evaluating an input
with many further signed operations in it. The physical reads of these
polynomials use ordinary **separated** correlation functions. Totalizations
(at points outside Conf) are not a distributional extension.

Choose coherent OPE.Prescription solely for *filtration coordinates*, so
that the polynomial letters have no linear redundancies. This is not yet
choosing the detector prescription at contacts. We can insert, in
particular, vectors homogeneous in a different splitting of our choice.
Also note that an insertion of the unit field is not the constant polynomial
one. We keep the unit fields' slots as in `sec:omult` of the revised ms.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts
open Function Filter Set MeasureTheory Table OPE MultipleContact.Script
open scoped Classical Topology ContDiff BigOperators
variable {G : Gauge} {L : Register G} {S : Table L} {P : DiffPlan S}
variable {I J : Type} [Fintype I] [Fintype J] {A : Type}

lemma spell_beside (x : I → A) (y : J → A) :
    spell (beside x y) = spell x * spell y := by
  unfold spell; rw [Fintype.prod_sum_type]; rfl

@[simp] lemma spell_sole (x : A) : spell (sole x) = stamp x := by simp [spell, sole]

lemma grammar_induction {p : Grammar A → Prop} (x : Grammar A)
    (hm : ∀ (n : ℕ) (f : Fin n → A), p (spell f))
    (ha : ∀ x y, p x → p y → p (x+y))
    (hs : ∀ r : ℂ, ∀ x, p x → p (r • x)) : p x := by
  refine AddMonoidAlgebra.induction_on x ?_ ha hs
  intro m
  obtain ⟨n, f, he⟩ := frame' m
  specialize hm n f
  rw [spell_eq] at hm
  rw [he]; exact hm

omit [Fintype I] in
/-- Simple induction to replace polynomial letters one at a time in any reading. -/
lemma replace_factors (g : Grammar A → ℂ) (f f' : I → Grammar A) (t : Finset I)
    (h : ∀ i ∈ t, ∀ x, g (f i * x)=g (f' i * x)) (x : Grammar A) :
    g ((t.prod f)*x)=g ((t.prod f')*x) := by
  induction t using Finset.induction generalizing x with
  | empty => simp
  | @insert i t hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, mul_assoc, h i (by simp)]
    rw [← mul_assoc, mul_comm (f' i), mul_assoc, ih, mul_comm (f' i) (t.prod f'), mul_assoc]
    exact fun k hk => h _ (Finset.mem_insert_of_mem hk)

section Raw
variable (T : Table L)

/-- The auxiliary totalization of separated readings is always zero on overlaps. -/
def totalObserve (x : I → E4) (p : I → L.Token) : ℂ := if Injective x then observe T x p else 0
lemma total_perm (h : T.Symmetric) (e : I ≃ J) (x : J → E4) (p : J → L.Token) :
    totalObserve T (x ∘ e) (p ∘ e) = totalObserve T x p := by
  have he : Injective (x ∘ e) ↔ Injective x := by
    refine ⟨fun hp i j hij => ?_, fun hx => hx.comp e.injective⟩
    exact e.symm.injective (hp (by simpa using hij))
  unfold totalObserve; by_cases hx : Injective x
  · rw [if_pos (he.mpr hx), if_pos hx]; exact perm_observe T h e p hx
  rw [if_neg (mt he.mp hx), if_neg hx]
private lemma total_unique_aux (x : I → L.Plant) (y : J → L.Plant) (h : letters x = letters y)
    (hx : Injective (Prod.fst ∘ x)) : ∃ e : I ≃ J, x=y ∘ e := by
  have he := (letters_card x).symm.trans ((congr_arg Multiset.card h).trans (letters_card y))
  have hu (i) : ∃ j, y j = x i := (letters_image y).mp (h ▸ (letters_image x).mpr ⟨i,rfl⟩)
  choose f hf using hu
  have hi : Injective f := fun i j e => hx (by change (x i).1=(x j).1; rw [← hf i,← hf j,e])
  exact ⟨Equiv.ofBijective f (Fintype.bijective_iff_injective_and_card f|>.mpr ⟨hi,he⟩),funext fun i=>(hf i).symm⟩
private lemma total_unique (x : I → L.Plant) (y : J → L.Plant) (h : letters x = letters y) (hs : T.Symmetric) :
    totalObserve T (Prod.fst ∘ x) (Prod.snd ∘ x)= totalObserve T (Prod.fst ∘ y) (Prod.snd ∘ y) := by
  by_cases hx : Injective (Prod.fst ∘ x)
  · obtain ⟨e,rfl⟩:=total_unique_aux x y h hx; exact total_perm T hs e (Prod.fst ∘ y) (Prod.snd ∘ y)
  by_cases hy : Injective (Prod.fst ∘ y)
  · obtain ⟨e,rfl⟩:=total_unique_aux y x h.symm hy; exact (total_perm T hs e _ _).symm
  simp only [totalObserve,hx,hy,if_false]

def rawSee : Grammar L.Plant →ₗ[ℂ] ℂ := Extend (fun x =>
  let f := (letters_frame x).choose; totalObserve T (Prod.fst ∘ f) (Prod.snd ∘ f))
lemma raw_spell (hs : T.Symmetric) (x : I → L.Plant) : rawSee T (spell x)=
    totalObserve T (Prod.fst ∘ x) (Prod.snd ∘ x) :=
  (extend_word _ x).trans (total_unique T _ _ (letters_frame _).choose_spec.symm hs)
end Raw

/-- Same coherent basis will be used on every word. -/
abbrev Expression (P : DiffPlan S) := Grammar (E4 × OPE.Mode P)

variable (D : OPE.Prescription P)

def unitLetter (x : E4) (i : Mode P) : Expression P := stamp (x,i)

def letterWord (x : I → E4) (p : I → Mode P) : Expression P := spell (fun i => (x i,p i))
lemma letters_beside (x : I → E4) (p : I → Mode P) (y : J → E4) (q : J → Mode P) :
    letterWord (beside x y) (beside p q)=letterWord x p*letterWord y q := by
  rw [letterWord,letterWord,letterWord,← spell_beside]; congr; funext i; cases i <;> rfl
lemma letters_sole (x : E4) (i : Mode P) : letterWord (sole x) (sole i)=unitLetter x i := spell_sole _
lemma expression_induction {M : Expression P → Prop} (e : Expression P)
    (hm : ∀ (n : ℕ) (x : Fin n → E4) (p : Fin n → Mode P), M (letterWord x p))
    (ha : ∀ x y, M x → M y → M (x+y))
    (hs : ∀ r : ℂ, ∀ x, M x → M (r • x)) : M e := grammar_induction e
      (fun n f=>hm n (fun i=> (f i).1) (fun i=>(f i).2)) ha hs

def insertField (x : E4) (d : ℕ) : S.Field d →ₗ[ℂ] Expression P :=
  ∑ i∈bands P d, (D.test i d).smulRight (unitLetter x i)
theorem insert_formula (x d) (v : S.Field d) :
    insertField D x d v = ∑ i∈bands P d, D.test i d v • unitLetter x i := by simp [insertField]
variable (hD : D.Coherent)
include hD
lemma insert_loaded {d : ℕ} {i : Mode P} (hi : i ∈ bands P d) (x : E4) : insertField D x d (D.loaded i d) = unitLetter x i := by
  rw [insert_formula, Finset.sum_eq_single_of_mem _ hi]; simp only [(hD d).bothWays i i hi hi, if_true, one_smul]
  intro j hj hij; rw [(hD d).bothWays j i hj hi, if_neg hij, zero_smul]
lemma insert_rise (hs : S.Symmetric) (hp : P.Inclusions S) (x : E4) {n d : ℕ} (h : n ≤ d) (v : S.Field n) :
    insertField D x d (P.rise h v) = insertField D x n v := by
  rw [← (hD n).rebuilds v]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [map_smul,map_smul,map_smul, ← D.load_next hs hp i hi, insert_loaded D hD hi,
    insert_loaded D hD ((full_bands ..).mpr (((full_bands ..).mp hi).trans h))]
lemma insert_needle (hs : S.Symmetric) (hp : P.Inclusions S) (x : E4) (i : Mode P) :
    insertField D x i.1 (D.needle i) = unitLetter x i := by
  have he : i ∈ bands P i.1 := (full_bands ..).mpr le_rfl
  conv_lhs => rw [← P.arrival hs hp (D.needle i), ← D.cost i he]
  exact insert_loaded D hD he x
omit hD

def insertToken (x : E4) (p : L.Token) : Expression P := insertField D x p.1 (S.project _ p.2)
lemma insert_letter (hs : S.Symmetric) (hp : P.Inclusions S) (hD : D.Coherent) (x : E4) (i : Mode P) :
    insertToken D x (D.letter i)=unitLetter x i := by
  unfold insertToken Prescription.letter; dsimp only; rw [S.rep, insert_needle D hD hs hp]

def fieldWord (x : I → E4) (v : I → S.Tag) : Expression P := ∏ i, insertField D (x i) (v i).1 (v i).2
def tokenWord (x : I → E4) (p : I → L.Token) : Expression P := ∏ i, insertToken D (x i) (p i)
lemma token_to_field (x : I → E4) (p : I → L.Token) : tokenWord D x p = fieldWord D x (S.classTokens ∘ p) := rfl
lemma token_beside (x : I → E4) (p : I → L.Token) (y : J → E4) (q : J → L.Token) :
    tokenWord D (beside x y) (beside p q) = tokenWord D x p * tokenWord D y q := by unfold tokenWord; rw [Fintype.prod_sum_type]; rfl
lemma token_sole (x : E4) (p : L.Token) : tokenWord D (sole x) (sole p)=insertToken D x p := by simp [tokenWord, sole]
lemma field_beside (x : I → E4) (p : I → S.Tag) (y : J → E4) (q : J → S.Tag) :
    fieldWord D (beside x y) (beside p q) = fieldWord D x p * fieldWord D y q := by unfold fieldWord; rw [Fintype.prod_sum_type]; rfl
lemma field_sole (x : E4) (p : S.Tag) : fieldWord D (sole x) (sole p)=insertField D x p.1 p.2 := by simp [fieldWord,sole]; rfl
lemma letter_to_token (hs : S.Symmetric) (hp : P.Inclusions S) (hD : D.Coherent) (x : I → E4) (p : I → Mode P) :
    tokenWord D x (D.letter ∘ p)=letterWord x p := by unfold tokenWord letterWord spell; simp_rw [Function.comp_apply, insert_letter D hs hp hD]; rfl
lemma field_to_token (x : I → E4) (p : I → S.Tag) :
    fieldWord D x p = tokenWord D x (fun i=>⟨(p i).1,S.representative _ (p i).2⟩) := by simp [tokenWord,fieldWord,insertToken,S.rep]

def displayLetters : Expression P →ₐ[ℂ] Grammar L.Plant :=
  MultipleContact.Script.rewrite (fun p : E4 × Mode P => (p.1,D.letter p.2))
lemma display_unit (x : E4) (i : Mode P) : displayLetters D (unitLetter x i) = stamp (x, D.letter i) := rewrite_stamp ..
variable (T : Table L)
/-- Read any finite sum of finite products. Just uses separated Schwinger functions. -/
def readExpr : Expression P →ₗ[ℂ] ℂ := (rawSee T).comp (displayLetters D).toLinearMap
lemma read_letters (hT : T.Symmetric) (x : I → E4) (p : I → Mode P) :
    readExpr D T (letterWord x p) = totalObserve T x (D.letter ∘ p) := by
  change rawSee T ((MultipleContact.Script.rewrite _) (spell _)) = _
  rw [rewrite_spell]; exact raw_spell T hT _
variable (hT : T.Symmetric) (hh : T.respects S) (hp : P.Inclusions T)
include hD hT hh hp
lemma raw_one (p : L.Token) (x : E4) (q : Grammar L.Plant) :
    rawSee T (displayLetters D (insertToken D x p) * q) = rawSee T (stamp (x,p) * q) := by
  induction q using grammar_induction with
  | hm n f =>
    have he (p : L.Token) : rawSee T (stamp (x,p) * spell f) = totalObserve T (beside (sole x) (Prod.fst ∘ f)) (beside (sole p) (Prod.snd ∘ f)) := by
      rw [← spell_sole,← spell_beside,raw_spell T hT]; apply congrArg₂
      · funext i; cases i <;> rfl
      · funext i; cases i <;> rfl
    rw [insertToken, insert_formula,map_sum, Finset.sum_mul,map_sum]
    simp_rw [map_smul,display_unit,smul_mul_assoc, map_smul, he]
    unfold totalObserve; split
    next hx => exact Prescription.sumAll T D (Prod.snd ∘ f) hp hT hh hx hD _
    simp
  | ha a b ha hb => simp only [mul_add,map_add,ha,hb]
  | hs r a ha => simp only [mul_smul_comm,map_smul,ha]

lemma read_word (x : I → E4) (p : I → L.Token) : readExpr D T (tokenWord D x p)=totalObserve T x p := by
  unfold readExpr tokenWord; simp only [LinearMap.comp_apply,AlgHom.toLinearMap_apply,map_prod]
  have h := replace_factors (rawSee T) (fun i => displayLetters D (insertToken D (x i) (p i)))
    (fun i=> stamp (x i,p i)) Finset.univ (fun i _ q => raw_one D hD T hT hh hp (p i) (x i) q) 1
  simp only [mul_one] at h; exact h.trans (raw_spell T hT (fun i=>(x i,p i)))
lemma read_fields {n : ℕ} (x : Points n) (p : Fin n → S.Tag) :
    readExpr D T (fieldWord D x.ofLp p) = if x∈conf n then S.useAt T x p else 0 := by
  rw [field_to_token,read_word D hD T hT hh hp,totalObserve]; split
  next hx => rw [if_pos (show x∈conf n from hx)]; exact named_fin T hT (fun i=>⟨_,S.representative _ (p i).2⟩) hx
  next hx => rw [if_neg (show x∉conf n from hx)]
end YM.Contacts
