import YM.Contacts.Motions

/-!
# Local variation of readings

Finite expressions varying in parameters, with all words readable (positions
pairwise distinct in each monomial), and with explicit control of their
location within palettes. Palette at this level not obliged to be open nor to exclude
other letters of the same expression.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts
open Function Filter Set MeasureTheory Table OPE MultipleContact.Script
open scoped Classical Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {L : Register G} {S : Table L} {P : DiffPlan S}
variable {W Z I : Type} [TopologicalSpace W] [TopologicalSpace Z] [Fintype I]

inductive Displays (U : Set W) (A : W → Set E4) : (W → Expression P) → Prop
| zero : Displays U A (fun _=>0)
| atom (I : Type) [Fintype I] (x : W → I → E4) (p : I → Mode P)
    (h : ContinuousOn x U) (hp : ∀ t∈U, Injective (x t)) (hw : ∀ t∈U, Set.range (x t) ⊆ A t) :
    Displays U A (fun t=>letterWord (x t) p)
| plus {e f} : Displays U A e → Displays U A f → Displays U A (fun t=>e t+f t)
| coeff {c : W → ℂ} {e} : ContinuousOn c U → Displays U A e → Displays U A (fun t=> c t • e t)
-- restrict to U (allows various coe changes; support only used in U)
| agree {e f} : Displays U A e → EqOn e f U → Displays U A f

variable {U : Set W} {A B C : W → Set E4} {e f : W→Expression P}

namespace Displays
lemma subreg {V} (h : Displays U A e) (hu : V⊆U) (hb : ∀ t∈V, A t⊆ B t) : Displays V B e := by
  induction h with
  | zero => exact .zero
  | @atom I inst x p h h' hp => exact .atom I _ p (h.mono hu) (fun _ ht=> h' _ (hu ht)) (fun t ht => (hp t (hu ht)).trans (hb t ht))
  | plus _ _ hx hy => exact .plus hx hy
  | coeff h _ hx => exact .coeff (h.mono hu) hx
  | agree _ h hx => exact .agree hx (h.mono hu)
lemma widen (h : Displays U A e) (hb : ∀ t∈U,A t⊆ B t) : Displays U B e := subreg h (by rfl) hb
lemma minus (h : Displays U A e) : Displays U A (fun t => -e t) := by
  simpa only [neg_smul,one_smul] using coeff (e:=e) (c:=fun _=>(-1:ℂ)) continuousOn_const h
lemma diff (h : Displays U A e) (hf : Displays U A f) : Displays U A (fun t=>e t-f t) := by
  simpa only [sub_eq_add_neg] using h.plus hf.minus
omit [TopologicalSpace Z] in
lemma sum {a : Finset Z} {f : Z→W→ Expression P} (h : ∀ t∈a, Displays U A (f t)) :
   Displays U A (fun i=>∑ t∈a,f t i) := by
  induction a using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (Displays.zero : Displays (P:=P) U A _)
  | insert i a hi ih => simpa only [Finset.sum_insert hi] using (h i (by simp)).plus (ih fun j hj=> h _ (Finset.mem_insert_of_mem hj))
lemma use {V : Set Z} {q : Z → W} (h : Displays U A e) (hv : MapsTo q V U) (hq : ContinuousOn q V) : Displays V (A ∘ q) (e ∘ q) := by
  induction h with
  | zero => exact .zero
  | @atom I inst x p h h' hp => exact .atom I (x ∘ q) p (h.comp hq hv) (fun _ ht=> h' _ (hv ht)) (fun t ht=>hp _ (hv ht))
  | plus _ _ hx hy => exact .plus hx hy
  | coeff h _ hx => exact .coeff (h.comp hq hv) hx
  | agree _ h hx => exact .agree hx (fun x hx=>h (hv hx))
lemma supported (h : Displays U A e) {t : W} (ht : t∈U) : e t ∈ supportedAt (A t) := by
  induction h with
  | zero => exact (supportedAt _).zero_mem
  | @atom I inst x p h h' hp => exact (supportedAt (A t)).prod_mem (f:= fun i=>unitLetter (x t i) (p i)) (fun i _=>unit_supportedAt _ _ (hp t ht (Set.mem_range_self _)))
  | plus _ _ hx hy => exact (supportedAt _).add_mem hx hy
  | coeff h _ hx => exact (supportedAt _).smul_mem hx _
  | agree _ h hx => rw [← h ht]; exact hx
lemma times (h : ∀ t∈U, Disjoint (A t) (B t)) (he : Displays U A e) (hf : Displays U B f) :
    Displays U (fun t=> A t ∪ B t) (fun t=> e t*f t) := by
  induction he with
  | zero => simp only [zero_mul]; exact .zero
  | @atom I inst x p hx hp hw =>
    induction hf with
    | zero => simp only [mul_zero]; exact .zero
    | @atom J inst y q hy ht hu =>
      simp_rw [← letters_beside]
      apply Displays.atom
      · apply continuousOn_pi.mpr; intro i; cases i with
        | inl i=> exact continuousOn_pi.mp hx i
        | inr i=> exact continuousOn_pi.mp hy i
      · exact fun i hi=>beside_distinct.mpr ⟨hp i hi,ht i hi,fun a b hb=>Set.disjoint_left.mp (h i hi) (hb ▸ hw i hi (Set.mem_range_self a)) (hu i hi (Set.mem_range_self b))⟩
      rintro t ht s ⟨i,rfl⟩; cases i with
      | inl i=> exact Or.inl (hw t ht (Set.mem_range_self i))
      | inr i=> exact Or.inr (hu t ht (Set.mem_range_self i))
    | plus _ _ hx hy => simpa only [mul_add] using hx.plus hy
    | coeff h _ hx => simp_rw [mul_smul_comm]; exact .coeff h hx
    | agree _ h hx => exact .agree hx (fun t ht=> congrArg (letterWord (x t) p * ·) (h ht))
  | plus _ _ hx hy => simp_rw [add_mul]; exact .plus hx hy
  | coeff h _ hx => simp_rw [smul_mul_assoc]; exact .coeff h hx
  | agree _ h hx => exact .agree hx (fun i hi=> congrArg (· * f i) (h hi))
lemma constOne : Displays (P:=P) U A (fun _=> 1) := by
  have h := atom (A:=A) (U:=U) Empty (fun _ => 0) (fun i=> (i.elim : Mode P))  continuousOn_const (fun _ _=>injective_of_subsingleton _) (by rintro t ht w ⟨i,hi⟩; exact i.elim)
  simpa only [letterWord, spell, Fintype.prod_empty] using h
omit [Fintype I] in
lemma prod {a : Finset I} {A' : I→ W→ Set E4} {f : I→W→ Expression P} (hf : ∀ i∈a,Displays U (A' i) (f i))
    (hp : ∀ t∈U, (a : Set I).Pairwise fun i j => Disjoint (A' i t) (A' j t)) :
    Displays U (fun t=> ⋃ i∈ a,A' i t) (fun t=>∏ i∈a,f i t) := by
  induction a using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; apply constOne
  | @insert i a hi ih =>
    have hu : (a : Set I) ⊆ ↑(insert i a : Finset I) := Finset.coe_subset.mpr (Finset.subset_insert i a)
    specialize ih (fun j hj=>hf j (by simp [hj])) (fun t ht=> (hp t ht).mono hu)
    simp_rw [Finset.prod_insert hi,Finset.set_biUnion_insert]
    apply Displays.times (fun t ht=>?_) (hf i (by simp)) ih
    refine Set.disjoint_left.mpr (fun w hw hl=>?_); obtain ⟨j, hj, hwj⟩ := Set.mem_iUnion₂.mp hl
    exact Set.disjoint_left.mp (hp t ht (show i∈ (↑(insert i a : Finset I) : Set I) from by simp) (hu hj) (fun h=> hi (h ▸ hj))) hw hwj
lemma atPoint {x : W→ E4} (hA : ∀ t∈U,x t∈A t) (hx : ContinuousOn x U) (p : Mode P) : Displays U A (fun t=> unitLetter (x t) p) := by
  have h:= atom (P:=P) Unit (fun t=>sole (x t)) (sole p) (continuousOn_pi.mpr fun _=> hx) (fun t _=> injective_of_subsingleton _) (by rintro t ht w ⟨⟨⟩,rfl⟩; exact hA t ht)
  simpa only [letters_sole] using h
lemma field {D : Prescription P} {x : W → E4} {d : ℕ} {f : W→ S.Field d} (hA : ∀ t∈ U,x t∈A t) (hx : ContinuousOn x U) (hf : ContinuousOn f U) : Displays U A
    (fun t=> insertField D (x t) d (f t)) := by
  simp_rw [insert_formula]; apply Displays.sum; intro i hi
  exact coeff (((D.test i d).continuous_of_finiteDimensional).comp_continuousOn hf) (atPoint hA hx i)
lemma word {D : Prescription P} {x : W → I→ E4}{d : I→ℕ}{p : (i:I)→ W→ S.Field (d i)}
    (hA : ∀ t∈U,range (x t) ⊆ A t) (h : ∀ t∈U, Injective (x t)) (hx : ContinuousOn x U) (hp : ∀ i,ContinuousOn (p i) U) :
    Displays U A (fun t=>fieldWord D (x t) (fun i=>⟨d i,p i t⟩)) := by
  apply widen (prod (A':=fun i t=>{x t i}) (fun i (_:i∈(Finset.univ:Finset I))=>
    field (D:=D) (fun t _=>Set.mem_singleton _) (continuousOn_pi.mp hx i) (hp i)) (fun t ht i _ j _ he=> disjoint_singleton.mpr ((h t ht).ne he)))
    fun t ht=> by rintro z hz; obtain ⟨i,hi,h⟩:= Set.mem_iUnion₂.mp hz; exact hA t ht ((Set.mem_singleton_iff.mp h).symm ▸ Set.mem_range_self i)
lemma observes (D : Prescription P) (T : Table L) (H : T.Hierarchy) (h : Displays U A e) : ContinuousOn (fun t=> readExpr D T (e t)) U := by
  induction h with
  | zero => simpa using (continuousOn_const : ContinuousOn (fun _=> (0:ℂ)) U)
  | @atom I inst x p h h' hp =>
    refine (ContinuousOn.congr (f:=fun t=> observe T (x t) (D.letter ∘ p)) ?_ (fun t ht=> (read_letters D T H.laws.toSymmetric ..).trans (if_pos (h' t ht))))
    exact fun t ht=> (smooth_observe T H.smooth (D.letter ∘ p) (h' t ht)).comp_continuousWithinAt (h t ht)
  | plus _ _ hx hy => simp_rw [map_add]; exact hx.add hy
  | coeff h _ hx => simp_rw [map_smul]; exact h.smul hx
  | agree _ h hx => exact hx.congr fun t ht=> congr_arg (readExpr D T) (h ht).symm
end Displays
end YM.Contacts
