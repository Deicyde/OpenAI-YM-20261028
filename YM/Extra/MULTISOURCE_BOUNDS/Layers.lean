import YM.Extra.MULTISOURCE_BOUNDS.Merger


/-!
# Accounting across unforced log / repeated forced-component layers

Optional supplies towards the one-step `Raw`, see `System`. Structural
assumptions on TRUE supports/names/functions. Before L^D per-name rescaling.
Forced entries: keep one κ discount across the mandatory-parent mergers.
No positivity implied except for numerical prices. `negative` here uses the
positive cluster-coefficient sign simply because only its absolute norm will
enter a merger majorant (not claiming that sign in a physical identity).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Multi
open Function Filter Lattice RG Source Wilson Overlay Marker Labels MeasureTheory Finset LogTerms Germs Merger Repeated
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
variable {G : Gauge} {n : Side} {V : Type*}

namespace Merger.Pool
variable {α β V : Type*} {a a' b γ : ℝ} {M : ℕ} {s : α → Finset V} {X : α→Support n} {f : α → ℝ}

theorem join (h : Pool s X M a f b γ) {t : β→ Finset V} {Y : β→Support n} {g : β→ℝ} {b' γ' : ℝ}
    (h' : Pool t Y M a g b' γ') : Pool (Sum.elim s t) (Sum.elim X Y) M a (Sum.elim f g) (b+b') (γ+γ') := by
  refine ⟨Sum.rec h.positive h'.positive,Hit_merge h.hit h'.hit,fun x => ?_⟩
  apply Budget.certify
  · rintro (i|i)
    · convert! (h.root x).1 i using 1
    convert! (h'.root x).1 i using 1
  intro l
  rw [← toLeft_disjSum_toRight (u:=l),sum_disjSum]
  simpa using add_le_add (Budget.cap (h.root x) l.toLeft) (Budget.cap (h'.root x) l.toRight)

theorem vac (h : Ac.Hit X M f a γ) (hf : ∀ i,0 ≤ f i) (hb : 0≤b) (hs : ∀ i, s i = ∅) : Pool s X M a f b γ :=
  ⟨hf,h,fun _ => by simpa only [hs,Finset.notMem_empty,↓reduceIte] using! (Budget.zero (ι:=α) hb)⟩

theorem mono (h : Pool s X M a f b γ) {g : α → ℝ} {b' γ' : ℝ} (hg : ∀ i,0 ≤ g i) (he : ∀ i,g i ≤ f i)
    (ha : a' ≤ a) (hb : b ≤ b') (hγ : γ ≤ γ') : Pool s X M a' g b' γ' := by
  refine ⟨hg,fun x => Budget.mono (h.hit x) (fun i => ?_) (fun i => ?_) hγ,h.root.mono hg he ha hb⟩
  · split; exact mul_nonneg (hg _) (Real.exp_pos _).le; exact le_rfl
  split_ifs; exact mul_le_mul (he _) (Real.exp_le_exp.mpr (by gcongr)) (Real.exp_pos _).le (h.positive _); exact le_rfl

end Merger.Pool

structure Layer (G : Gauge) (V : Type*) (n : Side) where
  Id : Type
  supp : Id → Support n
  names : Id → Finset V
  value : Id → Config G n → ℂ

namespace Layer
variable (X Y O : Layer G V n) (P : BudgetPoint) (w : V → ℝ)

def combine : Layer G V n where
  Id := X.Id ⊕ Y.Id
  supp := Sum.elim X.supp Y.supp
  names := Sum.elim X.names Y.names
  value := Sum.elim X.value Y.value

abbrev weighted (g : X.Id → ℝ) := fun i => duty w (X.names i)*g i

def Covers (e : X.Id → ℝ) (κ : ℝ) := ∀ i,0≤e i ∧ ∀ U, ‖X.value i U‖ ≤ κ*e i

def joint (e : Tuple X.Id) := numbered X.supp e

def log : Layer G V n where
  Id := Tuple X.Id
  supp := X.joint
  names := nameSet X.names
  value := current X.names X.supp X.value

def negative : Layer G V n := { X.log with
    value := fun i => masked P.threshold (X.joint i) (X.log.value i) }

abbrev logPrice (P : BudgetPoint) := pay P * LogTerms.book P.power P.order

theorem logs {q : X.Id → Site n} {a b γ : ℝ} (e : X.Id → ℝ) (hw : ∀ i,0 ≤ w i) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 8*((P.B+P.B+1:ℕ):ℝ)^4*γ ≤ 1) (hγ : 0 ≤ γ)
    (hi : ∀ i, q i∈X.supp i ∧ P.Regular (X.supp i) (X.value i) ∧ P.supBounds (q i) (X.supp i) (X.value i) (e i))
    (h : Pool X.names X.supp P.B (a+2) (X.weighted w e) b γ) :
    ∃ g : Tuple X.Id → ℝ, (∀ i,0 ≤ g i ∧ P.Regular (X.joint i) (X.log.value i) ∧
      ∀ p∈X.joint i,P.supBounds p (X.joint i) (X.log.value i) (g i)) ∧
      Pool X.log.names X.joint P.B a (X.log.weighted w g) (logPrice P*(2*b)) (logPrice P*(2*γ)) ∧
      (X.negative P).Covers g 1 := by
  obtain ⟨f,hf,he,hh⟩ := (LogTerms.estimates P).2 X.value X.supp q e X.names w a b γ hb ha hγ hc hw hi h.root h.hit
  refine ⟨f,hf,⟨fun i => mul_nonneg (prod_nonneg fun v _ => hw v) (hf i).1,hh,he⟩,fun i => ⟨(hf i).1,fun U => ?_⟩⟩
  rw [one_mul]; by_cases hy : Healthy P.threshold (X.joint i) U
  · have hp : q (i.2 0)∈ X.joint i := mem_biUnion.mpr ⟨0,mem_univ _,(hi _).1⟩
    simp only [negative,masked_eq _ _ _ _ hy]; exact ((hf i).2.2 _ hp).2 U hy [] (Nat.zero_le _) (by simp)
  simp only [negative,masked_ne _ _ _ _ hy,norm_zero]; exact (hf i).1

lemma combine_weighted (e : X.Id→ℝ) (f : Y.Id→ℝ) : (combine X Y).weighted w (Sum.elim e f) = Sum.elim (X.weighted w e) (Y.weighted w f) :=
  funext (Sum.rec (fun _ => rfl) fun _ => rfl)

/-- Numerical test on a merger of forced X and optional/enlarged letters Y.
At fixed configuration, each nonzero output dominated by the actual
multiset product divided by its factorials. Each charged output costs one
old forced or more. No orientation or symmetry change inferred. -/
structure Merge : Prop where
  bill : ∃ m : O.Id → Multiset (X.combine Y).Id, Set.InjOn m {i | O.value i≠0} ∧
    ∀ i, O.value i ≠ 0 → ∃ j : X.Id, Sum.inl j ∈ m i ∧
      mesh (X.combine Y).supp (m i) ∧ O.supp i ⊆ collect (X.combine Y).supp (m i) ∧
      O.names i = collect (X.combine Y).names (m i) ∧ ((m i).toFinset : Set (X.combine Y).Id).PairwiseDisjoint (X.combine Y).names ∧
      (∀ j, 2 ≤ (m i).count j → (X.combine Y).names j = ∅) ∧ ∀ U, ‖O.value i U‖ ≤ paid (fun j => ‖(X.combine Y).value j U‖) (m i)

lemma Merge.display (h : Merge X Y O) {κ : ℝ} (hk : 0 ≤ κ) (hk' : κ ≤ 1) {e : X.Id → ℝ} {f : Y.Id→ℝ}
    (he : X.Covers e κ) (hf : Y.Covers f 1) : ∃ g, O.Covers g κ ∧
      Display (X.combine Y).names (X.combine Y).supp O.names O.supp (Sum.elim e f) g 1 := by
  obtain ⟨m,hi,hH⟩ := h.bill
  let g i := if O.value i ≠ 0 then paid (Sum.elim e f) (m i) else 0
  have hC i (hi : 0<g i) : O.value i ≠ 0 := by by_contra he; simp [g,not_ne_iff.mp (not_not.mpr he)] at hi
  have hv : ∀ i, 0 ≤ Sum.elim e f i := Sum.rec (fun i => (he i).1) fun i => (hf i).1
  refine ⟨g,fun i => ?_,⟨m,hi.mono (fun i => hC i),fun i hi => ?_⟩⟩
  · unfold g; split <;> rename_i hh
    · obtain ⟨j,hj,_,_,_,_,_,h⟩ := hH i hh
      obtain ⟨s,hs⟩ := Multiset.exists_cons_of_mem hj
      refine ⟨paid_nonneg hv _, fun U => (h U).trans ?_⟩
      dsimp only [combine] at m ⊢; unfold paid; rw [hs,Multiset.map_cons,Multiset.map_cons,Multiset.prod_cons,Multiset.prod_cons,←mul_div_assoc,←mul_assoc]; gcongr
      · exact (Multiset.prod_map_nonneg (by exact fun _ _ => norm_nonneg _))
      · exact mul_nonneg hk (he j).1
      · exact (he _).2 _
      exact Multiset.prod_map_le_prod_map₀ _ _ (fun i _ => norm_nonneg _) fun i _ => (by
        rcases i with j|j; exact ((he j).2 _).trans (mul_le_of_le_one_left (he j).1 hk'); simpa [combine] using (hf j).2 U)
    simp [not_ne_iff.mp hh]
  obtain ⟨_,_,ht,hg,hb,hc,hz,_⟩ := hH i (hC i hi)
  exact ⟨ht,hg,hb,hc,hz,by dsimp only [combine]; rw [one_mul,show g i = _ from if_pos (hC i hi)]⟩

lemma Merge.estimate (h : Merge X Y O) (w : V → ℝ) (hw : ∀ i, 0 ≤ w i) {a κ b b' γ γ' : ℝ} {M : ℕ} (ha : 0≤a)
    (hb : 0 ≤ b+b') (hγ : 0≤γ+γ') (hh : 8*((M+M+1:ℕ):ℝ)^4*(γ+γ') ≤ 1) (hk : 0 ≤ κ) (hk' : κ ≤ 1)
    {e : X.Id → ℝ} {f : Y.Id → ℝ} (he : X.Covers e κ) (hf : Y.Covers f 1)
    (hX : Pool X.names X.supp M (a+1) (X.weighted w e) b γ) (hY : Pool Y.names Y.supp M (a+1) (Y.weighted w f) b' γ') :
    ∃ g, O.Covers g κ ∧ Pool O.names O.supp M a (O.weighted w g) (2*(b+b')) (2*(γ+γ')) := by
  have he' : Pool (X.combine Y).names (X.combine Y).supp M (a+1) ((X.combine Y).weighted w (Sum.elim e f)) _ _ :=
    combine_weighted .. ▸ hX.join hY
  obtain ⟨g,hg,hh'⟩ := h.display _ _ _ hk hk' he hf
  exact ⟨g,hg,by simpa only [one_mul] using (he'.resold hh' hw (fun i => (hg i).1) ha hγ hh hb zero_le_one)⟩

end Layer
end YM.Extra.Multi
