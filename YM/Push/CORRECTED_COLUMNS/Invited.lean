import YM.Bid.Craft
import YM.Push.CORRECTED_COLUMNS.Meet
import YM.Push.CORRECTED_COLUMNS.Pad

/-!
# Using the failed-mask reserve in a new shared Rep

One set of merged addresses in each given calculation. The empty
padding may be common to all preparations at this vacuum, possibly used
for different combinations for each computation of an entire polynomial.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Corrected.UnionK
open Set Function MeasureTheory Filter Lattice Wilson RG Marker Width
open Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {V A : Type*} [DecidableEq A] [Fintype A] [DecidableEq V]
variable {P : Rep G n} {R : Census V} {v : V → Site n}
variable (L : Original P v R) (Q : AddedHeads P v R A)

omit [Fintype A] [DecidableEq A] in
private lemma one_one : Injective (singleton Q) := by
  intro i j he; exact Sum.inl.inj (Finset.singleton_inj.mp (congr_arg Subtype.val he))
def names (p : Piece Q) : Pad.Shape n := ⟨(unionOf Q p.val,inventory P p.val),rich_inv p,sized _⟩

omit [Fintype A] [DecidableEq A] in
private lemma unpopular (p : Piece Q) (h : ¬∃ i, p=singleton Q i) : p.val.toRight.Nonempty := by
  by_contra he; exact h (leftover Q (Finset.not_nonempty_iff_eq_empty.mp he))

private abbrev enc : Denumerable (Piece Q) := by
  classical
  haveI : Infinite (Piece Q) := Infinite.of_injective _ (one_one Q)
  exact Classical.choice (nonempty_denumerable _)
def newIndex := @Denumerable.eqv (Piece Q) (enc Q)
open scoped Classical in
def file (p : Piece Q) : ℕ := if h : ∃ i, p=singleton Q i then Pad.original n h.choose else Pad.slot (names Q p) (newIndex Q p)

omit [DecidableEq A] in
lemma atFile (i : ℕ) : file Q (singleton Q i) = Pad.original n i := by
  unfold file
  have h : ∃ j, singleton Q i=singleton Q j := ⟨_,rfl⟩
  rw [dif_pos h, (one_one Q h.choose_spec).symm]
omit [DecidableEq A] in
lemma fileRecords (p : Piece Q) : oldSites (Pad.enlarge P) (file Q p) = unionOf Q p.val ∧ claims (Pad.enlarge P) (file Q p)=inventory P p.val := by
  by_cases he : ∃ i,p=singleton Q i
  · obtain ⟨i,rfl⟩ := he; rw [atFile,was, still]; exact ⟨(Pad.old_shape P i).2,(Pad.old_shape P i).1⟩
  unfold file; rw [dif_neg he]; exact ⟨(Pad.new_shape ..).2,(Pad.new_shape ..).1⟩
omit [DecidableEq A] in
lemma specific : Injective (file Q) := by
  intro p q h; unfold file at h
  split_ifs at h with hp hq hq
  · exact hp.choose_spec.trans ((congr_arg _ (Pad.original_inj n h)).trans hq.choose_spec.symm)
  · have hh := (Pad.number n).injective (show Pad.number n _ = _ from h); cases hh -- type
  · have hh := (Pad.number n).injective (show Pad.number n _ = _ from h); cases hh
  have hh := congr_arg Prod.snd (Sum.inr.inj ((Pad.number n).injective h)); exact (newIndex Q).injective hh

-- Build Original on the new Rep
private def place := Function.extend (file Q) (activated L (Q:=Q)) (fun _ => 0)
omit [DecidableEq A] in
lemma obtained (i : Piece Q) : place L Q (file Q i)=activated L i := (specific Q).extend_apply ..
omit [DecidableEq A] in
lemma absent {i} (h : i ∉ Set.range (file Q)) : place L Q i=0 := Function.extend_apply' _ _ i h

def issue : Original (Pad.enlarge P) v R where
  value := place L Q
  pure i U := by
    by_cases h : i∈Set.range (file Q)
    · obtain ⟨y,rfl⟩ := h; rw [obtained]
      by_cases hh : ∃ b,y=singleton Q b
      · obtain ⟨b,rfl⟩ := hh; rw [atFile,Pad.subject,older,L.pure]
      unfold file; rw [dif_neg hh,Pad.emptyK]; simp only [onlyMarks L Q _ (unpopular Q y hh), Pi.zero_apply, Complex.ofReal_zero]
    obtain (⟨j,rfl⟩|⟨p,j,rfl⟩) := Pad.casesTag (n:=n) i
    · exact False.elim (h ⟨_,atFile Q j⟩)
    rw [absent _ _ h,Pad.emptyK]; simp only [Pi.zero_apply,Poly.part_nil,Complex.ofReal_zero]
  locality i := by
    by_cases h : i∈Set.range (file Q)
    · obtain ⟨y,rfl⟩ := h; rw [obtained,(fileRecords Q y).1]; exact gathered L y
    rw [absent L Q h]; exact ⟨fun _ _=>rfl,measurable_const,fun _ _ _ _=>rfl,fun _ _ he => (he rfl).elim⟩
  keeps i U hu := by
    by_cases h : i∈Set.range (file Q)
    · obtain ⟨y,rfl⟩ := h
      rw [obtained] at hu
      by_cases hy : ∃ b,y=singleton Q b
      · obtain ⟨b,rfl⟩ := hy; rw [atFile]; rw [older] at hu
        unfold permits; rw [Pad.same]; exact L.keeps b _ hu
      have hh : actual y U := by by_contra hb; exact hu (if_neg hb)
      refine ⟨?_,?_⟩
      · have hx := fileRecords Q y
        change oldSites _ _∩ flags P.p.threshold U=claims _ _; rw [hx.1,hx.2]; exact hh
      unfold file; rw [dif_neg hy,Pad.empty]; trivial
    rw [absent L Q h] at hu; exact (hu rfl).elim

omit [DecidableEq A] in
lemma post (U : Config G n) (X : Finset (Piece Q)) :
    oldEval (issue L Q) (X.image (file Q)) U=newEval L Q X U := by
  have ht : (Pad.enlarge P).activities.admissible (Pad.enlarge P).p U (X.image (file Q)) ↔ lives Q X U := by
    have hi : (X.image (file Q)).biUnion (fun i => claims (Pad.enlarge P) i)=X.biUnion (fun i => inventory P i.val) := by
      ext; simp [← (fileRecords Q _).2]
    unfold lives Activities.admissible; rw [hi]; apply and_congr_left
    intro hb; constructor
    · intro H i hf j hh h
      change Disjoint (unionOf Q i.val) (unionOf Q j.val)
      rw [← (fileRecords Q i).1, ← (fileRecords Q j).1]
      exact H (mem_image_of_mem _ hf) (mem_image_of_mem _ hh) ((specific Q).ne h)
    intro H i hf j hh h
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hf
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hh
    have he : Disjoint (unionOf Q y.val) (unionOf Q z.val) := (H hy hz (fun e => h (congr_arg _ e)))
    rwa [← (fileRecords Q y).1, ← (fileRecords Q z).1] at he
  unfold oldEval newEval; split_ifs with h h' h'
  · rw [Finset.prod_image (specific Q).injOn]; exact Finset.prod_congr rfl (fun i _ => congr_fun (obtained L Q i) U)
  · exact (h' (ht.1 h)).elim
  · exact (h (ht.2 h')).elim
  rfl
omit [DecidableEq A] in
lemma post_sum (U : Config G n) : (∑' i, oldEval (issue L Q) i U)=∑' J,newEval L Q J U := by
  symm; apply Pad.sums _ (Finset.image_injective (specific Q)) _ _ (fun i => post L Q _ _) -- apply
  intro i hi; apply Pad.inclusive
  intro j hj; by_contra H; apply hi
  change oldEval _ _ _=0; unfold oldEval; split
  · exact Finset.prod_eq_zero hj (by rw [show (issue L Q).value j=0 from absent L Q H]; rfl)
  rfl

variable {M : ℕ} {a w : ℝ} {p : V → ℝ}
-- cleaned K hit
omit [DecidableEq A] in
lemma rigid (Y : ℕ ⊕ A → Poly R) (hv : ∀ i U, Width.Covered (value L Q i U) (Y i))
    (he : Ac.Hit (fun z : Piece Q => unionOf Q z.val) M (fun z => Poly.price p (limit Y z)) a w) :
    ∃ F : ℕ → Poly R, (∀ i U, Width.Covered ((issue L Q).value i U) (F i)) ∧
        Ac.Hit (oldSites (Pad.enlarge P)) M (fun i => Poly.price p (F i)) a w := by
  let f := file Q
  let F := Function.extend f (limit (Q:=Q) Y) (fun _=>0)
  have hf i : F (f i)=limit Y i := (specific Q).extend_apply ..
  have hh i (hi : i∉Set.range f) : F i=0 := extend_apply' _ _ _ hi
  refine ⟨F,fun i U => ?_,fun x => ?_⟩
  · change Covered (place L Q i U) (F i)
    by_cases hi : i∈ Set.range f
    · obtain ⟨y,rfl⟩ := hi; rw [hf,obtained]; exact dominated L Y hv y U
    rw [hh _ hi,absent L Q hi]; exact fun i => ⟨by simp,rfl⟩
  refine Pad.absolute f (specific Q) ?_ ?_ (he x)
  · intro i; dsimp only; rw [hf,(fileRecords ..).1]
  intro i hi; by_contra HB; apply hi; dsimp only; split <;> first | rfl | (rw [hh i HB]; simp)

-- enough for absolute convergence of old and new sums (not just all nonzero terms finite)
section
variable {P' : Rep G n} (O : Original P' v R)

private lemma global {M : ℕ} {k a : ℝ} (ha : 0 ≤ a) {f : ℕ → ℝ} (hf : ∀ i, 0≤ f i) (h : Ac.Hit (oldSites P') M f a k) : Summable f := by
  let v (x : Site n) i := if x∈ oldSites P' i then f i * Real.exp (a*coverNumber M (oldSites P' i)) else 0
  have he i : f i ≤ ∑ x,v x i := by
    obtain ⟨x,hx⟩ := (P'.activities.forced i).inventory_ne
    have hx' : x∈oldSites P' i := (P'.activities.forced i).inventory_sup hx
    apply le_trans _ (Finset.single_le_sum (f:=fun x => v x i) (fun x _ => (h x).1 i) (Finset.mem_univ x))
    unfold v; rw [if_pos hx']; exact le_mul_of_one_le_right (hf i) (Real.one_le_exp (by positivity))
  exact (summable_sum (f:=v) (s:=Finset.univ) (fun x _ => (h x).2.1)).of_nonneg_of_le hf he
lemma assess {F : ℕ → Poly R} (hF : ∀ i U, Width.Covered (O.value i U) (F i))
    (hp : ∀ i : V, 0<p i) (he : Ac.Hit (oldSites P') M (fun i => Poly.price p (F i)) a w) (ha : 0≤a) (U : Config G n) :
    Summable fun i => ‖oldEval O i U‖ := by
  have hn i : 0≤Poly.price p (F i) := Poly.nonnegative hp _
  obtain ⟨k,hk,H⟩ := Poly.equivalent_norm (R:=R) hp
  let t i := Poly.price p (F i)
  have hh (i : Finset ℕ) : Poly.price p (oldEval O i U) ≤ ∏ j∈i,t j := by
    unfold oldEval; split
    · exact ((Width.bulk i (F:=fun j => O.value j U) (fun j _=> hF j U)).reprice p hp).trans (Poly.multiple hp ..)
    rw [Poly.zero_price]; exact Finset.prod_nonneg fun j _ => hn _
  have hi := summable_finsetProd_of_summable_nonneg hn (global ha hn he)
  apply (hi.mul_right k).of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => (H _).trans (mul_le_mul_of_nonneg_right (hh i) hk))
end
end YM.Push.Corrected.UnionK
