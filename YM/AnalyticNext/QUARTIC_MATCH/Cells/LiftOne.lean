import YM.AnalyticNext.QUARTIC_MATCH.Cells.Long

/-!
# Costed primitive with OTHER slots present

Use any other slot as anchor; this costs only width here. Preserve closures even
in translation-tensor identities except possibly at that particular anchor. True
Laurent/cover costs. Obstruction for a degree-zero preimage uses the augmentation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.BoxChain
open Lattice Exterior Function Filter Topology Laurent
open scoped Topology BigOperators

variable {V I : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [DecidableEq I]
    {A D : ArrayC I ℤ V} {σ C : ℝ} {l r j : I}

def ClosedSlot (F : ArrayC I ℤ V) (l : I) := lower l F=0
lemma ClosedSlot.add (h : ClosedSlot A l) (hd : ClosedSlot D l) : ClosedSlot (A+D) l := by
  rw [ClosedSlot,map_add,h,hd,add_zero]
lemma ClosedSlot.sub (h : ClosedSlot A l) (hd : ClosedSlot D l) : ClosedSlot (A-D) l := by
  rw [ClosedSlot,map_sub,h,hd,sub_self]

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
lemma peek_rec (X : I → Cell ℤ) (B : ArrayC I ℤ V) : peek l X B (X l)=B X := by simp [peek]
lemma ClosedSlot.peek (h : ClosedSlot A l) (X : I → Cell ℤ) : rim (peek l X A)=0 := by
  rw [← peek_lower,h]; rfl
lemma ClosedSlot.transverse (h : ClosedSlot A l) (i : I) : ClosedSlot (lower i A) l := by rw [ClosedSlot,lower_switch i l,h,map_zero]
lemma atOperate (h : j≠l) (a : Axis) (X : I → Cell ℤ) (F : ArrayC I ℤ V) : peek l X (operate j l a F) =
    fillRay (X j).1 a (peek l X F) := by
  funext y
  change fillRay _ _ (peek l (update X l y) F) _ = _
  rw [show peek l (update X l y) F = peek l X F by funext z; simp [peek], update_self, update_of_ne h]

omit [DecidableEq I] [NormedSpace ℝ V] in
lemma Rank.zero (l : I) (k : ℕ) : Rank (0 : ArrayC I ℤ V) l k := fun _ _ => rfl

lemma Rank.higher {k : ℕ} (h : Rank A l k) (j : I) (i : Axis) : Rank (operate j l i A) l (k+1) := by
  intro X hA; unfold operate fillRay; split
  · rename_i hi
    have hh : along i (X l).1 ((X l).2.erase i) (peek l X A)=0 := by
      funext n; refine h _ ?_; rw [update_self]; have hv := Finset.card_erase_add_one hi; change ((X l).2.erase i).card ≠ k; omega
    rw [hh,Ray.solution_zero,smul_zero]
  rfl
lemma Rank.passive {k : ℕ} (h : Rank A r k) (he : r≠l) (j : I) (i : Axis) : Rank (operate j l i A) r k := by
  intro X hX
  have hh : peek l X A=0 := funext fun y => h (update X l y) (by rwa [update_of_ne he])
  rw [operate,hh,fillRay_zero]; rfl

variable [CompleteSpace V]

-- slot commutation with any unrelated axis. Needs actual summability.
lemma fillRay_sub (b : Cover) (i : Axis) {F G : Cell ℤ→V} (h : sums F) (g : sums G) :
    fillRay b i (F-G)=fillRay b i F-fillRay b i G := by
  rw [sub_eq_add_neg,← neg_one_smul ℝ G, fillRay_add b i h ?_,fillRay_scale,neg_one_smul,sub_eq_add_neg]
  exact fun x => (g x).const_smul (-1:ℝ)

private lemma fill_comm (b x : Cell ℤ) (o : Cover) (a : Axis) (f : Cell ℤ → Cell ℤ → V) (h : ∀ i, sums (f i)) :
    rim (fun i => fillRay o a (f i) x) b=fillRay o a (rim f b) x := by
  have hv (p : Cell ℤ) (s : Axis) : sums (sect s f p) := by
    rw [sect_at]; split
    · simp [sums]
    rename_i hs
    intro S
    exact (((h (p.1-step s,insert s p.2) S).sub (h (p.1,insert s p.2) S))).const_smul (sign p.2 s)
  have hh (s : Finset Axis) : fillRay o a (∑ j∈s,sect j f b) = ∑ j∈s, fillRay o a (sect j f b) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hd ih =>
      rw [Finset.sum_insert hd,Finset.sum_insert hd, fillRay_add o a (hv b j) ?_, ih]
      intro x; simp_rw [Finset.sum_apply]; exact summable_sum fun j _ => hv b j x
  rw [rim_at, rim_at, hh, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sect_at,sect_at]; split
  · rw [fillRay_zero]; rfl
  rw [fillRay_scale,fillRay_sub o a (h _) (h _)]; rfl

lemma other_fill (hp : Pricing A σ C) (hj : j≠l) (hi : r≠j) (he : r≠l) (a : Axis) :
    operate j l a (lower r A)=lower r (operate j l a A) := by
  funext X
  rw [operate, peek_else r l he,← fill_comm]
  · change rim _ _ = rim _ (X r); apply congr_arg (fun F : Cell ℤ→V => rim F (X r)); funext y
    unfold operate peek; simp only [update_of_ne (Ne.symm hi),update_of_ne (Ne.symm he)]
  exact fun y S => (hp.sum_leg hj _ S).of_norm

lemma ClosedSlot.bill (h : ClosedSlot A r) (hp : Pricing A σ C) (hj : j≠l) (hi : r≠j) (he : r≠l) (a : Axis) :
    ClosedSlot (operate j l a A) r := by
  rw [ClosedSlot,← other_fill hp hj hi he,h]
  funext X; rw [operate,show BoxChain.peek l X 0= (0 : Cell ℤ → V) from rfl,fillRay_zero]; rfl

/-- Vanish also on pivotal zero-slot augmentation when rank zero. -/
def EmptySum (A : ArrayC I ℤ V) (l : I) := ∀ X, (∑' x : Cover, peek l X A (x,∅))=0

def Shut (l j : I) (i : Axis) (F : ArrayC I ℤ V) := ∀ X, (X l).1 i≠(X j).1 i ∨ i∈(X l).2 → F X=0

lemma closed_squeeze (h : ClosedSlot A l) (hp : Pricing A σ C) (hj : j≠l) (a : Axis) (X : I → Cell ℤ) :
    (A-lower l (operate j l a A)) X = squeezed (X j).1 a (peek l X A) (X l) := by
  have hs : sums (peek l X A) := fun S => (hp.sum_leg hj X S).of_norm
  have hm := slides (X j).1 a hs
  rw [h.peek,fillRay_zero,add_zero,← atOperate hj a X A] at hm
  change A X - rim (BoxChain.peek l X (operate j l a A)) (X l) = _
  rw [hm, Pi.sub_apply, peek_rec]; abel
lemma Shut.here (h : ClosedSlot A l) (hp : Pricing A σ C) (hj : j≠l) (a : Axis) :
    Shut l j a (A-lower l (operate j l a A)) := by
  intro X hx; rw [closed_squeeze h hp hj]; unfold squeezed; split_ifs <;> grind
lemma Shut.remains {i : Axis} (z : Shut l j i A) (h : ClosedSlot A l) (hp : Pricing A σ C)
    (hj : j≠l) (a : Axis) : Shut l j i (A-lower l (operate j l a A)) := by
  by_cases w : i=a
  · subst i; exact Shut.here h hp hj a
  intro X hx; rw [closed_squeeze h hp hj]; unfold squeezed; split_ifs
  · rfl
  · have hv : along a (X l).1 (X l).2 (peek l X A)=0 := by
      funext k; refine z _ ?_; simpa [hj,w]
    rw [hv]; simp
  all_goals rfl

abbrev residueRay (j l : I) (i : Axis) (A : ArrayC I ℤ V) := A-lower l (operate j l i A)

omit [CompleteSpace V] in
lemma Pricing.erase (h : Pricing A σ C) (hj : j≠l) (a : Axis) :
    Pricing (residueRay j l a A) (σ/4) ((1+debit (σ/4)*overhead σ)*C) := by
  have he := h.rate
  have ht := ((h.fills hj a).smaller l)
  rw [add_mul,one_mul,mul_assoc]; exact (h.widen (by linarith) (by linarith) le_rfl).sub ht

lemma Leftovers (z : EmptySum A l) (hp : Pricing A σ C) (hj : j≠l) (a : Axis) :
    EmptySum (residueRay j l a A) l := by
  intro X
  let V' := operate j l a A
  have hs : sums (peek l X V') := fun S => ((hp.fills hj a).sum_leg hj X S).of_norm
  have he := totals hs
  change (∑' i : Cover,(peek l X A (i,∅)-peek l X (lower l V') (i,∅)))=_
  rw [peek_lower, ((hp.sum_leg hj X ∅).of_norm).tsum_sub (hs.rims _),he,z X,sub_self]

omit [CompleteSpace V] [NormedSpace ℝ V] in
lemma erased_null {k : ℕ} (hj : j≠l) (h : Rank A l k) (he : k=0 → EmptySum A l) (hx : ∀ i, Shut l j i A) : A=0 := by
  funext X
  by_cases hh : A X=0; · exact hh
  exfalso
  have hs i := not_or.mp (mt (hx i X) hh)
  have hz : (X l).2=∅ := Finset.eq_empty_iff_forall_notMem.mpr fun i => (hs i).2
  have hv : (X l).1=(X j).1 := funext fun i => not_not.mp (hs i).1
  have hg := he (by by_contra hK; exact hh (h X (by rw [hz]; exact Ne.symm hK))) X
  rw [tsum_eq_single (X l).1] at hg
  · rw [peek, show ((X l).1, (∅:Finset Axis))=X l by rw [← hz]] at hg
    exact hh (by simpa using hg)
  intro x hx'
  have ht : x≠(X j).1 := hv ▸ hx'
  obtain ⟨i,hi⟩ := Function.ne_iff.mp ht
  apply hx i _ (Or.inl ?_); simpa [hj]

lemma fill_finite {j l : I} (hj : j≠l) (σ : ℝ) (he : 0<σ) (k : ℕ) (s : List Axis) :
    ∃ u d : ℝ, 0<u ∧ u≤σ ∧ 0≤d ∧ ∀ (C : ℝ) (A : ArrayC I ℤ V), Pricing A σ C → Rank A l k → ClosedSlot A l →
      ∃ G : ArrayC I ℤ V, Pricing G u (d*C) ∧ Rank G l (k+1) ∧ (∀ i, i≠l → ∀ r, Rank A i r → Rank G i r) ∧
        (∀ i, i≠l → i≠j → ClosedSlot A i → ClosedSlot G i) ∧
          (∀ i, Shut l j i A ∨ i∈ s → Shut l j i (A-lower l G)) ∧
            (EmptySum A l → EmptySum (A-lower l G) l) := by
  induction s generalizing σ with
  | nil =>
    refine ⟨σ,0,he,le_rfl,le_rfl, fun C A h r hk => ?_⟩
    refine ⟨0,by rw [zero_mul]; exact Pricing.zero he,Rank.zero _ _,fun _ _ _ _ => Rank.zero _ _,
      fun _ _ _ _ => map_zero _, ?_,?_⟩
    · simp
    simp
  | cons i s ih =>
    obtain ⟨u,d,hu,he',hd,H⟩ := ih (σ/4) (by positivity)
    let g := 1+debit (σ/4)*overhead σ
    have hz : 0 ≤ g := add_nonneg zero_le_one (mul_nonneg (debit_pos _) (overhead_pos he).le)
    refine ⟨u,overhead σ+d*g,hu,he'.trans (by linarith),add_nonneg (overhead_pos he).le (mul_nonneg hd hz),?_⟩
    intro C A hp h hw
    let T := operate j l i A
    let B := A-lower l T
    have hT : Pricing T (σ/4) (overhead σ*C) := hp.fills hj _
    have ha : Pricing B (σ/4) (g*C) := hp.erase hj i
    have hb : ClosedSlot B l := hw.sub (lower_twice l T)
    have hZ : Rank T l (k+1) := h.higher j i
    obtain ⟨G,hp',hr,ha',hC,hG,hE⟩ := H _ B ha (h.sub hZ.descent) hb
    have hm : A-lower l (T+G)=B-lower l G := by rw [map_add]; unfold B; abel
    refine ⟨T+G, ?_, hZ.add hr, ?_,?_,fun m hx => hm.symm ▸ hG _ ?_, fun hx => hm.symm ▸ hE (Leftovers hx hp hj i)⟩
    · rw [add_mul,mul_assoc]; exact (hT.widen hu he' le_rfl).add hp'
    · intro t ht r hx
      have H : Rank T t r := hx.passive ht j i
      exact H.add (ha' t ht r (hx.sub (H.keeps ht)))
    · intro r hx he hS
      have H := hS.bill hp hj he hx i
      exact H.add (hC r hx he (hS.sub (H.transverse l)))
    rcases hx with hx|hx
    · exact Or.inl (hx.remains hw hp hj _)
    rcases List.mem_cons.mp hx with rfl|hx
    · exact Or.inl (Shut.here hw hp hj _)
    exact Or.inr hx

/-- Lift in one argument. Can use with ANY other argument as anchor. Width
 and constants simultaneous. Degree-zero requires no charge (augmentation zero).
 Preserves closures in other non-anchor arguments; do NOT assume automatic
 at the anchor. -/
theorem arm (l j : I) (hj : j≠l) (σ : ℝ) (he : 0<σ) (k : ℕ) :
    ∃ u d : ℝ, 0<u ∧ u≤σ ∧ 0≤d ∧ ∀ (C : ℝ) (A : ArrayC I ℤ V), Pricing A σ C → Rank A l k → ClosedSlot A l →
      (k=0 → EmptySum A l) → ∃ G : ArrayC I ℤ V, Pricing G u (d*C) ∧ Rank G l (k+1) ∧ lower l G=A ∧
        (∀ i, i≠l → ∀ r, Rank A i r → Rank G i r) ∧
          (∀ i, i≠l → i≠j → ClosedSlot A i → ClosedSlot G i) := by
  obtain ⟨u,d,h1,h2,h3,H⟩:= fill_finite (V:=V) hj σ he k (List.finRange 4)
  refine ⟨u,d,h1,h2,h3,fun C A hp hr hc h0 => ?_⟩
  obtain ⟨G,hG,hg,hp',hc',ho,he⟩ := H C A hp hr hc
  refine ⟨G,hG,hg, (sub_eq_zero.mp <| erased_null hj (hr.sub hg.descent) (fun h => he (h0 h)) (fun i => ho i (Or.inr (List.mem_finRange _)))).symm,hp',hc'⟩
end YM.AnalyticNext.QuarticMatch.BoxChain
