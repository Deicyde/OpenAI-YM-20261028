import YM.Extra.SOURCE_HISTORIES.Aggregate

/-!
Apply `AtomStep` to a column, rebased so its current x *is* a basis
vector. Summation costs & actual push identities on the column. No
assumption of coherent choices even *within* calculation of this column.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Histories
open Lattice Wilson RG Source Function Filter Set MeasureTheory Bid Labels Motion
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {d : ℕ}
variable {F : Labels.Frame G d} (B : SectionData F) (H : History G) (N p m : ℕ) (A : Hol G)

namespace InputColumn
-- root sum on One ⊕ (regular ⊕ forced)
abbrev Listing : Type := Unit ⊕ (ℕ ⊕ ℕ)

def consist {E : Type*} (x : E) (u v : ℕ → E) : Listing → E := Sum.elim (fun _ => x) (Sum.elim u v)

lemma added {E : Type*} [AddCommMonoid E] [TopologicalSpace E] [ContinuousAdd E] {f : Listing → E}
    {U V} (hp : HasSum (fun i => f (.inr (.inl i))) U) (hq : HasSum (fun i => f (.inr (.inr i))) V) :
    HasSum f (f (Sum.inl ()) + (U+V)) := by
  have h : HasSum (f ∘ Sum.inl) (f (Sum.inl ())) := by simpa using hasSum_fintype (f ∘ Sum.inl)
  exact h.sum (HasSum.sum hp hq)

lemma dominated {W : Type*} {f : Listing → W → ℂ} (ht : ∃ c : ℝ, ∀ i, ‖f (.inl ()) i‖ ≤ c)
    (hp : Dominated fun i => f (.inr (.inl i))) (hq : Dominated fun i => f (.inr (.inr i))) : Dominated f := by
  obtain ⟨c,hc⟩ := ht
  obtain ⟨a,ha,hu⟩ := hp
  obtain ⟨b,hb,hv⟩ := hq
  refine ⟨consist c a b, (added (f:=consist c a b) ha.hasSum hb.hasSum).summable,?_⟩
  rintro (x | (y | z)) U
  · exact hc _
  · exact hu ..
  exact hv ..

private lemma scalar_price {W : Type*} {u : W → ℂ} {f : ℕ → W → ℂ} (h : Dominated f) (hv : ∃ c : ℝ, ∀ x, ‖u x‖ ≤ c) :
    Dominated fun i x => u x * f i x := by
  obtain ⟨b,hb,hr⟩ := h
  obtain ⟨c,hh⟩ := hv
  refine ⟨_,hb.mul_left c,fun i x => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (hh x) (hr ..) (norm_nonneg _) ((norm_nonneg _).trans (hh x))

variable {T : Heading F} {C η t : ℝ}

/-- The costs after merge. Cone on the input is not even needed yet. -/
theorem individual (Q : Coefficient F (H.S.side (m+1) p)) (v : F.Coeff) (hr : H.Selected) (hM : m<N)
    (hp : AtomStep B H N p m A T C η) (hd : 0 ≤ η) (hi : Q.x=v)
    (h : Q.Format 0 A (H.rep N p (m+1)))
    (hw : Q.remBound 0 (H.rep N p (m+1)) (Real.sqrt (H.levels.clock.forcedAllowance (m+1))) t)
    (hPay : PaidAtom B H N p m A ((primary 0 v).density 0 B (H.rep N p (m+1)))
      (T.leads (H.S.block m) v) (η*F.coeffSize (F.core v)) (C * F.coeffSize (vowel F (H.S.block m) (F.core v)))) :
    let L := H.S.block m
    PaidAtom B H N p m A (Q.density 0 B (H.rep N p (m+1))) (T.leads L v)
      (η*(F.coeffSize (F.core v)+t)) (C*F.coeffSize (vowel F L (F.core v))+η*t) := by
  intro L
  let R := H.rep N p (m+1)
  let y := Real.sqrt (H.levels.clock.forcedAllowance (m+1))
  let x := F.coeffSize (F.core v)
  let D := F.coeffSize (vowel F L (F.core v))
  let f := consist ((primary 0 v).density 0 B R) (fun i => salary R (Q.support i) (Q.regular i)) (fun i => fare R i (Q.forced i))
  have hk := (hr.represents N p (m+1) hM).good
  have h0 : 0 < y := Real.sqrt_pos.2 (forcedPos ..)
  have he := Coefficient.envelope B hk (primary_rem v h0) (primary_format (o:=0) (H:=A) v)
  have hE := Rep.envelope R hk
  have hR := (Rep.exponentEnv R hk).exp
  have hL := rem_dominated hw
  have hu : Dominated f := by
    refine dominated he.cost (scalar_price (Q.regular_series hw) ?_) (scalar_price (dress_abs hk hL) ?_)
    · obtain ⟨c,hc⟩ := hE.cost; exact ⟨c, fun i => (Complex.norm_real _).trans_le (hc i)⟩
    obtain ⟨c,hc⟩ := hR.cost; exact ⟨c, fun i => (Complex.norm_real _).trans_le (hc i)⟩
  have hf (i : Listing) : Measurable (f i) := by
    cases i with
    | inl j => exact he.meas
    | inr j =>
      cases j with
      | inl i => exact (Complex.continuous_ofReal.measurable.comp hE.meas).mul (masked_measurable _ _ _ (h.smooth i).borel)
      | inr i => exact (Complex.continuous_ofReal.measurable.comp hR.meas).mul ((h.borel i).mul (dressed_meas hk i))
  have hv : Q.density 0 B R = fun U => ∑' i, f i U := by
    funext U
    let a i := Q.maskedTerm R i U
    let b i := Q.forced i U * dressed R i U
    have hm : HasSum a (∑' i, a i) := ((Q.regular_series hw).summable U).hasSum
    have hn : HasSum b (∑' i, b i) := ((dress_abs hk hL).summable U).hasSum
    rw [(added (f:=fun i => f i U) (hm.mul_left (R.eval U:ℂ)) (hn.mul_left (Real.exp (R.exponent U):ℂ))).tsum_eq]
    change _ = (primary 0 v).density 0 B R U + _
    rw [primary_density,Coefficient.density,dress_eq hk hL]
    change (R.eval U:ℂ)*(part B 0 R U Q.x+∑' i,a i) + _ = _
    rw [show Q.x=v from hi]; unfold b; ring
  obtain ⟨r,s,ha,hb,hS,-,⟨a,hA,hA'⟩,b,hB,hB'⟩ := hw
  let u : Listing → F.Coeff := consist (T.leads L v) (fun _ => 0) (fun _ => 0)
  let g i := R.p.mass (Q.support i) (a i)
  let k i := (R.p.mass (R.activities.forced i).support (b i))/y
  let V := consist (η*x) (fun i => η*g i) (fun i => η*k i)
  let W := consist (C*D) (fun i => η*g i) (fun i => η*k i)
  have ht (j : Listing) : PaidAtom B H N p m A (f j) (u j) (V j) (W j) := by
    cases j with
    | inl j => exact hPay
    | inr j =>
      cases j with
      | inl j => exact hp.regular _ _ _ ⟨h.smooth j,h.origin j,h.identity_null j,h.projects j⟩ (hA' j)
      | inr j =>
        exact hp.forced _ _ _ ⟨h.invariant j,h.borel j,h.supported j,h.carried j,h.forcing j⟩ (hB' j).1 (hB' j).2
  have hi : HasSum u (T.leads L v) := by simpa [u,consist] using added (f:=u) hasSum_zero hasSum_zero
  have hy : Summable fun i => F.coeffSize (u i) := Summable.sum _ (hasSum_fintype _).summable (by
    apply Summable.sum; all_goals simp [u,consist,comp_def,Frame.coeffSize])
  have Hg : HasSum g (∑' i, g i) := hA.2.1.hasSum
  have Hk : HasSum k (∑' i, k i) := (hB.2.1.div_const y).hasSum
  let z := η * ∑' i, g i + η * ∑' i, k i
  have hV : HasSum V (η*x + z) := added (f:=V) (Hg.mul_left η) (Hk.mul_left η)
  have hW : HasSum W (C*D + z) := added (f:=W) (Hg.mul_left η) (Hk.mul_left η)
  have hx : z ≤ η*t := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hS hd)
    have hz : ∑' i, k i ≤ s := by
      unfold k; rw [tsum_div_const]
      exact (div_le_iff₀ h0).mpr (le_trans hB.2.2 (by dsimp [y]; rw [mul_comm]))
    unfold z; rw [mul_add]; exact add_le_add (mul_le_mul_of_nonneg_left hA.2.2 hd) (mul_le_mul_of_nonneg_left hz hd)
  have HH := atom_total B H N p m A hr hM.le ht hu hf hy hV.summable hW.summable
  rw [← hv, hi.tsum_eq,hV.tsum_eq,hW.tsum_eq] at HH
  apply atom_mono HH
  · rw [mul_add]; exact add_le_add_right hx _
  exact add_le_add_right hx _

theorem main (Q : Coefficient F (H.S.side (m+1) p)) (i : F.Index) (hr : H.Selected) (hM : m<N)
    (hp : AtomStep B H N p m A T C η) (hd : 0 ≤ η) (hi : Q.x=Size.axis F i)
    (h : Q.Format 0 A (H.rep N p (m+1)))
    (hw : Q.remBound 0 (H.rep N p (m+1)) (Real.sqrt (H.levels.clock.forcedAllowance (m+1))) t) :
    let v := Size.axis F i
    let L := H.S.block m
    PaidAtom B H N p m A (Q.density 0 B (H.rep N p (m+1))) (T.leads L v)
      (η*(F.coeffSize (F.core v)+t)) (C*F.coeffSize (vowel F L (F.core v))+η*t) := by
  intro v L
  apply individual B H N p m A Q v hr hM hp hd hi h hw
  by_cases ht : i=0
  · subst i; exact paid_one B H N p m A T C η hr hM
  exact hp.main i ht

end InputColumn
end YM.Extra.Histories
