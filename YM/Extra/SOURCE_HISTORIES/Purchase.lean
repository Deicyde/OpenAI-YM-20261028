import YM.Extra.SOURCE_HISTORIES.Stock

/-! Exact absolute grouping/restoration of the old sector polynomial (one
source, all its meeting forced histories). -/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Histories.Attach
open Function Filter MeasureTheory Set Lattice Wilson RG Source Labels
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {n : Side} {G : Gauge} (R : Rep G n) (Y : Support n)
variable (H : Shelf R.activities) (q : ℕ)
variable (U : Config G n)

private lemma exchange (f : Config G n → ℂ) (p : Issued R Y H q U) :
    chunk R Y p.val.1 f U * coat R (stamp R Y H q p.val.1) p.val.2 U =
      f U * (R.activities.gasOccurrence R.p (redeem R Y H q U p).val U : ℂ) := by
  classical
  have he := seated R U p.property.2 p.property.1
  rw [stamp_x,stamp_i] at he
  unfold chunk coat Activities.gasOccurrence
  rw [if_pos he,if_pos p.property, if_pos (redeem R Y H q U p).property.1,
    show (redeem R Y H q U p).val = _ ∪ unchanged R Y H q U p from rfl, Finset.prod_union (separate R Y H q U p)]
  simp only [Complex.ofReal_mul, Complex.ofReal_prod, mul_assoc,unchanged]

private lemma always_meets (b : Finset ℕ) (hb : R.activities.admissible R.p U b) (hu : ¬Healthy R.p.threshold Y U) :
    (meet R Y b).Nonempty := by
  obtain ⟨x,hx,hi⟩ := Finset.not_disjoint_iff.mp hu
  rw [← hb.2] at hi
  obtain ⟨j,hj,he⟩ := Finset.mem_biUnion.mp hi
  exact ⟨j,(mem_meet ..).mpr ⟨hj,Finset.not_disjoint_iff.mpr ⟨x,(R.activities.forced j).inventory_sup he,hx⟩⟩⟩

lemma line_dominated {w : ℝ} {f : Config G n → ℂ} {C : ℝ} (hb : ∀ U, ‖f U‖ ≤ C)
    (hv : R.activities.KBound R.p w) : Dominated (line R Y H q f) := by
  obtain ⟨p,hp,hh⟩ := line_budget R Y H q hb hv
  exact ⟨_,hp.2.1,fun i U => ((hh i).2 U).trans (R.p.loMass _ _ (hh i).1)⟩

/-- Splicing a stencil bad-field multiplier at one marker gives exactly
f times the old gas **without mask restriction or division**, at every U.
`coat_all` & `Dress` guarantee the interchange; `routes` establishes
truth before even summing labels. -/
theorem paid {σ C Λ δ w : ℝ} (hv : R.Lawful σ C Λ δ w) {f : Config G n → ℂ}
    (hf : ∃ B : ℝ,∀ U, ‖f U‖ ≤ B) (hh : ∀ U, Healthy R.p.threshold Y U → f U=0) :
    ∑' b : Finset ℕ, ∑' i, line R Y H q f i U * coat R i b U = f U * (R.activities.gas R.p U : ℂ) := by
  classical
  obtain ⟨B,hB⟩ := hf
  let k := stamp R Y H q
  let g (p : Finset ℕ × ℕ) := line R Y H q f p.2 U * coat R p.2 p.1 U
  have hp : Summable g :=
    ((coat_all hv (line_dominated R Y H q hB hv.labels.boundK)).summable U).prod_symm
  let f' : Issued R Y H q U → Finset ℕ × ℕ := fun p => (p.val.2,k p.val.1)
  have ht : Injective f' := by
    intro i j he
    exact Subtype.ext (Prod.ext (k.injective (congr_arg Prod.snd he)) (congr_arg Prod.fst he))
  have hx (x) (hx : g x ≠ 0) : x ∈ range f' := by
    rcases x with ⟨b,i⟩
    change line R Y H q f i U * coat R i b U ≠ 0 at hx
    have hy : i∈range k := by by_contra he; rw [line_empty _ _ _ _ _ he] at hx; simp at hx
    obtain ⟨c,rfl⟩ := hy
    have hz : k c ∈ b ∧ R.activities.admissible R.p U b := by
      by_contra he; simp [coat,he] at hx
    exact ⟨⟨(c,b),hz⟩,rfl⟩
  let a (b : Finset ℕ) := f U * (R.activities.gasOccurrence R.p b U : ℂ)
  have ha (b) (ha : a b ≠ 0) : ∃ c : Old R Y U, c.val=b := by
    have h1 : ¬Healthy R.p.threshold Y U := fun h => ha (by simp [a,hh U h])
    have h2 : R.activities.admissible R.p U b := by by_contra h; simp [a,Activities.gasOccurrence,h] at ha
    exact ⟨⟨b,h2,always_meets R Y U b h2 h1⟩,rfl⟩
  calc
    _ = ∑' x, g x := hp.tsum_prod.symm
    _ = ∑' p, g (f' p) := (ht.tsum_eq (show Function.support g ⊆ _ from fun x h => hx x h)).symm
    _ = ∑' p : Issued R Y H q U, a (redeem R Y H q U p).val := by
      refine tsum_congr fun i => ?_
      change line R Y H q f ((stamp R Y H q) i.val.1) U * coat R _ _ _ = _
      rw [line_stamp]; exact exchange R Y H q U f i
    _ = ∑' c : Old R Y U, a c.val := (routes R Y H q U).symm.tsum_eq fun c => a c.val
    _ = ∑' b, a b := Subtype.val_injective.tsum_eq (show Function.support a ⊆ range ((↑):Old R Y U→_) from
      fun x h => ha x h)
    _ = _ := by unfold Activities.gas a; rw [Complex.ofReal_tsum,tsum_mul_left]

end YM.Extra.Histories.Attach
