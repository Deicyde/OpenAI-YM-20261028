import YM.Planned.ATOM_GUARDED_LAYOUT.Orbit
import YM.Push.LOCAL_SPLITTING.Direct


/-!
# The nil-direction inputs really are single addresses of Coefficient,
with their stated price, integrability and the specified prior.

In particular, summing the forced orbit in `fare` hasn't changed a sign
or overlap decision. The equality below uses the absolutely justified
interchange of `dress_eq`. No positive lower envelope on the output
vacuum is needed for these facts or for the main adapter.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.GuardedAtom
open Function Filter MeasureTheory Lattice Wilson RG Source Labels Bid Push.Local Next.Foundations Extra.Histories
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff

namespace Fine
variable {G : Gauge} {n : Side} {d : ℕ} {F : Labels.Frame G d}
  {A : Hol G} {B : SectionData F} {R : Rep G n} {o : Site n}

private lemma one_budget {i : ℕ} {g : ℕ → ℝ} (h : 0 ≤ g i) (he : ∀ j, j≠i → g j=0) : SumBudget g (g i) := by
  have hn j (hj : j∉({i}:Finset ℕ)) := he j (by simpa using hj)
  refine ⟨fun j => ?_,summable_of_ne_finset_zero hn,(tsum_eq_single i he).le⟩
  rcases eq_or_ne j i with hx|hx
  · exact hx.symm ▸ h
  rw [he _ hx]

/-- Support remains anchored even on all the other (zero) regular entries. -/
def exactReg (F : Labels.Frame G d) (X : Support n) (f : Config G n → ℂ) : Coefficient F n where
  x := 0
  support _ := X
  regular i := if i=0 then f else 0
  forced := 0

def exactSlot (F : Labels.Frame G d) (o : Site n) (i : ℕ) (f : Config G n → ℂ) : Coefficient F n where
  x := 0
  support _ := {o}
  regular := 0
  forced j := if j=i then f else 0

variable {X : Support n} {f : Config G n → ℂ} {i : ℕ} {κ c : ℝ}



lemma format_slot (h : SlotFit R o i f) : (exactSlot F o i f).Format o A R := by
  let M := exactSlot F o i f
  have he j : SlotFit R o j (M.forced j) := by
    by_cases H : j=i
    · simpa [M,exactSlot,H] using (H.symm ▸ h : SlotFit R o j f)
    simp only [M,exactSlot,if_neg H]; exact slot_zero ..
  exact ⟨fun _ => (regular0 _ _ o).1, fun _ => Finset.mem_singleton_self _, fun _ => rfl,fun _ _ => vanishing0 d o A,
    fun j => (he j).permits, fun j => (he j).tagged, fun j => (he j).invariant,fun j => (he j).read,fun j => (he j).borel⟩



lemma rem_slot (hκ : 0<κ) (hc : 0≤c) (h : ∀ U, ‖f U‖ ≤ c) :
    (exactSlot F o i f).remBound o R κ (R.p.mass (R.activities.forced i).support c/κ) := by
  let e (j : ℕ) := if j=i then c else 0
  let u := R.p.mass (R.activities.forced i).support c
  have hu : 0 ≤ u := hc.trans (R.p.loMass _ _ hc)
  have hx : κ*(u/κ)=u := by field_simp
  refine rem_tabs.mpr ⟨0,u/κ,⟨hκ,le_rfl,div_nonneg hu hκ.le,⟨fun _ => 0,budget0 _ _,fun _ => (regular0 _ _ o).2⟩, e, ?_,fun j => ?_⟩,by simp [u]⟩
  · rw [hx]; simpa only [Push.Local.patch,e,if_pos rfl] using
      one_budget (i:=i) (g:=fun j => R.p.mass (Push.Local.patch R.activities j) (e j)) (by simpa [e,Push.Local.patch,u] using hu) (fun j hj => by simp [e,hj,BudgetPoint.mass])
  by_cases H : j=i
  · simpa only [exactSlot,e,if_pos H] using And.intro hc h
  simp only [exactSlot,e,if_neg H,Pi.zero_apply,norm_zero]; simp



lemma slot_fare {σ C Λ δ v : ℝ} (h : R.Lawful σ C Λ δ v)
    {c : ℝ} (hc : 0≤c) (hf : ∀ U, ‖f U‖ ≤ c) : (exactSlot F o i f).density o B R = fare R i f := by
  funext U
  let M := exactSlot F o i f
  have he : M.exponentialEntry o B R U=0 := by
    have hg j : M.maskedTerm R j U=0 := congr_fun (map_zero (maskLinear R.p.threshold {o})) U
    unfold Coefficient.exponentialEntry; simp_rw [hg,tsum_zero]
    by_cases h : Healthy R.p.threshold (B.footprint o) U <;> simp [M,exactSlot,h,SectionData.places,SectionData.evaluate]
  have hw : Dominated M.forced := rem_dominated (rem_slot (F:=F) (o:=o) (i:=i) (R:=R) (show (0:ℝ)<1 from one_pos) hc hf)
  change M.density .. = _
  rw [Coefficient.density,he,dress_eq h hw, tsum_eq_single (f:=fun j => M.forced j U * dressed R j U) i _]
  · simp [M,exactSlot,fare]
  intro j hj; simp [M,exactSlot,hj]

/-! In particular, every input permits actual integration against the actual
prior (not relying on Bochner defaults) and is gauge invariant on the selected
history. -/
variable {H : History G} {N p j : ℕ} (h : H.Selected) (hj : j ≤ N) (ht : B.Sound A)
  {Q : Coefficient F (H.S.side j p)}
local notation "Cur" => H.rep N p j
include h hj ht

theorem ready {o : Site (H.S.side j p)} (hf : Q.Format o A Cur) (he : Q.remBound o Cur κ c) :
    Envelope (Q.density o B Cur) ∧ GaugeInvariant (Q.density o B Cur) :=
  let hd := (h.represents N p j hj).good
  ⟨Q.envelope B hd he hf,Kernel.insertion_gauge ht hd hf (Kernel.vacuum_actual (p:=p) h hj).2.1⟩



omit ht in
theorem ready_salary {o : Site (H.S.side j p)} {f : Config G (H.S.side j p) → ℂ} {X : Support (H.S.side j p)}
    (hf : RegFit Cur o d A X f) (he : (Cur).p.supBounds o X f c) :
    let g := salary Cur X f
    Integrable g (prior G _) ∧ GaugeInvariant g := by
  -- Since no footprint or Hol matters after this embedding, use any
  -- same-weight Foundations section (identity has no x dependence).
  -- Or prove directly, avoiding any section prerequisites at all.
  obtain ⟨hm,hB⟩ := Rep.envelope Cur (h.represents N p j hj).good
  have hM : Measurable (masked (Cur).p.threshold X f) := masked_measurable _ _ _ hf.smooth.borel
  -- integrable via global bound
  have hp U : ‖masked (Cur).p.threshold X f U‖ ≤ c := by
    by_cases hX : Healthy (Cur).p.threshold X U
    · rw [masked_eq _ _ _ _ hX]; exact he.2 U hX [] (Nat.zero_le _) (by simp)
    rw [masked_ne _ _ _ _ hX, norm_zero]; exact he.1
  constructor
  · apply Integrable.of_bound ((Complex.continuous_ofReal.measurable.comp hm).mul hM).aestronglyMeasurable (hB.choose * c)
    filter_upwards with U; rw [Pi.mul_apply,norm_mul]
    exact mul_le_mul ((Complex.norm_real _).trans_le (hB.choose_spec U)) (hp U) (norm_nonneg _) ((norm_nonneg _).trans (hB.choose_spec U))
  intro k U; unfold salary; rw [(Kernel.vacuum_actual (p:=p) h hj).2.1 k U,invariant_mask hf.smooth.symmetry (Cur).p.threshold X k U]

omit ht in
theorem ready_fare {o : Site (H.S.side j p)} {f : Config G (H.S.side j p) → ℂ}
    (hf : SlotFit Cur o i f) (hc : 0≤c) (he : ∀ U,‖f U‖ ≤ c) :
    let g := fare Cur i f
    Integrable g (prior G _) ∧ GaugeInvariant g := by
  -- use the Slot embedding; fare construction itself is independent of A,B.
  let F := (frames G).level 0
  rw [← slot_fare (F:=F) (o:=o) (B:=localSection G 0) (h.represents N p j hj).good hc he]
  obtain ⟨h1,h2⟩ := ready h hj (sound G 0) (format_slot (F:=F) hf) (rem_slot (κ:=1) zero_lt_one hc he)
  exact ⟨Integrable.of_bound h1.meas.aestronglyMeasurable _ (.of_forall h1.cost.choose_spec),h2⟩

end Fine
end YM.Planned.GuardedAtom
