import YM.Extra.WILSON_STARTUP.Store

/-!
# Exact initial single-source encoding inside the *same* gas

For a tight local placement at startup, every nonzero vacuum label whose
inventory meets the footprint already covers all of it. This argument
also allows zeros, duplicate addresses and additional tests. Not assuming
weight continuity wrt hard link tests. Section read multiplied before pushing,
at any actual origin and on the physical threshold. Subsequent `Paper`
recursions must start with compatible entries.
-/
noncomputable section
set_option autoImplicit false
namespace YM.WilsonStartup.Mark
open Function Filter RG Wilson Lattice Source Work Start
open scoped Topology Matrix.Norms.Frobenius Classical
variable {G : Gauge} {d : ℕ} {F : Labels.Frame G d} {n : Side} {A : Hol G}

abbrev Tight (b : BudgetPoint) (Y : Support n) := ∀ x ∈ Y, ∀ y ∈ Y, separation x y ≤ 2*b.B

def guard (R : Rep G n) (Y : Support n) (i : ℕ) := let p := R.activities.forced i
   ¬ Disjoint Y p.inventory ∧ Y ⊆ p.support

theorem pack {R : Rep G n} {Y : Support n} (h : Wide R) (ht : Tight R.p Y)
    (D : Finset ℕ) {U : Config G n} (hb : R.activities.admissible R.p U D)
    (he : ¬ Healthy R.p.threshold Y U) (hK : ∀ i∈D,R.activities.K i U ≠ 0) : ∃! i, i∈D ∧ guard R Y i := by
  obtain ⟨z,hz,hz'⟩ := Finset.not_disjoint_iff.mp he
  obtain ⟨i,hi,hj⟩ := Finset.mem_biUnion.mp (hb.2.symm ▸ hz' : z ∈ D.biUnion (fun j => (R.activities.forced j).inventory))
  have hY : Y ⊆ (R.activities.forced i).support := by
    intro w hw; exact h.footprints i U (hK _ hi) (Finset.mem_biUnion.mpr ⟨z,hj,(mem_pad ..).mpr (ht z hz w hw)⟩)
  refine ⟨i,⟨hi,fun H => Finset.disjoint_left.mp H hz hj,hY⟩,?_⟩
  intro j ⟨hj,hg⟩; by_contra h'; exact Finset.disjoint_left.mp (hb.1 hj hi h') (hg.2 hz) (hY hz)

def realMaskFree (C : SectionData F) (o : Site n) (R : Rep G n) : F.Coeff →ₗ[ℂ] Config G n → ℂ :=
    let atPoint : F.Coeff →ₗ[ℂ] Config G n → ℂ := {
      toFun := fun v => C.places v o
      map_add' := fun u v => funext fun U => congr_fun (C.eval_linear.map_add u v) (expandAt o U)
      map_smul' := fun s v => funext fun U => congr_fun (C.eval_linear.map_smul s v) (expandAt o U) }
    atPoint ∘ₗ F.scaled R.p.threshold⁻¹

def probe (C : SectionData F) (o : Site n) (R : Rep G n) := realMaskFree C o R ∘ₗ F.core

def inscription (C : SectionData F) (o : Site n) (R : Rep G n) (v : F.Coeff) (i : ℕ) (U : Config G n) :=
    if guard R (C.footprint o) i then (R.activities.K i U:ℂ) * probe C o R v U else 0

def entry (C : SectionData F) (o : Site n) (R : Rep G n) (v : F.Coeff) : Coefficient F n where
  x := v
  support := fun _ => {o}
  regular := 0
  forced := inscription C o R v

theorem fee_linear (C : SectionData F) (o : Site n) (R : Rep G n) : IsLinearMap ℂ (fun v : F.Coeff => (entry C o R v).forced) := by
  constructor
  · intro v w; funext i U; simp only [entry,Pi.add_apply,inscription]; split
    · rw [map_add,Pi.add_apply,mul_add]
    simp
  intro s v; funext i U; simp only [entry,inscription,Pi.smul_apply]; rw [map_smul,Pi.smul_apply,smul_eq_mul]; split <;> ring

lemma format (C : SectionData F) (ha : C.Sound A) (o : Site n) (R : Rep G n) (h : R.activities.ForcedFamily R.p) (v : F.Coeff) :
    (entry C o R v).Format o A R := by
  have ho : o ∈ C.footprint o := Finset.mem_image.mpr ⟨0,ha.anchored, by simp⟩
  let Y := C.footprint o
  let u := F.scaled R.p.threshold⁻¹ (F.core v)
  have he i : (entry C o R v).forced i = if guard R Y i then fun U => (R.activities.K i U:ℂ)*C.places u o U else fun _ => 0 := by
    funext U; unfold entry inscription; dsimp only; split <;> rfl
  constructor
  · exact fun _ => ⟨fun _ _ _ => rfl,measurable_const,fun _ _ => rfl,fun _ _ => contDiffAt_const,
      fun U _ a _ hl => Next.Foundations.left_has (f:=fun _ => 0) (U:=U) a hl contDiffAt_const⟩
  · exact fun _ => Finset.mem_singleton_self _
  · exact fun _ => rfl
  · intro i _ J; change ContDiffAt _ _ (fun _ : ℝ => (0:ℂ)) _ ∧ _
    exact ⟨contDiffAt_const,fun _ _ => by change iteratedDeriv _ (fun _ => (0:ℂ)) 0 = 0; simp⟩
  · intro i U hj; rw [he] at hj; split at hj
    · exact h.permit i U fun H => hj (by simp only [H,Complex.ofReal_zero,zero_mul])
    exact (hj rfl).elim
  · intro i hj; rw [he] at hj; split at hj
    next hg => exact hg.2 ho
    exact (hj rfl).elim
  · intro i k U; rw [he]; split
    · dsimp only; rw [h.sym i k U,C.placed_invariant ha o u k U]
    rfl
  · intro i U V h1 h2; rw [he]; split
    next hg => dsimp only; rw [h.reads i U V h1 h2, C.placed_local o u U V (agrees_mono h1 (Finset.coe_subset.mpr hg.2))]
    rfl
  intro i; rw [he]; split
  · exact (Complex.continuous_ofReal.measurable.comp (h.meas i)).mul (C.continuous_places .. |>.measurable)
  exact measurable_const

theorem probe_unit (C : SectionData F) (ha : C.Sound A) (o : Site n) (R : Rep G n) : realMaskFree C o R F.e0 = 1 := by
  change C.places (F.scaled _ F.e0) o = _; funext U; simp [SectionData.places,ha.unit]

theorem constantPart (v : F.Coeff) : v = v 0 • F.e0 + F.core v := by
  funext i; by_cases h : i=0 <;> simp [Labels.Frame.core,Labels.Frame.e0,h]

def unseen (C : SectionData F) (o : Site n) (R : Rep G n) (v : F.Coeff) (U : Config G n) :=
    if Healthy R.p.threshold (C.footprint o) U then 0 else probe C o R v U

lemma bulk_match (C : SectionData F) (ha : C.Sound A) (o : Site n) (R : Rep G n) (v : F.Coeff) (U : Config G n) :
    (entry C o R v).exponentialEntry o C R U + unseen C o R v U = realMaskFree C o R v U := by
  have he i : (entry C o R v).maskedTerm R i U = 0 := by
    by_cases h : Healthy R.p.threshold ({o}:Support n) U
    · exact masked_eq _ _ _ _ h
    exact masked_ne _ _ _ _ h
  nth_rw 3 [constantPart v]; rw [map_add,map_smul,probe_unit C ha o R]
  simp_rw [Coefficient.exponentialEntry, he,tsum_zero,add_zero, Pi.add_apply,Pi.smul_apply,Pi.one_apply,smul_eq_mul,mul_one]
  change v 0 + masked _ _ (probe C o R v) U + unseen .. = _
  unfold unseen; split <;> rename_i h
  · rw [masked_eq _ _ _ _ h,add_zero]; rfl
  rw [masked_ne _ _ _ _ h,add_zero]; rfl

lemma mark_product (C : SectionData F) (o : Site n) (R : Rep G n) (h : Wide R) (ht : Tight R.p (C.footprint o))
    (v : F.Coeff) (U : Config G n) (s : Finset ℕ) : (entry C o R v).marked R s U = (R.activities.gasOccurrence R.p s U : ℂ) * unseen C o R v U := by
  let f := fun i => (R.activities.K i U : ℂ)
  let Y := C.footprint o
  unfold Activities.gasOccurrence Coefficient.marked
  split <;> rename_i hs
  · rw [Complex.ofReal_prod]
    have he i (hi : i∈s) : (entry C o R v).forced i U * ∏ j∈s.erase i, f j = if guard R Y i then
        (∏ j ∈ s,f j) * probe C o R v U else 0 := by
      change (if _ then _ else _) * _ = _
      rw [s.mul_prod_erase f hi |>.symm]; split <;> ring
    change (∑ i∈s, (entry C o R v).forced i U * ∏ j ∈ s.erase i,f j) = (∏ i∈s, f i) * _
    rw [Finset.sum_congr rfl he]
    unfold unseen; split <;> rename_i hh
    · rw [mul_zero]; refine Finset.sum_eq_zero fun i hi => if_neg (fun hg => ?_)
      apply hg.1
      exact Finset.disjoint_of_subset_right (fun x hx => hs.2 ▸ Finset.mem_biUnion.mpr ⟨i,hi,hx⟩) hh
    by_cases hk : ∏ i∈s, f i = 0
    · simp [hk]
    have hK := Finset.prod_ne_zero_iff.mp hk
    obtain ⟨i,hi,hu⟩ := pack h ht s hs hh fun i hi H => hK i hi (show f i=0 from by simp [f,H])
    rw [Finset.sum_eq_single_of_mem i hi.1 (fun j hj hn => if_neg fun H => hn (hu j ⟨hj,H⟩)), if_pos hi.2]
  simp

lemma encoding (C : SectionData F) (ha : C.Sound A) (o : Site n) (R : Rep G n) (h : Wide R) (ht : Tight R.p (C.footprint o))
    (v : F.Coeff) (U : Config G n) : (entry C o R v).density o C R U = (R.eval U : ℂ) * realMaskFree C o R v U := by
  unfold Coefficient.density
  simp_rw [mark_product C o R h ht,tsum_mul_right,← Complex.ofReal_tsum]
  rw [← bulk_match C ha o R,Rep.eval,Complex.ofReal_mul]; change _ + (_:ℂ) * (↑(R.activities.gas R.p U) * _) = _; ring
end YM.WilsonStartup.Mark
