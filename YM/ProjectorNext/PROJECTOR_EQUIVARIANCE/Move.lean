import YM.Next.FOUNDATIONS.Reorient
import YM.Next.FOUNDATIONS.Split
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Test
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Trails
import YM.Work.A01.Mirror

/-!
# Concrete reanchored Coefficient

When pulling a charge density by an allowed orientation/translation, can
actually realize that expression with moved supports and the same history,
with cap. Requires the vacuum's genuine `Activities.Moves` and fixed Sound
section, not equivariance of a fitted marking prescription. This is an
operation (available even if other representations of the same density have
been chosen); not asserting another unaligned transfer gave its result.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Equivariance
open Function Filter Labels Lattice Wilson RG Source Analysis MeasureTheory Next.Foundations Push.CutoffProjectors
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {n : Side} {d : ℕ} {F : Frame G d}
    {Q : Coefficient F n} {R : Rep G n} {t : Signed} {o b : Site n}

section Family

/-- Gauge/premask, and actual ordered differentiability of the moved germ,
including at equality. -/
lemma pulls_regular (s : Signed) (b : Site n) {P : BudgetPoint} {D : Support n} {F : Config G n → ℂ}
    (h : P.Regular D F) : P.Regular (D.image (affine s b)) (F ∘ pull s b) := by
  have he (U : Config G n) (ht : Healthy P.threshold (D.image (affine s b)) U) :
      HasOrderAt (F ∘ pull s b) U P.order := hasOrder_pull s b U (h.smooth _ ((healthy_pull ..).mpr ht))
  refine ⟨local_pull s b _ h.sites, h.borel.comp (prior_pull ..).measurable, ?_,he,?_⟩
  · intro k U; simp only [comp_apply,pull_gauge]; exact h.symmetry _ _
  intro U hu l A hA; exact left_has l hA (he U hu)

/-- Pairwise admissibility test is performed after moving the **whole**
occurrence set, even addresses with zero material. -/
lemma moves_admissible {A : Activities G n} (p : BudgetPoint) (M : A.Moves t b) (U : Config G n) (q : Finset ℕ) :
    A.admissible p U (q.map M.kp.toEmbedding) ↔ A.admissible p (pull t b U) q := by
  classical
  let g := affine t b
  have hJ : Injective g := affine_injective t b
  have he (i j) : Disjoint (A.forced (M.kp i)).support (A.forced (M.kp j)).support ↔
      Disjoint (A.forced i).support (A.forced j).support := by
    rw [M.forced_support,M.forced_support,Finset.disjoint_image hJ]
  have hf : (q.map M.kp.toEmbedding).biUnion (fun i => (A.forced i).inventory) =
      (q.biUnion (fun i => (A.forced i).inventory)).image g := by
    ext x; obtain ⟨x,rfl⟩ := affine_surjective t b x
    simp only [Finset.mem_image,Finset.mem_biUnion,Finset.mem_map,Equiv.coe_toEmbedding]
    constructor
    · rintro ⟨i,⟨j,hj,rfl⟩,ht⟩
      rw [M.forced_inventory] at ht; obtain ⟨y,hy,hr⟩ := Finset.mem_image.mp ht; exact ⟨y,⟨j,hj,hy⟩,hr⟩
    rintro ⟨y,⟨j,hj,hy⟩,ht⟩; exact ⟨M.kp j,⟨j,hj,rfl⟩,by rw [M.forced_inventory]; exact Finset.mem_image.mpr ⟨y,hy,ht⟩⟩
  unfold Activities.admissible
  rw [hf,← Work.H03.flags_send t b p.threshold U,(Finset.image_injective hJ).eq_iff]; refine and_congr ?_ Iff.rfl
  constructor
  · intro H i hi j hj ht
    exact (he i j).1 (H (Finset.mem_map.mpr ⟨i,hi,rfl⟩) (Finset.mem_map.mpr ⟨j,hj,rfl⟩) (M.kp.injective.ne ht))
  rintro H i hi j hj ht
  obtain ⟨k,hk,rfl⟩ := Finset.mem_map.mp hi
  obtain ⟨l,hl,rfl⟩ := Finset.mem_map.mp hj
  exact (he k l).2 (H hk hl (fun e => ht (congr_arg M.kp e)))

lemma gas_pull {R : Rep G n} (U : Config G n) {s : Signed} {b : Site n} (h : R.activities.Moves s b) :
    R.activities.gas R.p (pull s b U) = R.activities.gas R.p U := by
  classical
  unfold Activities.gas; rw [← h.kp.finsetCongr.tsum_eq (fun q => R.activities.gasOccurrence R.p q U)]
  refine tsum_congr fun i => ?_
  unfold Activities.gasOccurrence
  rw [show h.kp.finsetCongr i = i.map h.kp.toEmbedding from rfl]
  split <;> rename_i he
  · rw [if_pos ((moves_admissible R.p h U i).2 he)]
    rw [Finset.prod_map]; exact Finset.prod_congr rfl fun x _ => (h.valuesK x U).symm
  rw [if_neg (fun hx => he ((moves_admissible R.p h U i).1 hx))]
end Family

/-- Coefficient operation. Don't shorten ANY supports. `M` keeps R fixed;
use it on the *forced* part. No need to share its unmarked-regular names
with the marked regular terms (those can just keep their index here). -/
def shifted (M : R.activities.Moves t b) (Q : Coefficient F n) : Coefficient F n := {
  x := turn F t Q.x
  support i := (Q.support i).image (affine t b)
  regular i := Q.regular i ∘ pull t b
  forced i := Q.forced (M.kp.symm i) ∘ pull t b }

lemma turn_scalar (F : Frame G d) (s : Signed) (v : F.Coeff) : turn F s v 0 = v 0 := by
  have he (v : F.Coeff) : F.scaled 0 v = v 0 • F.e0 := by
    funext i
    by_cases hi : i=0
    · subst i; simp [Frame.e0,F.zero_degree]
    simp [Frame.e0,hi,Nat.ne_of_gt (F.factors_pos i hi)]
  have hu : turn F s F.e0 = F.e0 := by
    have ht : tensor (Signed.inclusionO s) (Labels.unit G d) = Labels.unit G d := Subtype.ext (map_one (rotated ..))
    rw [← F.coords_unit,turn,F.act_coords,ht]
  have hp := F.scaling 0 (Signed.inclusionO s) v
  change F.scaled 0 (turn F s v) = turn F s (F.scaled 0 v) at hp
  rw [he,he,map_smul,hu] at hp
  simpa only [Frame.e0,Pi.smul_apply,Pi.single_eq_same,smul_eq_mul,mul_one] using congr_fun hp 0

namespace shifted
variable (M : R.activities.Moves t b) (C : SectionData F) {H : Hol G}

lemma expEntry (hc : C.Sound H) (Q : Coefficient F n) (U : Config G n) (o : Site n) :
    (shifted M Q).exponentialEntry (affine t b o) C R U =
      Q.exponentialEntry o C R (pull t b U) := by
  let V := pull t b U
  let y := affine t b o
  let z := R.p.threshold
  have he : C.footprint y = (C.footprint o).image (affine t b) := by
    unfold SectionData.footprint
    nth_rw 1 [← hc.stable t]
    simp only [Finset.image_image,Function.comp_def,wrap_signed,y,affine,Signed.act_add,add_assoc]
  have ha (v : F.Coeff) :
      v 0 + masked z (C.footprint o) (C.places (F.scaled z⁻¹ (F.core v)) o) V =
        turn F t v 0 + masked z (C.footprint y) (C.places (F.scaled z⁻¹ (F.core (turn F t v))) y) U := by
    have hh : Healthy z (C.footprint y) U ↔ Healthy z (C.footprint o) V := by rw [he]; exact (healthy_pull ..).symm
    by_cases hx : Healthy z (C.footprint o) V
    · rw [masked_eq _ _ _ _ (hh.mpr hx),masked_eq _ _ _ _ hx,atCore C hc,atCore C hc,turn,F.scaling]
      exact C.placed_signed hc t o b _ _
    rw [masked_ne _ _ _ _ hx,masked_ne _ _ _ _ (fun h => hx (hh.mp h)),turn_scalar]
  unfold Coefficient.exponentialEntry
  refine congr_arg₂ (·+·) (ha Q.x).symm ?_; refine tsum_congr fun i => ?_
  exact mask_pull t b (Q.support i) (Q.regular i) R.p.threshold U

lemma marked (Q : Coefficient F n) (U : Config G n) (i : Finset ℕ) :
    (shifted M Q).marked R (M.kp.finsetCongr i) U = Q.marked R i (pull t b U) := by
  classical
  unfold Coefficient.marked
  split <;> rename_i he
  · rw [if_pos ((moves_admissible R.p M U i).mp he)]
    change Finset.sum (i.map _) _ = _
    rw [Finset.sum_map]; refine Finset.sum_congr rfl fun j hj => ?_
    have ht : (i.map M.kp.toEmbedding).erase (M.kp j) = (i.erase j).map M.kp.toEmbedding := (Finset.map_erase ..).symm
    change Q.forced (M.kp.symm (M.kp j)) _ * Finset.prod ((i.map _).erase (M.kp j)) _ = _
    rw [Equiv.symm_apply_apply,ht,Finset.prod_map]; congr 1
    exact Finset.prod_congr rfl fun k _ => congr_arg ((↑) : ℝ → ℂ) (M.valuesK k U)
  rw [if_neg (fun h => he ((moves_admissible R.p M U i).2 h))]

lemma density (hc : C.Sound H) (Q : Coefficient F n) (o : Site n) :
    (shifted M Q).density (affine t b o) C R = Q.density o C R ∘ pull t b := by
  funext U
  have he : ∑' i, (shifted M Q).marked R i U = ∑' i, Q.marked R i (pull t b U) := by
    rw [← M.kp.finsetCongr.tsum_eq (fun i => (shifted M Q).marked R i U)]
    exact tsum_congr (marked M Q U)
  rw [Function.comp_apply,Coefficient.density,Coefficient.density,expEntry M C hc,Rep.eval,Rep.eval,
    exponent_pull _ M,gas_pull _ M,he]

/-- Format requires the usual nonwrapping test comparison (including flips),
valid on sides ≥ 2. Always met at scheduled levels under Fits. -/
lemma format (o : Site n) (hn : 2 ≤ n.val) (hQ : Q.Format o H R) :
    (shifted M Q).Format (affine t b o) H R := by
  have he (i) : (shifted M Q).forced (M.kp i) = Q.forced i ∘ pull t b := by simp [shifted]
  constructor
  · intro i; exact pulls_regular t b (hQ.smooth i)
  · exact fun i => Finset.mem_image_of_mem _ (hQ.origin i)
  · intro i; unfold shifted; simp only [Function.comp_apply,pull_constant,hQ.identity_null]
  · intro i hi
    have hp : Reads H o (Q.support i) (0:Label G d) (Q.regular i) :=
      (reads_null_iff H d o (Q.support i) (Q.regular i)).mpr ⟨hQ.identity_null i,hQ.projects i⟩
    have hr : Reads H (affine t b o) ((Q.support i).image (affine t b)) (0:Label G d) (Q.regular i ∘ pull t b) := by
      simpa only [map_zero] using reads_pull (b:=b) hp (hQ.smooth i).sites hn t
    exact ((reads_null_iff ..).mp hr).2 hi
  · intro i U; obtain ⟨j,rfl⟩ := M.kp.surjective i; rw [he]
    intro ha
    exact (Work.H03.eligible_send t b R.p.threshold U _ _ (M.forced_support j) (M.forced_inventory j) (M.forced_tests j U)).2
      (hQ.forcing j (pull t b U) ha)
  · intro i; obtain ⟨j,rfl⟩ := M.kp.surjective i; rw [he,M.forced_support]
    intro ha; exact Finset.mem_image_of_mem _ (hQ.carried j (fun he => ha (by rw [he]; rfl)))
  · intro i; obtain ⟨j,rfl⟩ := M.kp.surjective i; rw [he]; intro k U; simp only [comp_apply,pull_gauge]; exact hQ.invariant j _ _
  · intro i; obtain ⟨j,rfl⟩ := M.kp.surjective i; rw [he,M.forced_support]; exact final_pull t b _ (hQ.supported j)
  intro i; unfold shifted; exact (hQ.borel _).comp (prior_pull ..).measurable

lemma cap {v c : ℝ} (hQ : Q.Format o H R) (he : Q.remBound o R v c) :
    (shifted M Q).remBound (affine t b o) R v (permission R.p t * c) := by
  let D := permission R.p t
  have hD : 1 ≤ D := one_permission _ _
  have h0 : 0 ≤ D := zero_le_one.trans hD
  obtain ⟨a,g,ha,hg,hc,hv,⟨E,hE,hX⟩,⟨B,hB,hY⟩⟩ := he
  have he : D*a+g ≤ D*c := ((add_le_add_right (le_mul_of_one_le_left hg hD) _).trans_eq
    (mul_add D a g).symm).trans (mul_le_mul_of_nonneg_left hc h0)
  refine ⟨D*a,g,mul_nonneg h0 ha,hg,he,hv,⟨fun i => D*E i,?_,fun i =>
    paid_permission t b (hX i) (hQ.smooth i)⟩,fun i => B (M.kp.symm i),?_,?_⟩
  · have ht (i) : R.p.mass ((shifted M Q).support i) (D*E i) = D * R.p.mass (Q.support i) (E i) := by
      unfold BudgetPoint.mass shifted; rw [moves_cost]; ring
    simp_rw [ht]
    refine ⟨fun i => mul_nonneg h0 (hE.1 i), hE.2.1.mul_left D, ?_⟩
    rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hE.2.2 h0
  · let F i := R.p.mass (R.activities.forced i).support (B i)
    have ht (i) : R.p.mass (R.activities.forced i).support (B (M.kp.symm i)) = (F ∘ M.kp.symm) i := by
      obtain ⟨j,rfl⟩ := M.kp.surjective i
      unfold F; simp only [Function.comp_apply,Equiv.symm_apply_apply,M.forced_support,BudgetPoint.mass,moves_cost]
    simp_rw [ht]
    exact ⟨fun i => hB.1 _, M.kp.symm.summable_iff.mpr hB.2.1, (M.kp.symm.tsum_eq F).le.trans hB.2.2⟩
  exact fun i => ⟨(hY _).1,fun U => (hY _).2 _⟩
end shifted
end YM.ProjectorNext.Equivariance
