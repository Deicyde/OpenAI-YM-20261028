import YM.Next.FOUNDATIONS.Primary
import YM.Push.LOCAL_SPLITTING.Projection

/-!
# Singleton atom conversion in the vacuum threshold convention

Exact  (`Jmdef`) **prior** to a forced merger. No differentiation of the
bad-set contributions. The attaching correction retains its whole support at
zero amplitudes, permits the final flag read, and is evaluated with the actual
mask at this level, also at equality. Address costs here are per atom (sum
cost with enlargement and forced hits in subsequent modules).
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.Local
open Function Filter Lattice Wilson RG Source Labels Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff

variable {G : Gauge} {n : Side} {d : ℕ} {F : Labels.Frame G d}

/-- A term to multiply into the same vacuum gas. -/
structure Attaches (t : ℝ) (X : Support n) (f : Config G n → ℂ) : Prop where
  sites : UsesFinal t X f
  symmetry : GaugeInvariant f
  borel : Measurable f
  healthy_zero : ∀ U, Healthy t X U → f U = 0

theorem Attaches.zero (t : ℝ) (X : Support n) : Attaches t X (0 : Config G n → ℂ) :=
  ⟨fun _ _ _ _ => rfl,fun _ _ => rfl,measurable_const,fun _ _ => rfl⟩

theorem uses_mask (t : ℝ) {X : Support n} {f : Config G n → ℂ} (h : LocalOn X f) : UsesFinal t X (masked t X f) := by
  intro U V huv ht
  have he : Healthy t X U ↔ Healthy t X V := by simp only [Healthy, Finset.disjoint_iff_inter_eq_empty,ht]
  by_cases hx : Healthy t X U
  · simpa only [masked_eq _ _ _ _ hx,masked_eq _ _ _ _ (he.mp hx)] using h U V huv
  rw [masked_ne _ _ _ _ hx,masked_ne _ _ _ _ (mt he.mpr hx)]

theorem invariant_mask {f : Config G n → ℂ} (h : GaugeInvariant f) (t : ℝ) (X : Support n) : GaugeInvariant (masked t X f) := by
  intro g U
  have he : Healthy t X (gauge g U) ↔ Healthy t X U := by rw [Healthy,Healthy,gauge_flags]
  by_cases hx : Healthy t X U
  · simpa only [masked_eq _ _ _ _ hx, masked_eq _ _ _ _ (he.mpr hx)] using h g U
  rw [masked_ne _ _ _ _ (mt he.mp hx),masked_ne _ _ _ _ hx]

def maskLinear (t : ℝ) (X : Support n) : (Config G n → ℂ) →ₗ[ℂ] (Config G n → ℂ) where
  toFun := masked t X
  map_add' f g := by funext U; by_cases hx : Healthy t X U <;> simp [*,masked_ne,masked_eq]
  map_smul' f g := by funext U; by_cases hx : Healthy t X U <;> simp [*,masked_ne,masked_eq]

structure Readable (H : Hol G) (T : SectionData F) (B : BudgetPoint) (n : Side) (w : ℝ) : Prop where
  sound : T.Sound H
  fit (x : Cover) : x∈T.stencil → ∀ i : Axis, 20*((x i).natAbs+1) ≤ n.val
  order : d ≤ B.order
  power : d ≤ B.power
  paid : Bid.Credit T B.order B.power w
  nonneg : 0 ≤ w

theorem foundation_readable (G : Gauge) (d : ℕ) {n : Side} {B : BudgetPoint} (hf : minSide G d ≤ n.val) (h : d ≤ B.order) (hq : d ≤ B.power) :
    Readable (hol G) (localSection G d) B n (price G (max B.order B.power)) :=
  ⟨sound G d,stencil_price G hf,h,hq,priced G (h.trans (le_max_left _ _)) (le_max_left _ _) (le_max_right _ _),zero_le_one.trans (price_one_le G _)⟩

/-- Scaled section (all coordinates, unmasked). -/
def presented (T : SectionData F) (o : Site n) (t : ℝ) : F.Coeff →ₗ[ℂ] (Config G n → ℂ) where
  toFun v := T.places (F.scaled t⁻¹ v) o
  map_add' u v := by funext U; exact congr_fun ((congr_arg T.evaluate (map_add ..)).trans (T.eval_linear.map_add _ _)) (expandAt o U)
  map_smul' u v := by funext U; exact congr_fun ((congr_arg T.evaluate (map_smul ..)).trans (T.eval_linear.map_smul _ _)) (expandAt o U)

/-- Exponential coordinate entry, leaving the unit global as in `Coefficient`. -/
def primary (T : SectionData F) (o : Site n) (t : ℝ) : F.Coeff →ₗ[ℂ] (Config G n → ℂ) :=
  let g : F.Coeff →ₗ[ℂ] (Config G n → ℂ) := {
    toFun v := fun _ => v 0
    map_add' _ _ := rfl
    map_smul' _ _ := rfl
  }
  g + maskLinear t (T.footprint o) ∘ₗ presented T o t ∘ₗ F.core

variable {H : Hol G} {T : SectionData F} {B : BudgetPoint} {w : ℝ}

theorem presented_good (o : Site n) (h : Readable H T B n w) (v : F.Coeff) :
    B.Regular (T.footprint o) (presented T o B.threshold v) ∧ B.supBounds o (T.footprint o) (presented T o B.threshold v) (w*F.coeffSize v) := by
  simpa [presented, F.scaled_inv B.threshold_pos.ne'] using combination_bound B o h.paid (F.scaled B.threshold⁻¹ v)

theorem presented_primary (o : Site n) {t : ℝ} (h : T.Sound H) (v : F.Coeff) (U : Config G n)
    (hU : Healthy t (T.footprint o) U) : primary T o t v U = presented T o t v U := by
  change v 0 + masked .. = _
  rw [masked_eq _ _ _ _ hU]
  conv_rhs => rw [core_split F v,map_add, map_smul, Pi.add_apply,Pi.smul_apply]
  congr 1; change _ = v 0 • T.evaluate (F.scaled t⁻¹ F.e0) (expandAt o U)
  simp [h.unit]

theorem primary_price (o : Site n) (h : Readable H T B n w) (v : F.Coeff) (U : Config G n) :
    ‖primary T o B.threshold v U‖ ≤ (1+w)*F.coeffSize v := by
  by_cases hU : Healthy B.threshold (T.footprint o) U
  · rw [presented_primary o h.sound v U hU]
    apply ((presented_good o h v).2.2 U hU [] (Nat.zero_le _) (by simp)).trans
    exact mul_le_mul_of_nonneg_right (by linarith) (Work.G08.size_nonneg ..)
  change ‖v 0 + masked ..‖ ≤ _
  rw [masked_ne _ _ _ _ hU, add_zero]
  exact ((norm_le_pi_norm v 0).trans (norm_le_size ..)).trans (le_mul_of_one_le_left (Work.G08.size_nonneg ..) (le_add_of_nonneg_right h.nonneg))

variable (H T) in
def joint (o : Site n) (X : Support n) : Support n := X ∪ T.footprint o
variable (H T) in
def residual (o : Site n) (X : Support n) (t : ℝ) (f : Config G n → ℂ) := f - presented T o t (weighted H F o X t f)
variable (H T) in
def rebate (o : Site n) (X : Support n) (t : ℝ) (f : Config G n → ℂ) :=
  masked t X f - primary T o t (weighted H F o X t f) - masked t (joint T o X) (residual H T o X t f)

variable (o : Site n) {X : Support n} {f : Config G n → ℂ}

theorem convert_atom (h : Readable H T B n w) (hf : B.Regular X f) :
    let Z := joint T o X
    let g := residual H T o X B.threshold f
    B.Regular Z g ∧ o ∈ Z ∧ Reads H o Z (0 : Label G d) g ∧ Attaches B.threshold Z (rebate H T o X B.threshold f) := by
  intro Z g
  let v := weighted H F o X B.threshold f
  have hp := project_reads H o hf h.order
  have hz : F.scaled B.threshold⁻¹ v = F.coords (project H o X f d) := by
    simpa [v,weighted] using F.scaled_inv (inv_ne_zero B.threshold_pos.ne') (F.coords (project H o X f d))
  have hY : Nonwrapping (T.footprint o) o := nonwrapping_placement T o h.fit
  have hx : X ⊆ Z := Finset.subset_union_left
  have hy : T.footprint o ⊆ Z := Finset.subset_union_right
  have hu : B.Regular Z f := regular_larger hf hx
  have hr := presented_good o h v
  have hg : B.Regular Z g := regular_sub hu (regular_larger hr.1 hy)
  refine ⟨hg,hy (Finset.mem_image.mpr ⟨0,h.sound.anchored,by simp⟩), ?_,?_⟩
  · unfold g residual presented
    dsimp only [LinearMap.coe_mk,AddHom.coe_mk]; rw [hz]
    have hZ : Nonwrapping Z o ↔ Nonwrapping X o := by simp [Z,joint,Nonwrapping, or_imp, forall_and]; exact fun _ => hY
    have he : Reads H o Z (project H o X f d) f := by
      classical
      rw [Reads] at hp ⊢
      simp_rw [hZ]; exact hp
    have h' : Reads H o Z (project H o X f d) (T.places (F.coords (project H o X f d)) o) := by
      unfold Reads
      split <;> rename_i hN
      · have ht := placed_reads T o h.fit h.sound (F.coords (project H o X f d))
        rwa [Reads,if_pos hY,F.coords.symm_apply_apply] at ht
      rw [Reads,if_neg (mt hZ.mpr hN)] at hp
      rw [hp,map_smul,F.coords_unit,SectionData.places,T.eval_linear.map_smul,h.sound.unit]; simp
    simpa only [sub_self] using reads_sub he h'
  unfold rebate
  let t := B.threshold
  have hcore : B.Regular (T.footprint o) (presented T o t (F.core v)) := (presented_good o h _).1
  have hP (U : Config G n) : primary T o t v U = v 0 + masked t (T.footprint o) (presented T o t (F.core v)) U := rfl
  refine ⟨?_,?_, (masked_measurable _ _ _ hf.borel |>.sub (show Measurable (fun U => v 0 + masked t _ _ U) from measurable_const.add (masked_measurable _ _ _ hcore.borel)) |>.sub (masked_measurable _ _ _ hg.borel)),?_⟩
  · intro U V huv ht; change _ - primary T o t v U - masked t Z g U = _ - primary T o t v V - masked t Z g V
    rw [Work.H03.reads_larger hx (uses_mask t hf.sites) U V huv ht,hP,hP,Work.H03.reads_larger hy (uses_mask _ hcore.sites) U V huv ht, uses_mask _ hg.sites U V huv ht]
  · intro k U; change _ - primary T o t v (gauge k U) - masked t Z g (gauge k U) = _ - primary T o t v U - masked t Z g U
    rw [invariant_mask hf.symmetry t X k U,hP,hP,invariant_mask hcore.symmetry t _ k U,invariant_mask hg.symmetry t Z k U]
  intro U hU
  change masked t X f U - primary T o t v U - masked t Z g U = 0
  rw [masked_eq _ _ _ _ (Finset.disjoint_of_subset_left hx hU), masked_eq _ _ _ _ hU, presented_primary o h.sound v U (Finset.disjoint_of_subset_left hy hU)]
  exact sub_self _

def atomPrice (H : Hol G) (F : Labels.Frame G d) (w : ℝ) := 1 + (1+w)*readPrice H F

theorem atomPrice_ge_one (H : Hol G) (F : Labels.Frame G d) {w : ℝ} (h : 0 ≤ w) : 1 ≤ atomPrice H F w := by
  unfold atomPrice; exact le_add_of_nonneg_right (by positivity [readPrice_pos H F])

theorem charge_atom (h : Readable H T B n w) (hf : B.Regular X f) {c : ℝ} (hc : B.supBounds o X f c) :
    B.supBounds o (joint T o X) (residual H T o X B.threshold f) (atomPrice H F w*c) ∧
    ∀ U, ‖rebate H T o X B.threshold f U‖ ≤ atomPrice H F w*c := by
  let v := weighted H F o X B.threshold f
  have he : F.coeffSize v ≤ readPrice H F*c := weighted_bound H F o hf h.order h.power hc
  obtain ⟨hr,hb⟩ := presented_good o h v
  have ht : 0 ≤ 1+w := by linarith [h.nonneg]
  have hy : c+(1+w)*F.coeffSize v ≤ atomPrice H F w*c := by
    exact le_trans (add_le_add_right (mul_le_mul_of_nonneg_left he ht) c) (by unfold atomPrice; linarith)
  constructor
  · exact bound_weaken (bound_sub (regular_larger hf Finset.subset_union_left) (regular_larger hr Finset.subset_union_right) (bound_larger hc Finset.subset_union_left) (bound_larger hb Finset.subset_union_right)) (le_trans (add_le_add_right (mul_le_mul_of_nonneg_right (by linarith) (Work.G08.size_nonneg ..)) c) hy)
  intro U
  by_cases hU : Healthy B.threshold (joint T o X) U
  · rw [(convert_atom o h hf).2.2.2.healthy_zero U hU, norm_zero]; exact mul_nonneg (zero_le_one.trans (atomPrice_ge_one _ _ h.nonneg)) hc.1
  have hX : ‖masked B.threshold X f U‖ ≤ c := by
    by_cases hx : Healthy B.threshold X U
    · rw [masked_eq _ _ _ _ hx]; exact hc.2 U hx [] (Nat.zero_le _) (by simp)
    rw [masked_ne _ _ _ _ hx,norm_zero]; exact hc.1
  rw [rebate,Pi.sub_apply, Pi.sub_apply, masked_ne _ _ _ _ hU, sub_zero]
  exact (norm_sub_le ..).trans ((add_le_add hX (primary_price o h v U)).trans hy)

end YM.Push.Local
