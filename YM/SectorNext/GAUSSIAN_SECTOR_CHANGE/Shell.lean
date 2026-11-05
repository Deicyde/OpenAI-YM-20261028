import YM.Push.SECTOR_MEASURE.Decompose
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Broad





set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Freezing on the intact sector. Chart delay and exact broad insertion

Prove broad release on the actual A, even when the retained (bounded)
multiplier also uses predicates/tails or correction factors. Post-L costs
for each L,J,W group and chart receipt. No volume-dependence in that
threshold. Holds even without selecting a K address or dropping incoherent
seeds: only use (i) the global Seeded prerequisite of Allocation *on nonzero
bill support*, and (ii) actual likelihood support for Cops. In particular
applies to actual `cutEntry` / `leftOver` sections; see consumer. Contrast
`Plot` which tests defaults only in the 5B halo, so alone would not license
this substitution outside.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.SectorChange
open Function Filter Finset MeasureTheory Lattice Wilson RG Precision Tree Metric YM.Pressure
  YM.Pressure.Stores YM.Bid YM.Push.SectorMeasure
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f} {x W d : ℝ}

/-- freeze is determined by the *seed table*, not Y or complements. -/
def chill (A : Stores S) (x : ℝ) (F : Forest S.ratio) (i : F.Free) : Prop :=
  S.ratio.parent i.val.1 ∈ A.dome (10*radiusB x) ∨
    S.ratio.parent (i.val.1+Lattice.step i.val.2) ∈ A.dome (10*radiusB x)

abbrev Frozen (A : Stores S) (x : ℝ) (F : Forest S.ratio) := Held F (chill A x F)
abbrev Active (A : Stores S) (x : ℝ) (F : Forest S.ratio) := Regular F (chill A x F)

lemma remote {F : Forest S.ratio} {A : Stores S} (i : Active A x F) :
    S.ratio.parent i.val.val.1 ∉ A.dome (10*radiusB x) := fun h => i.property (Or.inl h)



/-- Guard for the change, just on locations still integrated. -/
def Standing {F : Forest S.ratio} {A : Stores S} (D : Allocation G S x W) (Z : ChartRatio G) (d : ℝ)
    (k : S.Choices) (V : Config G c) : Prop :=
  ∀ u : F.Slice G, D.bill A k (F.drape u) V ≠ 0 → Alive S (F.drape u) k →
    ∀ i : Active A x F, ∃ a : G.Color, ‖a‖ ≤ d ∧ a ∈ ball 0 Z.radius ∧
      G.lieExp a * replica S.ratio V i.val.val = u i.val



section multiplier
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable (D : Allocation G S x W) (A : Stores S) (F : Forest S.ratio) (V : Config G c) (k : S.Choices)

abbrev returned (Y : LinkArray G (Frozen A x F)) (a : LogArray G (Active A x F)) :=
  thaw F (chill A x F) (replica S.ratio V) Y a

abbrev physical (Y : LinkArray G (Frozen A x F)) (a : LogArray G (Active A x F)) : Config G f :=
  F.drape (returned (x:=x) A F V Y a)

/-- Intact tagged term on this record. Use complete multipliers g of
either sign (k *fixed* through every appearance in g). -/
def attending (g : Config G f → X) (u : F.Slice G) :=
  (D.bill A k (F.drape u) V * S.likelihood (F.drape u) k) • g (F.drape u)

/-- Exact broad insertion for any tagged multiplier (with all cutoff
and profile factors on the given U). Takes just support guard on u. -/
lemma sheltered {Z : ChartRatio G} (h : LocalRatio Z) (q : Chi) (hd : 0 < d) (hs : 2*d < Z.radius)
    (hw : Standing (F:=F) (A:=A) D Z d k V) (g : Config G f → X)
    (Y : LinkArray G (Frozen A x F)) (y : LogArray G (Active A x F)) :
    let u := returned A F V Y
    let v := attending D A F V k g
    (mouth Z).indicator (fun a => pay Z a • v (u a)) y =
      Z.scale ^ Fintype.card (Active A x F) •
        ((reserve q Z d y * doors q d y) • v (u y)) := by
  classical
  intro u v
  by_cases hv : v (u y) = 0
  · by_cases hl : y ∈ mouth Z
    · rw [Set.indicator_of_mem hl]
      simp [hv]
    rw [Set.indicator_of_notMem hl]; simp [hv]
  have hU : D.bill A k (F.drape (u y)) V ≠ 0 ∧ Alive S (F.drape (u y)) k := by
    constructor
    · intro he; apply hv
      unfold v attending; rw [he, zero_mul, zero_smul]
    by_contra ht; apply hv; unfold v attending; rw [dead ht,mul_zero,zero_smul]
  by_cases hy : y ∈ mouth Z
  · rw [Set.indicator_of_mem hy]
    have hi (i : Active A x F) : ‖y i‖ ≤ d := by
      obtain ⟨a,ha,hh,he⟩ := hw _ hU.1 hU.2 i
      unfold u returned thaw at he; rw [freeze_regular] at he
      have ht : a=y i := h.inject hh (hy i (Set.mem_univ _)) (mul_right_cancel he)
      exact ht ▸ ha
    have he : doors q d y=1 := by unfold doors; simp only [broad_one q hd (hi _), prod_const_one]
    rw [he,mul_one,smul_smul, (protected_pay q h hd hs (x:=y) (he.symm ▸ one_ne_zero)).2]
  rw [Set.indicator_of_notMem hy]
  have he : doors q d y=0 := by
    by_contra ht
    exact hy (protected_pay q h hd hs ht).1
  rw [he,mul_zero,zero_smul,smul_zero]


variable [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]

lemma attend_env (h : S.patch.Branches S.kernel G) {g : Config G f → X} (he : Envelope g) :
    Envelope (attending D A F V k g) := by
  have hf := (F.continuous_drape (G:=G)).measurable
  exact Env.scale ((D.envelope h (V:=fun _ => V) hf measurable_const A k).mul (env_likelihood k h hf)) (Env.along he hf)

/-- Integrand of the inner  chart integral before extracting affine
squares. Scale outside. -/
def regularized (q : Chi) (Z : ChartRatio G) (d : ℝ) (g : Config G f → X)
    (Y : LinkArray G (Frozen A x F)) (a : LogArray G (Active A x F)) : X :=
  (reserve q Z d a * doors q d a) • attending D A F V k g (returned A F V Y a)

@[fun_prop] lemma physical_meas : Measurable (uncurry (physical A F V (x:=x))) :=
  F.continuous_drape.measurable.comp ((freeze_meas F _).comp
    (measurable_fst.prodMk ((release_continuous _).measurable.comp measurable_snd)))

lemma regularized_meas {Z : ChartRatio G} (h : LocalRatio Z) (q : Chi) (hd : 0 < d) (hs : 4*d < Z.radius)
    (g : Config G f → X) (hS : S.patch.Branches S.kernel G) (hg : Envelope g) :
    Measurable (uncurry (regularized D A F V k q Z d g)) := by
  let u := uncurry (returned A F V (x:=x))
  let M := LinkArray G (Frozen A x F) × LogArray G (Active A x F)
  have he : Measurable u := (freeze_meas F _).comp (measurable_fst.prodMk ((release_continuous _).measurable.comp measurable_snd))
  change Measurable (fun a : M => _)
  exact (((reserve_smooth q h hd hs).continuous.measurable.comp measurable_snd).mul
    ((doors_smooth q d).continuous.measurable.comp measurable_snd)).smul ((attend_env D A F V k hS hg).meas.comp he)

/-- Exact equality and absolute integrability at fixed V in the iterated
formula, including the outer integral of the norm integral. d post-L,
ratios in integrand protected. -/
theorem regularized_price {Z : ChartRatio G} (h : LocalRatio Z) (q : Chi) (hd : 0 < d) (hs : 4*d < Z.radius)
    (hw : Standing (F:=F) (A:=A) D Z d k V) (g : Config G f → X) (hS : S.patch.Branches S.kernel G)
    (hg : Envelope g) :
    let u := attending D A F V k g
    let v := regularized D A F V k q Z d g
    let M := piHaar G (Frozen A x F)
    let p := Z.scale ^ Fintype.card (Active A x F)
    Integrable u (F.order G) ∧ (∀ Y, Integrable (v Y)) ∧ Integrable (fun Y => ∫ a, ‖v Y a‖) M ∧
      Integrable (uncurry v) (M.prod volume) ∧
      (∫ a, u a ∂F.order G) = p • ∫ Y, (∫ a, v Y a) ∂M := by
  intro u v M p
  obtain ⟨hM,C,hC⟩ := attend_env D A F V k hS hg
  have ht x (hx : u x ≠ 0) : D.bill A k (F.drape x) V ≠ 0 ∧ Alive S (F.drape x) k := by
    unfold u attending at hx
    constructor
    · intro he; simp [he] at hx
    by_contra he; simp [dead he] at hx
  let L := replica S.ratio V
  have he aY (hx : u aY ≠ 0) : ∀ i : Active A x F, aY i.val ∈ groupLip Z (L i.val.val) := by
    intro i
    obtain ⟨a,-,ha,h⟩ := hw aY (ht aY hx).1 (ht aY hx).2 i
    exact ⟨_,⟨a,ha,rfl⟩, h⟩
  have hp : 0 < p := pow_pos h.scale _
  have hn g Y : (fun y : LogArray G (Active A x F) => (mouth Z).indicator
      (fun a => pay Z a • attending D A F V k g (returned A F V Y a)) y) = fun y => p • regularized D A F V k q Z d g Y y :=
    funext (sheltered D A F V k h q hd (by linarith) hw (g : Config G f → X) Y)
  obtain ⟨hx,hv,hy,H⟩ := thaw_integral F (chill A x F) h L u hM.stronglyMeasurable C hC he
  dsimp only at H hv
  simp_rw [u,L,show thaw F (chill A x F) (replica S.ratio V)=returned A F V from rfl,congr_fun (hn g _),
    integral_smul] at H
  simp_rw [u,L,show thaw F (chill A x F) (replica S.ratio V)=returned A F V from rfl,hn g _] at hv
  have hl (Y : LinkArray G (Frozen A x F)) : Integrable (v Y) := by
    have hk := (hv Y).smul p⁻¹
    change Integrable (p⁻¹ • p • v Y) volume at hk
    simpa only [smul_smul,inv_mul_cancel₀ hp.ne',one_smul, Pi.smul_apply, v] using hk
  -- norm integrand receives the same price since ratios/profiles ≥0
  obtain ⟨-, -, hπ, -⟩ := thaw_integral F (chill A x F) h L (fun x => ‖u x‖) hM.stronglyMeasurable.norm C
    (fun a => (Real.norm_of_nonneg (norm_nonneg _)).trans_le (hC a))
    (fun x hh => he x (norm_ne_zero_iff.mp hh))
  let I := fun Y => (mouth Z).indicator (fun a : LogArray G (Active A x F) => pay Z a • ‖u (returned A F V Y a)‖)
  change Integrable (fun Y => ∫ a, I Y a) M at hπ
  have hr (Y : LinkArray G (Frozen A x F)) (a : LogArray G (Active A x F)) : I Y a=p • ‖v Y a‖ := by
    have hb := congr_arg (‖·‖) (congr_fun (hn g Y) a)
    change ‖(mouth Z).indicator _ a‖ = ‖p • v Y a‖ at hb
    rw [norm_smul,Real.norm_of_nonneg hp.le, ← smul_eq_mul] at hb
    rw [← hb]
    unfold I
    by_cases hi : a∈mouth Z
    · have ht : 0 ≤ pay Z a := Finset.prod_nonneg fun i _ => mul_nonneg h.scale.le (h.pos _ (hi i (Set.mem_univ _))).le
      simp only [Set.indicator_of_mem hi,norm_smul,Real.norm_of_nonneg ht, smul_eq_mul,u]
    simp [Set.indicator_of_notMem hi]
  simp_rw [hr,integral_smul] at hπ
  have hi := hπ.smul p⁻¹
  have ho : Integrable (fun Y => ∫ a, ‖v Y a‖) M := by
    change Integrable (p⁻¹ • p • (fun Y => ∫ a, ‖v Y a‖)) M at hi
    simpa only [smul_smul,inv_mul_cancel₀ hp.ne',one_smul, Pi.smul_apply] using hi
  refine ⟨hx,hl,ho,(integrable_prod_iff (regularized_meas D A F V k h q hd hs g hS hg).aestronglyMeasurable).mpr
    ⟨Eventually.of_forall hl,ho⟩, H⟩

end multiplier
end YM.Next.SectorChange
