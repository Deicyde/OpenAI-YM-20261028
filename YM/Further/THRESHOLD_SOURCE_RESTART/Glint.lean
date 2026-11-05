import YM.Further.THRESHOLD_SOURCE_RESTART.Blaze
import YM.Further.THRESHOLD_SOURCE_RESTART.Narrow
/-!
# Sums are exact kit balances by old choices

The threshold-change data actually give the full account required for a
`Narrows`. Reindex all admissible covers using the old choices, even for old
zero-amplitude carriers: important, since `Narrows.award` may price these
carriers on a source-bearing payload.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.ThresholdSourceRestart.Sluice.Menu
open Function Set Filter MeasureTheory Wilson RG Lattice Marker Overlay
open Push.Corrected Work.H03 WilsonStartup Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {α : Type} {n : Side} {H : Rep G n} {q : BudgetPoint} (L : Menu H q α)

def accounted (t : Finset ℕ) (U : Config G n) (B : Finset L.Record) :=
  if (L.alloted B).toLeft=t ∧ L.Mass B U then ∏ i ∈ B,L.solid i U else 0

private lemma berserk {e : α → ℝ} (h : Summable e) :
    HasSum (fun B : Finset α => ∏ i∈B,(Real.exp (e i)-1)) (Real.exp (∑' i,e i)) := by
  let f i := Real.exp (e i)-1
  let g (i : Finset α) := ∏ j∈i,f j
  have he : Summable f := by
    refine (h.norm.mul_left 2).of_norm_bounded_eventually ?_
    have he := h.norm.tendsto_cofinite_zero.eventually (ge_mem_nhds (show (0:ℝ)<1 by norm_num))
    exact he.mono fun i hi => Real.abs_exp_sub_one_le hi
  have hP : Summable g := by
    refine Summable.of_norm ?_; simp only [g,Real.norm_eq_abs,Finset.abs_prod]
    exact summable_finsetProd_of_summable_nonneg (fun i => abs_nonneg (f i)) he.norm
  have hp : Tendsto (Finset.powerset (α:=α)) atTop atTop := by
    apply tendsto_atTop_atTop.mpr
    intro B
    exact ⟨B.biUnion id,fun a ha s hs => mem_powerset.mpr (fun x hx => ha (Finset.mem_biUnion.mpr ⟨s,hs,hx⟩))⟩
  apply hP.hasSum_iff.mpr
  refine tendsto_nhds_unique (hP.hasSum.comp hp) ((Real.continuous_exp.continuousAt.tendsto.comp h.hasSum).congr fun s => ?_)
  change Real.exp _ = ∑ i∈s.powerset,g i
  unfold g; rw [Real.exp_sum,← Finset.prod_one_add]; exact Finset.prod_congr rfl fun i _ => by unfold f; ring

private lemma all_has {t : Finset ℕ} {U} (h : H.activities.admissible H.p U t) (h' : ∀ i∈t,permits H i U) :
    HasSum (L.accounted t U) (Real.exp (H.exponent U-(wished q H).exponent U)) := by
  let X B := L.accounted t U B
  let αi (B : Finset α) := Real.exp (∑ i∈listAll q U,L.flare.charge i U)*∏ i∈B,(Real.exp (L.more.leaf i U)-1)
  let W := Function.support X
  let f : W → Finset α := fun s => L.solicit (L.alloted s.val)
  have hT (x : W) : (L.alloted x.val).toLeft=t ∧ L.Mass x.val U := by_contra fun h => x.property (show X x.val=0 from if_neg h)
  have ht (x : W) i (hi : i∈x.val) : (L.sole i).eligible q.threshold U := by_contra fun e => x.property
    (show X x.val=0 from (if_pos (hT _)).trans (Finset.prod_eq_zero hi (show L.solid i U=0 from if_neg e)))
  let a (B : Finset α) := t.disjSum ((listAll q U).disjSum B)
  have he (x : W) : L.alloted x.val=a (f x) := eq_disjSum_iff.mpr ⟨(hT x).1, eq_disjSum_iff.mpr
    ⟨L.all_of_it (hT _).2 (fun i h => (ht _ _ h).2),rfl⟩⟩
  have hh (B : Finset L.Record) (p) (hf : L.Mass B U) (hi : ∀ i∈B,(L.sole i).eligible q.threshold U)
      (hP : L.alloted B=a p) : X B=αi p := by
    unfold X accounted
    rw [if_pos ⟨(eq_disjSum_iff.mp hP).1,hf⟩]
    calc
      _ = ∏ i∈L.alloted B,L.glow i U := by
        rw [alloted, prod_biUnion]
        · exact Finset.prod_congr rfl fun i h => if_pos (hi i h)
        intro i h j hh he; refine Finset.disjoint_left.mpr fun k hx ht => ?_
        obtain ⟨x,hp⟩ := L.zone_ne k
        exact Finset.disjoint_left.mp (hf.1 h hh he) (mem_biUnion.mpr ⟨_,hx,hp⟩) (mem_biUnion.mpr ⟨_,ht,hp⟩)
      _ = _ := by unfold αi; rw [hP,Real.exp_sum]; simp only [a,Finset.prod_disjSum,glow, Sum.elim_inl, prod_const_one,one_mul,Sum.elim_inr]
  have hp (B) (h : L.Mass B U) : Ac.Parts L.zone (L.alloted B)= B.image Subtype.val := by
    rw [show L.alloted B=(B.image Subtype.val).biUnion id by ext; simp [alloted]]
    apply Ac.separates _ _
    · intro p hp; obtain ⟨i,-,rfl⟩ := mem_image.mp hp; exact i.property.1
    intro p hp j hj he; obtain ⟨i,hi,rfl⟩ := mem_image.mp hp; obtain ⟨b,hb,rfl⟩ := mem_image.mp hj
    exact h.1 hi hb fun h => he (congr_arg Subtype.val h)
  have hX : Injective f := by
    intro s t H; refine Subtype.ext (Finset.image_injective (f:= (Subtype.val : L.Record → _)) Subtype.val_injective ?_)
    rw [← hp s.val (hT s).2,←hp t.val (hT t).2,he s,H,← he t]
  have hY : Function.support αi ⊆ Set.range f := by
    intro p hp
    obtain ⟨B,hb,hE,hV⟩ := L.takeoff h h' (A:=p) fun i he => fun e => hp (by
      unfold αi; rw [Finset.prod_eq_zero he (show Real.exp (L.more.leaf i U)-1=0 from e),mul_zero])
    refine ⟨⟨B, fun z => hp ((hh B _ hb hE hV).symm.trans z)⟩,(eq_disjSum_iff.mp (eq_disjSum_iff.mp hV).2).2⟩
  have hx : HasSum αi (Real.exp (H.exponent U-(wished q H).exponent U)) := by
    rw [L.cut U, Real.exp_add]; exact (berserk (L.absolute U)).mul_left _
  exact (hasSum_iff_hasSum_of_ne_zero_bij f hX hY (fun x => (hh x.val _ (hT _).2 (ht _) (he x)).symm)).mp hx

variable [Countable α]

def shelf (i : L.Record) := L.label.symm (Sum.inl i)
lemma scan : Injective L.shelf := L.label.symm.injective.comp Sum.inl_injective

def face (i : ℕ) := L.party (L.label i)
def gain (i : ℕ) := L.busy (L.label i)

private lemma pay (U) {B : Finset ℕ} (h : ∀ i∈B,L.gain i U ≠ 0) : B∈ Set.range (Finset.image L.shelf) := by
  apply Pad.inclusive
  intro i hi; have he := h i hi; cases ht : L.label i
  next b => exact ⟨b,L.label.symm_apply_eq.mpr ht.symm⟩
  next b => exact (he (by rw [gain,ht]; rfl)).elim
lemma coins (i : L.Record) (U) : L.gain (L.shelf i) U=L.solid i U := by rw [gain,shelf,Equiv.apply_symm_apply]; rfl
lemma ram (B : Finset L.Record) : (B.image L.shelf).biUnion L.face=(L.alloted B).toLeft := by
  ext x; rw [L.quota]; simp [face,shelf,party]
lemma living (B : Finset L.Record) (U) : L.printer.activities.admissible q U (B.image L.shelf) ↔ L.Mass B U := by
  unfold Activities.admissible Mass
  have he (i : L.Record) : L.printer.activities.forced (L.shelf i)=L.sole i := L.kept_entry i
  rw [show (B.image L.shelf).biUnion (claims L.printer) =B.biUnion (fun i => L.inv i.val) by
    ext x; simp only [claims,Finset.mem_biUnion, Finset.mem_image, exists_exists_and_eq_and,he,sole]]
  apply and_congr_left; intro h; constructor
  · intro H i hi j hj h
    change Disjoint (L.sole i).support (L.sole j).support
    rw [← he,←he]; exact H (mem_image_of_mem L.shelf hi) (mem_image_of_mem L.shelf hj) (L.scan.ne h)
  intro h i hi j hj H; obtain ⟨x,hx,rfl⟩ := mem_image.mp hi; obtain ⟨y,hy,rfl⟩ := mem_image.mp hj
  rw [he,he]; exact h hx hy fun e => H (congr_arg L.shelf e)

/-- Narrows construction and physical density delivery output on this
level, before any normalization, on the same domain (even with compulsory
short-row stencils). -/
def world {u v : ℝ} (h : H.activities.Valid H.p u v) : Sill.Narrows H L.printer where
  lowers := L.shrinks
  sites := L.face
  contains i j he := by
    unfold face at he; change _ ⊆ (L.stamp (L.label i)).support
    cases H : L.label i <;> rw [H] at he
    · exact L.halo_charge _ _ he
    exact absurd he (Finset.notMem_empty _)
  step := L.gain
  registers i := by
    unfold gain; change UsesFinal q.threshold (L.stamp (L.label i)).support _
    cases e : L.label i
    next p => exact (L.real_solid h p).2.2
    next p => exact fun _ _ _ _ => rfl
  measurable i := by unfold gain; cases L.label i; exact (L.real_solid h _).1; exact measurable_const
  gauge i := by unfold gain; cases L.label i; exact (L.real_solid h _).2.1; exact fun _ _ => rfl
  admitted i U hu := by
    unfold gain at hu; change (L.stamp (L.label i)).eligible q.threshold U
    cases he : L.label i <;> rw [he] at hu
    next p => exact show (L.sole p).eligible q.threshold U from by_contra fun H => hu (if_neg H)
    exact (hu rfl).elim
  priced _ _ := rfl
  sent s U he H := by
    obtain ⟨p,rfl⟩ := pay L U H; rw [L.ram]
    refine L.old_survives ((L.living p U).mp he) fun i hi => ?_
    have hx := H (L.shelf i) (mem_image_of_mem _ hi)
    rw [coins] at hx
    exact (show (L.sole i).eligible q.threshold U from by_contra fun e => hx (if_neg e)).2
  balance p U he hv := by
    let f (s : Finset ℕ) := if s.biUnion L.face=p ∧ L.printer.activities.admissible q U s then ∏ i∈s,L.gain i U else 0
    change HasSum f _; rw [new_power]
    have hX : Function.support f ⊆ Set.range (Finset.image L.shelf) := fun s hs =>
      L.pay U fun i hi h => hs (by unfold f; rw [Finset.prod_eq_zero hi h]; split <;> rfl)
    apply ((Finset.image_injective L.scan).hasSum_iff (fun x hx => by_contra fun h => hx (hX h))).mp
    refine (L.all_has he hv).congr_fun fun a => ?_
    unfold f accounted comp
    dsimp only; rw [ram,living]
    split
    · rw [prod_image L.scan.injOn]; exact prod_congr rfl fun i _ => L.coins _ _
    rfl
end YM.Further.ThresholdSourceRestart.Sluice.Menu
