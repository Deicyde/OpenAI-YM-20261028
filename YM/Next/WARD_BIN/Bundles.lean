import YM.Next.WARD_BIN.Merges
import YM.Work.H03


/-!
# Forced startup, structural and total-pay receipts

Filter by rank/copies BEFORE evaluation. Same reps across all sizes.
At fixed tags T the price bound uses only OLD site hits (not extrapolating a
hit estimate to a larger exponent or counting all touches as separate events).
All allowed T with this stencil family are charged separately; thus this bill
later suffices for *fused* order (mesh threshold can depend on period). Not a
uniform price asserted for ∀ᶠ N, ∀ p.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WardBin.Gas
open Filter Lattice Wilson RG Finset Function Ac MeasureTheory
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {V : Type*} [DecidableEq V] [Fintype V] {G : Gauge} {n : Side} {p : BudgetPoint} {w δ : ℝ}

section Complete
variable {R : Type*} [CommSemiring R] (Y : V → Support n) (f : V → R) (K : Shape n→R)

def pool (T : Finset V) (i : Shape n) := (univ : Finset (Camp Y)).filter (fun q => markers Y q=T ∧ spans Y q=i)
lemma goes (T : Finset V) (i : Shape n) (q) : q∈pool Y T i ↔ markers Y q=T ∧ spans Y q=i := by simp [pool]

def till (M : Support n) (T : Finset V) (q : Shape n) : R := if T≠∅ ∧ wall q ∩ M=inv q then
    ∑ i∈pool Y T q,chance f K (markers Y i,olds Y i) else 0

theorem front (M : Support n) (q : Shape n) :
    merge Y f K M q = K q + ∑ T : Finset V,till Y f K M T q := by
  unfold merge
  let v (q' : Camp Y) := if spans Y q'=q then foot Y f K M q' else 0
  let F (T : Finset V) : R := ∑ i∈ (univ.filter (fun i : Camp Y => markers Y i=T)), v i
  change ∑ i,v i = _
  rw [← sum_fiberwise _ (markers Y)]; change ∑ T,F T=_
  have hx : F ∅=K q := by
    have h : markers Y (just Y q)=∅ := by ext; simp [markers,just]
    unfold F; rw [sum_eq_single (just Y q)]
    · simp [v,foot,h]
    · intro y hy hh; have he := (mem_filter.mp hy).2
      have hw : spans Y y≠q := fun H => hh ((no_marker Y he).trans (congr_arg _ H))
      unfold v; rw [if_neg hw]
    exact fun H => False.elim <| H (mem_filter.mpr ⟨mem_univ _,h⟩)
  have he (T : Finset V) (ht : T≠∅) : F T=till Y f K M T q := calc
    _ = ∑ i ∈ pool Y T q, v i := by
      unfold F; symm; apply sum_subset (fun y hy => mem_filter.mpr ⟨mem_univ _,((goes Y _ _ _).mp hy).1⟩)
      intro y hy hh; unfold v; rw [if_neg (fun H => hh ((goes Y _ _ _).mpr ⟨(mem_filter.mp hy).2,H⟩))]
    _ = _ := by
      unfold till
      rw [← sum_const_zero (s:=pool Y T q),← sum_ite_irrel]
      refine sum_congr rfl fun i hi => ?_
      obtain ⟨hM,hS⟩ := (goes Y _ _ _).mp hi
      by_cases h : wall q∩M=inv q <;> simp [v,foot,h,hM,hS,ht]
  have hv : (∅:Finset V) ∈ univ := mem_univ _
  rw [← sum_erase_add univ F hv,hx, ← sum_erase_add _ (till Y f K M · q) hv,
    show till Y f K M ∅ q=0 by simp [till], add_zero, add_comm _ (K q)]
  congr 1; exact sum_congr rfl fun i hi => he i (mem_erase.mp hi).1

/-- One-marker formulas independent of the ambient census. -/
def aisle (W : Support n) (i : Shape n) : Finset (Finset (Shape n)) := univ.filter fun D =>
    D.Nonempty ∧ (D:Set (Shape n)).PairwiseDisjoint wall ∧ (∀ q∈D,(W∩wall q).Nonempty) ∧
      W∪D.biUnion wall=wall i ∧ D.biUnion inv=inv i

def tag (W M : Support n) (g : R) (K : Shape n→R) (i : Shape n) :=
  if wall i ∩ M=inv i then g * ∑ D∈aisle W i,∏ q∈D,K q else 0

omit [DecidableEq V] [Fintype V] in
lemma singleton_wall (v : V) (D : Finset (Shape n)) :
    (({v}:Finset V).disjSum D).biUnion (hull Y) = Y v ∪ D.biUnion wall := by
  ext i; simp_rw [mem_union,mem_biUnion]
  constructor
  · rintro ⟨a,h,H⟩; cases a with
    | inl k => rw [mem_singleton.mp (inl_mem_disjSum.mp h)] at H; exact Or.inl H
    | inr k => exact Or.inr ⟨_,inr_mem_disjSum.mp h,H⟩
  rintro (hw|⟨q,h1,h2⟩)
  · exact ⟨Sum.inl v,by simp,hw⟩
  exact ⟨Sum.inr q, inr_mem_disjSum.mpr h1,h2⟩

theorem singleton_till (M : Support n) (v : V) (q : Shape n) : till Y f K M {v} q=tag (Y v) M (f v) K q := by
  by_cases ht : wall q ∩ M=inv q
  · unfold till tag
    rw [if_pos ⟨(singleton_nonempty _).ne_empty,ht⟩,if_pos ht,mul_sum]
    refine sum_bij (fun p _ => olds Y p) (fun p hp => ?_) (fun p hp p' hp' H => ?_) (fun D hD => ?_)
      (fun p hp => by unfold chance; rw [((goes Y _ _ p).mp hp).1]; simp)
    · obtain ⟨hi,hj⟩ := (goes Y _ _ _).mp hp
      have hh := splitCamp Y p; rw [hi] at hh
      refine mem_filter.mpr ⟨mem_univ _,roots Y p,distinct Y p, (one_marker Y v _ (roots Y p) (distinct Y p)).mp
        (by rw [hh]; exact active Y p),?_, ?_⟩
      · rw [← singleton_wall,hh,← hj]; rfl
      rw [← hj]; rfl
    · apply Subtype.ext
      exact (splitCamp Y p).symm.trans (by rw [H,((goes Y _ _ _).mp hp).1, ← ((goes Y _ _ _).mp hp').1,splitCamp])
    obtain ⟨ha,hb,hc,hr,hi⟩ := (mem_filter.mp hD).2
    have he : Spark _ _ := (one_marker Y _ _ ha hb).mpr hc
    let p : Camp Y := ⟨_, he, toRight_disjSum.symm ▸ ha, toRight_disjSum.symm ▸ hb⟩
    have h : p.val=({v}:Finset V).disjSum D := rfl
    have hS : markers Y p={v} := toLeft_disjSum
    have hg : olds Y p=D := toRight_disjSum
    refine ⟨p,(goes Y _ _ _).mpr ⟨hS,Subtype.ext (Prod.ext ?_ ?_)⟩,hg⟩
    · change p.val.biUnion (hull Y)=wall q; rwa [h,singleton_wall]
    change (olds Y p).biUnion inv=inv q; rwa [hg]
  simp [ht,till,tag]
end Complete

section Actual
variable {Y : V → Support n} {A : Activities G n} {T : Finset V} {c : V → ℝ} {d : V → Config G n → ℂ}

abbrev offer (Y : V → Support n) (d : V → Config G n → ℂ) (A : Activities G n) (t : ℝ)
    (T : Finset V) (i : Shape n) (U : Config G n) := till Y (d · U) (fun i => (vacuum A U i:ℂ)) (flags t U) T i

/-- Genuine complement relative to the residual argument's flag set. -/
structure Fault (p : BudgetPoint) (X : Support n) (f : Config G n → ℂ) : Prop where
  born U : f U ≠ 0 → ¬Healthy p.threshold X U
  sym : GaugeInvariant f
  borel : Measurable f
  vicinity : UsesFinal p.threshold X f

/-- Recycled costs with no change to overlap pricing. -/
structure Boxed (p : BudgetPoint) (i : Shape n) (X : Support n) (f : Config G n → ℂ) : Prop where
  born U : f U ≠ 0 → wall i ∩ flags p.threshold U=inv i
  needed : f≠0 → X ⊆ wall i
  sym : GaugeInvariant f
  borel : Measurable f
  vicinity : UsesFinal p.threshold (wall i) f

lemma collect (h : A.ForcedFamily p) (T : Finset V) (hx : ∀ v, Fault p (Y v) (d v)) (i : Shape n) :
    Boxed p i (T.biUnion Y) (offer Y d A p.threshold T i) := by
  have hm (z : Shape n) : Measurable (fun U => vacuum A U z) := by
    apply Measurable.tsum; intro l; dsimp only
    split; exact h.meas _; exact measurable_const
  have hs (U : Config G n) k (z : Shape n) : vacuum A (gauge k U) z=vacuum A U z := by
    unfold vacuum bucket; refine tsum_congr fun j => ?_
    dsimp only; rw [h.sym j k U]
  have hu (z : Shape n) : UsesFinal p.threshold (wall z) (fun U => vacuum A U z) := by
    intro U W hf hd; unfold vacuum bucket; refine tsum_congr fun j => ?_
    by_cases hk : shape A j=z
    · subst z; rw [if_pos rfl,if_pos rfl]; exact h.reads _ U W hf hd
    simp [hk]
  let F := offer Y d A p.threshold T i
  constructor
  · intro U h; unfold offer till at h; split at h; (rename_i H; exact H.2); contradiction
  · intro h; by_cases hp : (pool Y T i).Nonempty
    · obtain ⟨z,hz⟩ := hp; obtain ⟨hf,hH⟩ := (goes _ _ _ _).mp hz
      rw [← hf,← hH]; exact biUnion_subset.mpr fun _ he => has_marker _ _ he
    exfalso; apply h; funext U; simp [offer,till,not_nonempty_iff_eq_empty.mp hp]
  · intro k U
    simp only [offer,till,gauge_flags, funext (hs U k), chance]; simp_rw [fun i => (hx i).sym k U]
  · unfold offer till
    by_cases hk : T=∅
    · simp [hk]
    have hy : MeasurableSet {U : Config G n|wall i∩flags p.threshold U=inv i} := by
      let t : ForcedAddress G n := ⟨wall i, inv i,present i,grows i,fun _ => True⟩
      simpa [t,ForcedAddress.eligible] using! Work.H03.eligible_measurable p.threshold t (by simp [t])
    refine Measurable.ite (show MeasurableSet {U : Config G n| T≠∅ ∧ wall i∩flags p.threshold U=inv i} from by simpa [hk] using hy) (measurable_fun_sum _ fun q _ => ?_) measurable_const
    unfold chance
    exact (measurable_fun_prod _ (fun i _ => (hx i).borel)).mul
      (measurable_fun_prod _ fun j _ => Complex.continuous_ofReal.measurable.comp (hm j))
  intro U W ha H
  unfold offer till
  rw [H]; split_ifs with he
  · apply sum_congr rfl; intro q hh
    have hj := ((goes Y _ _ _).mp hh).2
    subst i; unfold chance
    rw [prod_congr (s₁:=markers Y q) rfl (fun i hi => show d i U=d i W from
      Work.H03.reads_larger (has_marker Y q hi) (hx i).vicinity U W ha H), prod_congr (s₁:=olds Y q) rfl (fun i hi =>
        show ((vacuum A U i):ℂ)=((vacuum A W i):ℂ) from congr_arg _ (Work.H03.reads_larger (has_wall Y q hi) (hu i) U W ha H))]
  rfl

lemma vacuum_cost (h : A.KBound p w) : ∃ K : Shape n→ℝ, (∀ i,0≤K i) ∧
    (∀ i U,‖vacuum A U i‖ ≤ K i) ∧ ∀ x : Site n, ∑ i : Shape n, (if x∈wall i then p.mass (wall i) (K i) else 0) ≤ w := by
  obtain ⟨b,hb,hB⟩ := h
  have h := show A.KBound p w from ⟨b,hb,hB⟩
  have hs := Activities.summable_charge (fun i => mentions (shape A i)) (fun i => (hb i).1) hB
  let K := bucket A b
  have hn {i j} : 0≤(if shape A i=j then b i else 0) := by split; exact (hb i).1; exact le_rfl
  refine ⟨K,fun i => tsum_nonneg (fun j => hn),fun i U => ?_,fun x => ?_⟩
  · unfold vacuum bucket
    have hz (j) : ‖if shape A j=i then A.K j U else 0‖ ≤ if shape A j=i then b j else 0 := by
      split; exact (hb _).2 _; simp
    have ht := summable_ite hs (fun j => shape A j=i)
    have h := ht.of_nonneg_of_le (fun _ => norm_nonneg _) hz
    exact (norm_tsum_le_tsum_norm h).trans (h.tsum_le_tsum hz ht)
  let a (i : Shape n) (j : ℕ) := if shape A j=i then if x∈wall i then p.mass (wall i) (b j) else 0 else 0
  have hc (i : Shape n) : (if x∈wall i then p.mass (wall i) (K i) else 0)=∑' j,a i j := by
    by_cases ht : x∈wall i
    · simp only [a,ht,if_true,BudgetPoint.mass,K,bucket, ← tsum_mul_left]
      refine tsum_congr fun j => ?_; split <;> simp
    simp [a,ht]
  have hw (j) : ∑ i,a i j=(if x∈wall (shape A j) then p.mass (wall (shape A j)) (b j) else 0) := by simp [a]
  simp_rw [hc, ← Summable.tsum_finsetSum (f:=a) (fun i _ => show Summable _ from by
    unfold a
    by_cases he : x∈wall i
    · simp only [he,if_true]; exact summable_ite (hs.mul_left _) _
    simp [he]), hw]; exact (hB x).2.2

omit [DecidableEq V] [Fintype V] in
lemma mass_chance (i : Camp Y) {K : Shape n→ℝ} (hk : ∀ i,0≤K i) (hc : ∀ i,0≤c i) (p : BudgetPoint) :
    p.mass (wall (spans Y i)) (chance c K (markers Y i,olds Y i)) ≤
      chance (fun v => p.mass (Y v) (c v)) (fun q => p.mass (wall q) (K q)) (markers Y i,olds Y i) := by
  have he := Ac.cover (hull Y) p.B (active Y i)
  change coverNumber p.B (wall (spans Y i)) ≤ _ at he
  have hz : ∑ j∈i.val, coverNumber p.B (hull Y j) = ∑ v∈markers Y i, coverNumber p.B (Y v) +
          ∑ q∈olds Y i, coverNumber p.B (wall q) :=
    sum_sum_eq_sum_toLeft_add_sum_toRight ..
  rw [hz] at he
  unfold chance BudgetPoint.mass
  simp only [prod_mul_distrib,← Real.exp_sum, ← mul_sum]
  rw [mul_mul_mul_comm (Real.exp ..),← Real.exp_add, ← mul_add]
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ p.exponent_pos.le))
    (mul_nonneg (prod_nonneg fun _ _ => hc _) (prod_nonneg fun _ _ => hk _))
  exact_mod_cast he

omit [DecidableEq V] [Fintype V] in
lemma stands_cost (i : Camp Y) {K : Shape n→ℝ} (U : Config G n)
    (he : ∀ v, ‖d v U‖ ≤ c v) (h : ∀ i, ‖vacuum A U i‖ ≤ K i) :
    ‖chance (d · U) (fun i => (vacuum A U i:ℂ)) (markers Y i,olds Y i)‖ ≤ chance c K (markers Y i,olds Y i) := by
  unfold chance
  simp only [norm_mul,norm_prod,Complex.norm_real]
  exact mul_le_mul (prod_le_prod (fun _ _ => norm_nonneg _) (fun v _ => he v))
    (prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => h i)) (prod_nonneg fun _ _ => norm_nonneg _)
    (prod_nonneg fun i _ => (norm_nonneg _).trans (he i))

/-- Bill independent of exterior period, except card X. No factorial.
Not yet charging number of T. -/
def bill (p : BudgetPoint) (w : ℝ) (Y : V → Support n) (c : V → ℝ) (T : Finset V) :=
    (∏ v∈T,p.mass (Y v) (c v))*(Real.exp ((T.biUnion Y).card*w)-1)

lemma all_cost (Y : V → Support n) {T : Finset V} (hh : T.Nonempty) (h : A.KBound p w)
    (hx : ∀ v U, ‖d v U‖ ≤ c v) :
    ∃ b : Shape n→ℝ, (∀ i,0 ≤ b i) ∧ (∀ i U, ‖offer Y d A p.threshold T i U‖ ≤ b i) ∧
      ∑ i,p.mass (wall i) (b i) ≤ bill p w Y c T := by
  obtain ⟨K,hk,hK,H⟩ := vacuum_cost h
  let f (q : Camp Y) := chance c K (markers Y q,olds Y q)
  let b (i : Shape n) := ∑ q∈pool Y T i,f q
  have hc v : 0 ≤ c v := (norm_nonneg _).trans (hx v 1)
  have hb (i : Shape n) : 0 ≤ b i := sum_nonneg fun j _ => mul_nonneg (prod_nonneg fun i _ => hc _)
    (prod_nonneg fun i _ => hk _)
  refine ⟨b,hb,fun i U => ?_,?_⟩
  · unfold offer till; split
    · exact (norm_sum_le ..).trans (sum_le_sum fun q _ => stands_cost q U (hx · _) (hK · _))
    rw [norm_zero]; exact hb _
  let D := univ.filter fun q : Camp Y => markers Y q=T
  let a (i : Shape n) := p.mass (wall i) (K i)
  have ha i : 0≤a i := mul_nonneg (Real.exp_pos _).le (hk i)
  have hre : ∑ i,p.mass (wall i) (b i)=∑ q∈D,p.mass (wall (spans Y q)) (f q) := by
    symm; rw [← sum_fiberwise _ (spans Y)]
    refine sum_congr rfl fun q _ => ?_
    have he : pool Y T q=D.filter (fun i => spans Y i=q) := by ext i; simp [pool,D]
    unfold b BudgetPoint.mass; rw [he,mul_sum]; refine sum_congr rfl (fun i hi => ?_)
    rw [(mem_filter.mp hi).2]
  let t := T.biUnion Y
  let Q := buds wall univ t
  have hy : ∑ i∈Q,a i ≤ t.card*w :=
    (sum_congr rfl (g:=fun i => K i * Real.exp (p.supportExponent * coverNumber p.B (wall i)))
      (fun _ _ => mul_comm ..)).trans_le <| Ac.demand wall p.B (show Hit wall p.B K p.supportExponent w from by
        intro x
        refine ⟨fun i => ?_,(hasSum_fintype _).summable,?_⟩
        · dsimp only; split
          · exact mul_nonneg (hk _) (Real.exp_pos _).le
          exact le_rfl
        rw [tsum_fintype]
        apply le_trans _ (H x); refine sum_le_sum fun i _ => ?_
        split
        · exact (mul_comm ..).le
        exact le_rfl) t univ
  have hg (q) (hq : q∈D) : olds Y q⊆ Q := by
    intro i hi
    have ht := (mem_filter.mp hq).2
    obtain ⟨v,hv,k,hk⟩ := outer_stem _ q (ht.symm ▸ hh) hi
    obtain ⟨hk,hK⟩ := mem_inter.mp hk
    exact (alive ..).mpr ⟨mem_univ _, k,mem_biUnion.mpr ⟨v,ht ▸ hv,hk⟩,hK⟩
  have hn : ∑ q∈D, ∏ i∈olds Y q,a i ≤ Real.exp (t.card*w)-1 := by
    let Q' := Q.powerset
    let Z := D.image (olds Y)
    have he : Z ⊆ Q'.erase ∅ := by
      intro q hq; obtain ⟨i,hi,rfl⟩ := mem_image.mp hq
      exact mem_erase.mpr ⟨(roots Y i).ne_empty,mem_powerset.mpr (hg i hi)⟩
    calc
      _ = ∑ q∈Z, ∏ i∈q,a i := by
        rw [show Z = image _ _ from rfl, sum_image]; intro i hi j hj hh
        apply Subtype.ext
        have hz := splitCamp Y i
        exact hz.symm.trans (by
          rw [hh,(mem_filter.mp (show i∈D from hi)).2,← (mem_filter.mp (show j∈D from hj)).2,splitCamp])
      _ ≤ ∑ q∈ Q'.erase ∅, ∏ i∈q,a i := sum_le_sum_of_subset_of_nonneg he (fun _ _ _ => prod_nonneg fun _ _ => ha _)
      _ ≤ _ := by
        rw [le_sub_iff_add_le]
        change (∑ q∈ Q'.erase ∅, ∏ i∈q,a i)+1 ≤ _
        rw [← show ∏ i∈ (∅:Finset (Shape n)), a i=1 from prod_empty, sum_erase_add Q' (fun q => ∏ i∈q,a i) (show ∅∈Q' by simp [Q']),
          show Q'=Q.powerset from rfl,← prod_add_one]
        calc
          _ ≤ ∏ i∈ Q, Real.exp (a i) := prod_le_prod (fun i _ => by have := ha i; positivity) (fun _ _ => Real.add_one_le_exp _)
          _ ≤ _ := by rw [← Real.exp_sum,Real.exp_le_exp]; exact hy
  rw [hre]; unfold bill
  calc
    _ ≤ ∑ q∈ D, (∏ v∈T,p.mass (Y v) (c v)) * ∏ i∈olds Y q,a i := by
      refine sum_le_sum fun i hi => (mass_chance i hk hc p).trans (le_of_eq ?_)
      unfold chance; rw [(mem_filter.mp hi).2]
    _ ≤ _ := by
      rw [← mul_sum]; exact mul_le_mul_of_nonneg_left hn (prod_nonneg fun v _ => mul_nonneg (Real.exp_pos _).le (hc _))
end Actual
end YM.WardBin.Gas
