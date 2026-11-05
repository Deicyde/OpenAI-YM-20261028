import YM.Bid.Craft
import YM.Ovens.Coffee
import YM.Push.CORRECTED_COLUMNS.Pad
/-!
# Turn the full comparison K functions back to Bands format

Charge every slot's rooted bounds (uniform, even if many markers).
Also do regular repacked from exact unforced address family. Keep exponential
support order in both for next steps of comparison (we only use weaker
versions in the last torus consumer).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Corrected.Prepare
open Marker Lattice Wilson RG Overlay Endpoint Ac Function Set MeasureTheory
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {V : Type*} [DecidableEq V] [Fintype V] {R : Census V}
variable {n : Side} {G : Gauge} {P : Rep G n} {v : V → Site n}

def emit (M : ℕ) (a : ℝ) (X : Support n) := Real.exp (a * coverNumber M X)
lemma emit_pos (M : ℕ) (a : ℝ) (X : Support n) : 0 < emit M a X := Real.exp_pos _

/-- Exponential support lengths on both kinds of charges in Value. `b=0`
 in Value ok (just a price). -/
structure Further (H : Bands R P) (w : V → ℝ) (M : ℕ) (a u b c : ℝ) : Prop extends Value H w u b c where
  regular_budget : ∃ t : ℕ → ℝ,
    (∀ i, 0≤t i ∧ ∀ U : Config G n, Healthy P.p.threshold (H.support i) U → ‖H.H i U‖≤t i) ∧
    ∀ i : V, SumBudget (fun j => if i∈ (H.rays j).val then
      Poly.toll w (H.rays j)*t j*emit M a (H.support j) else 0) b
  forced_budget : ∃ t : ℕ × ℕ → ℝ, (∀ i j, 0≤t (i,j) ∧ ∀ x, ‖H.entries i j x‖ ≤ t (i,j)) ∧
    ∀ i : V, SumBudget (fun k => if i∈ (H.marks k.1 k.2).val then
      Poly.toll w (H.marks k.1 k.2)*t k*emit M a (oldSites P k.1) else 0) c

-- Source exponential atoms (without vacuum). No global units here; absorb
 
structure Atoms (P : BudgetPoint) (R : Census V) (v : V → Site n) (G : Gauge) (X : Type*) where
  sites : X → Support n
  tag : X → R.Mode
  H : X → Config G n → ℂ
  proper i : (tag i).val.Nonempty
  pin i l : l ∈ (tag i).val → v l ∈ sites i
  borel i : Measurable (H i)
  footprint i : LocalOn (sites i) (H i)
  gauge i : GaugeInvariant (H i)

namespace Atoms
variable {X Y : Type*} {p : BudgetPoint} (F : Atoms p R v G X)
def portion (i : X) (U : Config G n) := Poly.send (F.tag i) (masked p.threshold (F.sites i) (F.H i) U)
def sum (U : Config G n) := ∑' i,F.portion i U

def Cost (w : V → ℝ) (M : ℕ) (a b : ℝ) : Prop := ∃ t : X → ℝ, (∀ i,
    0≤ t i ∧ ∀ U, Healthy p.threshold (F.sites i) U → ‖F.H i U‖≤ t i) ∧
    ∀ i, SumBudget (fun j => if i∈ (F.tag j).val then Poly.toll w (F.tag j)*t j*emit M a (F.sites j) else 0) b
variable {w : V → ℝ}
lemma summablePortions (hw : ∀ i, 0<w i) {M a b} (h : F.Cost w M a b) (ha : 0≤a) (U) :
    Summable fun i => F.portion i U := by
  obtain ⟨q,hq,H⟩ := h
  have he := per_system (f:=fun j => Poly.toll w (F.tag j)*q j*emit M a (F.sites j)) (fun j =>
    mul_nonneg (mul_nonneg (Poly.worth hw _).le (hq j).1) (emit_pos ..).le) F.proper H
  refine (Poly.budgeted hw he.2.1 ?_).1
  intro i; rw [portion,Poly.solo]; apply le_trans ?_ (le_mul_of_one_le_right (mul_nonneg (Poly.worth hw _).le (hq i).1)
    (Real.one_le_exp (mul_nonneg ha (Nat.cast_nonneg _))))
  apply mul_le_mul_of_nonneg_left _ (Poly.worth hw _).le
  by_cases hv : Healthy p.threshold (F.sites i) U
  · rw [masked_eq _ _ _ _ hv]; exact (hq i).2 U hv
  rw [masked_ne _ _ _ _ hv,norm_zero]; exact (hq i).1
lemma no_unit (hw : ∀ i, 0<w i) {M a b} (h : F.Cost w M a b) (ha : 0≤a) (U) :
    (F.sum U).part R.quiet=0 := by
  unfold Atoms.sum; rw [Poly.share (F.summablePortions hw h ha U)]
  have ht i : ((F.portion i U).part R.quiet)=0 := by
    unfold portion
    rw [Poly.part_send, if_neg (fun v => ((F.proper i).ne_empty (congr_arg Subtype.val v.symm)))]
  simp_rw [ht,tsum_zero]
end Atoms

variable [Nonempty V]
private abbrev Hot (R : Census V) := {x : R.Mode // x≠R.quiet}
omit [Fintype V] in
private lemma usable (R : Census V) : Nonempty (Hot R) := by
  obtain ⟨w⟩ := ‹Nonempty V›; exact ⟨⟨R.fire w,R.fire_hot _⟩⟩
private def invite (R : Census V) (i : Hot R) := ((Fintype.equivFin (Hot R)) i).val
omit [Fintype V] [Nonempty V] in
private lemma invite_inj : Injective (invite R) := fun _ _ h => (Fintype.equivFin (Hot R)).injective (Fin.ext h)
private def whereOf (R : Census V) := Function.extend (invite R) Subtype.val fun _ => (Classical.choice (usable R)).val
omit [Fintype V] in
private lemma where_of (i : Hot R) : whereOf R (invite R i)=i.val := invite_inj.extend_apply ..
omit [Fintype V] in
private lemma isWhere (i : ℕ) : (whereOf R i).val.Nonempty := by
  by_cases h : i ∈ range (invite R)
  · obtain ⟨x,rfl⟩ := h
    rw [where_of]; exact Finset.nonempty_iff_ne_empty.mpr fun w => x.property (Subtype.ext w)
  rw [whereOf,extend_apply' _ _ _ h]
  exact Finset.nonempty_iff_ne_empty.mpr (fun h => (Classical.choice (usable R)).property (Subtype.ext h))

variable {X : Type*} [Countable X]
variable (L : Original P v R)
def reads (i : ℕ) (j : ℕ) (U : Config G n) := Function.extend (invite R)
    (fun p : Hot R => (L.value i U).part p.val) 0 j

omit [Fintype V] [Nonempty V] in
private lemma paid (i) (j : Hot R) (U) : reads L i (invite R j) U=(L.value i U).part j.val := invite_inj.extend_apply ..
omit [Fintype V] [Nonempty V] in
private lemma ignored (i j) (U) (h : j∉ range (invite R)) : reads L i j U=0 := Function.extend_apply' _ (0:ℕ → ℂ) _ h

variable (F : Atoms P.p R v G X)
open scoped Classical in
private def reserve (X : Type*) [Countable X] : X ↪ ℕ :=
    let H : ∃ f : X → ℕ, Injective f := (countable_iff_exists_injective X).mp ‹_›
    ⟨H.choose, H.choose_spec⟩

-- padding if needed
private def pad (j : ℕ) : R.Mode := Function.extend (reserve X) F.tag (fun _ => R.fire (Classical.choice ‹Nonempty V›)) j
private def area (j : ℕ) : Support n := Function.extend (reserve X) F.sites (fun _ => Finset.univ) j
private def marker (j : ℕ) := Function.extend (reserve X) F.H (fun _ => 0) j

/-- New actual valuation output. -/
def construct : Bands R P where
    origins := v
    units _ := 0
    support := area F
    rays := pad F
    H := marker F
    marks _ := whereOf R
    entries := reads L

omit [Fintype V] in
lemma sameReg (s : X) : (construct L F).rays (reserve X s)= F.tag s ∧
    area F (reserve X s)=F.sites s ∧ marker F (reserve X s) = F.H s := by
  refine ⟨(reserve X).injective.extend_apply F.tag (fun _ => R.fire (Classical.choice ‹Nonempty V›)) _,(reserve X).injective.extend_apply ..,(reserve X).injective.extend_apply ..⟩
omit [Fintype V] in
lemma sameRay (s : X) (U) : (construct L F).ray (reserve X s) U=F.portion s U := by
  obtain ⟨he,ha,hh⟩ := sameReg L F s
  unfold Bands.ray Atoms.portion; rw [he,show (construct L F).support (reserve X s)=_ from ha, show (construct L F).H (reserve X s)=_ from hh]
omit [Fintype V] in
lemma noRay {i} (h : i∉ Set.range (reserve X)) (U) : (construct L F).ray i U=0 := by
  unfold Bands.ray
  rw [show (construct L F).H i=0 from Function.extend_apply' _ (fun _=>0) _ h]
  unfold masked; by_cases hx : Healthy P.p.threshold ((construct L F).support i) U
  · rw [Set.indicator_of_mem hx]; simp
  rw [Set.indicator_of_notMem hx]; simp

omit [Fintype V] in
lemma sameEq (i : ℕ) (U : Config G n) : (construct L F).each i U = L.value i U := by
  classical
  let H := construct L F
  let K := L.value i U
  unfold Bands.each
  rw [← show ∑' j : Hot R, Poly.send j.val (K.part j.val) = _ from Pad.sums _ (invite_inj (R:=R)) _
    (fun l => H.tagged i l U) (fun j => by
      change Poly.send (whereOf R (invite R j)) (reads L i (invite R j) U)=_
      rw [where_of,paid]) (fun j w => by
      by_contra h; apply w; change Poly.send (whereOf R j) (reads L i j U) = _; rw [ignored _ _ _ _ h,Poly.send_zero]),
    tsum_fintype]
  ext u
  rw [Poly.part_plus, Poly.part_sum, Poly.part_send]
  by_cases hu : u=R.quiet
  · subst u; rw [if_pos rfl, Finset.sum_eq_zero (fun y _ => ?h), add_zero]
    · exact (by rw [L.pure])
    rw [Poly.part_send, if_neg (Ne.symm y.property)]
  rw [if_neg hu,zero_add,Finset.sum_eq_single (⟨u,hu⟩ : Hot R)]
  · rw [Poly.part_send,if_pos rfl]
  · intro x hx hh; rw [Poly.part_send,if_neg fun w => hh (Subtype.ext w.symm)]
  simp
lemma evaluated (U) : (construct L F).density U = (Real.exp (P.exponent U) : ℂ) •
    (Poly.pass (F.sum U) * ∑' i,UnionK.oldEval L i U) := by
  let H := construct L F
  have he : H.extra U=F.sum U := by
    unfold Bands.extra
    simp only [H,show (construct L F).units=(fun _=>0) from rfl,Poly.send_zero,Finset.sum_const_zero,zero_add]
    refine Eq.symm (Pad.sums _ (reserve X).injective _ _ (fun s => sameRay L F s U) (fun y hy => by
      by_contra h; exact hy (noRay _ _ h _)))
  have hv (i : Finset ℕ) : H.packet i U=UnionK.oldEval L i U := by
    classical
    unfold Bands.packet UnionK.oldEval; split; apply Finset.prod_congr rfl; intro j _; exact sameEq ..; rfl
  unfold Bands.density Bands.cluster; rw [he]; change _ • (_ * ∑' i,H.packet i U)=_; simp_rw [hv]

private lemma weaken {W : Type*} {f g : W→ℝ} {A : ℝ} (h : SumBudget f A) (hf : ∀ i,0≤g i) (ht : ∀ i,g i ≤ f i) :
    SumBudget g A := by
  have hp := h.2.1.of_nonneg_of_le hf ht
  exact ⟨hf,hp,(hp.tsum_le_tsum ht h.2.1).trans h.2.2⟩

variable {w : V → ℝ} {M : ℕ} {a b c : ℝ}
omit [Fintype V] in
private lemma rooted_reg (H : F.Cost w M a b) :
    let A := construct L F
    ∃ t : ℕ → ℝ, (∀ i, 0≤t i ∧ ∀ U : Config G n, Healthy P.p.threshold (A.support i) U → ‖A.H i U‖≤t i) ∧
      ∀ i : V, SumBudget (fun j => if i∈ (A.rays j).val then
      Poly.toll w (A.rays j)*t j*emit M a (A.support j) else 0) b := by
  intro A; obtain ⟨q,hq,h⟩ := H
  let t := Function.extend (reserve X) q 0
  have he i : t (reserve X i)=q i := (reserve X).injective.extend_apply ..
  have hv i (h : i∉ Set.range (reserve X)) : t i=0 := Function.extend_apply' q (0:ℕ→ℝ) i h
  have ht (s) : A.H (reserve X s)=F.H s ∧ A.support (reserve X s)=F.sites s ∧ A.rays (reserve X s)=F.tag s :=
    ⟨(sameReg L F s).2.2,(sameReg L F s).2.1, (sameReg L F s).1⟩
  refine ⟨t,fun i => ?_,fun i => Pad.absolute _ (reserve X).injective ?_ ?_ (h i)⟩
  · by_cases h : i∈ Set.range (reserve X)
    · obtain ⟨s,rfl⟩ := h; rw [he,(ht ..).1,(ht ..).2.1]; exact hq s
    rw [hv _ h, show A.H i=0 from Function.extend_apply' _ (fun _=>0) _ h]; simp
  · intro j; rw [he,(ht ..).2.1,(ht ..).2.2]
  intro j hj; by_contra h; apply hj; dsimp only; rw [hv _ h]; split <;> simp

private lemma forced {Y : ℕ → Poly R} (hw : ∀ i,0<w i) (hf : ∀ i U, Width.Covered (L.value i U) (Y i))
    (H : Hit (oldSites P) M (fun i => Poly.price w (Y i)) a c) :
    ∃ t : ℕ × ℕ → ℝ, (∀ i j, 0≤t (i,j) ∧ ∀ x, ‖(construct L F).entries i j x‖ ≤ t (i,j)) ∧
    ∀ i : V, SumBudget (fun k => if i∈ ((construct L F).marks k.1 k.2).val then
      Poly.toll w ((construct L F).marks k.1 k.2)*t k*emit M a (oldSites P k.1) else 0) c := by
  classical
  let e : ℕ × Hot R → ℕ × ℕ := Prod.map id (invite R)
  -- price only actually anchored. Drop budget for other masks after ht proof.
  let q (p : ℕ × Hot R) := if h : ∀ j∈ p.2.val.val, v j ∈ oldSites P p.1 then ‖(Y p.1).part p.2.val‖ else 0
  let t := Function.extend e q 0
  have hx : Function.Injective e := by
    intro x y h
    change (x.1,invite R x.2)=(y.1, invite R y.2) at h
    exact Prod.ext (Prod.mk.inj h).1 (invite_inj (Prod.mk.inj h).2)
  have he i j : t (i, invite R j)=q (i,j) := hx.extend_apply q (0:ℕ×ℕ→ℝ) (i,j)
  have hv i j (h : j∉ Set.range (invite R)) : t (i,j)=0 := Function.extend_apply' q (0:ℕ×ℕ→ℝ) _ (fun ⟨s,e⟩ => h ⟨s.2,(show _ from congr_arg Prod.snd e)⟩)
  refine ⟨t,fun i j => ?_,fun i => ?_⟩
  · by_cases h : j∈ Set.range (invite R)
    · obtain ⟨u,rfl⟩ := h
      rw [he]; unfold q
      split_ifs with h
      · exact ⟨norm_nonneg _,fun U=> by
          have h := paid L i u U
          change ‖reads L i (invite R u) U‖ ≤ _; rw [h, (hf i U).norm]; exact (hf i U u.val).1⟩
      refine ⟨le_refl _,fun U => ?_⟩
      change ‖reads L i (invite R u) U‖ ≤ _; rw [paid]; apply le_of_eq
      rw [norm_eq_zero]; by_contra w; exact h ((L.locality i).carry U u.val w)
    rw [hv _ _ h]; exact ⟨le_rfl,fun U => by change ‖reads L i j U‖≤0; rw [ignored L _ _ _ h,norm_zero]⟩
  let C (k : ℕ × Hot R) := if i∈ k.2.val.val then Poly.toll w k.2.val * q k * emit M a (oldSites P k.1) else 0
  have hn k : 0 ≤ C k := by unfold C q; split_ifs <;> first | exact le_rfl | exact mul_nonneg (mul_nonneg (Poly.worth hw _).le (by positivity)) (emit_pos ..).le
  refine Pad.absolute e hx (u:=C) (fun ⟨i,j⟩ => ?_) ?_ (show SumBudget C _ from ?_)
  · rw [show (construct L F).marks (e (i,j)).1 (e (i,j)).2=j.val from where_of _]
    change (if _∈j.val.val then _* t (i,invite R j)*_ else _)=_
    rw [he]; rfl
  · rintro ⟨x,y⟩ hy; by_contra H; apply hy; dsimp only; rw [show t (x,y)=0 from Function.extend_apply' q (0:ℕ×ℕ → ℝ) _ H]; split <;> simp
  let y k := if v i∈ oldSites P k then Poly.price w (Y k)*emit M a (oldSites P k) else 0
  have hj : SumBudget y c := H (v i)
  have h' k : ∑' j : Hot R,C (k,j) ≤ y k := by
    rw [tsum_fintype]; unfold y; split_ifs with h
    · unfold Poly.price; rw [Finset.sum_mul]
      let p j := Poly.toll w j * ‖(Y k).part j‖ * emit M a (oldSites P k)
      refine (le_trans (b:=∑ j∈ (Finset.univ: Finset (Hot R)).image Subtype.val,p j) ?_
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _=> ?_)))
      · rw [Finset.sum_image Subtype.val_injective.injOn]; refine Finset.sum_le_sum (fun j hj => ?_)
        unfold C q p; split_ifs <;> (try simp only [mul_zero,zero_mul]) <;> first | exact le_rfl | exact mul_nonneg (mul_nonneg (Poly.worth hw _).le (norm_nonneg _)) (emit_pos ..).le
      exact mul_nonneg (mul_nonneg (Poly.worth hw _).le (norm_nonneg _)) (emit_pos ..).le
    exact le_of_eq (Finset.sum_eq_zero fun j _ => by unfold C q; split_ifs with he hh; exact (h (hh i he)).elim; all_goals simp)
  have ht := hj.2.1.of_nonneg_of_le (fun i => tsum_nonneg fun j => hn (i,j)) h'
  have hh : Summable C := (summable_prod_of_nonneg hn).mpr ⟨fun _ => (hasSum_fintype _).summable,ht⟩
  exact ⟨hn,hh,hh.tsum_prod.trans_le ((ht.tsum_le_tsum h' hj.2.1).trans hj.2.2)⟩

theorem after {Y : ℕ → Poly R} (hw : ∀ i,0<w i) (hf : ∀ i U, Width.Covered (L.value i U) (Y i))
    (H : Hit (oldSites P) M (fun i => Poly.price w (Y i)) a c) (he : F.Cost w M a b) (ha : 0≤a) :
    Further (construct L F) w M a 0 b c := by
  let Q := construct L F
  have hx s : Q.H (reserve X s)=F.H s ∧ Q.rays (reserve X s)=F.tag s ∧ Q.support (reserve X s)=F.sites s :=
    ⟨(sameReg L F s).2.2,(sameReg L F s).1,(sameReg L F s).2.1⟩
  have hy i (h : i∉Set.range (reserve X)) : Q.H i=0 ∧ Q.rays i=R.fire (Classical.choice ‹Nonempty V›) ∧ Q.support i=Finset.univ :=
    ⟨Function.extend_apply' F.H (fun _=> 0) i h, Function.extend_apply' F.tag (fun _ => R.fire (Classical.choice ‹Nonempty V›)) i h,
      Function.extend_apply' F.sites (fun _ => Finset.univ) i h⟩
  have ht i j : Q.marks i (invite R j)=j.val := where_of j
  have hv i j : Q.entries i (invite R j)=fun U => (L.value i U).part j.val := funext (paid L i j)
  have hu i j h : Q.entries i j=0 := funext fun U => ignored L i j U h
  have hm : Endpoint.Value Q w 0 b c := by
    refine ⟨hw,?_,?_,?_,?_,?_,fun i j => isWhere j,?_,?_,?_,?_,?_,fun i => ?_,?_,?_⟩
    · intro i; by_cases h : i∈Set.range (reserve X)
      · obtain ⟨j,rfl⟩ := h; rw [(hx _).2.1]; exact F.proper j
      rw [(hy _ h).2.1]; exact Finset.singleton_nonempty _
    · intro i j; by_cases h : i∈Set.range (reserve X)
      · obtain ⟨s,rfl⟩ := h; rw [(hx _).2.1,(hx _).2.2]; exact F.pin _ _
      rw [(hy _ h).2.2]; simp
    · intro i; by_cases h : i∈Set.range (reserve X)
      · obtain ⟨s,rfl⟩ := h; rw [(hx _).1]; exact F.borel _
      rw [(hy _ h).1]; exact measurable_const
    · intro i; by_cases h : i∈Set.range (reserve X)
      · obtain ⟨s,rfl⟩ := h; rw [(hx _).1,(hx _).2.2]; exact F.footprint _
      rw [(hy _ h).1]; exact fun _ _ _=>rfl
    · intro i; by_cases h : i∈Set.range (reserve X)
      · obtain ⟨s,rfl⟩ := h; rw [(hx _).1]; exact F.gauge _
      rw [(hy _ h).1]; exact fun _ _ => rfl
    · intro i j; by_cases h : j∈Set.range (invite R)
      · obtain ⟨s,rfl⟩ := h; rw [hv,ht]; intro a
        obtain ⟨U,hU⟩ := Function.ne_iff.mp a; exact (L.locality i).carry U _ hU
      rw [hu _ _ h]; simp
    · intro i j; by_cases h : j∈Set.range (invite R)
      · obtain ⟨s,rfl⟩ := h; rw [hv]; exact fun U W H E => congr_arg (fun P : Poly R => P.part _) ((L.locality i).reads U W H E)
      rw [hu _ _ h]; exact fun _ _ _ _=>rfl
    · intro i j; by_cases h : j∈Set.range (invite R)
      · obtain ⟨s,rfl⟩ := h; rw [hv]; intro U H; exact L.keeps i U fun w => H (congr_arg (fun p : Poly R => p.part _) w)
      rw [hu _ _ h]; simp
    · intro i j; by_cases h : j∈Set.range (invite R)
      · obtain ⟨s,rfl⟩ := h; rw [hv]; exact (Poly.part_cont _).measurable.comp (L.locality i).borel
      rw [hu _ _ h]; exact measurable_const
    · intro i j; by_cases h : j∈Set.range (invite R)
      · obtain ⟨s,rfl⟩ := h; rw [hv]; exact fun t U => congr_arg (fun p : Poly R => p.part _) ((L.locality i).gauge t U)
      rw [hu _ _ h]; exact fun _ _ => rfl
    · rw [show Q.units i=0 from rfl,norm_zero,mul_zero]
    · obtain ⟨t,h,hM⟩ := rooted_reg L F he; refine ⟨t,h,fun i => weaken (hM i) ?_ ?_⟩
      · intro j; split; exact mul_nonneg (Poly.worth hw _).le (h j).1; exact le_rfl
      intro j; change (if i∈(Q.rays j).val then _ else _) ≤ (if i∈(Q.rays j).val then _ else _); split
      · apply le_mul_of_one_le_right (mul_nonneg (Poly.worth hw _).le (h j).1) (Real.one_le_exp (mul_nonneg ha (Nat.cast_nonneg _)))
      exact le_rfl
    obtain ⟨t,h,hM⟩ := forced L F hw hf H; refine ⟨t,h,fun i => weaken (hM i) ?_ ?_⟩
    · rintro ⟨j,k⟩; split; exact mul_nonneg (Poly.worth hw _).le (h j k).1; exact le_rfl
    rintro ⟨j,k⟩; change (if i∈ (Q.marks j k).val then _ else _) ≤ (if i∈ (Q.marks j k).val then _ else _); split
    · exact le_mul_of_one_le_right (mul_nonneg (Poly.worth hw _).le (h j k).1) (Real.one_le_exp (mul_nonneg ha (Nat.cast_nonneg _)))
    exact le_rfl
  exact ⟨hm,rooted_reg L F he,forced L F hw hf H⟩
end YM.Push.Corrected.Prepare
