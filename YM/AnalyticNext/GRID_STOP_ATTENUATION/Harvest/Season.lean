import YM.AnalyticNext.GRID_STOP_ATTENUATION.Alphabet.Accounts
import YM.AnalyticNext.GRID_STOP_ATTENUATION.Harvest.Fuse
import YM.Bid.Craft

set_option warningAsError false

/-! # Full support and retained predicates after E detachment

Legible all parts & their origin tests at true new addresses.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.GridStop.Harvest
open Filter Function MeasureTheory RG Marker Wilson Lattice Multi Multi.Couples Finset
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {I W : Type} [Fintype I] [DecidableEq I] [DecidableEq W] [Fintype W] {R : Census W}
variable {G : Gauge} {n : Side} {P : Rep G n} {s t : Support n}
set_option maxHeartbeats 1000000

/-- Monad-lite. Track all underlying input anchors already, can't
infer by prices. -/
structure Season (P : BudgetPoint) (X : W→Support n) (T : Support n) (A : Config G n → Poly R) : Prop where
  borel q : Measurable fun V => (A V).part q
  gauge q : GaugeInvariant fun V => (A V).part q
  reads q : UsesFinal P.threshold T fun V => (A V).part q
  tags q : (fun V => (A V).part q) ≠ 0 → ∀ i∈q.val,X i ⊆ T

variable {X : W→Support n} {A B : Config G n → Poly R}

namespace Season
omit [Fintype W] in
lemma blank (u : ℂ) : Season P.p X s (fun _ => Poly.bead R u : Config G n → Poly R) := by
  constructor
  · exact fun q => measurable_const
  · exact fun q _ _ => rfl
  · exact fun q _ _ _ _ => rfl
  intro q h
  by_cases he : q=R.quiet
  · intro i hi; subst q; exact False.elim (notMem_empty _ hi)
  exact False.elim (h (by ext1 v; simp only [Poly.bead,RingHom.coe_mk,MonoidHom.coe_mk,OneHom.coe_mk,
    Poly.part_send, he,↓reduceIte, Pi.zero_apply]))

omit [Fintype W] in
lemma empty : Season P.p X s (fun _ => (0:Poly R) : Config G n → Poly R) := by simpa using blank (R:=R) (G:=G) (X:=X) (s:=s) (P:=P) 0
omit [Fintype W] in
lemma unit : Season P.p X s (fun _ => (1:Poly R) : Config G n → Poly R) := by simpa using blank (R:=R) (G:=G) (X:=X) (s:=s) (P:=P) 1

omit [Fintype W] in
lemma sum {I : Type*} (V : Finset I) (f : I → Config G n → Poly R) (h : ∀ i∈V, Season P.p X s (f i)) :
    Season P.p X s (fun U => ∑ i∈ V,f i U) := by
  constructor
  · intro i
    simp_rw [Poly.part_sum]
    exact Finset.measurable_fun_sum _ (fun j hj => (h j hj).borel i)
  · intro i t U; simp_rw [Poly.part_sum]
    exact sum_congr rfl fun j hj => (h j hj).gauge i t U
  · intro i U W hh he; simp_rw [Poly.part_sum]
    exact sum_congr rfl fun j hj => (h j hj).reads i U W hh he
  intro q hA i hi; contrapose! hA
  ext1 U; rw [Poly.part_sum]
  exact sum_eq_zero (fun j hj => not_not.mp fun he : (f j U).part q ≠ 0 => hA ((h j hj).tags q (fun H => he (congr_fun H U)) i hi))

omit [Fintype W] in
lemma shield {h : Set (Config G n)} (H : MeasurableSet h) (hh : ∀ t U, Lattice.gauge t U∈h ↔ U∈h)
    (hv : ∀ U V, s∩flags P.p.threshold U=s∩flags P.p.threshold V → (U∈h ↔ V∈h)) (ha : Season P.p X s A) :
    Season P.p X s (fun U => if U∈h then A U else 0) := by
  let f U := if U∈h then A U else 0
  have he U q : (f U).part q = if U∈h then (A U).part q else 0 := by unfold f; split <;> rfl
  change Season _ _ _ f
  constructor
  · intro i; simp_rw [he]; exact (ha.borel i).ite H measurable_const
  · intro i t U; dsimp only; simp_rw [he, hh t U, show (A (Lattice.gauge t U)).part i = _ from ha.gauge i t U]
  · intro i U V ht hx; dsimp only; simp_rw [he, hv U V hx, show (A U).part i=(A V).part i from ha.reads i U V ht hx]
  intro i h
  exact ha.tags i (fun H => h (by ext1 U; rw [he]; split <;> first| exact congr_fun H U| rfl))

omit [Fintype W] in
lemma product (h : Season P.p X s A) (hh : Season P.p X t B) : Season P.p X (s∪t) (A*B) := by
  let g (i x y) (U : Config G n) := if Poly.merges x y i then (A U).part x*(B U).part y else 0
  have hf (i x y) : Measurable (g i x y) ∧ GaugeInvariant (g i x y) ∧ UsesFinal P.p.threshold (s∪t) (g i x y) ∧
      (g i x y ≠ 0 → ∀ v∈(i : R.Mode).val,X v⊆ s∪t) := by
    unfold g; by_cases he : Poly.merges x y i
    · simp_rw [if_pos he]
      refine ⟨(h.borel x).mul (hh.borel y),fun t U => congr_arg₂ (·*·) (h.gauge _ _ _) (hh.gauge _ _ _),fun U V ha hl => ?_,fun H v hv => ?_⟩
      · exact congr_arg₂ (·*·) (Alphabet.final_parent _ (Finset.subset_union_left) _ (h.reads x) U V ha hl)
          (Alphabet.final_parent _ (Finset.subset_union_right) _ (hh.reads y) U V ha hl)
      · rw [← he.2] at hv
        rcases mem_union.mp hv with hv|hv
        · exact Finset.Subset.trans (h.tags x (fun e => H (by funext U; rw [show (A U).part x=0 from congr_fun e U,zero_mul]; rfl)) _ hv) subset_union_left
        exact Finset.Subset.trans (hh.tags y (fun e => H (by funext U; rw [show (B U).part y=0 from congr_fun e U,mul_zero]; rfl)) _ hv) subset_union_right
    simp_rw [if_neg he]
    exact ⟨measurable_const,fun _ _ => rfl,fun _ _ _ _ => rfl,fun h => False.elim (h rfl)⟩
  have hg i U : ((A*B) U).part i = ∑ x, ∑ y,g i x y U := Poly.part_mul ..
  constructor
  · intro i; simp_rw [hg]; exact Finset.measurable_fun_sum _ (fun p _ => Finset.measurable_fun_sum _ (fun y _ => (hf ..).1))
  · intro i j U; simp_rw [hg]; refine sum_congr rfl fun p _ => sum_congr rfl fun q _ => (hf ..).2.1 j U
  · intro i U V hv hx; simp_rw [hg]; exact sum_congr rfl fun x _ => sum_congr rfl fun y _ => (hf i x y).2.2.1 U V hv hx
  intro i H v hv; contrapose! H
  ext1 U; rw [hg]; refine Finset.sum_eq_zero (fun p _ => Finset.sum_eq_zero (fun q _ => congr_fun (g:=(0:Config G n→ℂ)) ?_ U))
  exact not_not.mp (fun e : g i p q ≠ 0 => H ((hf i p q).2.2.2 e v hv))

omit [Fintype W] in
lemma multiplies {I : Type*} [DecidableEq I] (f : I → Support n) (U : I → Config G n → Poly R) (L : Finset I) (hL : ∀ j∈L, Season P.p X (f j) (U j)) :
    Season P.p X (L.biUnion f) (fun v => ∏ i∈L,U i v) := by
  induction L using Finset.induction with
  | empty => simp only [prod_empty]; exact Season.unit
  | insert l V he ih =>
    rw [biUnion_insert]; simp_rw [prod_insert he]
    exact Season.product (hL _ (mem_insert_self ..)) (ih (fun i hi => hL _ (mem_insert_of_mem hi)))
end Season

variable (R P) (D : Hot R → Pulse G n) (Y : I → Support n) (tag : I → W) (F : I → Config G n → ℂ) (U : Config G n) (p : Pack n)

-- Legibility needs input D & tag supports
structure School (X : W → Support n) : Prop where
  keeps i : Weight P.p (Y i) (F i)
  based i : X (tag i) ⊆ Y i
  art x q : Legible P.p q ((D x).2 q)
  state x q : (D x).2 q ≠ 0 → ∀ v∈x.sites,X v ⊆ q.zone

variable {R P D Y tag F}
namespace School
variable (h : School R P D Y tag F X) {κ δ : ℝ}
include h

omit [Fintype I] [DecidableEq I] [Fintype W] in
lemma paints (he : P.activities.Valid P.p δ κ) (i : Atom n I) : Season P.p X (span Y i) (fun U => palette R P D tag F U i) := by
  cases i with
  | inl i =>
    let f U := Alphabet.share P D U i
    have heQ q : Measurable (fun U => (f U).part q) ∧ GaugeInvariant (fun U => (f U).part q) ∧ UsesFinal P.p.threshold i.zone (fun U => (f U).part q) ∧
        ((fun U => (f U).part q)≠0 → ∀ v∈q.val,X v ⊆ i.zone) := by
      by_cases hF : q.val.Nonempty
      · let x : Hot R := ⟨q,hF⟩
        have hf U : (f U).part q=(D x).2 i U := Alphabet.share_at P D U i x
        simp_rw [hf]; obtain ⟨hk,hh,hr,hs⟩ := h.art x i
        exact ⟨hk,hh,hr,h.state x i⟩
      rw [show q=R.quiet from Subtype.ext (Finset.not_nonempty_iff_eq_empty.mp hF)]; simp_rw [f,Alphabet.share_quiet]
      obtain ⟨ha,hb,hc,hG⟩ := incumbent_legible P i he.forced
      exact ⟨ha,hb,hc,fun _ _ hi => False.elim (notMem_empty _ hi)⟩
    exact ⟨fun q => (heQ q).1,fun q => (heQ q).2.1,fun q => (heQ q).2.2.1,fun q => (heQ q).2.2.2⟩
  | inr i =>
    let f U := pigment R tag F U i
    have heQ q : Measurable (fun U => (f U).part q) ∧ GaugeInvariant (fun U => (f U).part q) ∧ UsesFinal P.p.threshold (Y i) (fun U => (f U).part q) ∧
        ((fun U => (f U).part q) ≠0 → ∀ v∈q.val,X v ⊆ Y i) := by
      unfold f pigment; simp_rw [Poly.part_send]
      by_cases ha : q=R.fire (tag i)
      · subst q; simp only [if_true]
        exact ⟨(h.keeps i).meas,(h.keeps i).gauge,(h.keeps i).reads,fun _ v hv => (mem_singleton.mp hv).symm ▸ h.based i⟩
      simp_rw [if_neg ha]; exact ⟨measurable_const,fun _ _ => rfl,fun _ _ _ _ => rfl,fun e => False.elim (e rfl)⟩
    exact ⟨fun q => (heQ q).1,fun q => (heQ q).2.1,fun q => (heQ q).2.2.1,fun q => (heQ q).2.2.2⟩

omit [Fintype W] [DecidableEq I] in
lemma legislates (he : P.activities.Valid P.p δ κ) (x : Hot R) : Legible P.p p ((new R P D Y tag F x).2 p) ∧
    ((new R P D Y tag F x).2 p ≠ 0 → ∀ v∈x.sites,X v ⊆ p.zone) := by
  let Z := trays Y p
  let A (U : Config G n) := flags P.p.threshold U
  let L (j : Recipe n I) U := earning Y (A U) (palette R P D tag F U) j
  let V (j : Recipe n I) (U : Config G n) := ∏ i∈j,palette R P D tag F U i
  have hT j (hj : j∈Z) : L j = fun U => if p.zone ∩ A U=p.flagsAt then V j U else 0 := by
    unfold L V earning
    obtain ⟨hq,hq'⟩ := mem_filter.mp hj; rw [← merged_zone Y hq,←merged_tags Y hq,hq']
  have hu : Season P.p X p.zone (fun U => fusion R P D Y tag F U p) := by
    unfold fusion till; refine Season.sum (P:=P) (R:=R) _ (fun j U => earning Y (flags P.p.threshold U) (palette R P D tag F U) j) (fun j hj => ?_)
    obtain ⟨hv,hr⟩ := mem_filter.mp hj
    have hv' := Season.multiplies (P:=P) (X:=X) (span Y) (fun i U => palette R P D tag F U i) j (fun i _ => h.paints he i)
    change Season _ _ (ground Y j) _ at hv'
    rw [← merged_zone Y hv,hr] at hv'
    convert (Season.shield (P:=P) (s:=p.zone) (h:={U| p.zone∩ A U=p.flagsAt}) (Pack.neighborhood_meas _ _) (by intro t u; change (_ ∩ flags _ _=_ ↔ _ ∩ flags _ _=_); rw [gauge_flags])
      (fun U V hi => show p.zone∩A U=p.flagsAt ↔ p.zone∩A V=p.flagsAt from by unfold A; rw [hi]) hv') using 1
    ext1 i; unfold earning; rw [← merged_zone Y hv,hr,←merged_tags Y hv,hr]; unfold A; by_cases he : p.zone ∩ flags P.p.threshold i=p.flagsAt <;> simp [he]
  refine ⟨⟨hu.borel _,hu.gauge _,hu.reads _,fun U hi => ?_⟩,hu.tags _⟩
  by_contra hh; apply hi
  unfold new fusion till; dsimp only; rw [Poly.part_sum]; apply sum_eq_zero; intro j hj; unfold earning; obtain ⟨hs,hj⟩ := mem_filter.mp hj; rw [← merged_zone Y hs, ← merged_tags Y hs,hj]; rw [if_neg hh]; rfl
end School
end YM.AnalyticNext.GridStop.Harvest
