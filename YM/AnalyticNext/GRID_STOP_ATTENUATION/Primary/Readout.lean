import YM.AnalyticNext.GRID_STOP_ATTENUATION.Alphabet.Accounts
import YM.AnalyticNext.GRID_STOP_ATTENUATION.Pair
import YM.Next.FOUNDATIONS.Split
import YM.Next.FOUNDATIONS.TestBounds
import YM.Push.RELAY_DIFFERENCE.Attaching
import YM.Push.RELAY_DIFFERENCE.RawTop
import YM.Push.RELAY_DIFFERENCE.TwoSided


set_option warningAsError false

/-!
# One local canonical extraction from a raw singleton bulk term

Before summing the terms of a complete signed response.  in
B70 conventions. Need actually implement also the wrapping rule, the
indicator shift (and the UNIT indicator correction!), use full Pack lane
& exact masks. Pre-charged projection norms (with B70's chosen stage
threshold and order, no inverse-coupling losses even to reconstruct the
section payments from coordinates *on their good domain only*).
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.GridStop.Primary
open Function Filter MeasureTheory RG Wilson Lattice Marker Overlay Source Bid Labels Multi Finset
open Multi.Couples
open Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G : Gauge} (C : Family G) (m p d : ℕ)


abbrev SiteSpace (C : Family G) (m p) := Site (C.side m p)

def patron (C : Family G) (d : ℕ) := (price_of_readout C.params (C.labels.level d)).choose
lemma patron_support (C : Family G) (d : ℕ) : 1 ≤ patron C d := (price_of_readout C.params (C.labels.level d)).choose_spec.1
lemma patron_uses (C : Family G) (d : ℕ) {n : Side} (o : Site n) (X : Support n) (B : BudgetPoint)
    (F : Config G n → ℂ) (c : ℝ) (he : d ≤ B.order) (hr : d ≤ B.power) (hF : B.Regular X F) (hc : B.supBounds o X F c)
    (q : Label G d) (hQ : Reads C.params o X q F) :
    (C.labels.level d).coeffSize ((C.labels.level d).scaled B.threshold ((C.labels.level d).coords q)) ≤ patron C d*c :=
  (price_of_readout C.params _).choose_spec.2 n o X B F c he hr hF hc q hQ

variable {m p d}

def unionMap (o : SiteSpace C m p) (d : ℕ) (V : Support (C.side m p)) := V ∪ (C.localSection d).footprint o
def exhibit (o : SiteSpace C m p) (v : C.label d) :=
  (C.localSection d).places ((C.labels.level d).scaled (C.path.levels.budget m).threshold⁻¹ v) o
def marked (o : SiteSpace C m p) (v : C.label d) := exhibit C o ((C.labels.level d).core v)
def artifact (o : SiteSpace C m p) (H : Config G (C.side m p)→ℂ) (v : C.label d) := H-exhibit C o v

/-- Difference of raw placement and canonical extraction. Not H-G
through *one* mask: use the UNION on v's residual, Q support for its
own field, old support for H, and global unit. -/
def gap (o : SiteSpace C m p) (V : Support (C.side m p)) (H : Config G (C.side m p)→ℂ) (v : C.label d) :=
    let t := (C.path.levels.budget m).threshold
    masked t V H - (masked t (unionMap C o d V) (artifact C o H v) +
      masked t ((C.localSection d).footprint o) (marked C o v) + (fun _ => v 0))

-- Credential at this station.
def wage (C : Family G) (d m : ℕ) := 1+(C.path.levels.params m).columns*patron C d
lemma wage_one (C : Family G) (d m : ℕ) : 1 ≤ wage C d m := le_add_of_nonneg_right (mul_nonneg
  (le_trans zero_le_one (C.path.levels.params _).columns_ge) (zero_le_one.trans (patron_support ..)))

lemma unit_placed (h : C.Makes) (o : SiteSpace C m p) (v : C.label d) :
    exhibit C o v = fun U => marked C o v U + v 0 := by
  let F := C.labels.level d
  let T := C.localSection d
  have hf : v=v 0 • F.e0+F.core v := by
    ext1 i; by_cases e : i=0 <;> simp [Frame.e0,Frame.core,e]
  unfold marked exhibit
  conv_lhs => rw [hf,map_add,map_smul,F.scaled_unit]
  unfold SectionData.places; change (fun _ => (T.evaluate _ _)) = _; simp_rw [T.eval_linear.map_add,T.eval_linear.map_smul,show T.evaluate F.e0=1 from (h.sections d).unit]
  funext i; simp [add_comm]; rfl

private lemma mask_uses {n : Side} (Y : Support n) (P : BudgetPoint) (F : Config G n→ℂ) (hF : P.Regular Y F) :
    UsesFinal P.threshold Y (masked P.threshold Y F) := by
  intro U V hh hf
  have h : Healthy P.threshold Y U ↔ Healthy P.threshold Y V := by unfold Healthy; rw [Finset.disjoint_iff_inter_eq_empty,
    Finset.disjoint_iff_inter_eq_empty,hf]
  unfold masked
  by_cases he : Healthy P.threshold Y U
  · rw [Set.indicator_of_mem (by exact he),Set.indicator_of_mem (by exact h.mp he),hF.sites U V hh]
  rw [Set.indicator_of_notMem (by exact he),Set.indicator_of_notMem (by exact mt h.mpr he)]

private lemma mask_gauge {n : Side} (Y : Support n) (P : BudgetPoint) (F : Config G n→ℂ) (hF : P.Regular Y F) :
    GaugeInvariant (masked P.threshold Y F) := by
  intro t U; have h : Healthy P.threshold Y (gauge t U) ↔ Healthy P.threshold Y U := by unfold Healthy; rw [gauge_flags]
  by_cases he : Healthy P.threshold Y U
  · rw [masked_eq _ _ _ _ he,masked_eq _ _ _ _ (h.mpr he),hF.symmetry t U]
  rw [masked_ne _ _ _ _ he,masked_ne _ _ _ _ (mt h.mp he)]

lemma price_through {n : Side} (Y : Support n) (P : BudgetPoint) (F : Config G n→ℂ) (o : Site n) (c : ℝ) (h : P.supBounds o Y F c) :
    ∀ U,‖masked P.threshold Y F U‖ ≤ c := fun U => by
      by_cases he : Healthy P.threshold Y U
      · rw [masked_eq _ _ _ _ he]; exact h.2 U he [] (by simp) (by simp)
      rw [masked_ne _ _ _ _ he,norm_zero]; exact h.1

/-- Extracted currency and *alignment* for one raw term, using E indicator
relations on the actual stencil. Does not ask for a smooth extension of H
on a different domain; even the price at each U uses only the cap *at the
same placement* of the raw H. Pick a fixed frame & calibrated sections from
`C.Makes`. -/
theorem piece (h : C.Makes) {d : ℕ} (hr : C.ref d ≤ m) (o : SiteSpace C m p) (V : Support (C.side m p))
    {F : Config G (C.side m p)→ℂ} {c : ℝ} (hF : (C.path.levels.budget m).Regular V F)
    (hC : (C.path.levels.budget m).supBounds o V F c) :
    ∃ v : C.label d, (C.labels.level d).coeffSize v ≤ patron C d*c ∧
    let _S := C.localSection d; let P := C.path.levels.budget m
    let B := artifact C o F v; let D := gap C o V F v
    Reads C.params o V ((C.labels.level d).coords.symm ((C.labels.level d).scaled P.threshold⁻¹ v)) F ∧
      P.Regular (unionMap C o d V) B ∧ B 1=0 ∧
      (Nonwrapping (unionMap C o d V) o → C.params.PiVanish d o B) ∧
      P.supBounds o (unionMap C o d V) B (wage C d m * c) ∧
      Weight P (unionMap C o d V) D ∧ ∀ U, ‖D U‖ ≤ 4*wage C d m*c := by
  let T := C.labels.level d
  let S := C.localSection d
  let P := C.path.levels.budget m
  have hH : d ≤ P.power := (h.stages d).2 m hr |>.2
  have he : d ≤ P.order := le_trans (Nat.le_succ d) ((h.stages d).2 m hr |>.1)
  obtain ⟨q,Hf,_⟩ := exists_read C.params d o P he hF
  let v0 := T.coords q
  let v := T.scaled P.threshold v0
  have hP : T.coeffSize v ≤ patron C d*c := patron_uses C d o V P F c he hH hF hC q Hf
  have ht : T.scaled P.threshold⁻¹ v=v0 := by unfold v; convert! T.scaled_inv (inv_ne_zero P.threshold_pos.ne') v0 using 1; rw [inv_inv]
  have ht' : T.coords.symm (T.scaled P.threshold⁻¹ v)=q := (congr_arg _ ht).trans (T.coords.symm_apply_apply _)
  let B := artifact C o F v; let X := S.footprint o; let D := unionMap C o d V
  obtain ⟨hx,hx'⟩ := Push.RelayDifference.section_bounds C d m p h hr o v -- ‹ℕ› may be m
  obtain ⟨hy,hy'⟩ := Push.RelayDifference.section_bounds C d _ _ h hr o (T.core v)
  let a := exhibit C o v
  change P.Regular X a at hx
  change P.Regular X (marked C o v) at hy
  have hV := regular_larger hF (Finset.subset_union_left (s₂:=X))
  have ha := regular_larger hx (Finset.subset_union_right (s₁:=V))
  let w := (C.path.levels.params m).columns
  let e := wage C d m
  have hw (j) := (C.path.levels.params j).columns_ge
  have hc : w*T.coeffSize v ≤ (w*patron C d)*c :=
    (mul_le_mul_of_nonneg_left hP (show 0≤w from zero_le_one.trans (hw _))).trans_eq (mul_assoc ..).symm
  have hQ : c+w*T.coeffSize v ≤ e*c := by unfold e wage; apply (add_le_add_right hc c).trans_eq; ring
  have hp : P.Regular D B := regular_sub hV ha
  have hp' : P.supBounds o D B (e*c) := by
    obtain ⟨hm,hM⟩ := bound_sub hV ha (bound_larger hC (Finset.subset_union_left)) (bound_larger hx' (Finset.subset_union_right))
    exact ⟨hm.trans hQ,fun j hi a ha hA => (hM j hi a ha hA).trans hQ⟩
  have hh := h.places d m p hr
  have hX : Nonwrapping X o := nonwrapping_placement S o hh
  have hl := placed_reads S o hh (h.sections _) v0
  rw [show T.coords.symm v0=q from T.coords.symm_apply_apply q] at hl
  have hF0 : Reads C.params o D q F := by
    unfold Reads at Hf ⊢; split
    next hD => rwa [if_pos (show Nonwrapping V o from fun x hx => hD _ (mem_union_left _ hx))] at Hf
    next hD => rwa [if_neg (show ¬ Nonwrapping V o from fun ht => hD fun x hx =>
      (mem_union.mp hx).elim (fun h => ht _ h) (fun h => hX _ h))] at Hf
  have hA : Reads C.params o D q a := by
    have hm : a=S.places v0 o := congrArg (fun v : C.label d => S.places v o) ht
    rw [hm]; unfold Reads at hF0 hl ⊢ -- not hX
    split
    next hD => rwa [if_pos hX] at hl
    next hD =>
      rw [if_neg hD] at hF0
      unfold SectionData.places v0; rw [hF0,map_smul,T.coords_unit,S.eval_linear.map_smul,(show S.evaluate T.e0=1 from (h.sections _).unit)]; simp -- scaled conjugate identity only
  have h0 := (reads_null_iff C.params d o D B).1 (show Reads C.params o D 0 (F - a) from sub_self q ▸ reads_sub hF0 hA)
  let draw := masked P.threshold V F; let res := masked P.threshold D B; let hit := masked P.threshold X (marked C o v)
  have hu : UsesFinal P.threshold D draw := Alphabet.final_parent _ Finset.subset_union_left _ (mask_uses _ _ _ hF)
  have hu' : UsesFinal P.threshold D res := mask_uses D P B hp
  have hR : UsesFinal P.threshold D hit := Alphabet.final_parent _ Finset.subset_union_right _ (mask_uses _ _ _ hy)
  refine ⟨v,hP,?_,hp,h0.1,h0.2,hp',?_,?_⟩
  · change Reads _ _ _ (T.coords.symm (T.scaled _ v)) _; rw [ht']; exact Hf
  · change Weight P D (draw - (res + hit + _))
    refine ⟨(masked_measurable _ _ _ hF.borel).sub (((masked_measurable _ _ _ hp.borel).add (masked_measurable _ _ _ hy.borel)).add measurable_const),fun i t => ?_,fun U V hh hx => ?_,fun U hU => ?_⟩
    · have hu := mask_gauge V P _ hF i t; have hu' := mask_gauge _ _ _ hp i t; have hr := mask_gauge _ _ _ hy i t
      simp only [draw,res,hit,Pi.sub_apply,Pi.add_apply, hu,hu',hr]
    · simp only [Pi.sub_apply,Pi.add_apply,hu U V hh hx,hu' U V hh hx, hR U V hh hx]
    by_cases hV : Healthy P.threshold D U
    · exfalso; apply hU; unfold draw res hit
      have hg := unit_placed C h o v
      rw [Pi.sub_apply,Pi.add_apply,Pi.add_apply,masked_eq _ _ _ _ hV,
        masked_eq _ _ _ _ (show Healthy P.threshold V U from hV.mono_left Finset.subset_union_left),
        masked_eq _ _ _ _ (show Healthy P.threshold X U from hV.mono_left Finset.subset_union_right)]
      unfold B artifact; rw [Pi.sub_apply,hg]; dsimp only; abel
    exact Finset.not_disjoint_iff.mp hV
  intro U
  have H : w*T.coeffSize v ≤ e*c := (le_add_of_nonneg_left hC.1).trans hQ
  have hi : c ≤ e*c := le_mul_of_one_le_left hC.1 (wage_one ..)
  have hh : ‖v 0‖ ≤ e*c := by
    apply (norm_le_pi_norm v _).trans ((Push.RelayDifference.norm_cost T _).trans ?_)
    exact (le_mul_of_one_le_left (Work.G08.size_nonneg ..) (hw m)).trans H
  have ha' := price_through _ P _ o _ hy'
  unfold gap; dsimp only [Pi.sub_apply,Pi.add_apply]
  have H' := (norm_add_le (res U+hit U) (v 0)).trans (add_le_add ((norm_add_le ..).trans
    (add_le_add (price_through D P B o (e*c) hp' U) (show ‖hit U‖≤e*c from (ha' U).trans ((mul_le_mul_of_nonneg_left
     (Push.RelayDifference.core_price T _) (le_trans zero_le_one (hw m))).trans H)))) hh)
  apply (norm_sub_le ..).trans ((add_le_add ((price_through V P F o c hC U).trans hi) H').trans_eq ?_)
  unfold e; ring
end YM.AnalyticNext.GridStop.Primary
