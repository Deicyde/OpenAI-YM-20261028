import YM.Next.EXTRACTION.Base
import YM.Push.RELAY_DIFFERENCE.Attaching
import YM.Push.RELAY_DIFFERENCE.Matching

/-!
# Quantitative one-body attachment cost

WE15668. Charge local bad stencils (UsesFinal, anchor a
literal physical copy). A proposed initialization paying only J init with
no cost of actual signed differences would not yield the Solo inputs. Use
per-hit bounds of the actual vacuum rep and K weight after gathering. Need
Slots purchased at these steps already (cf docs/Budget, addresses reserve).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.RelayDifference.Attach
open Function Set Filter MeasureTheory Lattice RG Wilson Source
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {n : Side} {X : Support n} {R : Rep G n}
local notation "Family'" => Finset ℕ

lemma cap_agree {t : ℝ} {X Y : Support n} {U V : Config G n} (hs : Y ⊆ X) (h : X∩flags t U=X∩flags t V) :
    Y∩flags t U=Y∩flags t V := by
  ext i
  simp only [Finset.mem_inter]
  by_cases hi:i∈Y
  · have hh : i∈flags t U ↔ i∈flags t V := by
      have hv (A : Config G n) : i∈X∩flags t A ↔ i∈flags t A := by simp [hs hi]
      rw [←hv,←hv,h]
    rw [hh]
  simp only [hi, false_and]

lemma uses_larger {F : Config G n → ℂ} {Y : Support n} {t : ℝ} (h : UsesFinal t X F) (hh : X ⊆ Y) :
    UsesFinal t Y F := fun U V hc ht => h U V (agrees_mono hc (Finset.coe_subset.mpr hh)) (cap_agree hh ht)

namespace Slots
variable (s : Slots X R)

private lemma eligible_measible (p : Catch X R) : MeasurableSet
    {U : Config G n | (R.activities.forced (s.code p)).eligible R.p.threshold U} := by
  classical
  let k := R.activities.forced (s.code p)
  have ht (j : Site n) : MeasurableSet {U : Config G n | (j∈ k.support∩flags R.p.threshold U)=(j∈k.inventory)} := by
    have he : Measurable fun U : Config G n => j ∈ flags R.p.threshold U := measurableSet_setOf.mp (flags_open ..).measurableSet
    by_cases hh:j∈k.support <;> by_cases hi:j∈k.inventory <;>
      simp only [Finset.mem_inter,hh,hi,true_and, false_and]
    all_goals simp [he,he.not]
  convert MeasurableSet.iInter ht
  ext U
  simp only [mem_iInter,mem_setOf_eq,ForcedAddress.eligible,s.allowed,and_true]
  exact ⟨fun h j => by rw [←show _=_ from h], fun h => Finset.ext fun x => by rw [h x]⟩

/-- The actual `s.out` obeys Format restrictions on the marker entries
(vacuum addresses and probes needed as in R.Lawful). -/
structure Proper (X : Support n) (Q : Config G n → ℂ) (t : ℝ) : Prop where
  local_ : UsesFinal t X Q
  gauge : GaugeInvariant Q
  measurable : Measurable Q

theorem precise {Q : Config G n → ℂ} (H : Proper X Q R.p.threshold)
    {κ w : ℝ} (hs : R.activities.Valid R.p κ w) (o : Site n) (hg : o∈X) (i : ℕ) :
    let p := s.out Q i
    GaugeInvariant p ∧ UsesFinal R.p.threshold (home R i) p ∧ Measurable p ∧
      (p ≠ 0 → o∈home R i) ∧ (∀ U : Config G n,p U ≠ 0 → (R.activities.forced i).eligible R.p.threshold U) := by
  classical
  by_cases hi:i∈Set.range s.code
  · obtain ⟨b,rfl⟩ := hi
    dsimp only; rw [s.restored]; unfold assigned
    let k := R.activities.forced (s.code b)
    let F := fun U : Config G n => Q U * ∏ i∈ b.val, (R.activities.K i U:ℂ)
    have hl : GaugeInvariant F := fun t U => by simp only [F,H.gauge t U,hs.forced.sym _ t U]
    have hc : UsesFinal R.p.threshold b.cloth F := by
      intro U V ha hb
      unfold F; congr 1
      · exact uses_larger H.local_ Finset.subset_union_left U V ha hb
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [hs.forced.reads _ U V (agrees_mono ha (Finset.coe_subset.mpr (b.insertLabel hj)))
        (cap_agree (b.insertLabel hj) hb)]
    change GaugeInvariant (fun U => if k.eligible R.p.threshold U then F U else 0) ∧ _
    refine ⟨?_,?_,?_,fun _ => (s.exactCover b).symm ▸ Finset.mem_union_left _ hg,?_⟩
    · intro t U
      simp only [ForcedAddress.eligible, gauge_flags, hl t U]; simp [k,s.allowed]
    · rw [s.exactCover]
      intro U V he ht; have hs : k.support ∩ flags R.p.threshold U=k.support∩flags R.p.threshold V := by
        rwa [show k.support=b.cloth from s.exactCover b]
      change (if k.eligible _ U then F U else 0)=(if k.eligible _ V then F V else 0)
      simp_rw [ForcedAddress.eligible, hs, hc U V he ht]; simp [k,s.allowed]
    · exact Measurable.ite (eligible_measible s b) (Measurable.mul H.measurable
        (Finset.measurable_fun_prod _ fun i hi => Complex.continuous_ofReal.measurable.comp (hs.forced.meas i))) measurable_const
    intro U; split; next h => exact fun _ => h
    simp
  simp only [out,dif_neg hi]; exact ⟨fun _ _ => rfl,fun _ _ _ _ => rfl,measurable_const,fun h => (h rfl).elim,fun _ h => (h rfl).elim⟩
end Slots

private lemma supercost {b : Family'} (M : ℕ) (h : ∀ i∈b,collides X R i) : coverNumber M (X∪b.biUnion (home R)) ≤
    coverNumber M X + ∑ i∈b,coverNumber M (home R i) := by
  classical
  induction b using Finset.induction_on with
  | empty => simp
  | insert a b ha ih =>
    obtain ⟨i,hi,hb⟩ := Finset.not_disjoint_iff.mp (h a (Finset.mem_insert_self ..))
    have ht := Corona.meets_sum (Finset.mem_union_left (b.biUnion (home R)) hb) hi M
    rw [Finset.biUnion_insert, show X∪(home R a∪b.biUnion (home R))=(X∪b.biUnion (home R))∪home R a by
      ext j; simp only [Finset.mem_union]; tauto, Finset.sum_insert ha]
    have he := ih (fun i hi => h _ (Finset.mem_insert_of_mem hi)); omega

def fresh (M : Family') := M.Nonempty

private lemma small_families {ι : Type*} (q : ι → ℝ) (h : ∀ i,0 ≤ q i) {b : ℝ} (hb : ∀ s : Finset ι,∑ i∈s,q i ≤ b)
    (V : Finset (Finset ι)) (hv : ∀ x∈V,x.Nonempty) :
    ∑ s∈ V, (∏ i∈s,q i) ≤ b*Real.exp b := by
  classical
  let w := V.biUnion id
  have he : (insert ∅ V) ⊆ w.powerset := by
    intro a ha
    refine Finset.mem_powerset.mpr ?_
    rcases Finset.mem_insert.mp ha with e|e
    · subst a; exact Finset.empty_subset _
    intro x hx; exact Finset.mem_biUnion.mpr ⟨_,e,hx⟩
  have hc := (Finset.sum_le_sum_of_subset_of_nonneg (f:=fun s => ∏ i∈s,q i) he
    (fun i _ _ => Finset.prod_nonneg (fun j _ => h j)))
  rw [← Finset.prod_one_add] at hc
  have hc := hc.trans ((Real.prod_one_add_le_exp_sum w h).trans (Real.exp_monotone (hb w)))
  have ha := Real.add_one_le_exp (-b)
  rw [Real.exp_neg] at ha
  have ha := mul_le_mul_of_nonneg_right ha (Real.exp_pos b).le
  rw [inv_mul_cancel₀ (Real.exp_pos b).ne'] at ha
  have hx : ∅ ∉ V := fun h => Finset.not_nonempty_empty (hv _ h)
  rw [Finset.sum_insert hx,Finset.prod_empty] at hc
  -- fill
  nlinarith

namespace Slots

variable (s : Slots X R)

/-- Quantitative K hit payment of the attached force (must still divide by
any `remBound` varkappa in use). No spare convergence assumptions. All copy
placements cost this only when using their own Slots for this same R. -/
lemma hitbill {Q : Config G n → ℂ} {p w : ℝ} (H : 0 ≤ p) (he : ∀ U, ‖Q U‖ ≤ p)
    (hw : 0 ≤ w) (hR : R.activities.KBound R.p w) :
    ∃ a : ℕ → ℝ, (∀ i,0 ≤ a i ∧ ∀ U, ‖s.out Q i U‖ ≤ a i) ∧
      SumBudget (fun i => R.p.mass (home R i) (a i)) (R.p.mass X p * (X.card*w)*Real.exp (X.card*w)) := by
  classical
  obtain ⟨b,hb,hB⟩ := hR
  let c (v : Catch X R) := p * ∏ i∈v.val,b i
  have hc (v) : 0 ≤ c v := mul_nonneg H (Finset.prod_nonneg fun i _ => (hb i).1)
  let f : ℕ → ℝ := fun i => if h : i∈Set.range s.code then c (Classical.choose h) else 0
  let g i := R.p.mass (home R i) (f i)
  let q i := if collides X R i then R.p.mass (home R i) (b i) else 0
  have hq i : 0 ≤ q i := by unfold q; split; exact mul_nonneg (Real.exp_pos _).le (hb i).1; exact le_rfl
  have ht v : f (s.code v) = c v := by
    unfold f; split; next h => rw [s.code.injective (Classical.choose_spec h)]
    next h => exact (h ⟨_,rfl⟩).elim
  have hp : ∀ i,0 ≤ f i ∧ ∀ U, ‖s.out Q i U‖ ≤ f i := by
    intro i
    by_cases hi:i∈Set.range s.code
    · obtain ⟨v,rfl⟩ := hi; rw [ht,s.restored]; refine ⟨hc v,fun U => ?_⟩; unfold assigned
      split
      · unfold c; rw [norm_mul,norm_prod]
        exact mul_le_mul (he _) (Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => by rw [Complex.norm_real]; exact (hb i).2 U))
          (Finset.prod_nonneg fun i _ => norm_nonneg _) H
      rw [norm_zero]; exact hc _
    simp only [f,out,dif_neg hi]; simp
  have hn i : 0 ≤ g i := mul_nonneg (Real.exp_pos _).le (hp i).1
  have hit (K : Family') : ∑ i∈K,q i ≤ X.card*w := by
    let e (x : Site n) (i) := if x∈home R i then R.p.mass (home R i) (b i) else 0
    calc
      _ ≤ ∑ i∈K,∑ x∈X,e x i := Finset.sum_le_sum fun i _ => by
        unfold q; split
        · rename_i hg
          obtain ⟨x,hx,hh⟩ := Finset.not_disjoint_iff.mp hg
          exact le_trans (le_of_eq (show _ = e x i from (if_pos hx).symm))
            (Finset.single_le_sum (fun j _ => (hB j).1 i) hh)
        exact Finset.sum_nonneg fun j _ => (hB j).1 i
      _ = ∑ x∈X,∑ i∈K,e x i := Finset.sum_comm ..
      _ ≤ ∑ _∈X,w := Finset.sum_le_sum fun i _ => by
        have hv : SumBudget (e i) w := hB i
        exact (hv.2.1.sum_le_tsum K (fun j _ => hv.1 j)).trans hv.2.2
      _ = _ := by simp
  have cost (v : Catch X R) : g (s.code v) ≤ R.p.mass X p * ∏ i∈v.val, q i := by
    have hv : coverNumber R.p.B v.cloth ≤ coverNumber R.p.B X + ∑ i∈v.val,coverNumber R.p.B (home R i) := supercost _ v.property.2.1
    let z := R.p.supportExponent
    have he (i) (hi : i∈v.val) : q i = R.p.mass (home R i) (b i) := if_pos (v.property.2.1 _ hi)
    rw [Finset.prod_congr rfl he]
    unfold g; rw [ht,s.exactCover]
    unfold BudgetPoint.mass; simp_rw [Finset.prod_mul_distrib,←Real.exp_sum]
    unfold c
    have hh : Real.exp (z*coverNumber R.p.B v.cloth) ≤ Real.exp (z* (coverNumber R.p.B X + (∑ i∈v.val,coverNumber R.p.B (home R i)):ℕ)) := by
      apply Real.exp_monotone; have hp : 0 ≤ z := R.p.exponent_pos.le; exact mul_le_mul_of_nonneg_left (by exact_mod_cast hv) hp
    apply (mul_le_mul_of_nonneg_right hh (hc v)).trans_eq
    push_cast; rw [mul_add,Real.exp_add, Finset.mul_sum]; unfold c z; ring
  have finish (V : Family') : ∑ i∈V,g i ≤ R.p.mass X p * (X.card*w)*Real.exp (X.card*w) := by
    let T := V.preimage s.code s.code.injective.injOn
    have hu : (∑ i∈T,g (s.code i))=∑ i∈V,g i := Finset.sum_preimage _ _ _ _
      fun i _ hi => by unfold g f; rw [dif_neg hi]; exact mul_zero _
    let W := T.image (Subtype.val)
    have ht : ∀ x∈W,x.Nonempty := fun x hx => by obtain ⟨j,-,rfl⟩ := Finset.mem_image.mp hx; exact j.property.1
    rw [←hu]; refine (Finset.sum_le_sum (fun i _ => cost i)).trans ?_
    rw [← Finset.mul_sum, mul_assoc, ← Finset.sum_image (f:=fun v => ∏ i ∈ v, q i) (g:=Subtype.val)
      Subtype.val_injective.injOn]
    exact mul_le_mul_of_nonneg_left (small_families q hq hit W ht) (mul_nonneg (Real.exp_pos _).le H)
  have hx : 0 ≤ R.p.mass X p := mul_nonneg (Real.exp_pos _).le H
  exact ⟨f,hp,hn,summable_of_sum_le hn finish,tsum_le_of_sum_le' (by positivity) finish⟩
end Slots
end YM.Push.RelayDifference.Attach
