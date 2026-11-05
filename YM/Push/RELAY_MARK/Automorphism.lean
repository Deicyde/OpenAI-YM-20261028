import YM.Push.RELAY_MARK.HGroup

/-!
# From triangular jet test to actual SectionData production

Does *not* require switching to threshold-dependent sections to
make the equation space. One portfolio for T per d before any L,N,
period, t, β, derivative budget queries. Critical to deliver such
section in RAuthors, whichever planner proof is later used. -/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Mark
open Function Set MeasureTheory Labels Wilson Source Lattice
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators InnerProductSpace
variable {G : Gauge} {H : Hol G} {d : ℕ} {p : Label G d} {F : Switch G d}

def regrade (F : Switch G d) := (LinearMap.fst ℂ ..) ∘ₗ F
def reel (F : Switch G d) := (LinearMap.snd ℂ ..) ∘ₗ F

section Triangular

private lemma gradePart_above (p : Label G d) (m) (h : p.val∈above m) : gradePart m p=0 := by
  classical
  apply Subtype.ext; change piece m p.val=0
  ext i
  rw [MvPolynomial.coeff_weightedHomogeneousComponent]; split
  next he =>
    rw [MvPolynomial.coeff_zero]; by_contra hu
    have ht : stamp m < stamp (weight i) := (MvPolynomial.mem_restrictSupport_iff ℂ).mp h (MvPolynomial.mem_support_iff.mpr hu)
    rw [show weight i = m from he] at ht; exact (lt_irrefl _) ht
  simp

private lemma gradePart_before {a b : ℕ × ℕ} (p : Label G d) (h : p.val∈rise b) (he : stamp a < stamp b) :
    gradePart a p=0 := gradePart_above _ a (rise_later he h)

private lemma rise_order (p : Label G d) (b : ℕ × ℕ) (h : ∀ a∈code d, gradePart a p ≠ 0 → stamp b ≤ stamp a) : p.val∈rise b := by
  classical
  rw [← fees p, Submodule.coe_sum]; refine Submodule.sum_mem _ fun i hi=>?_
  by_cases hc : gradePart i p=0
  · simp [hc]
  exact rise_anti (h i hi hc) (rise_sector i (gradePart_mem i p))

lemma regrade_tri (h : Campaign H d F) (p : Label G d) (a) (_ha : a∈code d) (he : p.val∈rise a) :
    ((regrade F p).val-p.val)∈above a := by
  classical
  rw [← fees p, map_sum, Submodule.coe_sum,Submodule.coe_sum,← Finset.sum_sub_distrib];
  refine Submodule.sum_mem _ fun b hb=>?_
  by_cases hp : stamp b<stamp a
  · rw [gradePart_before p he hp,map_zero]; simp
  exact above_anti (le_of_not_gt hp) (h.each b hb _ (gradePart_mem ..)).takes.grow

private lemma low_part (hp : p ≠ 0) : ∃ b∈code d, p.val∈rise b ∧ gradePart b p≠0 := by
  classical
  let W : Set (ℕ ×ₗ ℕ) := {x| ∃ b∈code d,x=stamp b ∧ gradePart b p≠0}
  have ht : W.Nonempty := by
    have he : ∃ b∈code d, gradePart b p≠0 := by
      by_contra! h
      exact hp ((fees p).symm.trans (Finset.sum_eq_zero (fun i hi=> h i hi)))
    obtain ⟨b,h,hb⟩ := he; exact ⟨_,b,h,rfl,hb⟩
  obtain ⟨y,hy,hh⟩ := wellFounded_lt.has_min W ht
  obtain ⟨b,hb,rfl,hc⟩ := hy
  exact ⟨b,hb,rise_order p b (fun a ha hk => le_of_not_gt (hh _ ⟨a,ha,rfl,hk⟩)),hc⟩

private lemma fixed_first (h : Campaign H d F) (p : Label G d) (a) (_ha : a∈code d) (he : p.val∈rise a) :
    gradePart a (regrade F p) = gradePart a p := sub_eq_zero.mp (by
  rw [← map_sub]; exact gradePart_above _ a (regrade_tri h p a _ha he))

lemma regrade_inj (h : Campaign H d F) : Injective (regrade F) := LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr fun p he=>by
  by_contra hp; obtain ⟨b,hb,hc,hq⟩ := low_part hp
  rw [← fixed_first h p b hb hc,he,map_zero] at hq; exact hq rfl)

def twist (h : Campaign H d F) : Label G d ≃ₗ[ℂ] Label G d :=
    LinearEquiv.ofBijective (regrade F) ⟨regrade_inj h,(LinearMap.injective_iff_surjective).1 (regrade_inj h)⟩

lemma inverse_tier (h : Campaign H d F) (p : Label G d) (a) (he : p.val∈rise a) : ((twist h).symm p).val∈rise a := by
  let x := (twist h).symm p
  have ht : regrade F x=p := (twist h).apply_symm_apply _
  change x.val∈_
  by_cases h0 : x=0
  · simp [h0]
  obtain ⟨b,hb,hx,hj⟩ := low_part h0
  apply rise_anti ?_ hx
  apply le_of_not_gt; intro hv
  rw [← fixed_first h x b hb hx,ht] at hj
  exact hj (gradePart_before p he hv)
end Triangular

section Reel

lemma cost_reel (h : Campaign H d F) (p : Label G d) (a) (ha : p.val∈rise a) : reel F p∈powered G a.2 := by
  classical
  rw [← fees p,map_sum]; refine Submodule.sum_mem _ fun b hb=>?_
  by_cases hv : stamp b < stamp a
  · rw [gradePart_before p ha hv,map_zero]; exact Submodule.zero_mem _
  exact power_drop (stamp_monotone (le_of_not_gt hv)) (h.each b hb _ (gradePart_mem ..)).takes.cost

lemma form_reel (h : Campaign H d F) (p : Label G d) : Forms H d (reel F p) (twist h p).val := by
  rw [← fees p,map_sum,map_sum,Submodule.coe_sum]
  exact Forms.sum _ _ _ (fun b hb=> (h.each b hb _ (gradePart_mem ..)).takes.glyph)
lemma paid_reel (h : Campaign H d F) (p : Label G d) (hv : p∈Maxwell.equationIdeal G d) : Micro (reel F p) := by
  rw [← fees p,map_sum]; exact Submodule.sum_mem (micros G)
    (fun b hb=> (h.each b hb _ (gradePart_mem ..)).exacts (clip_sectors p hv b))
lemma reel_gauge (h : Campaign H d F) (p : Label G d) : GaugeInvariant (reel F p) := by
  rw [← fees p,map_sum]; intro t U
  simp only [Finset.sum_apply]; exact Finset.sum_congr rfl (fun b hb=> (h.each b hb _ (gradePart_mem ..)).takes.gauge t U)
lemma reel_real (h : Imprint H d F) (p : Label G d) : reel F (realBar p)=star (reel F p) := congr_arg Prod.snd (h.real_ p)
lemma twist_real (h : Imprint H d F) (p : Label G d) : twist h.toCampaign (realBar p)=realBar (twist h.toCampaign p) := congr_arg Prod.fst (h.real_ p)
lemma reel_orient (h : Imprint H d F) (s : Signed) (p) : reel F (theta s p)=reel F p ∘ pull s 0 := congr_arg Prod.snd (h.signed s p)
lemma twist_orient (h : Imprint H d F) (s : Signed) (p) : twist h.toCampaign (theta s p)=theta s (twist h.toCampaign p) := congr_arg Prod.fst (h.signed s p)
lemma twist_unit (h : Campaign H d F) : twist h (unit G d)=unit G d := congr_arg Prod.fst h.start
lemma reel_unit (h : Campaign H d F) : reel F (unit G d)=1 := congr_arg Prod.snd h.start
end Reel
end YM.Push.Mark
