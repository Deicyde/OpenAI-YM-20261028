import YM.AnalyticBridge.VERIFIED_RESET_STEP.Downstream
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Script
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Psalm.Breaks

/-! # One marker per exclusive trigger variant (γ & Γ same center);
order all tested positions before selection and with tag transforms where
required. Zero centers or positions repeated BY OTHER LETTERS no exception
from the physical price/telescoping rules. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Psalm
open Function Filter Set Lattice Wilson RG Tree Pressure Precision Next Next.SectorChange Wisps Bid
   Push.SectorMeasure WardBin.Lies Heir AnalyticBridge.LocalGaussian
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {A : Stores S} {k : S.Choices} {d : Desk G S}
    {I : Type} [Fintype I] {X : Support f} {Y : Support c} {n m : ℕ} {Pt : Teller G} {C : Libretto G n} {D : Record} {Bt : Baton G}
    {r θ : ℝ} {V : Config G c} {a : Museum F d.betaHat A X Y I} {p : Pitch S I}

def peels {n : ℕ} (f : Fin n → ℝ) (i : Fin n) := (∏ j : Fin n, (if j < i then f j else 1))*(1-f i)
private lemma peel_sum {n : ℕ} (f : Fin n → ℝ) : ∑ i,peels f i = 1-∏ i,f i := by
  induction n with
  | zero => simp [Finset.univ_eq_empty]
  | succ n ih =>
    simp only [Fin.sum_univ_succ,Fin.prod_univ_succ]
    have he i : peels f (Fin.succ i) = f 0 * peels (fun j => f (Fin.succ j)) i := by rw [peels,Fin.prod_univ_succ]; simp only [if_pos (show 0 < Fin.succ i by simp),Fin.succ_lt_succ_iff,mul_assoc]; rfl
    simp_rw [he]; rw [← Finset.mul_sum, ih,peels]; simp only [Fin.not_lt_zero,if_false,Finset.prod_const_one,one_mul]; ring

namespace Pitch
abbrev height (D : Record) (d : Desk G S) := cap D d / d.g / 32
def snare (D : Record) (d : Desk G S) (z : Prices G I) (i : I) := broad d.profile (height D d) (tape z i)
abbrev Ordering (p : Pitch S I) (a : Museum F d.betaHat A X Y I) (m : ℕ) := Fin m ≃ ↥(p.carriers a)

lemma Ordering.excludes (e : Ordering p a m) : m≤Fintype.card I := (Fintype.card_fin m) ▸ Fintype.card_le_of_injective _ (@Subtype.val_injective I _ |>.comp e.injective)
variable (k) (e : Ordering p a m) (j : Fin m) (D) (b : Finset ℕ) (U : Config G c → Config G f) (w : Config G c → Prices G I)

def verse (W : Config G c) := peels (snare D d (w W) ∘ Subtype.val ∘ e) j * p.continued k D a b U w W
def page (V : Config G c) (y : Ratings (k:=k)) := peels (snare D d (gaussRead k a y) ∘ Subtype.val ∘ e) j * p.actual k D a b V y

lemma peel_price (x : Prices G I) : peels (snare D d x ∘ Subtype.val ∘ e) j ∈ Icc (0:ℝ) 1 := by
  have hg (j) := broad_range d.profile (tape x (e j).val) (height D d)
  let F (i : Fin m) := if i < j then snare D d x (e i).val else 1
  have hf i : F i∈Icc (0:ℝ) 1 := by unfold F; split; exact hg i; exact ⟨zero_le_one,le_rfl⟩
  exact ⟨mul_nonneg (Finset.prod_nonneg (fun i _ => (hf i).1)) (sub_nonneg.mpr (hg j).2), mul_le_one₀
    (le_of_le_of_eq (Finset.prod_le_prod (fun i _ => (hf i).1) (fun i _ => (hf i).2)) Finset.prod_const_one) (sub_nonneg.mpr (hg j).2) (sub_le_self _ (hg j).1)⟩
private lemma beam_event (z : Prices G I) (hz : peels (snare D d z ∘ Subtype.val ∘ e) j ≠ 0) (hg : 0 < d.g) : height D d ≤ ‖tape z (e j).val‖ := by
  have ht : 1-snare D d z (e j).val ≠ 0 := right_ne_zero_of_mul hz; have hh := d.input.p.threshold_pos; have he := D.guards
  exact le_of_not_ge (fun h => ht (sub_eq_zero.mpr (broad_one _ (by unfold height cap; positivity) h).symm))
lemma page_event (hg : 0 < d.g) {y : Ratings (k:=k)} (hz : page k D e j b V y≠0) : height D d ≤ ‖tape y.2 (a.seat (e j).val)‖ := beam_event D e j (gaussRead k a y) (left_ne_zero_of_mul hz) hg
lemma germ_event (hg : 0<d.g) (hw : ContinuousAt w V) (hz : ∃ᶠ W in 𝓝 V, verse k D e j b U w W ≠ 0) : height D d ≤ ‖tape (w V) (e j).val‖ := by
  by_contra! h
  obtain ⟨W,hh,hW⟩ := (hz.and_eventually (((continuous_apply ((e j).val)).continuousAt.comp (gaugeCount.continuous.continuousAt.comp hw)).norm.eventually
    (gt_mem_nhds (show ‖gaugeCount (w V) (e j).val‖ < height D d from h)))).exists
  exact not_lt_of_ge (beam_event D e j (w W) (left_ne_zero_of_mul hh) hg) hW
lemma page_protected (hg : 0 < d.radius) {y : Ratings (k:=k)} (he : ∀ i,p≠.door i) (hz : page k D e j b V y≠0) : Protected d (p.carriers a) (actualRead k a V y) := Pitch.closure k D b a he (right_ne_zero_of_mul hz) hg


variable {D} (he : p.Eligibility a) (hs : p.Allowed d) (hT : Sounded Pt C D Bt r d)
    (hw : ContinuousAt w V) (hV : Healthy d.out.threshold Y V)
include he hs hT hV
lemma page_matches (y : Ratings (k:=k)) (hw : gaussRead k a y=w V) : page k D e j b V y = verse k D e j b U w V := by
  rw [page,holds b he hs hT hV y U w hw,hw]; rfl

include hw
omit hs in
theorem recombined : p.continued k D a b U w =ᶠ[𝓝 V] fun W => ∑ i,verse k D e i b U w W := by
  let f W := snare D d (w W) ∘ Subtype.val ∘ e
  have he' W : ∑ i, verse k D e i b U w W = (1-∏ i,f W i)*p.continued k D a b U w W := by unfold verse; rw [← Finset.sum_mul, peel_sum]
  simp_rw [he']; by_cases ht : Small D a p (w V)
  · filter_upwards [vanquished k b U w hT hw hV he ht] with W h; rw [h]; simp
  unfold Small at ht; push Not at ht; obtain ⟨i,hi,h⟩ := ht; obtain ⟨i',h'⟩ := e.surjective ⟨i,hi⟩
  have hh := (((continuous_apply i).continuousAt.comp (gaugeCount.continuous.continuousAt.comp hw)).norm.const_mul d.g).eventually (lt_mem_nhds h)
  filter_upwards [hh] with W h
  rw [Finset.prod_eq_zero (Finset.mem_univ i'),sub_zero,one_mul]; unfold f; rw [Function.comp_apply,Function.comp_apply,h']
  have ht := hT.heat; have h₁ := D.guards; have h₂ := d.input.p.threshold_pos
  by_contra! h'
  have he := broad_span _ (d:=height D d) (by unfold height cap; positivity) (tape (w W) i) h'
  have hA := mul_lt_mul_of_pos_left he ht
  rw [show d.g*(2*height D d)=cap D d/16 by field_simp; norm_num] at hA
  exact hA.not_gt (show _ < _ from h)

omit hw in
lemma recoup (y : Ratings (k:=k)) : p.actual k D a b V y = ∑ i,page k D e i b V y := by
  let U := fun _ : Config G c => (1:Config G f); let w := fun _:Config G c => gaussRead k a y
  simp_rw [page_matches k e _ b U w he hs hT hV y rfl, holds b he hs hT hV y U w rfl]
  exact (recombined k e b U w he hT continuousAt_const hV).self_of_nhds
end Pitch
end YM.PhysicalNext.JointLoad.Psalm
