import YM.Planned.PRIMARY_INTEGRAL_295.Oval

/-! # Real score charges and pointwise marginal comparison of jets

For every marginal sample, with no exchange yet, and a branch to
include zeros wherever true derivatives of the weight also vanish
(NO differentiating hard masks). Customer may pay less by restricting to
a common measured conditional Ω. Value-changing tag normalizations and
vacuum choices also not supplied by this analysis.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Purse
open Function Filter Set Metric Labels Tones Oval
open scoped Topology ContDiff BigOperators
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {x : E} {f q : E → F} {h : F → G} {t : ℝ} {n l m k : ℕ}

/-- Include positive orders separately and weight by moments to
be paid by Gaussian/vacuum. -/
def slip (ρ : E→ℝ) (x : E) (k : ℕ) := ∑ i∈Finset.range k, ‖iteratedFDeriv ℝ (i+1) ρ x‖

lemma slip_paid (ρ : E→ℝ) (x : E) (k : ℕ) : 0≤slip ρ x k := Finset.sum_nonneg fun _ _=> norm_nonneg _

def due (ρ : E→ℝ) (x : E) (k m : ℕ) (e : ℝ) : ℝ := (‖ρ x‖*e + slip ρ x k)*(1+e)^m
lemma tab (ρ : E→ℝ) (x : E) (k m : ℕ) (e : ℝ) (he : 0≤e) : 0≤due ρ x k m e := by unfold due; have h:= slip_paid ρ x k; positivity

section
variable {ρ : E → ℝ} {V W : E → G} {K e : ℝ}
private lemma slip_less (hr : ContDiffAt ℝ k ρ x) : Envelope x k (fun y=> ρ y-ρ x) (slip ρ x k) := by
  refine ⟨slip_paid ..,fun b hb=>?_⟩
  rcases b with _ | b
  · simpa using slip_paid ρ x k
  rw [show (fun y=>ρ y-ρ x)=ρ-(fun _=>ρ x) from rfl, iteratedFDeriv_sub_apply (hr.of_le (Nat.cast_le.mpr hb)) contDiffAt_const,
     iteratedFDeriv_const_of_ne (by simp)]
  simp only [Pi.zero_apply,sub_zero]; exact Finset.single_le_sum (fun (i:ℕ) _=>norm_nonneg (iteratedFDeriv ℝ (i+1) ρ x)) (Finset.mem_range.mpr hb)

-- real scalar ℝ throughout. Allows large constants/norms (e).
lemma local_multiply (hr : ContDiffAt ℝ k ρ x) (hw : ContDiffAt ℝ k W x) {B C : ℝ} (h : Envelope x k ρ B) (hW : Envelope x k W C) :
    Envelope x k (fun y=> ρ y • W y) (2^k * B*C) := by
  have hb:=h.1; have hc:=hW.1
  let S:= interior { z | ContDiffAt ℝ k ρ z ∧ ContDiffAt ℝ k W z }
  have hS : IsOpen S:=isOpen_interior
  have hh : x∈S := mem_interior_iff_mem_nhds.mpr ((hr.eventually (by simp)).and (hw.eventually (by simp)))
  have he : ContDiffOn ℝ k ρ S := fun x hx => (interior_subset hx).1.contDiffWithinAt
  have hg : ContDiffOn ℝ k W S := fun x hx => (interior_subset hx).2.contDiffWithinAt
  refine ⟨by positivity,fun n hn=>?_⟩
  have hy := norm_iteratedFDerivWithin_smul_le he hg hS.uniqueDiffOn hh (Nat.cast_le.mpr hn)
  simp_rw [iteratedFDerivWithin_of_isOpen _ hS hh] at hy
  apply hy.trans
  refine (Finset.sum_le_sum (fun i hi => mul_le_mul
    (mul_le_mul_of_nonneg_left (h.2 i ((Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hn)) (Nat.cast_nonneg (α:=ℝ) (n.choose i)))
    (hW.2 (n-i) ((Nat.sub_le ..).trans hn)) (by positivity) (by positivity))).trans ?_
  rw [← Finset.sum_mul,← Finset.sum_mul,← Nat.cast_sum,Nat.sum_range_choose]; push_cast; gcongr; norm_num

/-- Includes score and its mass, every order including zero. -/
theorem badge (hr : ContDiffAt ℝ k ρ x) (_hV : ContDiffAt ℝ k V x) (hW : ContDiffAt ℝ k W x) (he : 0≤e)
    (hc : 0≤K) (hB : Envelope x k W (K*(1+e)^m)) (hF : Fuzz x k W V (K*(1+e)^m*e)) (hn : n≤k) :
    ‖iteratedFDeriv ℝ n (fun y=>ρ y • W y) x - ρ x • iteratedFDeriv ℝ n V x‖ ≤
       2^k*K*due ρ x k m e := by
  let S := slip ρ x k; let A:E→ℝ := fun y=>ρ y-ρ x
  have ha : ContDiffAt ℝ k A x := hr.sub contDiffAt_const
  have hj := local_multiply ha hW (slip_less hr) hB
  have hn' : (n:WithTop ℕ∞) ≤ (k:WithTop ℕ∞) := Nat.cast_le.mpr hn
  have hz := (ha.smul hW).of_le hn'
  have he' : (fun y=>ρ y • W y)=(A • W)+(ρ x • W) := by funext y; simp [A,sub_smul]
  have hf' : ContDiffAt ℝ n (ρ x • W) x := (hW.of_le hn').const_smul _
  let Z:=‖ρ x‖
  have hh:=mul_le_mul_of_nonneg_left (hF.2 n hn) (show 0≤Z from norm_nonneg _)
  rw [he',iteratedFDeriv_add_apply hz hf',iteratedFDeriv_const_smul_apply (hW.of_le hn'),add_sub_assoc, ← smul_sub]
  apply (norm_add_le ..).trans; rw [norm_smul]; apply (add_le_add (hj.2 n hn) hh).trans
  calc
    _ = 2^k*S*(K*(1+e)^m) + 1*(Z*K*(1+e)^m*e) := by unfold S; ring
    _ ≤ 2^k*S*(K*(1+e)^m) + 2^k*(Z*K*(1+e)^m*e) := by gcongr; exact one_le_pow₀ (by norm_num)
    _ = _ := by unfold due S Z; ring

lemma nulled (hr : ContDiffAt ℝ k ρ x) (hw : ContDiffAt ℝ k W x) (h : slip ρ x k=0) (hq : ρ x=0)
    (hn : n ≤ k) : iteratedFDeriv ℝ n (fun y=>ρ y • W y) x = 0 := by
  classical
  have he:=slip_less hr; rw [h,hq,show (fun y=>ρ y-0)=ρ by simp] at he
  let C:=∑ i∈Finset.range (k+1), ‖iteratedFDeriv ℝ i W x‖
  have hc : Envelope x k W C := ⟨Finset.sum_nonneg (fun (i:ℕ) _=>norm_nonneg (iteratedFDeriv ℝ i W x)),fun b hb=> Finset.single_le_sum (fun (i:ℕ) _=>norm_nonneg (iteratedFDeriv ℝ i W x))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hb))⟩
  have hh := (local_multiply hr hw he hc).2 n hn; simpa using hh
end

/-- Can also skip an Ω-point if all corresponding weight jets really
vanish there, not relying on pointwise coefficient multiplication.
Smooth-germ conditions still necessary as phrased. -/
def Present (ρ : E→ℝ) (x : E) (k : ℕ) := ¬(ρ x=0 ∧ slip ρ x k=0)

theorem coated_badge (hQ : ContDiffAt ℝ k q x) (hf : ContDiffAt ℝ k f x) {u C e : ℝ} {ρ : E → ℝ} (hr : ContDiffAt ℝ k ρ x)
    (hu : Envelope x k q u) (hh : ContDiff ℝ ω h) {R : ℝ} (ht : t∈Ioc 0 1) (hB : Width h (k+1) l R C) (hn : n ≤ k)
    (hq : ‖t • q x‖ ≤ R) (he : 0≤e) (hg : Present ρ x k → ‖t • f x‖≤R ∧ Fuzz x k f q e) :
    let H := coat h l t
    ‖iteratedFDeriv ℝ n (fun a=> ρ a • H (f a)) x - ρ x • iteratedFDeriv ℝ n (H ∘ q) x‖ ≤
       2^k*Oval.league k l u C * due ρ x k (l+k) e := by
  intro H
  let V:=H ∘ q; let W:= H ∘ f
  have he' := coat_smooth hh l t; have hW : ContDiffAt ℝ k W x := (he'.contDiffAt.of_le le_top).comp x hf
  by_cases H' : Present ρ x k
  · obtain ⟨hv,hp⟩:= hg H'
    obtain ⟨hv',hb,hF⟩:= Oval.sticker hQ hf hp hu hh ht hB hq hv
    have hV : ContDiffAt ℝ k V x := (he'.contDiffAt.of_le le_top).comp x hQ
    exact badge hr hV hW he hv'.1 hb hF hn
  obtain ⟨hz,hg⟩:= Classical.not_not.mp H';
  rw [show (fun a=>ρ a • H (f a))=(fun a=> ρ a • W a) from rfl,nulled hr hW hg hz hn]
  simp [due,hz,hg]
end YM.Planned.PrimaryIntegral295.Purse
