import YM.ProofPorts.COMMON_COMPLEX_PRODUCTION.Pin
import YM.ProofPorts.COMMON_COMPLEX_PRODUCTION.Story

/-! # Value-independent positive-order jet inputs for exponential and velocity prices -/
set_option autoImplicit false
noncomputable section
namespace YM.ProofPorts.CommonComplexProduction
open Function Filter Finset Lattice RG Wilson Multi Multi.Vacuum Jets Puff Complex
open scoped Topology BigOperators Classical ContDiff
variable {n : Side} {G : Gauge} {k : ℕ} {D : Directions G n → Prop} {U : Config G n} {r p c c' : ℝ}
  {F H : Config G n → ℂ}

lemma band_plus (h : Band k D U r c F) (he : Band k D U r c' H) : Band k D U r (c+c') (F+H) := by
  refine ⟨Puff.into k _ (h.readable.germ.add he.readable.germ), h.sane, add_nonneg h.nonneg he.nonneg,fun l hl hL => ?_⟩
  rw [Crest.sum_at l hl U h.readable he.readable,add_mul]; exact (norm_add_le ..).trans (add_le_add (h.caps l hl hL) (he.caps l hl hL))

lemma band_constant (k : ℕ) (c : ℂ) (hr : 0≤r) : Band k D U r ‖c‖ (fun _=>c) := by
  refine ⟨into k _ contDiffAt_const,hr,norm_nonneg _,fun l hl hL => ?_⟩; rw [Work.G07.left_const]; cases l <;> simp
  positivity



lemma band_comb {I : Type} {f : I → Config G n→ℂ} {g : I→ℝ} {s : Finset I}
    (hr : 0 ≤ r) (h : ∀ i∈s, Band k D U r (g i) (f i)) : Band k D U r (∑ i∈s, g i) (∑ i∈s, f i) := by
  induction s using Finset.induction with
  | empty => rw [sum_empty,sum_empty,← (norm_zero : ‖(0:ℂ)‖=0)]; exact band_constant k _ hr
  | insert i s hi ih =>
    simp only [sum_insert hi]; exact band_plus (h i (by simp)) (ih fun j hj => h j (mem_insert_of_mem hj))

lemma crest_move (h : Crest k F U) (he : H =ᶠ[𝓝 U] F) : Crest k H U := by obtain ⟨g,hf,h⟩:=h; exact ⟨g,hf,he.trans h⟩

lemma band_move (h : Band k D U r c F) (he : H =ᶠ[𝓝 U] F) : Band k D U r c H :=
  ⟨crest_move h.readable he,h.sane,h.nonneg,fun l hl hv => Jets.agrees he l ▸ h.caps l hl hv⟩

lemma band_rise {c' r' : ℝ} (h : Band k D U r c F) (hc : c ≤ c') (hr : r ≤ r') : Band k D U r' c' F :=
  ⟨h.readable,h.sane.trans hr,h.nonneg.trans hc,fun l hl hv => (h.caps l hl hv).trans
    (mul_le_mul hc (pow_le_pow_left₀ h.sane hr _) (pow_nonneg h.sane _) (h.nonneg.trans hc))⟩

structure Slope (k : ℕ) (D : Directions G n→Prop) (U : Config G n) (r c : ℝ) (F : Config G n→ℂ) : Prop where
  read : Crest k F U
  starts : 0 ≤ r
  nonneg : 0 ≤ c
  caps l : l ≠ [] → l.length ≤ k → (∀ i ∈ l,D i) → ‖leftDerivs F l U‖ ≤ c*r^l.length



namespace Slope
lemma band (h : Slope k D U r c F) {d : ℝ} (hc : ‖F U‖≤d) (hd : c ≤ d) : Band k D U r d F := by
  refine ⟨h.read,h.starts,h.nonneg.trans hd,fun l hl hv => ?_⟩; by_cases he:l=[]
  · subst l; simpa [leftDerivs] using hc
  exact (h.caps l he hl hv).trans (mul_le_mul_of_nonneg_right hd (pow_nonneg h.starts _))
lemma shorten (h : Slope (k+1) D U r c F) : Slope k D U r c F :=
  ⟨Jets.shorten h.read,h.starts,h.nonneg,fun l he hl => h.caps l he (by omega)⟩
lemma core (h : Slope (k+1) D U r c F) {v : Directions G n} (hv : D v) : Band k D U r (c*r) (leftDerivs F [v]) := by
  refine ⟨h.read.falls _,h.starts,mul_nonneg h.nonneg h.starts,fun l hl hL => ?_⟩
  rw [← Work.G07.left_append]
  have he := h.caps (l++[v]) (by simp) (by simpa) (fun i hi => (List.mem_append.mp hi).elim (hL i) (fun h => (List.mem_singleton.mp h).symm ▸ hv))
  simp only [List.length_append,List.length_singleton,pow_succ] at he; convert he using 1; ring

lemma rise (h : Slope k D U r c F) (hr : r≤p) (hc : c≤c') : Slope k D U p c' F := by
  refine ⟨h.read,h.starts.trans hr,h.nonneg.trans hc,fun l he hl hv => (h.caps l he hl hv).trans ?_⟩
  exact mul_le_mul hc (pow_le_pow_left₀ h.starts hr _) (pow_nonneg h.starts _) (h.nonneg.trans hc)
lemma move (h : Slope k D U r c F) (he : H =ᶠ[𝓝 U] F) : Slope k D U r c H :=
  ⟨crest_move h.read he,h.starts,h.nonneg,fun l hl hv hh => Jets.agrees he l ▸ h.caps l hl hv hh⟩
lemma fixed (k : ℕ) (x : ℂ) (hr : 0≤r) : Slope k D U r 0 (fun _=> x) := by
  refine ⟨into k _ contDiffAt_const,hr,le_rfl,fun l hl _ _ => ?_⟩; simp only [Work.G07.left_const, if_neg hl,norm_zero,zero_mul,le_rfl]
lemma plus (h : Slope k D U r c F) (he : Slope k D U r c' H) : Slope k D U r (c+c') (F+H) := by
  refine ⟨into k _ (h.read.germ.add he.read.germ),h.starts,add_nonneg h.nonneg he.nonneg,fun l he' hl hv => ?_⟩
  rw [Crest.sum_at l hl U h.read he.read, add_mul]
  exact (norm_add_le ..).trans (add_le_add (h.caps l he' hl hv) (he.caps l he' hl hv))
lemma scale (h : Slope k D U r c F) (x : ℂ) : Slope k D U r (‖x‖*c) (x • F) := by
  refine ⟨into k _ (h.read.germ.const_smul x),h.starts,mul_nonneg (norm_nonneg _) h.nonneg,fun l he hl hv => ?_⟩
  rw [scaled_left,norm_mul,mul_assoc]; exact mul_le_mul_of_nonneg_left (h.caps l he hl hv) (norm_nonneg _)
lemma minus (h : Slope k D U r c F) (he : Slope k D U r c' H) : Slope k D U r (c+c') (F-H) := by
  simpa only [norm_neg,norm_one,one_mul,neg_one_smul, sub_eq_add_neg] using h.plus (he.scale (-1))

lemma scheduled {I : Type} (f : I → Config G n→ℂ) {g : I→ℝ} {s : Finset I}
    (hr : 0 ≤ r) (h : ∀ i∈s, Slope k D U r (g i) (f i)) : Slope k D U r (∑ i∈s, g i) (∑ i∈s, f i) := by
  induction s using Finset.induction with
  | empty => rw [sum_empty,sum_empty]; exact fixed k _ hr
  | insert i s hi ih => simp only [sum_insert hi]; exact (h i (by simp)).plus (ih fun j hj => h j (mem_insert_of_mem hj))

lemma from_core (hr : 0≤r) (hc : 0≤c) (h : Crest k F U)
    (he : ∀ i : ℕ,k=i+1 → ∀ v,D v → Band i D U r (c*r) (leftDerivs F [v])) : Slope k D U r c F := by
  refine ⟨h,hr,hc,fun l hl hh hv => ?_⟩
  induction l using List.reverseRecOn with
  | nil => exact False.elim (hl rfl)
  | append_singleton l A _ =>
    have hK : 0<k := by simp only [List.length_append,List.length_singleton] at hh; omega
    rw [Work.G07.left_append,List.length_append,List.length_singleton]
    apply ((he (k-1) (by omega) A (hv _ (by simp))).caps l (by simp only [List.length_append,List.length_singleton] at hh; omega)
      (fun i hi => hv i (List.mem_append_left _ hi))).trans_eq
    ring

private def ef (F : Config G n → ℂ) := fun x => Complex.exp (F x)
private lemma smooth (h : Slope k D U r c F) : Crest k (ef F) U := into k _ h.read.germ.cexp
private lemma hop (h : Crest (k+1) F U) (A : Directions G n) : leftDerivs (ef F) [A] U = ef F U * leftDerivs F [A] U := by
  have he := ((h.line [] (by simp) A).hasDerivAt.cexp).deriv; rw [zero_smul,inc_zero] at he; exact he

/-- Score relative to the exponentiated value, at cost polynomial in all
size arguments when log COSTS AT POSITIVE ORDERS are. No cost exponential
in the size even when `c` grows. Through requested order total (not k+1). -/
lemma exp_band (h : Slope k D U r c F) : Band k D U (k*(1+c)*r) ‖Complex.exp (F U)‖ (fun x => Complex.exp (F x)) := by
  induction k with
  | zero => exact ⟨smooth h,by rw [Nat.cast_zero,zero_mul,zero_mul],norm_nonneg _,fun l hl _ => by
                    have he:l=[]:=List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)
                    subst l; simp [leftDerivs]⟩
  | succ k ih =>
    have hc:=h.nonneg; have hr:=h.starts
    let t : ℝ := (k+1)*(1+c)*r
    suffices Slope (k+1) D U t ‖ef F U‖ (ef F) by push_cast; exact this.band le_rfl le_rfl
    have hg (A) (hv:D A) := (ih h.shorten).multiply (h.core hv)
    refine from_core (by unfold t; positivity) (norm_nonneg _) (smooth h) ?_
    rintro i hi A hv; have hi:i=k:=by omega
    subst i
    refine band_rise (band_move (hg A hv) (h.read.near.mono fun V hV => hop hV A)) (by unfold t ef; gcongr; nlinarith) ?_
    unfold t; nlinarith
end Slope
end YM.ProofPorts.CommonComplexProduction
