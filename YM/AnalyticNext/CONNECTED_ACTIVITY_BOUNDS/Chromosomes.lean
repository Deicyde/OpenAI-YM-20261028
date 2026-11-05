import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Tablets
import YM.Push.RELAY_DIFFERENCE.TwoSided

/-!
# Within-step derivative by two actual transactions

Interpolation specialized for the true `beta` experiment, not analytic continuation of
field direction/masks. No premise of any analyticity of indicator gates. `polar`
here may see ANY sign for constant payloads. Extent estimates at radius s later with Mark.
Determining complex ledger from the *two real scenes* also for Borel with hard gates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Plotter
open Filter MeasureTheory Complex
open scoped Topology BigOperators Classical

def pit : ℝ := -(1/4)
def ridge : ℝ := 1/4

def hour (t : ℝ) := (1+t)^2

def zone (t : ℂ) := (1+t)^2 - ↑(hour pit)

lemma distance' {t : ℂ} (h : ‖t‖≤1/16) : ‖(1+t)^2-1‖ ≤ 3*‖t‖ := by
  calc
    _ = ‖2*t+t^2‖ := by congr 1; ring
    _ ≤ ‖(2:ℂ)‖*‖t‖+‖t‖^2 := by rw [← _root_.norm_pow t 2, ← norm_mul]; exact norm_add_le _ _
    _ ≤ _ := by norm_num; nlinarith [norm_nonneg t]

lemma limits {t : ℂ} (h : ‖t‖≤1/16) : ‖zone t‖≤1 ∧ ‖1-zone t‖≤1 := by
  have hv := distance' h
  have ht : zone t = ((1+t)^2-1)+(1-↑(hour pit)) := by unfold zone; abel
  have hs : (1-(1-↑(hour pit)):ℂ)=(↑(hour pit):ℂ) := by ring
  have hx := norm_add_le ((1+t)^2-1) (1-(↑(hour pit):ℂ))
  have hy := norm_sub_le (↑(hour pit):ℂ) ((1+t)^2-1)
  rw [ht,show 1-(((1+t)^2-1)+(1-↑(hour pit)))=(↑(hour pit):ℂ)-((1+t)^2-1) by abel]
  have he : ‖(1-↑(hour pit):ℂ)‖=7/16 := by rw [← ofReal_one, ← ofReal_sub,norm_real,Real.norm_eq_abs]; norm_num [hour,pit]
  have hW : ‖(↑(hour pit):ℂ)‖=9/16 := by rw [norm_real,Real.norm_eq_abs]; norm_num [hour,pit]
  exact ⟨hx.trans (by rw [he]; linarith),hy.trans (by rw [hW]; linarith)⟩

lemma polarPeak (r s : ℝ) {t : ℂ} (h : ‖t‖≤1/16) :
    ‖Complex.exp ((1-zone t)*↑r + zone t*↑s)‖ ≤ Real.exp (max r s) := by
  obtain ⟨hv,hb⟩ := limits h
  have h₁ : (zone t).re ≤ 1 := (Complex.re_le_norm _).trans hv
  have h₂ := (Complex.re_le_norm (1-zone t)).trans hb
  rw [Complex.norm_exp, Real.exp_le_exp]
  simp only [Complex.add_re,Complex.mul_re,Complex.one_re,Complex.sub_re,Complex.ofReal_re,ofReal_im,mul_zero,sub_zero] at h₂ ⊢
  rcases le_total r s with hh|hh
  · rw [max_eq_right hh]; nlinarith
  rw [max_eq_left hh]; nlinarith

def Fractional (f : ℝ → ℝ) := (∃ r : ℝ, ∀ t, 0 < 1+t → f t=r) ∨
    (∃ A B : ℝ, ∀ t, 0<1+t → f t=Real.exp (A+B*hour t)-1)

def Voyage (m : ℕ) (f : ℝ→ℝ) := ∃ D A B : ℝ, ∀ t, 0<1+t → f t=(1+t)^m * D * Real.exp (A+B*hour t)

def coin (x y : ℝ) (t : ℂ) := if x=y then (x:ℂ) else
    Complex.exp ((1-zone t)*↑(Real.log (1+x))+zone t*↑(Real.log (1+y))) - 1



lemma lode (x : ℝ) (he : |x|≤1/4) : |Real.log (1+x)|≤ 2*|x| := by
  let y := Real.log (1+x)
  have hz : 0 < 1+x := by linarith [neg_le_of_abs_le he]
  have hx := Real.add_one_le_exp y
  have hs : Real.exp y=1+x := Real.exp_log hz
  have hY := Real.add_one_le_exp (-y)
  rw [hs] at hx; rw [Real.exp_neg,hs] at hY
  have hk := mul_le_mul_of_nonneg_right hY hz.le; rw [inv_mul_cancel₀ hz.ne'] at hk
  refine abs_le.mpr ⟨?_,by linarith [le_abs_self x,abs_nonneg x]⟩; change _ ≤ y
  by_contra! h
  nlinarith [abs_nonneg x,le_abs_self x, neg_le_of_abs_le he,neg_abs_le x]

lemma coinPrice (x y : ℝ) (hx : 0<1+x) (hy : 0<1+y) {t : ℂ} (h : ‖t‖≤1/16) :
    ‖coin x y t‖ ≤ 10*(|x|+|y|) := by
  unfold coin; split
  next => rw [norm_real,Real.norm_eq_abs]; linarith [abs_nonneg y,abs_nonneg x]
  next =>
    let f := Real.log (1+x); let g := Real.log (1+y); let z := zone t
    let U : ℂ := (1-z)*↑f + z*↑g
    by_cases hn : |x|+|y|≤1/4
    · obtain ⟨h₁,h₂⟩ := limits h
      have hF := lode x (by linarith [abs_nonneg y]); have hG := lode y (by linarith [abs_nonneg x])
      have hu : ‖U‖≤2*(|x|+|y|) := by
        refine (norm_add_le _ _).trans ?_; rw [norm_mul,norm_mul,norm_real,norm_real]
        have hs := mul_le_of_le_one_left (norm_nonneg f) (show ‖1-z‖≤1 from h₂)
        have ht := mul_le_of_le_one_left (norm_nonneg g) (show ‖z‖≤1 from h₁)
        simp_rw [Real.norm_eq_abs,f,g] at hs ht ⊢; linarith
      exact (Complex.norm_exp_sub_one_le (show ‖U‖≤1 by linarith)).trans (by linarith [abs_nonneg y,abs_nonneg x])
    have hp := polarPeak f g h
    apply (norm_sub_le (Complex.exp U) 1).trans; rw [norm_one]
    change ‖Complex.exp U‖ ≤ _ at hp
    rcases le_total f g with H|H
    · rw [max_eq_right H,show Real.exp g=1+y from Real.exp_log hy] at hp; linarith [le_abs_self y,abs_nonneg x]
    rw [max_eq_left H,show Real.exp f=1+x from Real.exp_log hx] at hp; linarith [le_abs_self x,abs_nonneg y]

lemma counted (f : ℝ→ℝ) (he : Fractional f) {t : ℂ} (h : ‖t‖≤1/16) :
    ‖coin (f pit) (f ridge) t‖ ≤ 10*(|f pit|+|f ridge|) := by
  have h₁ : 0<1+pit := by norm_num [pit]
  have h₂ : 0<1+ridge := by norm_num [ridge]
  rcases he with ⟨A,H⟩|⟨A,B,H⟩
  · rw [H pit h₁,H ridge h₂,coin,if_pos rfl,norm_real,Real.norm_eq_abs]; linarith [abs_nonneg A]
  apply coinPrice _ _ _ _ h
  · rw [H pit h₁]; linarith [Real.exp_pos (A+B*hour pit)]
  rw [H ridge h₂]; linarith [Real.exp_pos (A+B*hour ridge)]

-- a slightly simpler signed ratio interpolation

def holm (m : ℕ) (x y : ℝ) (t : ℂ) :=
    let L := x/(1+pit)^m; let H := y/(1+ridge)^m
    (1+t)^m * ↑L * Complex.exp (zone t*(Real.log (H/L)))

lemma emergent {m : ℕ} {f : ℝ → ℝ} {A B D : ℝ} (hd : D≠0) (hf : ∀ t,0<1+t → f t=(1+t)^m*D * Real.exp (A+B*hour t)) (t : ℂ) :
    holm m (f pit) (f ridge) t=(1+t)^m*↑D *Complex.exp ((1-zone t)*↑(A+B*hour pit)+zone t*↑(A+B*hour ridge)) := by
  unfold holm; dsimp only
  have he t (ht : 0<1+t) : f t/(1+t)^m=D*Real.exp (A+B*hour t) := by rw [hf _ ht]; field_simp
  rw [he _ (by norm_num [pit]),he _ (by norm_num [ridge]),mul_div_mul_left _ _ hd, ← Real.exp_sub,Real.log_exp,
    ofReal_mul,ofReal_exp,← mul_assoc (a:=(1+t)^m),mul_assoc (a:= (1+t)^m*(↑D:ℂ)), ← Complex.exp_add]
  congr 2; push_cast; ring



lemma massFare {m : ℕ} (f : ℝ→ℝ) (hc : Voyage m f) {t : ℂ} (h : ‖t‖≤1/16) :
    ‖holm m (f pit) (f ridge) t‖ ≤ 4^m*(|f pit|+|f ridge|) := by
  obtain ⟨D,A,B,hD⟩ := hc
  have ht (y : ℝ) (hy : 1/2≤1+y) : ‖1+t‖^m*|D| * Real.exp (A+B*hour y) ≤ 4^m*|f y| := by
    rw [hD y (by linarith),abs_mul,abs_mul,abs_of_pos (Real.exp_pos _),abs_of_pos (pow_pos (show 0<1+y by linarith) m)]
    rw [show (4:ℝ)^m*((1+y)^m*|D| * Real.exp _)= (4*(1+y))^m*|D| * Real.exp (A+B*hour y) by rw [mul_pow]; ring]
    have hh := norm_add_le (1:ℂ) t; rw [norm_one] at hh; gcongr; linarith
  rcases eq_or_ne D 0 with rfl|hd
  · simp only [holm,hD pit (by norm_num [pit]),hD ridge (by norm_num [ridge]),mul_zero,zero_mul,zero_div,ofReal_zero,norm_zero,
      abs_zero,add_zero,le_refl]
  rw [emergent hd hD,norm_mul,norm_mul,_root_.norm_pow,norm_real,Real.norm_eq_abs]
  apply (mul_le_mul_of_nonneg_left (polarPeak _ _ h) (by positivity)).trans
  rcases le_total (A+B*hour pit) (A+B*hour ridge) with H|H
  · rw [max_eq_right H]; exact (ht ridge (by norm_num [ridge])).trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left (abs_nonneg _)) (by positivity))
  rw [max_eq_left H]; exact (ht pit (by norm_num [pit])).trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (abs_nonneg _)) (by positivity))
end YM.AnalyticNext.ConnectedActivity.Plotter
