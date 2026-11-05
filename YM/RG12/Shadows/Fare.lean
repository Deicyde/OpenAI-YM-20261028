import YM.RG12.Spins.Catacomb
import YM.OPE.Rate
/-! # Coupling prices for all terms of a germ calculation

This is a sequence calculus, not immediately a statement uniform across all
RG auxiliary scopes (e.g. arbitrary [Fintype I]) BUT to derive those station bills
can select counterexample sequences incl stencils & all histories. Don't issue
requests via the changing scopes until proved. Sign convention gains exponent for
cool. Gamma k := exp(-H k) typically g_m(k) ≍ χ^-1/2 but retain losses strictly
AFTER L. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Shadows
open OPE Set Metric Function Filter
open scoped ContDiff Topology BigOperators Classical
structure Haze where
  H : ℕ→ℝ
  warmth : Tendsto H atTop atTop
-- Gains super or near power.Unrestricted fees

def Charges (R:Haze)(p:ℝ)(w:ℕ→ℝ):Prop:= RateLE atTop R.H w (-p)
namespace Charges
variable {R:Haze}{p q :ℝ}{w v:ℕ→ℝ} (h:Charges R p w)
include h
theorem transfer {v} (hv:∀ᶠ i:ℕ in atTop, ‖v i‖ ≤ ‖w i‖):Charges R p v:=RateLE.transfer h hv
lemma move {v} (he:∀ᶠ i:ℕ in atTop,|v i| ≤ w i): Charges R p v:= h.transfer (he.mono fun _ hi=> by simp only [Real.norm_eq_abs]; exact hi.trans (le_abs_self _))
lemma equates {v} (he : w =ᶠ[atTop] v): Charges R p v:= RateLE.congr h he
lemma slower (he:q ≤ p): Charges R q w:= RateLE.mono h (neg_le_neg he)
omit h in
lemma frozen (a:ℝ)(R:Haze): Charges R 0 (fun _=>a):= by unfold Charges; rw [neg_zero]; exact RateLE.const a R.warmth
omit h in
lemma idle (p:ℝ)(R:Haze): Charges R p (fun _=>0):=RateLE.zero atTop R.H (-p)
lemma add (hv:Charges R p v):Charges R p (fun i=> w i+v i):= RateLE.add h hv R.warmth
lemma mul (hv:Charges R q v):Charges R (p+q) (fun i=> w i*v i):= by unfold Charges; rw [neg_add]; exact RateLE.mul h hv
lemma norm : Charges R p (fun i=>‖w i‖):= RateLE.norm h
lemma absolute :Charges R p (fun i=> |w i|):= h.norm
lemma tend0 (hp:0<p) : Tendsto w atTop (𝓝 0):= RateLE.tends h (neg_neg_of_pos hp) R.warmth
lemma left (r:ℝ):Charges R p (fun i=> r*w i):= by simpa only [zero_add] using (frozen r R).mul h
lemma right (r:ℝ):Charges R p (fun i=> w i*r):= by simpa only [add_zero] using h.mul (frozen r R)
lemma power (n:ℕ):Charges R (n*p) (fun i=>w i^n):= by unfold Charges; simpa only [mul_neg] using RateLE.pow n h R.warmth
lemma raise (n:ℕ)(he:p=0):Charges R 0 (fun i=>w i^n):=by subst p; simpa only [mul_zero] using h.power n
end Charges
-- Uniform need classes indexed by day/tag of that day: no claiming sup
-- over parameter Θ where a schedule AFTER Θ required.
universe u
variable {R:Haze}{n:ℕ}{p q: ℝ}{I I' J:ℕ→Type}{E:ℕ→Type} [∀ i,NormedAddCommGroup (E i)][∀ i,NormedSpace ℝ (E i)]
def Keeps (R:Haze)(p:ℝ)(I:ℕ→Type)(F:∀ i:ℕ,I i→ℝ) := ∃ w, Charges R p w ∧ ∀ᶠ i:ℕ in atTop, ∀ j, |F i j| ≤ w i
namespace Keeps
variable {f g:∀ i:ℕ,I i→ℝ}(h:Keeps R p I f)
include h
lemma assures (hg:∀ᶠ i:ℕ in atTop,∀ j,|g i j| ≤ |f i j|):Keeps R p I g:=by obtain ⟨v,hv,hh⟩:=h; exact ⟨v,hv,(hh.and hg).mono fun i ha j=> (ha.2 j).trans (ha.1 j)⟩
lemma pays (k:∀ i,I i):Charges R p (fun i=> f i (k i)):=by obtain ⟨v,hv,hh⟩:=h; exact hv.move (hh.mono fun i ha=> ha (k i))
lemma rename (j:∀ i,I' i→ I i):Keeps R p I' (fun i k=> f i (j i k)):=by obtain ⟨v,hv,hh⟩:=h; exact ⟨v,hv,hh.mono fun i ha k=>ha _⟩
end Keeps
end YM.RG12.Shadows
