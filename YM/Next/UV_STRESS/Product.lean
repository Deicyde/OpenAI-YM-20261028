import Mathlib.Analysis.Matrix.Normed
import Mathlib.Data.Pi.Interval
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Topology.Algebra.Star.Unitary

/-!
# Factor functions in integrations over subsets of tags/links

Algebraic integral identities. As with `integral_prod_mul`, useful even
without integrability assumptions in the lemmas. Use as *expectations*
only when also proving integrability and positivity/normalization.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.UVStress
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
variable {ι B : Type*} [Fintype ι] [Nonempty B] (p : ι → Prop) [DecidablePred p]

abbrev MinusPart := Subtype (fun i => ¬ p i)

/-- Function depends only on these coordinates. -/
def Draws (p : ι → Prop) (f : (ι → B) → ℂ) := ∀ x y : ι → B, (∀ i,p i → x i=y i) → f x=f y

def traceLeft (f : (ι → B) → ℂ) (x : Subtype p→B) : ℂ :=
    f ((Equiv.piEquivPiSubtypeProd p (fun _ => B)).symm (x,Classical.ofNonempty))

def traceRight (f : (ι → B) → ℂ) (y : MinusPart p→ B) : ℂ :=
    f ((Equiv.piEquivPiSubtypeProd p (fun _ => B)).symm (Classical.ofNonempty,y))

private def letters (w : ι → B → ℂ) (f : (ι → B) → ℂ) (u : ι → B) := (∏ i,w i (u i))*f u

private lemma packetSplit (w : ι → B → ℂ) (f g : (ι → B) → ℂ) (hf : Draws p f) (hg : Draws (fun i => ¬ p i) g)
    (x : Subtype p→ B) (y : MinusPart p → B) : letters w (f*g) ((Equiv.piEquivPiSubtypeProd p _).symm (x,y))=
      letters (fun i : Subtype p => w i) (traceLeft p f) x *
        letters (fun i : MinusPart p => w i) (traceRight p g) y := by
  let U := Equiv.piEquivPiSubtypeProd p (fun _ => B)
  let z := U.symm (x,y)
  have he (i : Subtype p) : z i = x i := by simp [z,U,Equiv.piEquivPiSubtypeProd,i.property]
  have ht (i : MinusPart p) : z i = y i := by simp [z,U,Equiv.piEquivPiSubtypeProd,i.property]
  have hp : f z=traceLeft p f x := hf _ _ (fun i hi => by simp only [z,U,Equiv.piEquivPiSubtypeProd_symm_apply,dif_pos hi])
  have hq : g z=traceRight p g y := hg _ _ (fun i hi => by simp only [z,U,Equiv.piEquivPiSubtypeProd_symm_apply,dif_neg hi])
  change (∏ i : ι, w i (z i))*(f z*g z)=_
  rw [← Fintype.prod_subtype_mul_prod_subtype p fun i => w i (z i), hp,hq]; simp_rw [he,ht]
  unfold letters; ring

section Weights
variable [MeasurableSpace B] (μ : Measure B) [SigmaFinite μ]

def scatter (w : ι → B → ℂ) (f : (ι→ B) → ℂ) := ∫ x, (∏ i,w i (x i)) * f x ∂(Measure.pi fun _ => μ)

private lemma scatter_both (w : ι → B→ ℂ) {f g : (ι → B) → ℂ} (hf : Draws p f) (hg : Draws (fun i => ¬ p i) g) :
    scatter μ w (f*g)= scatter μ (fun i : Subtype p => w i) (traceLeft p f)*
      scatter μ (fun i : MinusPart p => w i) (traceRight p g) := by
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => B) p
  let m := Measure.pi (fun _ : ι => μ)
  change (∫ x, letters w (f*g) x ∂m)=_
  rw [← (measurePreserving_piEquivPiSubtypeProd (fun _ : ι => μ) p).symm.integral_comp e.symm.measurableEmbedding]
  have hx (z : (Subtype p→B) × (MinusPart p→B)) := packetSplit p w f g hf hg z.1 z.2
  convert integral_prod_mul (μ:=Measure.pi (fun _ : Subtype p => μ)) (ν:=Measure.pi (fun _ : MinusPart p => μ))
    (letters (fun i : Subtype p => w i) (traceLeft p f)) (letters (fun i : MinusPart p => w i) (traceRight p g)) using 1
  · congr! 2
    exact hx _
  rfl

omit [Nonempty B] in
private lemma scatter_mass (w : ι → B → ℂ) (h : ∀ i, (∫ x,w i x ∂μ)=1) : scatter μ w 1=1 := by
  unfold scatter; simp only [Pi.one_apply,mul_one]; rw [integral_fintype_prod_eq_prod]; simp_rw [h]; simp

lemma scatter_uses (w : ι → B→ ℂ) {f : (ι → B) → ℂ} (hf : Draws p f) (hp : ∀ i, (∫ x,w i x ∂μ)=1) :
    scatter μ w f=scatter μ (fun i : Subtype p => w i) (traceLeft p f) := by
  have he := scatter_both p μ w hf (g:=1) (fun _ _ _ => rfl)
  rwa [mul_one,show traceRight p (1: (ι→B)→ℂ)=1 from rfl,scatter_mass (ι:=MinusPart p) _ _ (fun i => hp i),mul_one] at he

lemma scatter_parts (w : ι → B→ ℂ) {f g : (ι → B) → ℂ} (hf : Draws p f) (hg : Draws (fun i => ¬ p i) g)
    (hp : ∀ i,(∫ x,w i x ∂μ)=1) : scatter μ w (f*g)=scatter μ w f*scatter μ w g := by
  have he := scatter_both p μ w (f:=1) (fun _ _ _ => rfl) hg
  rw [one_mul,show traceLeft p (1: (ι→B)→ℂ)=1 from rfl,scatter_mass (ι:=Subtype p) _ _ (fun i => hp i),one_mul] at he
  rw [scatter_both p μ _ hf hg,he,scatter_uses p μ _ hf hp]
end Weights

section FiniteTags
variable [DecidableEq ι] [Fintype B]

def scanning (w : ι → B → ℂ) (f : (ι→ B) → ℂ) := ∑ x : ι→B,(∏ i,w i (x i)) * f x

private lemma scanning_both (w : ι → B→ ℂ) {f g : (ι → B) → ℂ} (hf : Draws p f) (hg : Draws (fun i => ¬ p i) g) :
    scanning w (f*g)= scanning (fun i : Subtype p => w i) (traceLeft p f)*
      scanning (fun i : MinusPart p => w i) (traceRight p g) := by
  -- match actual finite Fintype-using sums
  let e := Equiv.piEquivPiSubtypeProd p (fun _ : ι => B)
  change (∑ x : ι → B, letters w (f*g) x) = _
  rw [← Equiv.sum_comp e.symm (letters w (f*g)), Fintype.sum_prod_type]
  simp_rw [show ∀ x y, letters w (f*g) (e.symm (x,y))=_ from packetSplit p w f g hf hg, ← Finset.mul_sum, ← Finset.sum_mul]; rfl

omit [Nonempty B] in
private lemma scanning_mass (w : ι → B → ℂ) (h : ∀ i, (∑ x,w i x)=1) : scanning w 1=1 := by
  unfold scanning; simp only [Pi.one_apply,mul_one]; rw [← Fintype.prod_sum]; simp_rw [h]; simp

lemma scanning_uses (w : ι → B→ ℂ) {f : (ι → B) → ℂ} (hf : Draws p f) (hp : ∀ i, (∑ x,w i x)=1) :
    scanning w f=scanning (fun i : Subtype p => w i) (traceLeft p f) := by
  have he := scanning_both p w hf (g:=1) (fun _ _ _ => rfl)
  rwa [mul_one,show traceRight p (1: (ι→B)→ℂ)=1 from rfl,scanning_mass (ι:=MinusPart p) _ (fun i => hp i),mul_one] at he

lemma scanning_parts (w : ι → B→ ℂ) {f g : (ι → B) → ℂ} (hf : Draws p f) (hg : Draws (fun i => ¬ p i) g)
    (hp : ∀ i,(∑ x,w i x)=1) : scanning w (f*g)=scanning w f*scanning w g := by
  have he := scanning_both p w (f:=1) (fun _ _ _ => rfl) hg
  rw [one_mul,show traceLeft p (1: (ι→B)→ℂ)=1 from rfl,scanning_mass (ι:=Subtype p) _ (fun i => hp i),one_mul] at he
  rw [scanning_both p _ hf hg,he,scanning_uses p _ hf hp]

lemma scanning_congr (w g : ι → B → ℂ) (f h : (ι → B) → ℂ) (hf : Draws p f) (hg : Draws p h) (hw : ∀ i, (∑ x,w i x)=1)
    (hu : ∀ i, (∑ x,g i x)=1) (he : ∀ i,p i → w i=g i) (hh : f=h) : scanning w f=scanning g h := by
  rw [scanning_uses p w hf hw,scanning_uses p g hg hu, hh,
    show (fun i : Subtype p => w i)=(fun i : Subtype p => g i) from funext fun i => he _ i.property]
end FiniteTags
end YM.Next.UVStress
