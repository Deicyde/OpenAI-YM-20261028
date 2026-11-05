import YM.Mink.Geometry
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
Not the all-Lorentz group or cover. Covectors via
Euclidean transpose (so inverse transpose for push of Fourier support). Prove ON SAME GROUP the constituent needed for cone transport, to make
sign/cone explicit. No assumption of spectral equivalence.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Mink
open Set Filter Function MeasureTheory
open scoped Topology Matrix.Norms.Frobenius InnerProductSpace BigOperators

abbrev Coord := E4 →L[ℝ] E4
abbrev General := Coordˣ

namespace General
def walk (g : General) := g.val
def stretch (g : General) := LinearMap.det g.walk.toLinearMap

@[simp] theorem walk_one (x : E4) : walk 1 x=x := rfl
@[simp] theorem walk_mul (g k : General) (x) : walk (g*k) x=walk g (walk k x) := rfl
@[simp] theorem retrace (g : General) (x) : walk g (walk g⁻¹ x) = x := by rw [← walk_mul, mul_inv_cancel,walk_one]
@[simp] theorem proceeds (g : General) (x) : walk g⁻¹ (walk g x) = x := by rw [← walk_mul, inv_mul_cancel,walk_one]
@[simp] theorem north : stretch 1=1 := LinearMap.det.map_one
@[simp] theorem comp (g k : General) : stretch (g*k) = stretch g * stretch k := LinearMap.det.map_mul ..
@[ext] theorem ext (g k : General) (h : ∀ x, walk g x = walk k x) : g=k := Units.ext (ContinuousLinearMap.ext h)
end General

def Proper : Subgroup General where
  carrier := {g | General.stretch g=1 ∧ (∀ x, m (g.walk x)=m x) ∧ (∀ x, g.walk x ∈ cone ↔ x ∈ cone)}
  one_mem' := ⟨General.north,fun _ => rfl,fun _ => Iff.rfl⟩
  mul_mem' := by
    rintro g k ⟨hg,hm,hp⟩ ⟨hk,hx,hs⟩
    exact ⟨by rw [General.comp,hg,hk,mul_one],fun x => (hm (k.walk x)).trans (hx x),fun x => (hp (k.walk x)).trans (hs _)⟩
  inv_mem' := by
    rintro g ⟨hg,hm,hp⟩
    refine ⟨?_,fun x => ?_,fun x => ?_⟩
    · calc _ = General.stretch (g*g⁻¹) := (by rw [General.comp,hg,one_mul])
           _ = 1 := by simp
    · simpa using (hm (General.walk g⁻¹ x)).symm
    simpa using (hp (General.walk g⁻¹ x)).symm

abbrev Lorentz := ↥Proper

namespace Lorentz
abbrev act (g : Lorentz) := g.val.walk

@[simp] theorem det (g : Lorentz) : LinearMap.det g.act.toLinearMap = 1 := g.property.1
@[simp] theorem keeps (g : Lorentz) (x) : m (g.act x) = m x := g.property.2.1 _
@[simp] theorem keepsCone (g : Lorentz) (x) : g.act x ∈ cone ↔ x ∈ cone := g.property.2.2 _
@[simp] theorem stays (g : Lorentz) (x) : g.act x ∈ inside ↔ x ∈ inside := by
  have he u : u ∈ inside ↔ u ∈ cone ∧ 0 < m u := by
    rw [strict_self,cone_self,@and_comm (0 ≤ time u), and_assoc]; unfold m
    constructor
    · rintro ⟨p,t⟩; exact ⟨by linarith,p.le,t⟩
    rintro ⟨_,p,t⟩; exact ⟨by nlinarith [norm_nonneg (spatial u)],t⟩
  rw [he,keepsCone,keeps, ← he]
@[simp] theorem act_one (v) : act 1 v=v := rfl
@[simp] theorem act_mul (g k : Lorentz) (x) : act (g*k) x=g.act (act k x) := rfl
@[simp] theorem undoes (g : Lorentz) (x) : g.act (act g⁻¹ x) = x := by rw [← act_mul];simp
@[simp] theorem starts (g : Lorentz) (x) : act g⁻¹ (g.act x) = x := by rw [← act_mul];simp

@[ext] theorem ext (g k : Lorentz) (h : ∀ x, g.act x=k.act x) : g=k := Subtype.ext (General.ext _ _ h)

def sends (g : Lorentz) : E4 ≃L[ℝ] E4 := ContinuousLinearEquiv.unitsEquiv ℝ E4 g.val
@[simp] theorem sent (g : Lorentz) (x) : g.sends x=g.act x := rfl
@[simp] theorem forwards (g : Lorentz) (x) : g.sends.symm x=act g⁻¹ x := rfl

example : IsTopologicalGroup Lorentz := inferInstance
@[fun_prop] theorem usual : Continuous act := Units.continuous_val.comp continuous_subtype_val

theorem preserves (g : Lorentz) : MeasurePreserving g.sends volume volume := by
  refine ⟨g.sends.continuous.measurable, ?_⟩
  change Measure.map (⇑g.act.toLinearMap) volume = _
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by simp),g.det];simp

/-- Spatial reversal for switching between placements and covectors via the
spacetime metric. Frequency/position pair, however, stays Euclidean. -/
def reverseL : General := (ContinuousLinearEquiv.unitsEquiv ℝ E4).symm
  (LinearEquiv.toContinuousLinearEquiv
    { toFun x := position (-spatial x) (time x)
      invFun x := position (-spatial x) (time x)
      map_add' x y := ext_by (by simp [add_comm]) (by simp)
      map_smul' c x := ext_by (by simp) (by simp)
      left_inv x := by simp
      right_inv x := by simp })

@[simp] theorem reversing (x : E4) : General.walk reverseL x=position (-spatial x) (time x) := rfl
@[simp] theorem reversal (x) : General.walk reverseL⁻¹ x=General.walk reverseL x := rfl
@[simp] theorem reverse_inv : reverseL⁻¹=reverseL := General.ext _ _ reversal

def dual (g : Lorentz) : Lorentz := ⟨reverseL*g.val*reverseL,by
  have he : General.stretch reverseL * General.stretch reverseL = 1 := by
    rw [← General.comp]
    nth_rw 1 [← reverse_inv]; simp only [inv_mul_cancel,General.north]
  refine ⟨by simp [he,show General.stretch g.val=1 from det g],fun x => ?_, fun x => ?_⟩
  · have hm x : m (General.walk reverseL x) = m x := by simp [m]
    rw [General.walk_mul,General.walk_mul,hm,g.keeps,hm]
  have hw x : General.walk reverseL x ∈ cone ↔ x ∈ cone := by simp [cone]
  rw [General.walk_mul,General.walk_mul,hw,g.keepsCone,hw]⟩

private lemma bil (g : Lorentz) (x p : E4) : inner ℝ (act g x) (General.walk reverseL (act g p)) = inner ℝ x (General.walk reverseL p) := by
  let f (x p : E4) := inner ℝ x (General.walk reverseL p)
  have hh x : f x x=m x := by simp [f,m,pairing, sub_eq_add_neg,pow_two, add_comm]
  have he x p : f x p=f p x := by simp [f,pairing,real_inner_comm,mul_comm]
  have ht x p : f (x+p) (x+p)=f x x+2*f x p+f p p := by
    calc
      _ = f x x + f x p + (f p x + f p p) := by dsimp only [f]; rw [inner_add_left,map_add]; simp only [inner_add_right]
      _ = _ := by rw [he p x];ring
  have h₁ := ht x p
  have h₂ := ht (act g x) (act g p)
  rw [← map_add] at h₂
  rw [hh,hh,hh] at h₁ h₂
  simp only [keeps] at h₂
  change f _ _ = f _ _; linarith

theorem dual_sent (g : Lorentz) (p x) : inner ℝ (act g x) (act g.dual p) = inner ℝ x p := by
  have he := bil g x (General.walk reverseL p)
  rw [show General.walk reverseL (General.walk reverseL p) = p by simp] at he; exact he

@[simp] theorem dual_involution (g : Lorentz) : dual (dual g) = g := by
  apply Subtype.ext
  change reverseL*(reverseL*g.val*reverseL)*reverseL=g.val
  have he : reverseL*reverseL=1 := General.ext _ _ (by simp)
  calc
    _ = (reverseL*reverseL)*g.val*(reverseL*reverseL) := by group
    _ = _ := by rw [he];simp

lemma dual_adjoint (g : Lorentz) : act g.dual = ContinuousLinearMap.adjoint (act g⁻¹) := by
  ext1 x; apply ext_inner_left ℝ
  intro y; rw [ContinuousLinearMap.adjoint_inner_right]
  simpa using dual_sent g x (act g⁻¹ y)
end Lorentz
end YM.Mink
