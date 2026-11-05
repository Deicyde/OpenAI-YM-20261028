import YM.Mink.Lorentz

/-! The full group. Orbit continuity with the indicated topology. Joint volume.
Spacetime proper rotations fixing temporal axis can be embedded via `room`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Mink
open MeasureTheory Set Filter Function
open scoped Topology Matrix.Norms.Frobenius

namespace Lorentz

abbrev properTurn (K : Ortho) := LinearMap.det K.motion.toLinearEquiv.toLinearMap=1

def spatialTurn (K : Ortho) := properTurn K ∧ ∀ x : E4, time (K.move x) = time x

def room (K : Ortho) (h : spatialTurn K) : Lorentz :=
  ⟨(ContinuousLinearEquiv.unitsEquiv ℝ E4).symm K.motion.toContinuousLinearEquiv,by
    have he x : ‖spatial (K.motion x)‖ = ‖spatial x‖ := by
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      have ht : time (K.motion x) = time x := h.2 x
      have hp := squares (K.motion x)
      rw [ht,LinearIsometryEquiv.norm_map,squares x] at hp; exact (add_right_cancel hp).symm
    refine ⟨show LinearMap.det K.motion.toLinearEquiv.toLinearMap=1 from h.1, ?_, ?_⟩
    · intro x; change m (K.motion x)=_
      rw [m,he,Ortho.motion_at,h.2];rfl
    intro x; change ‖spatial (K.motion x)‖ ≤ time (K.motion x) ↔ _
    rw [he,Ortho.motion_at,h.2];rfl⟩
end Lorentz

structure Poincare where
  Λ : Lorentz
  b : E4

namespace Poincare

@[ext] theorem ext (p q : Poincare) (h : p.Λ=q.Λ) (hp : p.b=q.b) : p=q := by
  cases p; cases q; congr

def sends (p : Poincare) (x : E4) := Lorentz.act p.Λ x + p.b
@[simp] lemma base (p : Poincare) : sends p 0 = p.b := by simp [sends]

theorem by_placement (p q) (h : ∀ x, sends p x = sends q x) : p=q := by
  have he : p.b=q.b := by simpa using h 0
  refine ext _ _ (Lorentz.ext _ _ (fun x => ?_)) he
  have hp := h x; unfold sends at hp; rw [he] at hp; exact add_right_cancel hp

instance : One Poincare := ⟨⟨1,0⟩⟩
instance : Mul Poincare := ⟨fun p q => ⟨p.Λ*q.Λ,sends p q.b⟩⟩
instance : Inv Poincare := ⟨fun p => ⟨p.Λ⁻¹,Lorentz.act p.Λ⁻¹ (-p.b)⟩⟩
@[simp] theorem oneL : (1 : Poincare).Λ = 1 := rfl
@[simp] theorem oneB : (1 : Poincare).b = 0 := rfl
@[simp] theorem productL (p q : Poincare) : (p*q).Λ = p.Λ*q.Λ := rfl
@[simp] theorem productB (p q : Poincare) : (p*q).b = sends p q.b := rfl
@[simp] theorem invL (p : Poincare) : p⁻¹.Λ = p.Λ⁻¹ := rfl
@[simp] theorem invB (p : Poincare) : p⁻¹.b = Lorentz.act p.Λ⁻¹ (-p.b) := rfl
@[simp] theorem sends_one (x) : sends 1 x=x := by simp [sends]
@[simp] theorem sends_mul (p q : Poincare) (x) : sends (p*q) x=sends p (sends q x) := by
  simp [sends];abel
@[simp] theorem backwards (p : Poincare) (x) : sends p⁻¹ x = Lorentz.act p.Λ⁻¹ (x - p.b) := by simp [sends,sub_eq_add_neg]

instance : Group Poincare where
  one_mul p := by_placement _ _ (by simp)
  mul_one p := by_placement _ _ (by simp)
  mul_assoc p q r := by_placement _ _ (by simp)
  inv_mul_cancel p := by
    apply by_placement; intro x; rw [sends_mul,sends_one,backwards]; simp [sends]

@[simp] theorem unmade (p : Poincare) (x) : sends p⁻¹ (sends p x) = x := by rw [← sends_mul];simp
@[simp] theorem emerges (p : Poincare) (x) : sends p (sends p⁻¹ x) = x := by rw [← sends_mul];simp

def presentations (p : Poincare) := (p.Λ,p.b)
instance : TopologicalSpace Poincare := TopologicalSpace.induced presentations inferInstance
lemma standard : Topology.IsEmbedding presentations := ⟨⟨rfl⟩,fun x y h => ext x y (congr_arg Prod.fst h) (congr_arg Prod.snd h)⟩
@[fun_prop] theorem continuousL : Continuous Λ := continuous_fst.comp standard.continuous
@[fun_prop] theorem continuousB : Continuous b := continuous_snd.comp standard.continuous
@[fun_prop] theorem ct : Continuous General.walk := Units.continuous_val
@[fun_prop] theorem togetherCt : Continuous (fun p : General × E4 => General.walk p.1 p.2) := (ct.comp continuous_fst).clm_apply continuous_snd
@[fun_prop] theorem continuousPlacement : Continuous (fun p : Poincare × E4 => sends p.1 p.2) := by unfold sends; fun_prop
instance : IsTopologicalGroup Poincare where
  continuous_inv := standard.continuous_iff.mpr (show Continuous (fun p : Poincare => (p.Λ⁻¹, Lorentz.act p.Λ⁻¹ (-p.b))) from by fun_prop)
  continuous_mul := standard.continuous_iff.mpr (show Continuous (fun p : Poincare × Poincare => (p.1.Λ * p.2.Λ, sends p.1 p.2.b)) from by unfold sends;fun_prop)

/-- Pure translations. -/
def translation (b : E4) : Poincare := ⟨1,b⟩
def motion (g : Lorentz) : Poincare := ⟨g,0⟩
@[simp] theorem stand : translation 0=1 := rfl
@[simp] theorem inactive : motion 1=1 := rfl
@[simp] theorem as_move (s : E4) (x) : sends (translation s) x=x+s := by simp [translation,sends]
@[simp] theorem as_active (s : Lorentz) (x) : sends (motion s) x=s.act x := by simp [sends,motion]
@[simp] theorem overL (s t : Lorentz) : motion (s*t)=motion s*motion t := by_placement _ _ (by simp)
@[simp] theorem overE (s t : E4) : translation (s+t)=translation s * translation t := by apply by_placement;intro x; simp;abel
@[fun_prop] theorem continuousM : Continuous motion := standard.continuous_iff.mpr (continuous_id.prodMk continuous_const)
@[fun_prop] theorem continuousE : Continuous translation := standard.continuous_iff.mpr (continuous_const.prodMk continuous_id)

open MeasureTheory.Measure

variable (g : Poincare)

lemma preserving : MeasurePreserving g.sends volume volume :=
  (measurePreserving_add_right volume g.b).comp g.Λ.preserves

def togetherL (A : Lorentz) (n : ℕ) : Points n ≃L[ℝ] Points n := LinearEquiv.toContinuousLinearEquiv
  { toFun p := points fun i => Lorentz.act A (p i)
    invFun p := points fun i => Lorentz.act A⁻¹ (p i)
    map_smul' c x := PiLp.ext fun i => map_smul  (A.act) c (x i)
    map_add' x y := PiLp.ext fun i => map_add  (A.act) (x i) (y i)
    left_inv p := by simp
    right_inv p := by simp }

@[simp] theorem togetherL_at (A : Lorentz) (n x i) : togetherL A n x i=A.act (x i) := rfl
@[simp] theorem togetherS_at (A : Lorentz) (n x i) : (togetherL A n).symm x i=Lorentz.act A⁻¹ (x i) := rfl

def zusammen (n : ℕ) (p : Points n) := points fun i => g.sends (p i)

lemma together (n : ℕ) : MeasurePreserving (zusammen g n) volume volume := by
  let e := MeasurableEquiv.toLp 2 (Fin n → E4)
  have he : MeasurePreserving e.symm volume volume := Points.volume_product n
  have ht := volume_preserving_pi (fun i : Fin n => g.preserving)
  exact he.symm.comp (ht.comp (Points.volume_product n))
end Poincare
end YM.Mink
