import YM.Ac.Table
import YM.Bid.Drops
import YM.Next.BOUNDARY.Derived

/-!
# Curves of Euclidean rotations

Not assuming differentiability of the whole representation from the producer.
Infinitesimal ports are on one-parameter groups and individual vectors. To pull
back along a general rotation factor k(t), work locally relative to k(t₀),
using the matrix exp chart in the *ambient* space and proving that the local
log lies in the right subspace. No choices of Euler angles.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.BOUNDARY.Descent
open Set Filter Function NormedSpace Table
open scoped Topology Matrix.Norms.Frobenius ContDiff

private lemma at_parameter_zero (u : Ortho.Skew) : Ortho.oneParameter u 0=1 :=
  Work.A13.oneParameter_zero u

private lemma at_parameter_add (u : Ortho.Skew) (s t : ℝ) :
    Ortho.oneParameter u (s+t)= Ortho.oneParameter u s * Ortho.oneParameter u t := by
  apply Subtype.ext
  letI : NormedAlgebra ℚ M4 := .restrictScalars ℚ ℝ _
  change exp ((s+t) • u.val)=exp (s • u.val)*exp (t • u.val)
  rw [add_smul]; exact exp_add_of_commute (((Commute.refl u.val).smul_left s).smul_right t)

/-- IFT use isolated from paths. -/
private lemma chart_at_one : ∃ f : M4→ Ortho.Skew, f 1=0 ∧ DifferentiableAt ℝ f 1 ∧
    ∀ᶠ k : Ortho in 𝓝 1, k=Ortho.oneParameter (f k.val) 1 := by
  let J := ContinuousLinearEquiv.refl ℝ M4
  have he : HasStrictFDerivAt exp (J : M4 →L[ℝ] M4) 0 := hasStrictFDerivAt_exp_zero
  let g := he.localInverse exp J 0
  have hg : g 1=0 := by
    rw [show (1 : M4)=exp (0 : M4) by simp]; exact he.localInverse_apply_image
  have hG := he.to_localInverse
  rw [show exp (0:M4)=1 by simp] at hG
  have ht : DifferentiableAt ℝ g 1 := hG.hasFDerivAt.differentiableAt
  refine ⟨(fun x => skP (g x)),by simp only [hg,map_zero], skP.differentiableAt.comp 1 ht, ?_⟩
  have hw : ∀ᶠ x in 𝓝 (0:M4), g (exp x)=x := he.eventually_left_inverse
  have hy : ∀ᶠ x in 𝓝 (1:M4), exp (g x)=x := by
    rw [show (1:M4)=exp (0 : M4) by simp] -- only the filter
    exact he.eventually_right_inverse
  have hq : Tendsto (fun k : Ortho => k.val) (𝓝 1) (𝓝 (1:M4)) := continuous_subtype_val.tendsto (1:Ortho)
  have hp : Tendsto (fun k : Ortho => g k.val) (𝓝 1) (𝓝 0) :=
    hg ▸ ht.continuousAt.tendsto.comp hq
  have ha : Tendsto (fun k : Ortho => star (g k.val)) (𝓝 1) (𝓝 0) := by simpa using hp.star
  have hn : Tendsto (fun k : Ortho => -(g k.val)) (𝓝 1) (𝓝 0) := by simpa using hp.neg
  filter_upwards [ha.eventually hw, hn.eventually hw, hq.eventually hy] with k HS HN HK
  change g (exp _) = star _ at HS
  change g (exp _) = -_ at HN
  change exp (g _) = _ at HK
  have hi : exp (-(g k.val)) = star k.val := by
    letI : NormedAlgebra ℚ M4 := .restrictScalars ℚ ℝ _
    have he : exp (g k.val) * exp (- (g k.val))=1 := by
      have ha : exp (g k.val + -(g k.val)) = exp (g k.val) * exp (-(g k.val)) := exp_add_of_commute ((Commute.refl _).neg_right)
      rw [← ha]; simp
    rw [HK] at he
    calc _ = (star k.val*k.val)*_ := by rw [k.property.1,one_mul]
         _ = star k.val := by rw [mul_assoc,he,mul_one]
  have hm : star (g k.val)= -(g k.val) := by
    rw [hi] at HN
    rw [← star_exp,HK] at HS
    exact HS.symm.trans HN
  apply Subtype.ext
  change k.val= exp ((1:ℝ) • (skP (g k.val)).val)
  rw [one_smul,skP_eval,sk_eq hm,HK]

variable {G : Gauge} {L : Register G} {S : Table L}

-- No change of norm. Expose standard norm consequences as propositional
-- instances locally (rid diamonds between operator and TVS structures).
private lemma cont_general (T : Type*) [NormedAddCommGroup T] [NormedSpace ℝ T] : ContinuousSMul ℝ T := inferInstance
private lemma ring_general (T : Type*) [NormedRing T] : IsTopologicalRing T := inferInstance
lemma fieldOp_smul (d : ℕ) : ContinuousSMul ℝ (FieldOp S d) := cont_general (FieldOp S d)
lemma fieldOp_top (d : ℕ) : IsTopologicalRing (FieldOp S d) := ring_general (FieldOp S d)
attribute [local instance] fieldOp_smul fieldOp_top

/-- Helper for reading the derivative of an End-valued function on given vectors. -/
lemma on_field {d : ℕ} {A : ℝ → FieldOp S d} {Z : FieldOp S d} {r : ℝ}
    (h : HasDerivAt A Z r) (x : S.Field d) : HasDerivAt (fun t => A t x) (Z x) r := by
  let J := (ContinuousLinearMap.apply ℂ (S.Field d) x).restrictScalars ℝ
  exact HasFDerivAt.comp_hasDerivAt (f := A) (f' := Z) r (J.hasFDerivAt (x := A r)) h

/-- Exponential identifies a one-parameter action given even vector derivatives just at zero. -/
lemma one_parameter_field {d : ℕ} {A : ℝ → FieldOp S d} {Z : FieldOp S d}
    (ha : A 0=1) (hg : ∀ s t : ℝ, A (s+t)=A s*A t)
    (hz : ∀ x : S.Field d, HasDerivAt (fun t => A t x) (Z x) 0)
    (u : ℝ) : A u=exp (u • Z) := by
  haveI : CompleteSpace (S.Field d) := FiniteDimensional.complete ℂ _
  ext x
  let P := Z.restrictScalars ℝ
  let X := fun t : ℝ => exp (t • Z) x
  let Y := fun t : ℝ => A t x
  have hX (t) : HasDerivAt X (P (X t)) t := on_field (hasDerivAt_exp_smul_const' Z t) x
  have hY (t) : HasDerivAt Y (P (Y t)) t := by
    have he := (hz (A t x)).scomp_of_eq t ((hasDerivAt_id' t).sub_const t) (by simp)
    rw [one_smul] at he
    rw [show (fun r => A r (A t x)) ∘ (fun r => r-t) = Y from funext fun r => by
      change (A (r-t)*A t) x=A r x; rw [← hg,sub_add_cancel]] at he
    exact he
  have h0 : Y 0=X 0 := by
    rw [show Y 0=(1 : FieldOp S d) x by simp [Y,ha]]
    have he : (0:ℝ) • Z=0 := by ext y; simp
    simp only [X,he,exp_zero]
  exact congr_fun (ODE_solution_unique_univ (s := fun _ => Set.univ)
    (fun (_ : ℝ) => P.lipschitz.lipschitzOnWith)
    (fun t => ⟨hY t,mem_univ _⟩) (fun t => ⟨hX t,mem_univ _⟩) h0) u

lemma er_exp (R : Rotation S) {H : S.RealSpin} (h : Spin.Port R H) (d : ℕ) (u : Ortho.Skew) (t : ℝ) :
    er R d (Ortho.oneParameter u t) = exp (t • lie R d u) := by
  let A := fun t => er R d (Ortho.oneParameter u t)
  refine one_parameter_field (A := A) (Z := lie R d u) ?_ ?_ (fun x => h.spinAt d u x) t
  · unfold A; rw [at_parameter_zero,er_one R h]
  intro s t; unfold A; rw [at_parameter_add, er_mul R h]

lemma linear_path {E T : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup T] [NormedSpace ℝ T] (P : E →L[ℝ] T) (f : ℝ → E) (p : E) (r : ℝ)
    (h : HasDerivAt f p r) : HasDerivAt (fun t => P (f t)) (P p) r :=
  P.hasFDerivAt.comp_hasDerivAt r h

lemma er_id_path (R : Rotation S) {H : S.RealSpin} (h : Spin.Port R H) {k : ℝ → Ortho} {r : ℝ}
    (ha : k r=1) (ht : DifferentiableAt ℝ (fun t => (k t).val) r) (d : ℕ) :
    ∃ V : Ortho.Skew, HasDerivAt (fun t => (k t).val) V.val r ∧ HasDerivAt (fun t => er R d (k t)) (lie R d V) r := by
  obtain ⟨f,hf,hp,hb⟩ := chart_at_one
  have hk : ContinuousAt k r := by
    apply tendsto_subtype_rng.mpr
    exact ht.continuousAt.tendsto
  have he : Tendsto k (𝓝 r) (𝓝 1) := ha ▸ hk.tendsto
  let p (t : ℝ) := f (k t).val
  have h0 : p r=0 := by unfold p; rw [ha]; exact hf
  have Hf : DifferentiableAt ℝ p r := by
    have he : DifferentiableAt ℝ f (k r).val := by rw [ha]; exact hp
    exact he.comp r ht
  let V := deriv p r
  have HV : HasDerivAt p V r := Hf.hasDerivAt
  have hu : ∀ᶠ t in 𝓝 r, k t = Ortho.oneParameter (p t) 1 := he.eventually hb
  refine ⟨V,?_,?_⟩
  · let a : ℝ → M4 := fun t => (p t).val
    have hx : HasDerivAt a V.val r := HasFDerivAt.comp_hasDerivAt (f := p) (f':= V) r Ortho.skewSpace.subtypeL.hasFDerivAt HV
    have hw : HasFDerivAt exp (1:M4→L[ℝ] M4) (a r) := (show a r=0 by simp [a,h0]) ▸ hasFDerivAt_exp_zero
    have hy : HasDerivAt (fun t => exp (a t)) V.val r := HasFDerivAt.comp_hasDerivAt (f := a) (f' := V.val) r hw hx
    refine hy.congr_of_eventuallyEq ?_
    filter_upwards [hu] with t ht
    change (k t).val = _
    rw [ht]
    change exp ((1:ℝ) • _) = _
    rw [one_smul]
  haveI : CompleteSpace (S.Field d) := FiniteDimensional.complete ℂ _
  let a : ℝ → FieldOp S d := fun t => lie R d (p t)
  have hx : HasDerivAt a (lie R d V) r := by
    exact linear_path (E:=Ortho.Skew) (T:=FieldOp S d) (by exact lie R d) p V r HV
  have hz : a r=0 := by rw [show a r=lie R d (p r) from rfl,h0,map_zero]
  have hw : HasFDerivAt exp (1: FieldOp S d→L[ℝ] FieldOp S d) (a r) := by
    rw [hz]
    exact hasFDerivAt_exp_zero (𝔸 := FieldOp S d) (𝕂 := ℝ)
  have hy : HasDerivAt (fun t => exp (a t)) (lie R d V) r := HasFDerivAt.comp_hasDerivAt
    (E := FieldOp S d) (𝕜 := ℝ) (F := FieldOp S d) (l' := 1) (l := exp) (f := a) (f' := lie R d V) r hw hx
  refine HasDerivAt.congr_of_eventuallyEq (F:=FieldOp S d) (𝕜:=ℝ) (x:=r)
    (f := fun t => exp (a t)) (f' := lie R d V) (f₁ := fun t => er R d (k t)) hy ?_
  filter_upwards [hu] with t ht'
  rw [ht',er_exp R h]
  exact congr_arg exp (show (1:ℝ) • lie R d (p t)=a t by ext x; simp [a])

/-- Simultaneous right-factor velocities. -/
lemma er_path (R : Rotation S) {H : S.RealSpin} (h : Spin.Port R H) {k : ℝ → Ortho} {r : ℝ}
    (ht : DifferentiableAt ℝ (fun t => (k t).val) r) (d : ℕ) : ∃ V : Ortho.Skew,
    HasDerivAt (fun t => (k t).val) ((k r).val*V.val) r ∧ HasDerivAt (fun t => er R d (k t)) (er R d (k r)*lie R d V) r := by
  let u (t : ℝ) := (k r)⁻¹*k t
  have hx : DifferentiableAt ℝ (fun t => (u t).val) r :=
    ht.const_mul ((k r)⁻¹.val)
  obtain ⟨X,hX,he⟩ := er_id_path R h (k:=u) (r:=r) (by simp [u]) hx d
  refine ⟨X,?_,?_⟩
  · have hw := hX.const_mul (k r).val
    have hm : (fun t => (k r).val * (u t).val)=fun t => (k t).val := by
      funext t; change (k r*u t).val = _; simp only [u, mul_inv_cancel_left]
    rw [hm] at hw; exact hw
  have hv : HasDerivAt (fun t => er R d (k r)*er R d (u t)) (er R d (k r)*lie R d X) r :=
    HasDerivAt.const_mul (𝕜 := ℝ) (x := r) (d := fun t => er R d (u t)) (d' := lie R d X) (er R d (k r)) he
  simp_rw [← er_mul R h, u, mul_inv_cancel_left] at hv
  exact hv

end YM.Next.BOUNDARY.Descent
