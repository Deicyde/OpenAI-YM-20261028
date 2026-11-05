import YM.Planned.PRIMARY_INTEGRAL_295.Kelps
import YM.Planned.PRIMARY_INTEGRAL_295.Seas

/-!
# Actual moving C marginal and Envelope of EVERY chart factor

Proving equivalent E.Jpr representation by canonical Gaussian input
(keep Γ of joint C image). Prices require only pointwise jets at central
chart of C-kernel and SPD gap there. Never infer that those traces are the
physical trajectory choice. `Radiate` produces same-measure *local*
coordinates, nowhere exchange independently drawn input modes for edges.
No radius-uniform search in dimension beyond polynomial constants.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Tropics
open Nimbuses Function Filter Set Oval Metric Kelps MeasureTheory ProbabilityTheory
open scoped Topology ContDiff BigOperators RightActions RealInnerProductSpace MatrixOrder
variable {k n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {f g : E → Plate ι}

abbrev MapB (ι:Type*) [Fintype ι] [DecidableEq ι] := Matrix.toEuclideanCLM (n:=ι) (𝕜:=ℝ)
variable (ι)
omit [DecidableEq ι] in
lemma costStrong (P : Plate ι) : ‖star P‖=‖P‖ := ContinuousLinearMap.adjoint.norm_map P
omit [DecidableEq ι] in
lemma costGram (H:Plate ι) (x:Sky ι) : ⟪x,(H*star H) x⟫ = ‖(star H) x‖^2 := by
  change ⟪x,H ((star H) x)⟫ = _
  rw [← ContinuousLinearMap.adjoint_inner_left]; exact real_inner_self_eq_norm_sq _
lemma starMap (C : Matrix ι ι ℝ) : MapB ι (star C)=star (MapB ι C) := map_star (MapB ι) C
lemma with_mirror {C:Matrix ι ι ℝ} (h : C.IsHermitian) : star (MapB ι C) = MapB ι C :=
    ((starMap ι C).symm).trans (congr_arg (MapB ι ·) h)
variable {ι}

-- lower gap at base E.LXE standardized 0. May change across paths.
def Clear (C : Matrix ι ι ℝ) (u:ℝ) := 1 ≤ u ∧ C.IsHermitian ∧ ∀ z:Sky ι, ‖z‖^2 ≤ u*⟪z, MapB ι C z⟫
lemma positive {C:Matrix ι ι ℝ} {u:ℝ} (h : Clear C u) : C.PosSemidef := by
  refine .of_dotProduct_mulVec_nonneg h.2.1 (fun x=>?_)
  let z : Sky ι:=WithLp.toLp 2 x
  have hz : star x=x:=rfl
  have hn := h.2.2 z; have hp :=h.1
  rw [Matrix.inner_toEuclideanCLM] at hn; change ‖z‖^2≤u* (x ⬝ᵥ C.mulVec x) at hn
  rw [hz]; 
  exact nonneg_of_mul_nonneg_right ((sq_nonneg _).trans hn) (zero_lt_one.trans_le hp)

-- base solves centered square root via mathlib real CFC sqrt. guaranteed SPD.
lemma cathedral {C:Matrix ι ι ℝ} {u:ℝ} (hu : Clear C u) (h : ‖MapB ι C‖ ≤ u) :
    ∃ H Q:Plate ι,H*Q=1 ∧ Q*H=1 ∧ H*star H=MapB ι C ∧ ‖Q‖≤u ∧ ‖H‖≤u := by
  have hr :=positive hu; let H:=MapB ι (CFC.sqrt C)
  have he : star H=H := (CFC.sqrt_nonneg C).isSelfAdjoint.map _
  have hH : H*star H=MapB ι C := by
    rw [he]; unfold H; rw [← map_mul, CFC.sqrt_mul_sqrt_self _ hr.nonneg];
  have hm :=hu.1
  have hy (x : Sky ι) : ⟪x,MapB ι C x⟫ = ‖H x‖^2 := (hH ▸ costGram ι H x).trans (by rw [he])
  have hh : ‖H‖≤u:=by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by linarith); intro x hx
    have ht:= real_inner_le_norm x (MapB ι C x); rw [hy,hx,one_mul] at ht
    have hl:‖MapB ι C x‖≤u:= ((MapB ι C).le_opNorm x).trans (by rw [hx,mul_one]; exact h)
    nlinarith
  have hv (x:Sky ι) : ‖x‖ ≤ u* ‖H x‖ := by
    have ha:=hu.2.2 x; rw [hy] at ha
    have hn: 0 ≤ u^2-u :=by nlinarith
    nlinarith [mul_nonneg hn (sq_nonneg ‖H x‖),mul_nonneg (by linarith:0≤u) (norm_nonneg (H x))]
  have ht:Injective H:=by
    intro x y h
    have hh:=hv (x-y); rw [map_sub,h,sub_self,norm_zero,mul_zero] at hh
    exact sub_eq_zero.mp (norm_le_zero_iff.mp hh)
  have hi:Bijective H.toLinearMap:= ⟨ht, (LinearMap.injective_iff_surjective (f:=H.toLinearMap)).1 ht⟩
  let J := (LinearEquiv.ofBijective H.toLinearMap hi).toContinuousLinearEquiv
  let Q : Plate ι := J.symm
  have hJ x : J x=H x:= rfl
  have hW : H*Q=1:= by ext1 x; exact J.apply_symm_apply x
  have hV : Q*H=1:= by ext1 x; exact J.symm_apply_apply x
  refine ⟨H,Q,hW,hV,hH,?_,hh⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (by linarith); intro x
  apply (hv (Q x)).trans_eq; rw [← hJ]; exact congr_arg (fun y=> u*‖y‖) (J.apply_symm_apply x)

lemma sky_law {C:Matrix ι ι ℝ} {B:Plate ι} (hb : B * star B=MapB ι C) :
    MeasurePreserving B (stdGaussian (Sky ι)) (multivariateGaussian (0:Sky ι) C) := by
  obtain ⟨X,hX⟩:=(MapB ι).surjective B
  change MapB ι X=B at hX
  have hC : X*star X=C:= (MapB ι).injective (show MapB ι (X*star X)=MapB ι C from by rw [map_mul, starMap,hX,hb])
  have h : C.PosSemidef := hC ▸ Matrix.posSemidef_self_mul_conjTranspose X
  constructor
  · exact B.continuous.measurable
  apply Measure.ext_of_charFun (E:=Sky ι); ext x
  have hG : (charFun (Measure.map B (stdGaussian (Sky ι)))) x = charFun (stdGaussian (Sky ι)) ((star B) x) := by
    rw [charFun_apply,charFun_apply,integral_map B.continuous.aemeasurable (by fun_prop)]
    apply integral_congr_ae; refine Eventually.of_forall (fun i=>?_)
    dsimp only
    rw [show ⟪B i,x⟫= ⟪i,(star B) x⟫ from (ContinuousLinearMap.adjoint_inner_right ..).symm]
  rw [hG,charFun_stdGaussian,charFun_multivariateGaussian h]
  have hw := costGram ι B x; rw [hb,Matrix.inner_toEuclideanCLM] at hw
  simp [hw,neg_div]

section LocalLayer
variable (Q : Plate ι) (x:E)

def front : Plate ι →L[ℝ] Plate ι := ContinuousLinearMap.compL ℝ (Sky ι) (Sky ι) (Sky ι) Q
def back : Plate ι →L[ℝ] Plate ι := (ContinuousLinearMap.compL ℝ (Sky ι) (Sky ι) (Sky ι)).flip (star Q)
omit [DecidableEq ι] in
lemma taxes : ‖front Q‖ ≤ ‖Q‖ ∧ ‖back Q‖ ≤ ‖Q‖ := ⟨ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun i => norm_mul_le ..),
   ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun i=> (norm_mul_le i (star Q)).trans_eq (by rw [costStrong,mul_comm])⟩



def crown (u:ℝ) (k:ℕ) := u*heats (u*(u*u)) k
lemma crown_ge {u:ℝ} (hu:1≤u) (k:ℕ):u≤ crown u k:=le_mul_of_one_le_right (zero_le_one.trans hu) (heats_pos (by positivity) _)


-- Price proof: assume eventual C mirror and gap at query. No derivative
-- assumptions on Gaussian distribution or over rest of fields.
theorem evades {C:E→Matrix ι ι ℝ} {u:ℝ} (hg : Clear (C x) u) (hd : ∀ᶠ z in 𝓝 x,(C z).IsHermitian)
    (hf : ContDiffAt ℝ k ((MapB ι) ∘ C) x) (hF : Envelope x k (MapB ι ∘ C) u) :
    ∃ F:E→Plate ι,ContDiffAt ℝ k F x ∧ Envelope x k F (crown u k) ∧ (∀ z,‖z‖ ≤ u * ‖F x z‖) ∧
       ∀ᶠ z in 𝓝 x, MeasurePreserving (F z) (stdGaussian (Sky ι)) (multivariateGaussian (0:Sky ι) (C z)) ∧ F z*star (F z)=MapB ι (C z) := by
  obtain ⟨H,Q,hH,hQ,hE,hq,h⟩:= cathedral hg hF.value
  let φ:=front Q; let b:=back Q; let c:=front H
  let R:= MapB ι ∘ C; let P:=b ∘ φ ∘ R
  have he (z:E) : P z=Q * MapB ι (C z)*star Q := rfl
  have hφ :=φ.contDiff.contDiffAt.comp x hf
  have hp := b.contDiff.contDiffAt.comp x hφ
  have hy : Envelope x k P (u*(u*u)) := Seas.paidLinear b hφ (Seas.paidLinear φ hf hF ((taxes Q).1.trans hq)) ((taxes Q).2.trans hq)
  have ha : P x=1:= by
    rw [he x, ←hE,← mul_assoc,hQ,one_mul,← starBoth, hQ,starPlate]
  have hw : ∀ᶠ z in 𝓝 x, star (P z)=P z:=by
    filter_upwards [hd] with z hz
    rw [he,starBoth,starBoth,with_mirror _ hz]
    rw [show star (star Q)=Q from ContinuousLinearMap.adjoint_adjoint Q,mul_assoc]
  obtain ⟨hM,hs,hB,hA⟩:= Kelps.costs P x hp ha hy hw
  let F:=c ∘ rise ∘ P
  have ht : F x =H:= by change H*rise (P x)=_; rw [hs,mul_one]
  refine ⟨F,c.contDiff.contDiffAt.comp _ hM,Seas.paidLinear c hM hB ((taxes H).1.trans h),fun z=>?_,?_⟩
  · rw [ht]; calc
      ‖z‖ = ‖Q (H z)‖ := by change _=‖(Q*H) z‖; rw [hQ]; rfl
      _ ≤ _ := (Q.le_opNorm _).trans (mul_le_mul_of_nonneg_right hq (norm_nonneg _))
  filter_upwards [hA] with z hz
  have hh : F z*star (F z)=MapB ι (C z) := by
    let G:=rise (P z)
    change H*G*star (H*G)=_
    rw [starBoth,mul_assoc, ←mul_assoc G,show G*star G=P z from hz,he]
    rw [← mul_assoc,← mul_assoc, ←mul_assoc, hH, one_mul,mul_assoc,← starBoth,hH, starPlate,mul_one]
  exact ⟨sky_law hh, hh⟩
end LocalLayer
end YM.Planned.PrimaryIntegral295.Tropics
