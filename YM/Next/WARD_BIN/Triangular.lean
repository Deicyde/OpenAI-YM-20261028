import YM.Next.WARD_BIN.Supported
import YM.Next.WARD_BIN.Taper
import YM.Work.G05


/-!
# The leading block of the equation family

Use the alternative construction by `sample`: constrain a radial complement by
*linear combinations* of lattice Euler samples; multiply via finite multilinearity.
Enough to be triangular in the same **factor** block. We don't claim the stronger
leading engineering statement for these nonlinear stencils. This suffices because
the actual precision uses `frame.scaled`, paying factor degree.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WardBin
open Function Set Filter MeasureTheory Wilson Lattice RG Source Source.Drops Labels Work.G05 Bid Maxwell
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {d l n m : ℕ} {H : Hol G}

namespace Rays
variable (R : Rays G d H)

/-- Two first variations: `predict` need not preserve degree, but knows through
any slot exact response on all *lower* degree+same degree inputs. -/
def predict : Snap G d →L[ℝ] Snap G d := R.lifts.comp (ContinuousLinearMap.pi (fun e => linearSample H e.val))

private lemma rayDiff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (v : F) :
    HasDerivAt (fun t : ℝ => t • v) v 0 := by simpa using! (hasDerivAt_id' (0:ℝ)).smul_const v

private lemma radial_limit {E F Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (A : E) (P : E → F) (T : E →L[ℝ] F) (X : F →L[ℝ] Z) (hX) (ht : HasFDerivAt P T 0) (h : P 0=0)
    (hp : X (T A) = hX) : Tendsto (fun t : ℝ => t⁻¹ • X (P (t • A))) (𝓝[>] (0:ℝ)) (𝓝 hX) := by
  have he := X.hasFDerivAt.comp_hasDerivAt 0 (ht.comp_hasDerivAt_of_eq 0 (rayDiff A) (by simp))
  exact value_scale (f:=fun t : ℝ => X (P (t • A))) (he.congr_deriv hp) (by rw [zero_smul,h,map_zero])

lemma guess_limit (A : Snap G d) :
    Tendsto (fun t : ℝ => t⁻¹ • R.guess (curve H (t • A))) (𝓝[>] (0:ℝ)) (𝓝 A) := by
  let P := bring H d R.slots
  have he : AnalyticAt ℝ P 0 := AnalyticAt.pi fun i => R.point (R.slots i)
  change Tendsto (fun t : ℝ => t⁻¹ • R.read (P (t • A))) _ _
  exact radial_limit A P (fderiv ℝ P 0) R.read.toContinuousLinearMap A
    he.differentiableAt.hasFDerivAt (funext fun i => (takes_zero H d (R.slots i))) (R.back A)

lemma predict_limit (A : Snap G d) :
    Tendsto (fun t : ℝ => t⁻¹ • R.gap (curve H (t • A))) (𝓝[>] (0:ℝ)) (𝓝 (R.predict A)) := by
  let B : Snap G d → (e : R.edg) → G.Color := fun J e => sample e.val (curve H J)
  let Y := ContinuousLinearMap.pi (fun e : R.edg => linearSample H (d:=d) e.val)
  have hd : HasFDerivAt B Y 0 := hasFDerivAt_pi'.mpr fun i => by
    let f := fun x : Snap G d => sample i.val (curve H x)
    have he : HasFDerivAt f (linearSample H i.val) 0 := (sample_germ H d i.val).differentiableAt.hasFDerivAt
    rw [show (ContinuousLinearMap.proj i).comp Y = linearSample H i.val by ext1; rfl]; exact he
  refine radial_limit A B Y R.lifts (R.predict A) hd ?_ rfl
  funext i
  simp only [B,curve_zero,sample,euler,wheel,Pressure.one,G.curvature_unit,
    add_zero,Finset.sum_const_zero, map_zero]; rfl

variable (M : Tensor.T (Snap G d) ℂ (l+1))

lemma slot_leading (A : Snap G d) : Tensor.diagonal (Tensor.coeff ((R.force M) ∘ curve (d:=d) H) (l+1) 0) A =
    Tensor.diagonal M A - Tensor.diagonal M (A-R.predict A) := by
  obtain ⟨S,hS⟩:=R.fitsAt_support
  let F := R.force M ∘ curve (d:=d) H
  have hf : ContDiffAt ℝ ((l+1:ℕ):WithTop ℕ∞) F 0 :=
    ((R.force_affordable hS M).smooth_poly H d).of_le (WithTop.coe_le_coe.mpr le_top)
  rw [← leading_tensor A (R.force M ∘ curve H) hf]
  have hx : ContDiffAt ℝ ((l+1:ℕ):WithTop ℕ∞) (fun t : ℝ => t • A) 0 := by simpa using (monoSmooth A 1 _|>.contDiffAt (x:=0))
  apply leading_of_lim ((show ContDiffAt ℝ (↑(l+1:ℕ) : WithTop ℕ∞) F ((0:ℝ) • A) by rw [zero_smul]; exact hf).comp 0 hx)
  have ha := R.guess_limit A
  have h := (Tensor.diag_smooth M ∞).continuous
  apply (((h.tendsto A).comp ha).sub
    ((h.tendsto (A-R.predict A)).comp (ha.sub (R.predict_limit A)))).congr'
  refine Eventually.of_forall fun t => ?_
  change Tensor.diagonal M (t⁻¹ • _) - Tensor.diagonal M (t⁻¹ • _ - t⁻¹ • _) = _
  have he {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (u v : E) (M : Tensor.T E ℂ (l+1)) :
      Tensor.diagonal M (t⁻¹ • u) - Tensor.diagonal M (t⁻¹ • u - t⁻¹ • v) =
      (t^(l+1))⁻¹ • (Tensor.diagonal M u-Tensor.diagonal M (u-v)) := by rw [← smul_sub,Tensor.homogeneous, Tensor.homogeneous M _ t⁻¹,inv_pow,← smul_sub]
  exact he (R.guess (curve H (t • A))) _ M

set_option maxHeartbeats 400000 in
/-- Split the weighted projection of `predict` on a scaled input so we can take
`+0` radial limit without treating an unbounded divided input as convergent. -/
theorem predict_scale (A : Snap G d) : ∃ f : ℝ → Snap G d,
    Tendsto f (𝓝[>] (0:ℝ)) (𝓝 (R.origin A : Snap G d)) ∧
    ∀ t, engineered t (f t) = engineered t A-R.predict (engineered t A) := by
  let I := Fin (d-1)
  let v (i : I) : Snap G d := Pi.single i (A i)
  let F t (i : Fin (d-1)) := A i -
    ∑ j : I, (t:ℝ)^(j.val-i.val) • R.predict (v j) i
  have hg (j i : I) (hj : j.val < i.val) : R.predict (v j) i = 0 := by
    have hV : v j∈through G d i.val := fun k hk => Pi.single_eq_of_ne (show k≠ j by intro h; rw [h] at hk; omega) _
    rw [show R.predict (v j) i=_ from R.triangular _ i hV, show v j i = 0 from Pi.single_eq_of_ne (fun H => hj.ne' (congr_arg Fin.val H)) _,map_zero]
  have ht (i : I) : R.predict (v i) i=R.T i (A i) := by
    have hV : v i∈through G d i.val := fun k hk => Pi.single_eq_of_ne (show k≠i by intro h; rw [h] at hk; omega) _
    rw [show R.predict (v i) i=_ from R.triangular (v i) i hV]; simp [v]
  have he (t : ℝ) : (∑ j : I, t^(j.val+2) • v j) = engineered t A := by
    funext i; rw [Finset.sum_apply, Finset.sum_eq_single i]
    · simp only [Pi.smul_apply, v,Pi.single_eq_same]; rfl
    · intro j _ hj; simp only [v,Pi.smul_apply,Pi.single_eq_of_ne hj.symm, smul_zero]
    simp
  refine ⟨F,tendsto_pi_nhds.mpr (fun i => ?_),fun t => ?_⟩
  · have H0 : F 0 i= R.origin A i := by
      unfold F; rw [Finset.sum_eq_single i]
      · rw [Nat.sub_self,pow_zero,one_smul,ht]; rfl
      · intro j _ hj
        rcases lt_or_gt_of_ne (show j.val≠i.val from Fin.val_ne_of_ne hj) with h|h
        · rw [hg _ i h,smul_zero]
        rw [zero_pow (Nat.sub_ne_zero_of_lt h),zero_smul]
      simp
    have hf : Continuous (fun t => F t i) := continuous_const.sub
      (continuous_finsetSum _ fun j _ => (monoSmooth (R.predict (v j) i) (j.val-i.val) 1).continuous)
    rw [← H0]; exact (hf.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  funext i; rw [Pi.sub_apply,engineered_at]; unfold F; rw [smul_sub,engineered_at, sub_right_inj, ← he, map_sum,Finset.sum_apply,Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul,Pi.smul_apply]
  rcases lt_or_ge j.val i.val with hv|hv
  · rw [hg _ i hv,smul_zero,smul_zero,smul_zero]
  rw [smul_smul,← pow_add, show i.val+2+(j.val-i.val) = j.val+2 by omega]

lemma residual_shell (A : Snap G d) : ∃ X : TaylorTower G, expand d (R.origin A) = fun i => gaugeJet (X i) := by
  classical
  let B := R.origin A
  have he (i : Fin (d-1)) : takeCurl (B i) ∈ onShell G.Color i.val := R.constrained i (A i)
  refine ⟨fun j => if h : j < d-1 then (⟨takeCurl (B ⟨j,h⟩),he _⟩ : Shell G j) else 0, ?_⟩
  funext i; by_cases h : i < d-1
  · simp only [dif_pos h,expand]; exact (potential_recover (B ⟨i,h⟩)).symm
  simp only [expand,dif_neg h,map_zero]
end Rays


abbrev evaluateLabel (p : Label G d) (J : Snap G d) := Labels.read (expand d J) p.val

lemma eval_eng (p : Label G d) (J : Snap G d) (t : ℝ) (hp : p∈Grade (n,l)) :
    evaluateLabel p (engineered t J) = t^n • evaluateLabel p J := by unfold evaluateLabel; rw [← expand_jet, scaled_grade t _ _ hp]

/-- Correspondence to a real multilinear form (with complex output). -/
def toTensor (l : ℕ) (p : Label G d) := Tensor.coeff (evaluateLabel p) l 0

lemma eval_diag {p : Label G d} (hp : p∈Grade (n,l)) (J : Snap G d) : Tensor.diagonal (toTensor l p) J = evaluateLabel p J := by
  have he (t : ℝ) : evaluateLabel p (t • J) = t^l • evaluateLabel p J := by
    unfold evaluateLabel; rw [expand_smul,multiplied_grade t _ _ hp]
  unfold toTensor; rw [← leading_tensor, funext he, lead_monomial, if_pos rfl]
  exact (snap_read_smooth d p.val _).contDiffAt

def CastL (u : G.El) : Snap G d→L[ℝ] Snap G d where
  toFun := Cast u
  cont := Cast_cont
  map_add' a b := funext fun i => map_add _ (a i) (b i)
  map_smul' t a := funext fun i => map_smul _ t (a i)

private lemma invariant_sym {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : Tensor.T E ℂ n) (L : E →L[ℝ] E) (hs : Tensor.Sym T)
    (h : ∀ v, Tensor.diagonal T (L v)=Tensor.diagonal T v) (a) : T (fun i => L (a i)) = T a := by
  let Q := T.compContinuousLinearMap fun _ => L
  have ht : Q = T := Tensor.ext_diag Q T (fun v s => hs (fun i => L (v i)) s) hs (funext h)
  exact DFunLike.congr_fun ht a

lemma tensor_eqv {p : Label G d} (hp : p∈Grade (n,l+1)) : Rays.covariantTensor (toTensor (l+1) p) := by
  intro u a
  let T := toTensor (l+1) p
  have hs : Tensor.Sym T := Tensor.coeff_symm ((snap_read_smooth d p.val _).contDiffAt)
  apply invariant_sym T (CastL u) hs _ a
  intro v; change Tensor.diagonal T (Cast u v) = Tensor.diagonal T v; unfold T
  rw [eval_diag hp,eval_diag hp]; unfold evaluateLabel; rw [expand_color]
  exact p.property.2 ..

namespace Rays

variable (R : Rays G d H) {p : Label G d} (hp : p∈Grade (n,l+1)) (hx : p∈equationIdeal G d)

include hp hx

lemma engineering_jet (A : Jet G) (ha : m≤n) :
    leading m (fun t : ℝ => Tensor.diagonal
      (Tensor.coeff (R.force (toTensor (l+1) p) ∘ curve (d:=d) H) (l+1) 0)
        (engineered t (trunk d A))) = if m=n then Labels.read A p.val else 0 := by
  let K := Tensor.coeff (R.force (toTensor (l+1) p) ∘ curve (d:=d) H) (l+1) 0
  let B := trunk d A
  let q (t : ℝ) := Tensor.diagonal K (engineered t B)
  have hs : Tendsto (fun t : ℝ => (t^n)⁻¹ • q t) (𝓝[>] 0) (𝓝 (Labels.read A p.val)) := by
    obtain ⟨g,hg,hB⟩ := R.predict_scale B
    have ht : Tendsto (fun t => evaluateLabel p (g t)) (𝓝[>] 0) (𝓝 (evaluateLabel p (R.origin B))) :=
      ((snap_read_smooth d p.val ∞).continuous.tendsto _).comp hg
    have hu : evaluateLabel p (R.origin B) = 0 := by
      unfold evaluateLabel; obtain ⟨X,hX⟩ := R.residual_shell B; rw [hX]; exact ideal_meaning.mp hx X
    have he := (tendsto_const_nhds (x:= Labels.read A p.val)).sub ht
    rw [hu,sub_zero] at he
    apply he.congr'
    filter_upwards [self_mem_nhdsWithin (s:=Ioi (0:ℝ))] with t ht
    have hv : 0<t:=ht
    unfold q K; rw [R.slot_leading,← hB,eval_diag hp,eval_diag hp,eval_eng _ B _ hp, eval_eng _ _ _ hp]
    rw [← smul_sub,inv_smul_smul₀ (pow_ne_zero n hv.ne')]; exact congrArg (fun c : ℂ => c-_) (racts p A).symm
  have h (n : ℕ) : ContDiffAt ℝ (n:WithTop ℕ∞) q 0 :=
    (Tensor.diag_smooth K (n:WithTop ℕ∞)).comp_contDiffAt _ (eng_cont B _|>.contDiffAt)
  change leading m q= _; rcases eq_or_lt_of_le ha with ha|ha
  · rw [ha, if_pos rfl]; exact leading_of_lim (h n) _ hs
  · rw [if_neg ha.ne]; exact leading_of_lim (h m) 0 (falls ha hs)

/-- The factor-`l+1` part has the chosen equation label precisely in
engineering degree n and none below. Use with `Taper.crownAt_below`.
No rank or epsilon conjecture involved. -/
theorem computes {S} (Y : R.FitsAt S) (t : n≤d) (ht : m ≤ n) :
    let T := toTensor (l+1) p
    let Q := R.force_affordable Y T
    crownAt H Q (R.force_gauge T (tensor_eqv hp)) d (l+1) m = if m=n then p else 0 := by
  intro T Q; apply Subtype.ext
  apply eval_ext; intro A
  rw [crownAt_ok _ _ _ _ (ht.trans t),crown, ← tile_reads, R.engineering_jet hp hx _ ht]
  split_ifs with hi
  · rfl
  exact (map_zero _).symm

end Rays
end YM.WardBin
