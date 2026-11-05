import YM.UVExtension.Span.Vials
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Strata
open Filter Function Metric Set RG Lattice Pressure Wilson Precision Exterior Push.AbsoluteSums Finset ConnectedActivityE6
open Push Bloch Next.Fluctuations Blaze Channel SliceRows Work.E03 Work.F03 Reward Laurent Tree
open Push SectorMeasure
open Pressure.Stores Pressure.Tube Scroll
open Progress.StationaryScenes Green Control Window Census Pulse Itinerary Coat Poll Pond AnalyticBridge.RelativeLogdet
open Blaze.Frond Steady
open scoped BigOperators Topology InnerProductSpace ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n c f L :Side}{S:StepData c f} {ι α β κ:Type}{v:Filter ι}
variable {qq: Filter κ} {T:ι→Tube G S} {w:ℝ} {X:Teller G}
    {Q: ConnectedActivityE6.Target G X} {U:Target.Order G w} {R:ι→ Rep G f}
    {s δ q η r W C B V f' a g u D' ψ Y ζ:ℝ} {k l:ℕ} {χ:Chi}
namespace Polish
open Matrix MeasureTheory WithLp Shield
section balls
variable {J: Type}[Fintype J] [DecidableEq J] {η b :ℝ}
-- input compact-nondegenerate uniform inverse; enough all hats w/B. exp dominates polynomial moments
-- around + profile
omit [DecidableEq J] in
lemma gaussian (t:ℝ)(hp:0<t): Integrable (fun x:Poll.Body J=> Real.exp (-t*‖x‖^2)):=by
   let e:ℂ:=t; have h:= GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (b:=e) (by exact hp) 0 (0:Poll.Body J)
   have ht (x:Poll.Body J) : Real.exp (-t*‖x‖^2)=‖Complex.exp (-e*(↑‖x‖:ℂ)^2+(0:ℂ)* ↑(inner ℝ (0:Poll.Body J) x:ℝ))‖:= by
      rw [zero_mul,add_zero]; rw [Complex.norm_exp]; unfold e; norm_cast
   simp_rw [ht]; exact h.norm
lemma gust (d r L:ℝ) (hD:0≤d)(hr:0<r)(hL:0<L) : ∃ P>0,∀ M∈ Minaret.Town (J:=J) d r, Bottom M⁻¹ L →∀ x: Poll.Body J, lens₀ M x ≤ P*Real.exp (-(L/2)*‖x‖^2):=by
    let q(M:Matrix J J ℝ):=(((Real.sqrt (2*Real.pi))^Fintype.card J)⁻¹ * Real.exp (-Real.log M.det/2))
    let K := Minaret.Town (J:=J) d r
    have hf i (hi:i∈K) : ContinuousAt q i:= continuousAt_const.mul (ContinuousAt.rexp (ContinuousAt.div_const (ContinuousAt.neg (continuous_id.matrix_det.continuousAt.log (Minaret.certified hi hr|>.det_pos.ne'))) _))
    obtain ⟨x,hx⟩:= (Minaret.suburbs d r).exists_bound_of_continuousOn (fun x hx=> (hf x hx).continuousWithinAt)
    refine ⟨|x|+1,by positivity,fun M hm h v=>?_⟩
    let b := dotProduct (ofLp v) (M⁻¹ *ᵥ ofLp v)
    have hV:(L/2)*(‖v‖^2) ≤ b / 2:=by
       have ht :dotProduct (ofLp v) (ofLp v)=‖v‖^2:=by simp_rw [EuclideanSpace.real_norm_sq_eq,dotProduct,pow_two] -- rfl?
       rw [div_mul_eq_mul_div]; exact div_le_div_of_nonneg_right ((congr_arg (L*·) ht.symm).trans_le (h _)) (by norm_num)
    calc
       _ = q M*Real.exp (-(b/2)):= by unfold lens₀ q b; rw [mul_assoc, ← Real.exp_add,sub_eq_add_neg]
       _ ≤ _:=by rw [neg_mul]; exact (mul_le_mul_of_nonneg_left (Real.exp_monotone (neg_le_neg hV)) (by unfold q; positivity)).trans (mul_le_mul_of_nonneg_right (((le_abs_self _).trans (hx M hm)).trans ((le_abs_self _).trans (le_add_of_nonneg_right zero_le_one))) (Real.exp_pos _).le)
lemma smoothL (k:ℕ)(M:Matrix J J ℝ) (x: Poll.Body J)(h:M.PosDef): ContDiffAt ℝ (↑k) (fun p:Matrix J J ℝ×Poll.Body J=> lens₀ p.1 p.2) (M,x):=by
    unfold lens₀; let L:=M⁻¹; let z:ℕ∞ω:=k
    have hx : ContDiffAt ℝ z (fun i:Matrix J J ℝ×Poll.Body J =>i.1⁻¹) (M,x):=((Push.Loops.inv_contDiffAt M (isUnit_iff_ne_zero.mpr h.det_pos.ne')).of_le le_top).comp (M,x) contDiffAt_fst
    have ht : ContDiffAt ℝ z (fun i:Matrix J J ℝ×Poll.Body J=> Real.log i.1.det) (M,x) := (((Push.Loops.det_contDiff.comp contDiff_fst).of_le le_top).contDiffAt.log h.det_pos.ne')
    have hp i: ContDiffAt ℝ z (fun p: Matrix J J ℝ×Poll.Body J=>ofLp p.2 i) (M,x):=((LinearMap.comp (LinearMap.proj i) (WithLp.linearEquiv 2 ℝ _).toLinearMap : Poll.Body J→ₗ[ℝ]ℝ).toContinuousLinearMap.contDiff.contDiffAt).comp (M,x) contDiffAt_snd
    apply ContDiffAt.mul contDiffAt_const; apply ContDiffAt.exp
    refine (ht.neg.div_const _).sub ?_; apply ContDiffAt.div_const _; unfold Matrix.mulVec dotProduct; apply ContDiffAt.sum; intro i _; refine (hp i).mul (ContDiffAt.sum ?_); intro j _
    let T:Matrix J J ℝ→ₗ[ℝ]ℝ:= { toFun:=fun M=>M i j,map_add':=fun M N=>rfl,map_smul':=fun M N=>rfl }
    exact (T.toContinuousLinearMap.contDiff.contDiffAt.comp (M,x) hx).mul (hp j)

-- σ = true beta. u=hat lower >0; η>0 bounds inverse. α covariance. uniform pdf at shifted real sheet.
open Span in
lemma sands (d r B t u b:ℝ) (ht:0<t) (hb:0 < b) (hu:t≤u) (hd:0≤d)(hr:0<r)(hB:0≤B)(k:ℕ): ∃ f':Poll.Body J→ℝ,Integrable f' ∧ (∀ i,0≤f' i) ∧ ∀ M∈ Minaret.Town (J:=J) d r, Bottom M⁻¹ b → ∀ v∈Set.Icc t u,∀ a:Poll.Body J, ‖a‖≤ B→∀ x:Poll.Body J,
    let y:=(gStep v)⁻¹ • (x-a); Wick.lint v (Fintype.card J)*lens₀ M y * (1+‖y‖)^k ≤ f' x:=by
  obtain ⟨P,hP,hH⟩:= gust (J:=J) d r b hd hr hb; let q:= b/2; have hq:0<q:=half_pos hb
  let C:= q/2; have hC:0<C:=half_pos hq
  obtain ⟨A,hA,hg⟩:= Span.Score.pays 1 zero_le_one C hC k
  have hx (z:ℝ)(h:0 ≤ z): (1+z)^k ≤ A*Real.exp (C*(z^2+1)):= by
     apply le_trans ?_ ((hg z h).trans ?_); exact le_of_eq (by rw [mul_one]); refine mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_left (by nlinarith : z≤z^2+1) hC.le)) hA
  let W:=Wick.lint u (Fintype.card J); have hw: 0<W:=Wick.lint_pos (ht.trans_le hu) _
  let K := W*P*(A*Real.exp C); have hK : 0≤K:=by unfold K; positivity
  let R:= Real.exp (C*t*B^2); have hR:0≤R:= Real.exp_nonneg _
  refine ⟨fun x=> K*R* Real.exp (-(C*t/2)*‖x‖^2),(gaussian _ (by positivity)).const_mul _,fun x=>by positivity,?_⟩
  intro M hm hg' v hv a ha x y
  have hv':0<v:= lt_of_lt_of_le ht hv.1
  have hy :‖y‖^2=v*‖x-a‖^2:=by unfold y gStep; rw [norm_smul,inv_inv,Real.norm_of_nonneg (Real.sqrt_nonneg _),mul_pow,Real.sq_sqrt hv'.le]
  have hf: ‖x‖^2/2-B^2 ≤ ‖x-a‖^2:=by
    have h:‖x‖≤‖x-a‖+B:= calc
        _ ≤ ‖x-a‖+‖a‖:=by simpa only [sub_add_cancel] using norm_add_le (x-a) a
        _ ≤ _:=by gcongr
    nlinarith only [pow_le_pow_left₀ (norm_nonneg _) h 2,sq_nonneg (‖x-a‖-B)]
  have hg : ‖x‖^2*t/2-t*B^2 ≤ ‖y‖^2 := by
     rw [hy]; nlinarith only [mul_le_mul_of_nonneg_left hf ht.le,mul_le_mul_of_nonneg_right hv.1 (sq_nonneg (‖x-a‖))]
  have hv' : Wick.lint v (Fintype.card J)≤W:=by unfold W Wick.lint gStep; simp_rw [inv_inv]; gcongr; exact hv.2
  calc
    _ ≤ W*(P*Real.exp (-q*‖y‖^2))*(A*Real.exp (C*(‖y‖^2+1))) := mul_le_mul (mul_le_mul hv' (hH M hm hg' _) (fullFuel _ _|>.le) hw.le) (hx _ (norm_nonneg _)) (by positivity) (by positivity)
    _ = K*Real.exp (-C*‖y‖^2):=by
        unfold K; have h: Real.exp (-q*‖y‖^2)*Real.exp (C*(‖y‖^2+1))=Real.exp C*Real.exp (-C*‖y‖^2):=by rw [←Real.exp_add,←Real.exp_add]; unfold C; congr 1; ring
        linear_combination W*P*A*h
    _ ≤ _ := by change _ ≤ K*R*_; rw [mul_assoc K R]; apply mul_le_mul_of_nonneg_left _ hK; unfold R; rw [← Real.exp_add]; exact Real.exp_monotone (by nlinarith only [mul_le_mul_of_nonneg_left hg hC.le])
end balls
end Polish
end YM.UVExtension.Strata
