import YM.RG12.Spins.Brush
/-! connect sharp unscaled Hessian port to marginal rep & literate hQ.
 Used with Beet release on same k. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir.Payed
open Function Filter Set Lattice Wilson Pressure RG Precision Tree Next Next.SectorChange Next.Fluctuations WardBin.Lies
    Matrix Multi Multi.Vacuum.Jets Multi.Puff ProofPorts.CommonComplexProduction ProofPorts.CommonComplexProduction.Score
    SelectedOrderedKernels SelectedOrderedKernels.Sector FreeResolvent Next.SectorChange.Rows Wisps Push.SectorMeasure
open Planned.AtomRegular Foliage Next.Foundations AnalyticBridge.NonflatCovarianceLocality.Placement YM.RG12 Labels Source Source.Drops Planned.PrimaryIntegral295 Place
open AnalyticBridge.LocalGaussianLaws (gap_positive gapped_iff)
open AnalyticBridge.LocalGaussian (Peak)
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{t:ℝ}{I:Type}[Fintype I][DecidableEq I]{p n r:ℕ}{P B:BudgetPoint}{c f:Side}{o: Site f}{α β δ η d x u N C M R Y' L' X':ℝ}
variable {S:StepData c f}{T:Tube G S}{Pt:Teller G}{L:Tree.Forest S.ratio}{b:S.Choices}{q χ:Chi}{X:Support f}{Y:Support c}{A₀: Stores S}
   (m:Museum L x A₀ X Y I)(U:Config G f){C':Libretto G p}{D:Record}
   (hb:Plays C' D P B Pt T x) (ho:o∈X)(hs:PhysicalNext.JointLoad.Heir.Short S B X)
variable {e:ℕ}{U0:Labels.Frame G e}(N:SectionData U0)(a:U0.Index)(w:ℂ→L[ℝ]ℝ)
set_option quotPrecheck false
local notation "Z!"=> amended x A₀ (1:Config G c)
local notation "Wh"=> YM.PhysicalNext.JointLoad.Heir.scope B X r x
open AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset
-- all demand tangent miss or post-block capture. share.
theorem evening (J: Patch) (hp:J.Branches Pt.bind G)(p:ℕ):∀ᶠ x:ℝ in atTop,∀{c f:Side}(S:StepData c f)(T:Tube G S), S.patch=J → Lift.Booth Pt S T → 100*(1+radiusB x) ≤ c.val →∀ (F:Forest S.ratio)(b:S.Choices),
  ‖fderiv ℝ (display T F x b true) 0 - mainStroke T F true‖ ≤ (x^p)⁻¹:=by
    obtain ⟨r₀,D,h₀,hD,hS⟩:= survey G J Pt hp 2
    obtain ⟨R,Q,hR,hQ,hY⟩:=orchestra G J Pt hp 2 le_rfl
    obtain ⟨M,hm,hL⟩:= budget_expandBare G
    filter_upwards [hS,hY,Pace.dissent G J Pt hp (p+1),eventually_gt_atTop (max M 0)] with x hS hY hA hx c f S T hP hT hZ F b
    have hk:=hS S T hP hT.1 hZ F b 0 (norm_zero.le.trans h₀.le)
    have hf:=hA S T hP hT hZ F b
    rw [display_deriv (hk.smooth.differentiableAt (by norm_num)) (sub_eq_zero.mp hf.1 |>.trans (_root_.map_zero (first T F x))) true (((hY S T hP hT hZ F b).costs true).uniform 0 (norm_zero.le.trans hR.le) |>.smooth.differentiableAt (by norm_num)),add_sub_cancel_left]
    have hz:0<x:=lt_of_le_of_lt (le_max_right ..) hx
    apply ((ContinuousLinearMap.opNorm_comp_le ..).trans (mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_fst_le ..))).trans
    refine ((ContinuousLinearMap.opNorm_comp_le ..).trans (mul_le_mul (hL S F x) hf.2 (norm_nonneg _) hm)).trans ?_
    rw [pow_succ]; apply (mul_le_mul_of_nonneg_right (lt_of_le_of_lt (le_max_left M 0) hx).le (by positivity)).trans_eq; field_simp
-- pivotRay conv vs exact deterministic. need fderiv unscaled stencil bound before x.
local notation "JK" => (w ∘ Push.Local.presented N o B.threshold (Place.copy U0 a))
include hb
lemma merit (h:Bid.pop N)(hSlots:(U0.grades a).2=2)(hw:‖w‖ ≤1)(hr:P.threshold ≤2*B.threshold)(hn:4≤p)
     (hV:Through 4 (Spins.drawing N o a) 0 R)(H:‖fderiv ℝ (display T L x b true) 0-mainStroke T L true‖ ≤ M)(he:M≤1)(v v':Directions G c)(hl:P.dirBound (S.ratio.parent o) v)(hv:P.dirBound (S.ratio.parent o) v'):
       let φ':=Complex.ofRealCLM ∘ Repeat.Cub.deem o x T (JK)
       let ξ:=Spins.pivotRay G (Spins.converter (T:=T) (L:=L) (x:=x) (b:=b) N o a w (P.threshold/B.threshold)) P.threshold (S.ratio.parent o) (reach x) 0
       ‖leftDerivs ξ [v,v'] 1-leftDerivs φ' [v,v'] 1‖ ≤ 8*R*(D.Q+1)*(Cube.fee C'.Z*(1+((reach x:ℕ):ℝ))^(P.power*p))^2*M:=by
    intro φ' ξ
    let t:= P.threshold; let k:=B.threshold; let γ:=t/k; let W:=Complex.ofRealCLM.comp w; let f:=Spins.drawing N o a; let f':=W ∘ f
    have hh:0<t:=P.threshold_pos; have hτ:0<k:= B.threshold_pos
    have ha:0≤γ:=by unfold γ; positivity
    have hy:γ ≤2:=(div_le_iff₀ hτ).mpr hr
    let φ:Directions G _→ℂ:= γ^2 • f'
    have hvh: ‖W‖≤1:=by
      refine (ContinuousLinearMap.opNorm_comp_le ..).trans (mul_le_one₀ ?_ (norm_nonneg _) hw)
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro z; simp
    have hF : Through 4 φ 0 (4*R):=by
       refine ((linear_through W hV hvh).scale (γ^2)).mono ?_; rw [abs_of_nonneg (sq_nonneg _),one_mul]; exact mul_le_mul_of_nonneg_right (by nlinarith) hV.nonneg
    have he0:fderiv ℝ f 0=0:=by rw [← norm_eq_zero, ← norm_iteratedFDeriv_one, Spins.no_low N _ a h (show 1 < (U0.grades a).2 by omega),norm_zero]
    let T0:=display T L x b true; let p':=mainStroke T L true
    have hψ : fderiv ℝ φ 0=0:=by
       unfold φ; rw [fderiv_const_smul (W.differentiableAt.comp 0 (hV.smooth.differentiableAt (by norm_num)))] -- unfolding coercions
       change γ^2 • fderiv ℝ (W ∘ f) 0 = _; rw [fderiv_comp 0 W.differentiableAt (hV.smooth.differentiableAt (by norm_num)),he0]; ext v; simp
    let c':= Cube.fee C'.Z; have hk:=Cube.fee_one C'.Z; have hm:P.threshold>0:=hh
    let R0:= loom P (reach x) c'; have hR:0 ≤ R0:=by unfold R0 loom; positivity
    have ht:Tour T L x b p R0 D.Q:=(hb.acts L b).toTour.weaker hb.rehearsed.tensions.allows.le le_rfl
    have hE:= Spins.prompt  (T:=T) (L:=L) (x:=x) (b:=b) (P:=P) φ rfl (hF.smooth.of_le (by norm_num)) hψ (hF.pay _ (by decide)) ht hR D.majorant (by omega) H he (Repeat.Cub.posed C'.Z hb.rehearsed.wire (o:= S.ratio.parent o)) hk v v' hl hv
    have hφ : φ'= Spins.flash (φ∘p') t (S.ratio.parent o) (reach x):=by
       funext V; unfold φ' Repeat.Cub.deem Spins.flash Spins.pivotRay p' mainStroke; simp only [Function.comp_apply,_root_.add_apply,ContinuousLinearMap.comp_apply, ↓reduceIte, add_zero]
       rw [Spins.draw N o a,hSlots,w.map_smul]; change ↑((k^2)⁻¹ • w (_)) = (t^2)⁻¹ • γ^2 • W (f _) -- parse right
       rw [smul_smul,show (t^2)⁻¹*γ^2=(k^2)⁻¹ by unfold γ; field_simp]; change ((Complex.ofRealCLM) ((k^2)⁻¹ • w (_))) = (k^2)⁻¹ • Complex.ofRealCLM (w (f (_+(0:Directions G _)))); rw [add_zero,Complex.ofRealCLM.map_smul]; rfl
    rw [hφ]; apply hE.trans_eq; ring
end YM.PhysicalNext.JointLoad.Heir.Payed
