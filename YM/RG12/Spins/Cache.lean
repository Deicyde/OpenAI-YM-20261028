import YM.RG12.Spins.Sundial
import YM.RG12.Spins.Forte

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
open Extra.Iteration Extra.Iteration.Scales
local notation "μ_0" => AnalyticBridge.LocalGaussian.Moments.meter
private lemma legal (G:Gauge)(L: Side) (ε:ℝ)(he:0<ε){K:ℝ}(hK:0<K)(j:ℕ) :∀ᶠ x in atTop, ∀ β:ℝ, betaF G x L / 2 ≤ β→ 0<coupling β ∧ Noise.fade (ε*fiery G x L) (coupling β) K ≤ (x^j)⁻¹ ∧ coupling β^2 ≤ 4/x :=by
    let a:=G.slopeConstant*Real.log (L.val:ℝ); let c:= K⁻¹/4*(ε/16)^2; have hc:0<c:=by unfold c; positivity
    filter_upwards [second a c (j:ℝ) 0 0 hc 0,eventually_gt_atTop (max (-(2*a)) 0)] with x hx ht β hb
    let y:=x+a; have hv:0<x:=lt_of_le_of_lt (le_max_right ..) ht; have hw:x ≤ 2*y:=by unfold y; linarith [le_max_left (- (2*a)) 0];
    have hY:0<y:=by linarith; -- lean dot
    change y/2 ≤ _ at hb; have hβ:0<β:=by linarith
    let t:= coupling y; let d:=coupling β; have hd:0<d:=coupling_pos hβ; have hδ:0<t:=coupling_pos hY
    have hy:d ≤ 2*t:=by
       unfold d t coupling; rw [inv_le_iff_one_le_mul₀ (Real.sqrt_pos.mpr hβ),← div_eq_mul_inv,div_mul_eq_mul_div,le_div_iff₀ (Real.sqrt_pos.mpr hY),one_mul]; nlinarith [Real.sq_sqrt hY.le, Real.sq_sqrt hβ.le, Real.sqrt_nonneg β]
    simp only [zero_mul,zero_add,Real.exp_zero,pow_zero,div_one,one_mul,Real.rpow_neg hv.le,Real.rpow_natCast] at hx
    refine ⟨hd, ?_,?_⟩
    · apply le_trans _ hx; unfold Noise.fade; apply Real.exp_monotone; unfold c; rw [neg_mul, neg_mul]; change -(_*(ε*(t*meter y)/(8*d))^2) ≤ _; rw [mul_assoc (K⁻¹/4),← mul_pow];
      gcongr
      · exact mul_nonneg (by linarith) (meter_pos _).le
      apply (le_div_iff₀ (by positivity)).mpr; have hGG:= mul_le_mul_of_nonneg_left hy (show 0≤ε*meter y from mul_nonneg he.le (meter_pos _).le); linarith only [hGG]
    unfold coupling; rw [inv_pow,Real.sq_sqrt hβ.le, ← one_div,div_le_div_iff₀ hβ hv]; linarith

protected def arcM (G:Gauge)(r:ℕ) (L:Side)(x:ℝ):ℝ:= Lute.season G L * Lute.bulk 1 r x^4
protected def plumeM (r b:ℕ)(Z:ℝ)(x:ℝ):ℝ:= Z*((Lute.bulk 1 r x)^b)^2
protected def foeM (G:Gauge)(r b:ℕ)(L:Side)(Z:ℝ)(x:ℝ) :ℝ:= 2*2*(1+Payed.arcM G r L x^2*(Payed.plumeM r b Z x+1)*Payed.plumeM r b Z x)
-- cost algebra
lemma postage (r b:ℕ)(G:Gauge)(L :Side)(A:ℝ)(hA : 0≤A) : let F := fun x=>Lute.bulk 1 r x
    Tiny id F ∧ Tiny id (Payed.arcM G r L) ∧ Tiny id (Payed.plumeM r b A) ∧ Tiny id (Payed.foeM G r b L A):=by
    intro F
    have hb:(r+48:ℝ)≥0:=by positivity
    have hB:Tiny id F:=by
       exact (((Tiny.const tendsto_id _ hb).mul Tiny.cover_size tendsto_id).mul (Tiny.const tendsto_id _ (by positivity)) tendsto_id) -- defeq?
    have h0:=Lute.season_nn G L
    have hC:Tiny id (Payed.arcM G r L):=(Tiny.const tendsto_id _ h0).mul (hB.pow tendsto_id 4) tendsto_id
    have hz:Tiny id (Payed.plumeM r b A):=(Tiny.const tendsto_id _ hA).mul ((hB.pow tendsto_id b).pow tendsto_id 2) tendsto_id
    have hi:= Tiny.const (g:=id) tendsto_id 1 zero_le_one
    exact ⟨hB,hC,hz,(Tiny.const tendsto_id ((2:ℝ)*2) (by norm_num)).mul (hi.add (((hC.pow tendsto_id 2).mul (hz.add hi tendsto_id) tendsto_id).mul hz tendsto_id) tendsto_id) tendsto_id⟩
protected def growM (j:ℕ)(δ x:ℝ):ℝ:= (1+x)*((1+x)^j* AnalyticBridge.LocalGaussian.Moments.inflate j (δ⁻¹/8))*2
lemma plumeG (G:Gauge)(j r:ℕ)(L:Side){δ:ℝ}(hd:0≤δ):Tiny id (fun x=>Payed.growM j δ (Payed.arcM G r L x)) := by
     have h:= (postage r 0 G L 1 zero_le_one).2.1
     have hz:= (Tiny.const tendsto_id 1 zero_le_one).add h tendsto_id
     let X:= AnalyticBridge.LocalGaussian.Moments.inflate j (δ⁻¹/8); have hi :Tiny id (fun _=>X):= Tiny.const tendsto_id _ (by unfold X AnalyticBridge.LocalGaussian.Moments.inflate; positivity)
     exact (hz.mul ((hz.pow tendsto_id j).mul hi tendsto_id) tendsto_id).mul (Tiny.const tendsto_id _ zero_le_two) tendsto_id
set_option quotPrecheck false
local notation "G!" a => Payed.growM 6 D.K a
local notation "P#" x => (P * ( (1+((reach x:ℕ):ℝ))^(η*n)))
protected def wax (t:ℝ)(b p:ℕ)(x:ℝ) := t*(1+((reach x:ℕ):ℝ))^(b*p)
lemma waxG (b p:ℕ){t:ℝ}(h:0≤t):Tiny id (Payed.wax t b p):=by
    unfold Payed.wax reach; push_cast
    have hu:= (Tiny.const tendsto_id 1 zero_le_one).add ((Tiny.const tendsto_id (45:ℝ) (by norm_num)).mul Tiny.cover_size tendsto_id) tendsto_id
    exact (Tiny.const tendsto_id _ h).mul (hu.pow tendsto_id _) tendsto_id
-- small budget aggregate cost with thermal
local notation "carG"=> Fintype.card G.ColorIndex
lemma concertG (r b p:ℕ)(L:Side){t C M Q W η:ℝ}(ht:0≤t)(hd:0≤C)(hW:0≤W)(hM:0≤M)(hQ:0≤Q)(hη:0<η):
   let K:=Payed.arcM G r L; let F:=Payed.foeM G r b L t; let B:=Payed.wax W b p
   ∀ᶠ x:ℝ in atTop, ∀ β:ℝ,betaF G x L/2 ≤ β → let f:=Noise.fade (D.ε*fiery G x L) (coupling β) D.K
   let H:= Spins.reserve Q (B x); let Y:=8*C*(D.Q+1)*B x^2
   0<coupling β ∧ (M+Y)*(2*f*K x*2^carG)+(F x+1)^2*(coupling β*H)^2*(G! (K x))+Y*(x^1)⁻¹ ≤ x^η/x:=by
     intro K F B
     let V:=fun x=>8*C*(D.Q+1)*B x^2
     let H:=fun x=>Spins.reserve Q (B x)
     have hY':=D.majorant; have hK:=D.peak
     have hA:= postage r b G L t ht
     have hG:=waxG b p hW
     have hQ':Tiny id V:=(Tiny.const tendsto_id (8*C*(D.Q+1)) (by positivity)).mul (hG.pow tendsto_id 2) tendsto_id
     have hi :Tiny id (fun _=>1):=Tiny.const tendsto_id _ zero_le_one
     have hH:Tiny id H:=hi.add ((Tiny.const tendsto_id (Q*patterns 2) (by positivity [patterns_nonneg 2])).mul (hG.pow tendsto_id 2) tendsto_id) tendsto_id
     filter_upwards [legal G L D.ε D.guards (zero_lt_one.trans_le hK) 1,
        (((((Tiny.const tendsto_id M hM).add hQ' tendsto_id).mul (((Tiny.const tendsto_id (2:ℝ) zero_le_two).mul hA.2.1 tendsto_id).mul (Tiny.const tendsto_id ((2:ℝ)^carG) (by positivity)) tendsto_id) tendsto_id).add ((((hA.2.2.2.add hi tendsto_id).pow tendsto_id 2).mul ((Tiny.const tendsto_id (4:ℝ) (by norm_num)).mul (hH.pow tendsto_id 2) tendsto_id) tendsto_id).mul (plumeG G 6 r L (δ:=D.K) (by positivity)) tendsto_id) tendsto_id).add hQ' tendsto_id) _ hη,eventually_gt_atTop (0:ℝ)] with x h hX hx β hb f W' Y'
     obtain ⟨he,hδ,hy⟩:=h β hb
     have hv:B x ≥0:=by unfold B Payed.wax; positivity
     have hV:V x ≥0:=by unfold V; positivity
     have hg0: K x ≥0:=by unfold K Payed.arcM Lute.season; positivity
     have hg: 0 ≤ (G! (K x)):=by unfold Payed.growM AnalyticBridge.LocalGaussian.Moments.inflate; positivity
     refine ⟨he, (le_div_iff₀ hx).2 <| le_trans ?_ hX.2⟩
     have hF: f*x ≤1:=by unfold f; rw [pow_one, ← one_div,le_div_iff₀ hx] at hδ; exact hδ
     rw [le_div_iff₀ hx] at hy; rw [mul_pow,pow_one];
     change _ ≤ (M+V x)*(2*K x*2^carG)+(F x+1)^2*(4*H x^2)*(G! (K x))+V x
     calc
      _ = (M+V x)*(2*K x*2^carG)*(f*x)+(F x+1)^2*H x^2*(G! (K x))*((coupling β)^2*x) + V x:=by change ((M+_)*(2*f*K x*2^carG)+(F x+1)^2*((coupling β)^2*H x^2)*_+V x*x⁻¹)*x= _; field_simp; ring
      _ ≤ _:=by nlinarith only [mul_le_mul_of_nonneg_left hF (show 0≤ (M+V x)*(2*K x*2^carG) by positivity),mul_le_mul_of_nonneg_left hy (show 0≤(F x+1)^2*H x^2*(G! (K x)) by positivity)]
end YM.PhysicalNext.JointLoad.Heir.Payed
