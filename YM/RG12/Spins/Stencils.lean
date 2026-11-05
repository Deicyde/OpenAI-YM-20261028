import YM.RG12.Spins.Muse
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cub.Finery
/-! # True canonical two-factor chart suppliers for the Hessian bill. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Spins
open Next.Foundations
open Function Filter Set Lattice Wilson Pressure RG Push.SectorMeasure
open Multi Multi.Vacuum.Jets Multi.Puff WardBin.Lies
open Planned.PrimaryIntegral295 Place Source Source.Drops Labels Metric
set_option maxHeartbeats 800000
open PhysicalNext.JointLoad.Heir PhysicalNext Next Next.SectorChange Next.SectorChange.Rows Wisps Next.Fluctuations AnalyticBridge.SectorAffine.Offset AnalyticBridge.LocalGaussian.Moments
open Finset Planned.AtomRegular Foliage MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{κ:ℝ}{f c:Side}{A K C u d x:ℝ}{m p:ℕ}{S:StepData c f}{T:Tube G S}{L:Tree.Forest S.ratio}{b:S.Choices}
    {Fr:Labels.Frame G m} (F:SectionData Fr) (o:Site f)(a:Fr.Index)
section grids
local notation "TX"=>F.stencil
-- all stencil points are requested
protected noncomputable def slip:Directions G f →L[ℝ] Dev (TX) G :=ContinuousLinearMap.pi fun i=> ContinuousLinearMap.proj ((wrap f (Place.placeEdge i).1+o),(Place.placeEdge i).2)
local notation "J!"=> Spins.slip F o
lemma slim: ‖J!‖ ≤ 1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v=> by rw [one_mul]; exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun i=> norm_le_pi_norm v _))
protected noncomputable def drawing (a:Fr.Index): Directions G f→ℂ:= Place.column F a ∘ Spins.slip F o
local notation "stmt!"=> Push.Local.presented F o κ (Place.copy Fr a)
lemma draw {κ:ℝ} (y:Directions G f): (Push.Local.presented F o κ (Place.copy Fr a) (increment 1 y))= (κ^(Fr.grades a).2)⁻¹ • Spins.drawing F o a y:= by
   let v:=Fr.scaled κ⁻¹ (Place.copy Fr a)
   have he: v=(((κ^(Fr.grades a).2)⁻¹:ℝ):ℂ) • Place.copy Fr a:=by ext1 i; by_cases hi:i=a <;> simp [v,hi,Place.copy]
   unfold Push.Local.presented; change F.places v o _ = _; rw [he]; unfold SectionData.places SectionData.evaluate; rw [map_smul,map_smul]; rw [Complex.real_smul]; refine congr_arg (fun i=>(_ * (i:ℂ))) ?_
   change F.places (Place.copy Fr a) o _= F.evaluate (Place.copy Fr a) _
   apply F.cylinder_local
   intro e hh hv; unfold Place.pore; split; swap; · next h => exact (h ⟨hh,hv⟩).elim
   unfold Lattice.expandAt increment; simp only [Pi.one_apply,mul_one]; rfl
-- Uniform unscaled chart ops of canon through fixed order. before L entirely.
include a
local notation "D!"=> Spins.drawing F o a
lemma uniform {n:ℕ} : ∃ M:ℝ,0 ≤ M∧ ∀ (f:Side)(o:Site f)(v:Directions G f), ‖v‖ ≤ 1→ Through n (Spins.drawing F o a) v M:= by
    haveI:=FiniteDimensional.proper ℝ (Dev F.stencil G)
    obtain ⟨M,hM,HE⟩:=Push.Uniform.exists_allows (f:=Place.column F a) (isCompact_closedBall (0:Dev F.stencil G) 1) (fun x hx=> (Place.column_smooth ..).contDiffAt) n
    refine ⟨M,hM,fun f o z hz=> pre_through _ (slim F o) z (.control (HE _ (by rw [mem_closedBall_zero_iff]; exact ((Spins.slip F o).le_opNorm _).trans (mul_le_one₀ (slim F o) (norm_nonneg _) hz))))⟩
lemma no_low {q:ℕ}(hLi:Bid.pop F)(hq:q<(Fr.grades a).2): iteratedFDeriv ℝ q (D!) 0=0:= by
   unfold Spins.drawing
   rw [ContinuousLinearMap.iteratedFDeriv_comp_right _ (Place.column_smooth ..) _ le_top, (J!).map_zero,Place.radials_vanish F hLi a q hq]; rfl
end grids
-- charter
variable (hLi:Bid.pop F)(hslots:(Fr.grades a).2=2)(w:ℂ →L[ℝ] ℝ)(hw:‖w‖ ≤ 1)
local notation "D!"=> Spins.drawing F o a
protected noncomputable def converter (w:ℂ →L[ℝ] ℝ) (γ:ℝ) (v:Deck G c f):ℂ:= γ^2 • ((w (D! (display T L x b true v))):ℂ)
local notation "ω!" t => Spins.converter (T:=T) (b:=b) (x:=x) (L:=L) F o a w t
lemma pin {t t':ℝ}(hk:(Fr.grades a).2=2)(v:Deck G c f): (ω! (t/t')) v=t^2 • ((w (Push.Local.presented F o t' (Place.copy _ a) (increment (1:Config G f) (display T L x b true v)))):ℂ) := by
    unfold Spins.converter; rw [draw F o a,hk,w.map_smul, Complex.real_smul,Complex.real_smul]; push_cast; rw [smul_eq_mul]; push_cast; rw [div_pow]; ring -- inv_smul etc
include hLi hslots
lemma angels (hQ:1≤K):∃ C:ℝ,1≤C∧∀{c f:Side}{S:StepData c f}{T:Tube G S}{L:Tree.Forest S.ratio}{b:S.Choices}{x z t t':ℝ}{p:ℕ}{w:ℂ→L[ℝ]ℝ}(o:Site f),0<t → t ≤ 2*t' → ‖w‖ ≤1 → z≥0 → Tour T L x b p z K → K*z ≤ 1→4 ≤ p→
      let f':= Spins.converter (T:=T) (b:=b) (x:=x) (L:=L) F o a w (t/t')
      (∀ v:Deck G c f, ‖v‖ ≤ z → Through 4 f' v C) ∧ f' 0=0 ∧ fderiv ℝ f' 0=0 := by
   obtain ⟨M,hM,hp⟩:=uniform F a (n:=4)
   let C₀:=Push.Uniform.composeCost 4 M K
   refine ⟨max 1 (4*C₀),le_max_left ..,fun {c f S T L b x z t t' p w} o ht hv hw hz h hv' hl=>?_⟩ -- binder h shadows
   let U:=Spins.drawing F o a; let D:=display T L x b true; let V:=U∘D; let W:=Complex.ofRealCLM.comp w
   let γ:=t/t'; let f':=W∘V
   intro Y
   have hw': ‖W‖≤1:= by unfold W; apply (ContinuousLinearMap.opNorm_comp_le ..).trans; apply mul_le_one₀ _ (norm_nonneg _) hw; apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro z; simp
   have he(v:Deck G c f)(hv'':‖v‖ ≤ z):Through p D v K:= (h.costs true).uniform _ hv''
   have he₀:= (h.costs true).home; change D 0=0 at he₀
   have H4(v:Deck G c f)(h'':‖v‖ ≤ z):Through 4 D v K:= ⟨(he v h'').smooth.of_le (Nat.cast_le.mpr hl),fun k ht => (he v h'').pay _ (ht.trans hl)⟩
   have hV (v:Deck G c f)(h'': ‖v‖ ≤ z): Through 4 Y v (max 1 (4*C₀)):=by
      have H := (H4 v h'')
      have H' : ‖D v‖ ≤ 1:= (locate he (by omega) he₀ h'').trans ((mul_le_mul_of_nonneg_left h'' (zero_le_one.trans hQ)).trans hv')
      have H'': Through 4 f' v (1*C₀):= linear_through W ((hp f o _ H').comp H) hw'
      have ht': 0<t':=by linarith
      refine (H''.scale (γ^2)).mono ?_; apply le_trans _ (le_max_right ..)
      rw [one_mul,abs_of_nonneg (sq_nonneg _)]; have hn:=H''.nonneg; rw [one_mul] at hn -- avoid all
      have hg:0 ≤ γ:=by unfold γ; positivity
      have hh0:γ ≤2:=(div_le_iff₀ ht').mpr hv; exact mul_le_mul_of_nonneg_right (by nlinarith only [hg,hh0]) hn
   have hzA:iteratedFDeriv ℝ 0 U 0=0:= no_low F o a hLi (by omega)
   have hzB:iteratedFDeriv ℝ 1 U 0=0:= no_low F o a hLi (by omega)
   have hz0:U 0=0:=by have hi:=congrArg Norm.norm hzA; rwa [norm_iteratedFDeriv_zero,norm_zero,norm_eq_zero] at hi
   have hz1:fderiv ℝ U 0=0:=by rw [← norm_eq_zero, ← norm_iteratedFDeriv_one, hzB,norm_zero]
   refine ⟨hV,by change γ^2 • ↑(w (U (D 0)))= (0:ℂ); rw [he₀,hz0,map_zero,Complex.ofReal_zero,smul_zero],?_⟩
   change fderiv ℝ (γ^2 • f') 0 = _
   have hD:(DifferentiableAt ℝ D 0):=(H4 0 (by simpa)).smooth.differentiableAt (by norm_num)
   have hU:(DifferentiableAt ℝ U (D 0)):=he₀.symm ▸ (hp f o 0 (by simp)).smooth.differentiableAt (by norm_num)
   have He : DifferentiableAt ℝ f' 0:= W.differentiableAt.comp (f:=V) 0 (hU.comp _ hD)
   rw [fderiv_const_smul He]; unfold f' V; rw [fderiv_comp 0 W.differentiableAt (hU.comp _ hD),fderiv_comp 0 hU hD,he₀,hz1]; apply ContinuousLinearMap.ext; intro v; simp only [_root_.smul_apply,ContinuousLinearMap.comp_apply,_root_.zero_apply,map_zero,smul_zero]

protected def ceiling (hQ:1≤K) := Classical.choose (angels F a hLi hslots hQ)
lemma roof (hQ:1 ≤ K): 1 ≤ Spins.ceiling F a hLi hslots hQ := Classical.choose_spec (angels F a hLi hslots hQ) |>.1
end YM.RG12.Spins
