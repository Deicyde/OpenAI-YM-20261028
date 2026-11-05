import YM.FullVolume.Sym.Glimmer
import YM.FullVolume.Sym.Words
import YM.FullVolume.Sym.Chill
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Jams
open Function Filter Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Empire
open FullVolume.Ray
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open FullVolume.Ray Residual Averaging Progress.DirectedRecipe Time
/-! Linearized actual Archive before Last Ovens. Works on same stamps before Sector currents;
 since δ is the diagonal Hessian Projection we need no common Moves here.
 Compute from real germs. -/
variable {G:Gauge}{c:Side}{p:BudgetPoint}{A:Listing G c} {R:PathData G}{b:Clip} {γ Δ C B H σ τ:ℝ}
variable {X:sun → Collection.Source G c}(w:Rung)
lemma mix_plus {E:Type*} [AddCommGroup E] [Module ℝ E] (f g:sun→E):mix w (fun i=> f i+g i)=mix w f+mix w g:=by unfold mix; simp_rw [smul_add,sum_add_distrib]
lemma mix_right (c:ℝ)(f:sun→ℝ):mix w (fun i=> f i * c) = mix w f * c:=by simp_rw [mul_comm _ c]; exact Jams.mix_scale c f
lemma mix_z {E:Type*}[AddCommGroup E][Module ℝ E]:mix w (fun _=> (0:E))=0:=by simp [mix]
lemma mix_h (x:sun→ Config G c→ℝ) (S:Support c) (h:∀ i,p.Regular S (x i)) (A B:Directions G c): mix w (fun i=>logHessian (x i) A B)=logHessian (mix w x) A B:=by
  let f i:= (AnalyticBridge.VerifiedReset.germ (x i)); let g:= ∑ i∈ w.support, w i • f i
  have he : AnalyticBridge.VerifiedReset.germ (mix w x)=g:=funext fun i=> by unfold germ g mix; simp only [Function.comp_apply,Finset.sum_apply,Pi.smul_apply]; rfl
  change (∑ i∈w.support,w i • ((iteratedFDeriv ℝ 2 (f i) 0) ![A,B]))=(iteratedFDeriv ℝ 2 (germ (mix w x)) 0) ![A,B]
  have hf i : ContDiffAt ℝ 2 (f i) 0:= germ_diff (h i)
  rw [he]; unfold g; rw [iteratedFDeriv_sum_apply (f:=fun i=>w i • f i) (u:=w.support) (fun i _=> (hf i).const_smul (w i)), ContinuousMultilinearMap.sum_apply] -- name
  exact sum_congr rfl fun i _=> by rw [iteratedFDeriv_const_smul_apply (hf i)]; rfl
lemma mix_projects {f:sun→ Config G c→ℝ} (i:RegularAddress c) (a b:PlaqAxes)(h:∀ j,p.Regular i.support (f j)):mix w (fun j=>projection i (f j) a b)=projection i (mix w f) a b:=by
  unfold projection; split
  next he=> exact mix_h w _ i.support h _ _
  exact mix_z _
lemma layersP (i: RegularAddress c) (f:sun→ Config G c→ℝ)(h: ∀ j,p.Regular i.support (f j)) (U) : mix w (fun j=> payout i (f j) U)=payout i (mix w f) U:= by
  unfold payout counter VerifiedReset.quad; simp_rw [div_eq_mul_inv]; rw [mix_right, mix_sum]; congr 1; refine sum_congr rfl fun a _=>?_
  rw [mix_sum]; refine sum_congr rfl (fun b _=> ?_); rw [mix_right, mix_projects w i _ _ h]
lemma layersE (i: RegularAddress c) (f:sun→ Config G c→ℝ)(h: ∀ j,p.Regular i.support (f j)) : mix w (fun j=> rebate i (f j)) = rebate i (mix w f):= by
  ext U; unfold rebate; simp_rw [mix_eval,Pi.sub_apply]; rw [mix_sub,mix_sub,layersP _ _ _ h,mix_eval f U]
lemma mix_if {p:Prop}[Decidable p]{E:Type*}[AddCommGroup E][Module ℝ E](f g:sun→E):mix w (fun i=>if p then f i else g i)=if p then mix w f else mix w g:=by split_ifs<;> rfl
lemma layersL (i: RegularAddress c)(f:sun→ Config G c→ℝ)(h:∀ j,p.Regular i.support (f j)) (U) : mix w (fun j=> fault i (f j) p.threshold U)=fault i (mix w f) p.threshold U:= by
  unfold fault; simp_rw [mix_eval]; split_ifs
  all_goals simp only [mix_sub,mix_plus,mix_z, layersP w i f h] -- diag
variable (g:G.Simple)(h:∀ t:sun,Meadow.Budget p A.reg (X t|>.logRead) C)
lemma reproages (U:Collection.Source G c)(h:Meadow.Budget p A.reg U.logRead C):Averaging.Projects (A.read U) p C:=by
  obtain ⟨k,hk,hL⟩:= h; exact ⟨fun i=>(hL i).1,k,fun i=>(hL i).2,Quotes.segment _ (fun i=>(hL i).2.1) hk⟩
def emitA (w:Rung)(X:sun→ Collection.Source G c):Collection.Source G c:= ⟨mix w (fun i=> (X i).logRead),mix w (fun i=> (X i).hardRead)⟩
local notation "Z"=> emitA w X
local notation "Δ'"=> fun x:sun=> Averaging.delta (A.read (X x))
include h g
lemma d_angle : mix w Δ'= Averaging.delta (A.read (emitA w X)):= by
  let a:= (axes01); have hv i:= (reproages _ (h i)).seriesAt g a a 0
  let N i:ℕ→ℝ:= censusAt (A.read (X i)) 0 a a; let D(i):= censusAt (A.read Z) 0 a a i
  change mix w (fun i=> ∑' j,N i j)=∑' i,D i
  unfold mix; simp_rw [smul_eq_mul, ← tsum_mul_left]; rw [← Summable.tsum_finsetSum (f:=fun i j=> w i * N i j) (fun i _=> (hv _).mul_left _)]
  refine tsum_congr (fun i=>?_); unfold N D censusAt; change mix w (fun j=> if (A.reg i).site=0 then _ else 0)=if (A.reg i).site=0 then _ else _
  rw [mix_if]; split; next=>
    have hh' : (Z).logRead i=mix w (fun j=> (X j).logRead i):= mix_eval ..; change mix w _=projection _ ((Z).logRead i) _ _; rw [hh']; exact mix_projects w (A.reg i) _ _ (fun j=> ((h j).choose_spec.2 i).1)
  exact mix_z _
local notation "A₀" => (mix w (fun _=>γ))
local notation "Δ₀" => Averaging.delta (A.read (emitA w X))
local notation "d₀"=>fill A R b p (emitA w X) A₀ Δ₀
local notation "E₀"=> Ovens.Tap.regular
local notation "L₀"=> Ovens.Tap.logarithm
lemma d_reg : mix w (fun i=>Ovens.Tap.regular (branch A R b p (X i) γ))=Ovens.Tap.regular d₀:= by
  ext i U; rw [mix_eval,mix_eval, ← d_angle w g h]
  change mix w (fun j=> archive A R b (X j) γ (Δ' j) (numbering (EKey c) i) U)=archive A R b Z A₀ (mix w Δ') (numbering _ i) U
  rcases numbering (EKey c) i with i|⟨i,z⟩|⟨i,z⟩
  · have hh' : (Z).logRead i=mix w (fun j=> (X j).logRead i):= mix_eval ..
    unfold archive; dsimp only [Sum.elim]; rw [hh', ← layersE w (A.reg i) _ (fun v=> ((h v).choose_spec.2 i).1),mix_eval]
  · unfold archive; dsimp only [Sum.elim,Function.comp_apply, Low.fresh]; rw [mix_right,mix_right, mix_times] -- mul variant
  unfold archive; dsimp only [Sum.elim,Function.comp_apply, High.fresh]; rw [mix_right]; have hg (f:sun→ℝ):mix w (fun i=> -f i)= -(mix w f):= by unfold mix; simp;
  rw [hg,mix_plus,Jams.mix_times (w:=w) VerifiedReset.factor (fun _=>γ),mix_times]
lemma d_soft : mix w (fun i=>Ovens.Tap.logarithm (branch A R b p (X i) γ))=Ovens.Tap.logarithm d₀:= by
  ext i U; rw [mix_eval,mix_eval, ← d_angle w g h]
  change mix w (fun j=> loses A R b p (X j) γ (Δ' j) (numbering (LKey c) i) U)=loses A R b p Z A₀ (mix w Δ') (numbering _ i) U
  rcases numbering (LKey c) i with i|⟨i,z⟩
  · have hh' : (Z).logRead i=mix w (fun j=> (X j).logRead i):= mix_eval ..
    unfold loses; dsimp only [Sum.elim]; rw [hh']; exact layersL w (A.reg i) _ (fun v=> ((h v).choose_spec.2 i).1) U
  unfold loses; dsimp only [Sum.elim, Function.comp_apply,Low.loan]; simp_rw [mix_if]; split_ifs
  all_goals simp only [mix_sub, mix_plus,mix_z,Jams.mix_times (w:=w) VerifiedReset.factor,mix_right] -- above need gamma column
end YM.PhysicalNext.Repeat.Jams
