import YM.FullVolume.Nectar.Regal
import YM.FullVolume.Nectar.Funnel
import YM.FullVolume.Nectar.Oust
import YM.FullVolume.Nectar.Tea
import YM.FullVolume.Nectar.Keys
import YM.FullVolume.Nectar.Bower
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Muse.Veil
set_option quotPrecheck false
open Function Filter Set Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Animals
open MeasureTheory ProbabilityTheory Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Height Input Org Supply Pane Slide
open Push.PriceCompiler Progress.DirectedRecipe Jams Apse Empire Time Roof Chord Ovens
open FullVolume.Ray FullVolume.Urns FullVolume.Amp Pass Tent
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{X:Metals G}{D:Rolls X.p}{A:Alloy X D}{R:Roost.Factor A}
variable {v q d t t':ℝ}{N n m:ℕ}{L:Lyrics R t t}
open UniformSpace
set_option maxHeartbeats 360000
set_option synthInstance.maxHeartbeats 140000
variable (H:Chord R N m n t t){T:Team (stageP A.B.a (m+1) n)}
local notation "P"=> (stageP A.B.a (m+1) n)
local notation "Q"=> A.B.a.budget (m+1)
local notation "Ω"=> A.B.a.clock.hatBeta (m+1)
local notation "β"=> A.B.a.clock.hatBeta m
local notation "S"=> A.B.a.S.side (m+1) n
local notation "α'"=> A.B.a.S.side m n
open Board MergeProof Marker
variable {V I:Type}[Fintype I][Fintype V][DecidableEq V] {W Z:Type} [SeminormedAddCommGroup W][NormedSpace ℝ W]
open Luna Frets Empire Imago
local notation "𝒬" => Board (A:=A) N m n T
open Luna.Aank Lotus
variable {B: Marker.Census V}
open UniformSpace
namespace ArmadaP
variable (x:Booker A N m n T){o:V→ Site (A.B.a.S.side (m+1) n)}(U:ArmadaP A N m n T x o B I)
local notation "aQ"=> A.B.a.budget (m+1)
local notation "G₁"=> Glacial I ℝ (Config G (A.B.a.S.side (m+1) n))
local notation "Yx"=> x.val.val.val
local notation "f_"=> fraz (A:=A) (m:=m) (n:=n)
local notation "K₁"=> U.inkLens x
local notation "mK"=> fun i=> (U.track i).support x.val.val.val
variable (C:I→ℝ)
open FullVolume.Amp FullVolume.Nectar FullVolume.Paint.Tower
variable (y:sun→ Booker A N m n T) (mK' : (s:sun) → I→Leaf (y s).val.val.val)
variable {v:ℝ}{b:I→ℝ}(hc:∀ i:I,0<C i) (hk:∀ s i,(mK' s i).turn=U.track i)
    (hX:∀ i,Feel (fun s=> (mK' s i).ingredient) (b i))(hv:∑ i,b i / C i ≤ v)
variable (w:V→ℝ) {u:V→ℝ}{c v1 v2:ℝ}
-- when toll weights charge positive. Typically signed `1` and `i`. For budget x=0 normalize.Aqu.Calls assign Ξ field zero EVEN family with ∥v∥=0. reserves.L.
def FoldT (c:ℝ)(u:V→ℝ)(v:ℝ)(b:I→ℝ):Prop:= (∑ i,Real.exp (((Q).supportExponent-4)*coverNumber (Q).B ((U.track i).support (Yx))) * (Poly.toll w (U.mode i)*‖U.charge i‖*b i)) / c+∑ j:V, (∑ i, if U.mode i=B.fire j then (Q).mass ((U.track i).support (Yx)) (‖U.charge i‖*b i) else 0)/(u j) ≤ v
lemma fundingP (hb:0≤b)(hY: FoldT x U w c u v b)(hw:∀ i,0 < w i)(h0:0<c)(hu:∀ i,0<u i)(hZ:∀ i,U.charge i≠0):∃ C:I→ℝ,(∀ i, 0<C i) ∧ EligibleP x U C w c u ∧∑ i,b i / C i≤ v:=by
    let f(i):= Real.exp (((Q).supportExponent-4)*coverNumber (Q).B (mK i))* (Poly.toll w (U.mode i)*‖U.charge i‖) /c
    let g(j:V)(i):= if U.mode i=B.fire j then (Q).mass (mK i) ‖U.charge i‖/ (u j) else 0
    let Z(i):=f i+∑ j,g j i
    have hf(i):0<f i:= div_pos (mul_pos (Real.exp_pos _) (mul_pos (Poly.worth hw _) (norm_pos_iff.mpr (hZ i)))) h0; have hg(j i):0≤g j i:= by unfold g; split;exact div_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) (hu j).le; rfl
    have hp(i):0< Z i:=add_pos_of_pos_of_nonneg (hf i) (sum_nonneg fun j _=> hg j i); let t i:=(Z i)⁻¹
    have ht i:0 < t i:=inv_pos.mpr (hp i); have hm i: Z i*|t i|=1:=by rw [abs_of_nonneg (ht i).le];exact mul_inv_cancel₀ (hp i).ne'
    refine ⟨_,ht,⟨fun i=>?_,fun i j hz=>?_⟩,le_trans (b:=_) ?_ (show _≤v from hY)⟩
    · have h:(f i)*|t i|≤1:= (mul_le_mul_of_nonneg_right (show f i≤ Z i from le_add_of_nonneg_right (sum_nonneg fun j _=>hg j i)) (abs_nonneg _)).trans_eq (hm i)
      unfold f at h; rw [div_mul_eq_mul_div, div_le_one h0] at h; change _ * (Real.exp _ * _)≤_; convert! h using 1; ring -- trivial
    · have h:g j i*|t i| ≤1:= (mul_le_mul_of_nonneg_right ((Finset.single_le_sum (fun x _=> hg x i) (mem_univ j)).trans (le_add_of_nonneg_left (hf i).le: _≤ Z i)) (abs_nonneg _)).trans_eq (hm i)
      unfold g at h; rw [if_pos hz,div_mul_eq_mul_div, div_le_one (hu j)] at h; unfold BudgetPoint.mass at * -- hY etc
      convert! h using 1; ring
    unfold FoldT at hY;
    apply le_of_eq; calc
     _= ∑ i,f i*b i +∑ j, ∑ i,g j i*b i:=by simp only [t,div_inv_eq_mul,Z,mul_add, mul_sum]; rw [sum_add_distrib, sum_comm]; congr! 2 with i _; all_goals first|apply mul_comm|simp_rw [mul_comm (b _)];
     _=_ :=by
       simp_rw [Finset.sum_div]; refine congr_arg₂ (·+·) (Finset.sum_congr rfl fun i _=> ?_) (Finset.sum_congr rfl fun j _=> Finset.sum_congr rfl fun i _=> ?_)
       · unfold f; rw [div_mul_eq_mul_div]; ring
       unfold g; split; next=> unfold BudgetPoint.mass; rw [div_mul_eq_mul_div]; ring
       next=>rw [zero_div,zero_mul]
include hk hX
lemma essential (hY: FoldT x U w c u v b)(hw:∀ i,0 < w i)(h0:0<c)(hu:∀ i,0<u i)(hZ:∀ i,U.charge i≠0): ∃ C:I→ℝ,(∀ i,0<C i) ∧ (pour x U C).Ensues w o c u ∧ ∃ p:sun→U.inkLens x, PaidBeam (fun i:sun=> ((p i:U.inkLens x): Completion (inkLens x U))) v ∧∀ s:sun,∀ i:I,((pour x U C).orbit (y s) (p s) i).ingredient= (mK' s i).ingredient:=by
    have hu' :0≤ u:=fun i=>show 0≤u i from (hu i).le; obtain ⟨a,hA,hp,hv⟩:= fundingP x U w (fun i=> (hX i).positives) hY hw h0 hu hZ
    exact ⟨a,hA,deemed x U a hw h0.le hu' hp,performs x U a y mK' hA hk hX hv⟩
end ArmadaP
end YM.PhysicalNext.Repeat.Muse.Veil
