import YM.FullVolume.Table.Vola
/-! Normalized square-root coordinates with common width and padding. Any prescribed phase center near interior, radius pays Power.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Pass
open Function Filter Set Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open MeasureTheory ProbabilityTheory Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Height Input Org Supply Pane Slide Push.PriceCompiler Progress.DirectedRecipe Jams Apse Empire Time Roof Chord Ovens
open FullVolume.Ray FullVolume.Urns
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{X:Metals G}{D:Rolls X.p}{A:Alloy X D}{R:Roost.Factor A}
variable (g:G.Simple){v q d t t':ℝ}{N n m:ℕ}(H:Chord R N m n t t)(h:Degree R.shape R.scout A.delay)(hq:Savvy R.scout R.target A.delay q v d t)
-- α scaled coordinates unbased hats. width epsilon fixed.P δ variations.C Need arcs on |normalized-v|max≤T q.Tolerance center h_i oct
abbrev grand (x:ℝ):=x^((1:ℝ)/256)
abbrev joy (x:ℝ):ℝ:= x^(-(1/128):ℝ)
abbrev normedWidth (x:ℝ):ℝ:= x^(-(1/32):ℝ) -- q/v units smaller
-- use absolute `lambda` weights and offset h.
local notation "δ" => normedWidth
abbrev salary (x:ℝ):ℝ:= normedWidth x*x -- pay derivative scales after.
def fromLambda (x u:ℝ):ℝ:=x*(normedWidth x *u)^2
def toLambda (x u:ℝ):ℝ:= Real.sqrt (u/x) / normedWidth x
lemma widthP {x:ℝ} (hx:0<x): 0< normedWidth x:=Real.rpow_pos_of_pos hx _
lemma currency {x u:ℝ} (hx:0<x)(hu:0≤u): fromLambda x (toLambda x u) = u ∧0≤toLambda x u:=by
  unfold fromLambda toLambda; let v:= δ x; have hp:= widthP hx; have hh:0≤u/x:=by positivity
  refine ⟨?_, div_nonneg (Real.sqrt_nonneg _) hp.le⟩; rw [mul_div_cancel₀ _ hp.ne', Real.sq_sqrt hh]; field_simp
-- eventual and late readiness
structure Climate (x:ℝ) : Prop where
   floor : 0<x
   grade : 1 ≤ grand x
   steps : joy x ≤1
   dust : 128*grand x*normedWidth x ≤ joy x
lemma yet : ∀ᶠ x in atTop,Climate x:=by
  have hp: (1/256:ℝ)-(1/32)-(-(1/128)) < 0:= by norm_num
  have he:= (tendsto_rpow_neg_atTop (y:=-( (1/256:ℝ)-(1/32)-(-(1/128)))) (by linarith)).eventually (gt_mem_nhds (show 0 < ((1:ℝ)/128) by norm_num))
  filter_upwards [he,eventually_gt_atTop (1:ℝ)] with x hx hy; have hv:= zero_lt_one.trans hy; have hg:= Real.rpow_pos_of_pos hv (-(1/128):ℝ); have hW:= widthP hv; simp only [neg_neg] at hx
  refine ⟨hv,(Real.one_lt_rpow hy (by norm_num)).le, Real.rpow_le_one_of_one_le_of_nonpos hy.le (by norm_num),?_⟩
  rw [Real.rpow_sub hv,show ((1/256:ℝ)-(1/32))= 1/256+(-(1/32)) from rfl,Real.rpow_add hv] at hx
  have ht:= (div_lt_iff₀ hg).1 hx; change grand x * normedWidth x < _ at ht; linarith
variable (a: Levels G){l b x r:ℝ}
local notation "P"=> a.clock.hatBeta
-- useful nested margins: route x root in middle ∈ [6/7? sqrt(.75)~.866,5/4]. choose middle [.85,1.15]; full arcs need .75 threshold √. etc. broad pad for neighboring.
def mild (x y:ℝ):Prop:=normedWidth x*y∈ Set.Icc (17/20:ℝ) (23/20)
def emcee (x y:ℝ): Prop:= normedWidth x*y∈ Set.Icc (33/40:ℝ) (47/40)
-- `.aim λ` builds token. warr ≥
lemma good_mild {x v:ℝ} (hx:Climate x)(h:3/4*x ≤ v ∧ v ≤ 5/4*x): mild x (toLambda x v):=by
  unfold mild toLambda; rw [mul_div_cancel₀ _ (widthP hx.floor).ne']; rw [Set.mem_Icc]; have hg:= hx.floor
  constructor
  · apply (Real.le_sqrt_of_sq_le); rw [le_div_iff₀ hg]; nlinarith only [h.1,hg]
  apply (Real.sqrt_le_left (by norm_num : 0 ≤ (23/20:ℝ))).2; rw [div_le_iff₀ hg]; nlinarith only [hg,h.2]
lemma samples {x v:ℝ} (hx:Climate x)(h:mild x v)(hy:|l-v| ≤2): emcee x l:=by
  have hg: δ x ≤ ((1:ℝ)/128):= by have hw:=hx.steps; have ht:=hx.dust; nlinarith [mul_le_mul_of_nonneg_right hx.grade (widthP hx.floor).le]
  have hu:= mul_le_mul_of_nonneg_left hy (widthP hx.floor|>.le); rw [←abs_of_nonneg (widthP hx.floor).le, ← abs_mul] at hu -- wreck
  unfold mild at h; unfold emcee; obtain ⟨hh,hv⟩:= h; obtain ⟨hL,ht⟩:=abs_le.mp (show |δ x*(l-v)| ≤δ x*2 from by simpa only [abs_of_nonneg (widthP hx.floor).le] using hu)
  constructor <;> linarith
lemma priced (hx:Climate (a.clock.hatBeta m))(h:emcee (a.clock.hatBeta m) x)(hv: |v| ≤ 1):∃ U:WilsonStartup.Fog.Bell (RG.Shoot.band a m) (grand (P m)) (joy (P m)),∀ i, |i|≤6*(grand (P m)) → (U.poses i).val=fromLambda (P m) (x+i*v):=by
  let y:=P m; let X:=δ y; let p:=grand y; let q:=joy y; let s:=X*x
  have hy:0<y:= hx.floor; have hp:1≤ p:= hx.grade; have hX:0<X:=widthP hy; have hq:0<q:= Real.rpow_pos_of_pos hy _; have hz:q ≤1:= hx.steps
  have hδ: 128*p*X ≤ q:= hx.dust; have hk :6*p*X ≤6/128*q:= by linarith
  have hv': 0 ≤6*p:=by positivity
  let L:= s-6*p*X
  have h:s∈Set.Icc (33/40) (47/40):= h; have hf : (3/4:ℝ)≤L := by unfold L; linarith [h.1];
  have hL: 0<L:= (by linarith); have ht : y*L^2 ∈ band a m:= by
    constructor
    · change y/2 ≤ _; nlinarith only [hy, hf,mul_le_mul_of_nonneg_right (sq_le_sq₀ (by norm_num : (0:ℝ)≤3/4) hL.le|>.2 hf) hy.le]
    apply le_trans (b:=2*y) _ le_rfl; have hu: L ≤ s:= sub_le_self _ (by positivity); nlinarith [mul_le_mul_of_nonneg_right (sq_le_sq₀ hL.le (by norm_num : (0:ℝ)≤47/40)|>.2 (hu.trans h.2)) hy.le] -- macro
  let A₀:= s/L; let a₀:= X*v/L
  let K: FullVolume.Ray.Fold p q:= by
    refine ⟨A₀,a₀,hp,?_,?_,hz⟩
    · change _≤ s/L-6*p* |a₀|; rw [show |a₀|= X* |v| /L from (by unfold a₀; rw [abs_div,abs_mul,abs_of_pos hX,abs_of_pos hL]), ← mul_div_assoc, ← sub_div, le_div_iff₀ hL]; unfold L; nlinarith only [mul_le_mul_of_nonneg_left hv (show 0 ≤ 6*p*X from (by positivity))]
    rw [show |a₀|= X* |v| /L from (by unfold a₀; rw [abs_div,abs_mul,abs_of_pos hX,abs_of_pos hL])]; unfold A₀; rw [← mul_div_assoc, ← add_div, div_le_iff₀ hL];
    rw [add_mul,one_mul]; conv_rhs=>lhs; unfold L
    nlinarith only [hk, mul_le_mul_of_nonneg_left hv (show 0≤6*p*X from by positivity), mul_le_mul_of_nonneg_left hf hq.le,hq]
  let f(i:ℝ):=fromLambda y (x+i*v)
  have he(i:ℝ) (hi:|i|≤6*p): f i ∈ band a m:= by
    have hf' : |i*v|≤6*p := (abs_mul ..).trans_le (mul_le_mul hi hv (abs_nonneg _) hv'|>.trans_eq (by ring)); obtain ⟨hX',hY⟩:= abs_le.mp hf'
    have h₀ : 3/4 ≤ X*(x+i*v):= le_trans hf (by unfold L s; nlinarith only [mul_le_mul_of_nonneg_left hX' hX.le])
    have h₂:X*x ≤ 47/40:= h.2
    have h₁ : X*(x+i*v)≤4/3:= by
       nlinarith only [h₂,hk,hz,mul_le_mul_of_nonneg_left hY hX.le]
    constructor
    · change y/2≤ y* _; apply le_trans (b:=y*(3/4:ℝ)^2) (by nlinarith) (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) h₀ 2) hy.le)
    change y*_ ≤ 2*y; exact le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (show (0:ℝ)≤_ from le_trans (by norm_num: (0:ℝ)≤3/4) h₀) h₁ 2) hy.le) (by nlinarith)
  let v₀:band a m:=⟨_,ht⟩; let F(i:ℝ):band a m:= if h:|i|≤6*p then ⟨f i,he i h⟩ else v₀
  have he i (hi:|i|≤6*p) :(F i).val=f i:=by unfold F; rw [dif_pos hi]
  refine ⟨⟨v₀,K,F,fun i hi=>?_⟩,he⟩; rw [he _ hi]; change f i = y*L^2*(A₀+a₀*i)^2; unfold A₀ a₀ f s; change y*(X*_)^2=_; field_simp
end YM.PhysicalNext.Repeat.Pass
