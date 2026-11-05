import YM.FullVolume.Luna.Frames
import YM.FullVolume.Glitz.RockG
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Luna
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
open Next.Foundations Jams YM.Source Labels
open YM.Source Planned.GuardedAtom Labels -- Angles
open Guard MergeProof MergeProof.Matric Extra.Histories
open YM.PhysicalNext.Repeat.Roof
variable {G:Gauge}{n:Side}{ι:Type*}{B:BudgetPoint}{X:ℕ→Support n}{o:Site n}{p q r s t u v a b c:ℝ}
variable {S:ℕ→Support n}{d k:ℕ}{F:Labels.Frame G d}{C: SectionData F}{Y:Hol G}{R:sun→RG.Rep G n}
local notation "zr"=> Config G n→ℂ
variable {x:ℕ}
lemma aspect {a:ℝ}{v:F.Coeff}: a • v=(a:ℂ) • v:= funext fun _=>Complex.real_smul
variable (Z:Support n){P:BudgetPoint}{f:sun→ Config G n→ℂ} (w:Rung) (hX:P.order≥d) (h:∀ i,P.Regular Z (f i))
include h hX in
lemma projL : Local.weighted Y F 0 Z P.threshold (mix w f)= mix w (fun i=> Local.weighted Y F 0 Z P.threshold (f i)):=by
  unfold mix; simp_rw [saneF,(show ∀ z:sun, w z • Local.weighted Y F 0 Z P.threshold (f z)=_ from fun z=>aspect)]
  exact (sum_weigh (f:=f) (y:=fun i=>(w i:ℂ)) _ h hX).2
variable {M:sun→Push.Local.Raw F n} (hp:∀ i,(R i).p=B)
variable (ht:Local.Readable Y C B n u)
variable {A:sun→ Coefficient F n} (hh:∀ i, ∃ T: Berths (R i).p (R i).activities (fun j=> Local.joint C 0 (X j)), A i=mint T (M i) Y)
variable (hs:∀ i,(M i).seed=0)
variable {xL:F.Coeff}
local notation "Φ"=> Local.factor Y C B.supportExponent u
local notation "λ!"=>Motion.orbitCost F
local notation "ξ"=> Local.turnCost B.order B.power
variable (hf:∀ i,Graces.Effort C (R i) Y X (M i) xL u a b v)
include ht in
lemma alphapos : 1≤ Φ:= by
    apply one_le_mul_of_one_le_of_one_le (Real.one_le_exp _) (Local.atomPrice_ge_one _ _ ht.nonneg)
    exact mul_nonneg (by have h:=B.exponent_pos; linarith) (by positivity)
lemma xi_pos (B:BudgetPoint) :1 ≤ Local.turnCost B.order B.power:= one_le_pow₀ (one_le_mul_of_one_le_of_one_le one_le_two (one_le_pow₀ one_le_two))
include hh hf ht hp
lemma upright (ha:0<a) (x:sun) : let e:= B.supportExponent + 2
    Summable ((M x).row 0 X Y B.threshold) ∧ Chand B 0 X (M x).bulk e (v / (ξ *Φ)) ∧ λ! * F.coeffSize ((A x).x-xL) ≤ b:=by
   intro e; obtain ⟨T,hT⟩:=hh x; have h' := hp x; have hr:= (show Local.Readable Y C (R x).p n u from h'.symm ▸ ht)
   obtain ⟨p,r,t,hK,h,hU,hv,hS⟩:= hf x; obtain ⟨t',v',hx,he⟩:= hU; obtain ⟨h₁,h₂,h₃⟩:= h.costs_nonneg (Real.sqrt_pos.mpr ha)
   refine ⟨?_,?_,?_⟩
   · rw [← h']; exact (Size.series F (h.row_cost hr hK|>.2.1)).of_norm
   · obtain ⟨c,hc,hY⟩:= hx.bulk
     have hb : Local.turnCost B.order B.power*p ≤ v:= by rw [← h']; exact (le_add_of_nonneg_right (add_nonneg h₂ h₃)).trans hv
     have hy: Brill B X c e t' := by unfold e; rw [← h']; exact hY
     have hc': ∀ i, B.supBounds 0 (X i) ((M x).bulk i) (c i):=by rw [← h']; exact hc
     rw [h'] at he
     refine ⟨c, Local.sumBudget_mono hy hy.1 le_rfl ((le_div_iff₀ (mul_pos (zero_lt_one.trans_le (xi_pos B)) (zero_lt_one.trans_le (alphapos ht)))).mpr ?_),hc'⟩
     calc _ = ξ*(Φ * t'):=by ring
          _ ≤ v:=he.symm ▸ hb
   rw [hT]; rcases hS with ⟨f,e,hp,ho,hs⟩|he
   · exact (mul_le_mul_of_nonneg_left (sensor T hK hr h hp ho) (by linarith [Motion.orbitCost_one_le F])).trans hs
   exact (mul_le_mul_of_nonneg_left (size_mint T hK hr h _) (zero_le_one.trans (Motion.orbitCost_one_le F))).trans he
set_option quotPrecheck false
local notation "fM"=> fun i:sun=> (M i).bulk
local notation "mF"=> fun t:sun=> (A t).x
include hs
lemma coined (ha:0<a)(i:ℕ) : mix w mF=∑' i, Local.weighted Y F 0 (X i) B.threshold ((mix w fM) i):=by
    let P i x:= (M i).row 0 X Y B.threshold x
    have ht' i:(A i).x=∑' j, P i j:=by obtain ⟨T,hT⟩:=hh i; rw [hT]; change (M i).seed + ∑' j,(M i).row 0 X Y (R i).p.threshold j=_; rw [hp,hs,zero_add]
    have hb (j:ℕ):Local.weighted Y F 0 (X j) B.threshold ((mix w fM) j) = mix w (fun i=>P i j):=by
        rw [mix_eval]; exact projL (X j) w ht.order (fun i=>hp i ▸ (hf i).choose_spec.choose_spec.choose_spec.1.regular j)
    simp_rw [ht',hb,mix]; have hh' i : Summable (P i):=(upright hp ht hh hf ha i).1 -- order
    rw [Summable.tsum_finsetSum _]; refine sum_congr rfl fun i _=> ((hh' i).tsum_const_smul _).symm; intro i _; exact (hh' i).const_smul _
lemma leaders {ha:0<a} (ww:Rung)(hL:Stripe ww p q)(he:Wires B 0 X (fun i:sun=>(M i).bulk) p (B.supportExponent+2) t): F.coeffSize (mix ww mF)≤ Φ*(q*t):=by
   rw [coined ww hp ht hh hs hf ha 0]
   obtain ⟨r,hr,hF⟩:= he.takes hL
   let g(i):= Local.weighted Y F 0 (X i) B.threshold (mix ww fM i); have hS i:B.Regular (X i) (mix ww fM i):= by rw [mix_eval]; exact paneR _ (fun z=>hp z ▸ (hf z).choose_spec.choose_spec.choose_spec.1.regular i)
   have hJ : Push.Local.readPrice Y F≤ Φ:=by
     have h1:Push.Local.readPrice Y F≤ Local.atomPrice Y F u:=by unfold Local.atomPrice;nlinarith [ht.nonneg,Local.readPrice_pos Y F]
     exact h1.trans (le_mul_of_one_le_left (by linarith [Local.atomPrice_ge_one Y F ht.nonneg]) (Real.one_le_exp (mul_nonneg (add_nonneg B.exponent_pos.le (by norm_num)) (by positivity))))
   have hu:=Local.sumBudget_mono (Local.sumBudget_mul_left hr (show 0≤ Φ from zero_le_one.trans (alphapos ht))) (fun i=> Work.G08.size_nonneg F (g i)) (fun i=>?_ ) le_rfl
   · exact (Size.bound F hu.2.1).trans hu.2.2
   apply (Local.weighted_bound Y F 0 (hS i) ht.order ht.power (hF i)).trans
   exact mul_le_mul hJ (le_mul_of_one_le_left (hF i|>.1) (Real.one_le_exp (mul_nonneg (add_nonneg B.exponent_pos.le (by norm_num)) (by positivity)))) (hF i|>.1) (zero_le_one.trans (alphapos ht))
lemma muscles (ha:0<a)(T:Tableau q k)(hv:q≤p)(he:Wires B 0 X (fun i:sun=>(M i).bulk) p (B.supportExponent+2) t): ∀ z:Rung,∀ η,Stripe z q η→ λ! * F.coeffSize (mix z fun y=> (A y).x - xL) ≤ η*(T.price*b+T.liftT p*(λ! *(Φ*t))):=by
  intro z η hx; let f':=fun i:sun=> (A i).x - xL
  let z₁:= z-T.cuts z
  have ht':mix z₁ f'=mix z₁ mF:=by
     have hm: mix z₁ (fun _=> xL)=(mix z₁ (fun i:sun=> (i.val/p)^(0:ℕ))) • xL:= by unfold mix; rw [sum_smul];simp
     rw [show mix z₁ (fun i:sun=> (i.val/p)^(0:ℕ))=0 from plays_exact _ _ T.unique z p 0 (Nat.zero_le _),zero_smul] at hm
     unfold f'; simp_rw [sub_eq_add_neg]
     rw [mix_plus]; have hp : mix z₁ (fun _=> -xL)= -(mix z₁ (fun _=>xL)):= by simp_rw [mix,smul_neg,Finset.sum_neg_distrib]
     rw [hp,hm,neg_zero,add_zero]
   -- bound samples
  have he' : λ! *F.coeffSize (mix (T.cuts z) f') ≤ η*T.price*b:=by
     let Q i:=mix z (gloss k T.p i)
     rw [show mix (T.cuts z) f'= _ from incomes ..]; have hA i: f' i=(A i).x-xL:=rfl
     apply (mul_le_mul_of_nonneg_left (Size.finite F _ _) (zero_le_one.trans (Motion.orbitCost_one_le F))).trans
     rw [mul_sum]; unfold Tableau.price;rw [mul_sum,sum_mul]; refine sum_le_sum (fun i _=> ?_)
     rw [aspect,Size.smul]; have h:=upright hp ht hh hf ha (T.p i)|>.2.2
     have hz: ‖((Q i:ℝ):ℂ)‖≤ η*T.u i:= (by rw [Complex.norm_real,Real.norm_eq_abs];exact T.use _ _ hx _)
     rw [mul_left_comm]; refine ((mul_le_mul_of_nonneg_left h (norm_nonneg ((Q i:ℝ):ℂ)))).trans (mul_le_mul_of_nonneg_right hz ?_)
     exact (mul_nonneg (zero_le_one.trans (Motion.orbitCost_one_le F)) (Work.G08.size_nonneg ..)).trans h
  let ν:= T.liftT p; let x:= η*ν
  rw [T.splitK z]; apply (mul_le_mul_of_nonneg_left (Size.add F _ _) (zero_le_one.trans (Motion.orbitCost_one_le F))).trans
  rw [mul_add,show mix z₁ f'= _ from ht']; apply (add_le_add he' (mul_le_mul_of_nonneg_left (leaders hp ht hh hs hf (ha:=ha) z₁ (T.lapse hv hx) he) (zero_le_one.trans (Motion.orbitCost_one_le F)))).trans_eq; unfold Tableau.liftT; ring
end YM.PhysicalNext.Repeat.Luna
