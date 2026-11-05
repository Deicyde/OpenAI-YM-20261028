import YM.UVExtension.Cloud.Pit
/-!
 # REAL spigot on the short-upper interval. No full-sequence assumptions.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Cloud
open Function Filter Set Lattice RG RG.Supply Wilson Precision Shoot Stock Org Input Extra.Histories Source Labels
open PhysicalNext PhysicalNext.Repeat Spire Orchard Lacing Eyelet
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Mallow Lotus Legato.Bandage Lacing.RoutesF MergeProof
open Planned.GuardedAtom Guard
open Fitted
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge} {hG:G.Simple} {M:Metals G} {P:Rolls M.p} {A:Alloy M P} {X:Roost.Factor A} (S: Uses X hG) {C:ℕ→ℝ} {W:Bid.Worth}(R:Legato.Bandage X C W)
    (d N m n:ℕ)(b:Shade)
set_option quotPrecheck false
local notation "H"=> S.fits N n
local notation "V"=> S.cart N n
local notation "τ"=> S.grove.coins
local notation "F"=> (frames G).level d
local notation "π"=> localSection G d
local notation "O!"=> hol G
local notation "J₀"=> A.B.a.clock.J m
local notation "J"=> A.B.a.clock.J (m+1)
local notation "Δ"=> P.L J
set_option quotPrecheck false
variable (hm:m<N)(hd:d+3≤A.B.a.clock.J m)
open Flake Camp Cart Oriel Metric Complex
include S
noncomputable abbrev pulseM (a:Levels G)(i:ℕ):ℝ:= a.clock.hatBeta i ^ (1/100:ℝ)
-- uniform in ALL p and cutoffs, early levels via equicontinuity Cauchy
local notation "Z"=> Broad A.B.a
local notation "T"=> ink S N m n hm.le
local notation "μ"=> pulseM A.B.a m
local notation "r!" => UVExtension.Spire.spatial
include hm
lemma upon : MapsTo T Z spreadK.span:= fun _ hz=> H|>.palmN V τ m hm.le hz
lemma funds (z:ℂ)(hz:z∈Z): |(T z).re|+3*fringe < UVExtension.Spire.spatial:=by
   have hx: |(T z).re|≤rad*5/8:=(abs_re_le_norm _).trans (Cart.ground hG A.B.a N (S.fits N n).Hut V m hm.le τ hz); exact (add_le_add_left hx _).trans_lt (by norm_num [Spire.spatial, fringe,rad,rim])
omit S hm in
lemma highP (i:ℕ):0< pulseM A.B.a i:= Real.rpow_pos_of_pos (zero_lt_one.trans (A.B.a.fits.delayed _)) _
omit hm
lemma winterM : ∀ᶠ m:ℕ in atTop, ∀ (N:ℕ)(hm:m<N)(n:ℕ) z,z∈Z → Speed (pulseM A.B.a m) (ink S N m n hm.le z):=by
   have ht:= Cart.skiesC hG A.B.a; let y:= A.B.a.clock.hatBeta
   let w i:= (y i)^(-(1/50:ℝ)); have hp:Tendsto w atTop (𝓝 0):= (tendsto_rpow_neg_atTop (by norm_num : 0<(1/50:ℝ))).comp ht
   let p i:= 4*(w i/fringe)*pulseM A.B.a i
   have hh: Tendsto p atTop (𝓝 0):= by
      have h i: p i= (4/fringe)*(y i)^(-(1/100:ℝ)):=by
         dsimp only [p,w]; unfold pulseM; rw [show 4*((y i^(-(1/50:ℝ)))/fringe)*(y i^(1/100:ℝ))=4/fringe *((y i^(-(1/50:ℝ)))*(y i^(1/100:ℝ))) from ?_, ← Real.rpow_add (show 0<y i from zero_lt_one.trans (A.B.a.fits.delayed i)),show -(1/50:ℝ)+ (1/100)= -(1/100) by ring]
         ring
      rw [show p= _ from funext h]; simpa only [mul_zero,y,Function.comp_apply]  using (((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/100)).comp ht).const_mul (4/fringe))
   filter_upwards [hp.eventually (gt_mem_nhds fringe_pos),hh.eventually (gt_mem_nhds (Real.log_pos (show (1:ℝ)<2 from one_lt_two))),framed hG A.B.a] with m hm hs hk N hv n z hz
   have he : |(ink S N m n hv.le z).im| ≤ w m:= (abs_im_le_norm _).trans (hk N hv.le _ _ _ _ hz); exact ⟨(highP (A:=A) m).le,funds S N m n hv z hz, he.trans hm.le,(mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right he fringe_pos.le) (by norm_num)) (highP (A:=A) m).le).trans hs.le⟩
-- uniform small i
private lemma taps (z:ℂ)(hp:z∈ ball 0 ((flatTime A.B.a)/3))(N n:ℕ)(hm:m<N): |(ink S N m n hm.le z).im| ≤ (UVExtension.Spire.spatial / (flatTime A.B.a/3)) * ‖z‖:=by
    let v := ink S N m n hm.le; let d:= flatTime A.B.a/3; have hD := flat_pos A.B.a; have he :0<d:= by unfold d; positivity
    have hg x(hx:x∈ball (0:ℂ) d): closedBall x d ⊆ Broad A.B.a:= by intro z h; apply mem_ball.mpr; have hx:=mem_ball.mp hx; have hh:=mem_closedBall.mp h; unfold d at *; linarith [dist_triangle z x 0]
    have hf:DifferentiableOn ℂ v Z:= Fitted.nodded (S.fits N n) (S.cart N n) τ m hm.le -- notations N n shadow after: will refer old names.S.F expansion captured. fix
    obtain ⟨b,hb⟩:= yells S N m n hm (Orchard.rose0 S)
    have h0:v 0=(b.val:ℂ):=by simpa only [v,Orchard.rose0,Complex.ofReal_zero] using hb.symm
    have ht: ‖v z-v 0‖≤r!/d*‖z-0‖:= (convex_ball (0:ℂ) d).norm_image_sub_le_of_norm_deriv_le (fun x hx=> hf.differentiableAt (Metric.isOpen_ball.mem_nhds (hg x hx (mem_closedBall_self he.le)))) (fun x hx=>by rw [←  cderiv_eq_deriv Metric.isOpen_ball hf he (hg x hx)]; exact  norm_cderiv_le he (fun y hy=> (mem_ball_zero_iff.mp (upon S N m n hm (hg x hx (sphere_subset_closedBall hy)))).le)) (mem_ball_self he) hp
    rw [sub_zero] at ht; exact (le_trans (b:=‖v z-v 0‖) (by simpa only [sub_im,h0,ofReal_im,sub_zero, v] using (abs_im_le_norm (v z-v 0))) ht) -- simp v too fast
lemma slidingP: ∃ t:ℝ,0<t∧ Metric.ball (0:ℂ) t ⊆ Broad A.B.a ∧ ∀ N n m:ℕ,∀ hm:m<N,∀ z∈ Metric.ball (0:ℂ) t, Speed (pulseM A.B.a m) (ink S N m n hm.le z):= by
   obtain ⟨r,hr⟩:=eventually_atTop.1 (winterM S)
   let d:=flatTime A.B.a/3; have hd:= flat_pos A.B.a; have he:0<d:=by unfold d; positivity
   have hs : ball (0:ℂ) d ⊆ Broad A.B.a:= Metric.ball_subset_ball (by change d≤ _; unfold d; linarith)
   let F'(z:ℂ):= UVExtension.Spire.spatial / d*‖z‖; have hh:Continuous F':=continuous_const.mul continuous_norm
   have hQ(i:Fin r):∀ᶠ z in 𝓝 (0:ℂ),4*(F' z/fringe)*pulseM A.B.a i.val < Real.log 2:= (show Continuous (fun z=>4*(F' z/fringe)*pulseM A.B.a i.val) by fun_prop).continuousAt.eventually (gt_mem_nhds (show 4*(F' 0/fringe)*pulseM A.B.a i.val < Real.log 2 by simp [F',Real.log_pos]))
   obtain ⟨t,ht,hT⟩:= Metric.nhds_basis_ball.mem_iff.mp (((eventually_all.mpr hQ).and (hh.continuousAt.eventually (gt_mem_nhds (show F' 0 < fringe from (by simpa [F'] using fringe_pos))))).and (ball_mem_nhds (0:ℂ) he)); refine ⟨t,ht,fun x hx=> hs (hT hx|>.2),fun N n m h z hz=> ?_⟩; have he:= hs (hT hz|>.2); by_cases hm:r≤ m; exact hr _ hm N h n z he
   have hk:= taps S m z (hT hz|>.2) N n h
   exact ⟨(highP ..).le, funds S N m n h z he,hk.trans (hT hz|>.1.2.le), (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hk fringe_pos.le) (by norm_num)) (highP ..|>.le)).trans (hT hz|>.1.1 (⟨m,by omega⟩:Fin r)|>.le)⟩
end YM.UVExtension.Cloud
