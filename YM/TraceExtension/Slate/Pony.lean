import YM.TraceExtension.Slate.Limit
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Slate
open Function Filter Lattice RG Wilson Labels Source Extra.Histories Bid MergeProof.Accent MergeProof
open Extraction Next.Rank.Price Next.Rank.East MergeProof.East Further.CorrectedLift Climb Analysis Work
open MeasureTheory
open Further.PhysicalPeriodLimitF933 Shunt Weir PhysicalNext.Repeat.Legato.Bandage Push.GridApprox Cells
open Relay Pull Terrace Terrace.Glade Perfect Turret Margin
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G}
variable (P:C.Makes) (h:G.Simple) (θ:PostT C.path.levels)(K:Stock.Tabs C.path.levels)
variable {W:Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p i:ℕ,i<N→GaugeDoor (C.path.rep N p (i+1)) (C.path.rep N p i)}
variable (ht:Scrim C W u ψ φ δ (fly C.path.levels) r D)(hM:Sceptre C W) (hT:supportQ C.path.levels)
variable {F:Extraction.Order}{𝓛:Ultrafilter (ℕ×ℕ)} (hb:(𝓛:Filter (ℕ×ℕ))≤F.fuse)
set_option quotPrecheck false
local notation "A"=> C.path.levels
local notation "V!"=> C.path
local notation "b!"=> (𝓛:Filter (ℕ×ℕ))
local notation "H!"=> C.path.levels.clock.hatBeta
variable {t:Tickets C} (hu:Grant C (𝓛:Filter (ℕ×ℕ)) t)
open Zn
variable {d:ℕ}{Z:Arch C}(hz:steep 𝓛 Z)
open Finset StressFlux
local notation "Fᵣ"=> C.labels.level 4
local notation "Zᵣ"=> C.labels.level 5
variable {X:Axis→ Logs C 5}(hp:∀ i,TravelsC (𝓛:Filter (ℕ×ℕ)) (exhibit t i) (Readout t i) (X i).v (X i).x)
abbrev Pig(R: Levels G):=AgeK R ((1:ℝ)/6)
include hz hp P h hb hu
lemma penumbra : ∃ c:ℝ,0≤c ∧ (∀ᶠ k in atTop,‖Shine5 Z X k‖≤ c*Pig A k) ∧ Tendsto (fun k=> Lease Zᵣ h (Shine5 Z X k)) atTop (𝓝 (-G.slopeConstant)):=by
    let F:= (Zᵣ); let ρ:=Lease F h; let T:= OrbitR F;let f:= MintR F h
    let P' (k:ℕ):=4*‖f‖*AgeK A (-1) k+calorie (H! k)/12+shock (H! k)/12
    have hk:= eventually_all.mpr (fun i=>TravelsC.hi hz (v:=X i) (hp i));
    let g(k):= ‖f‖*loss (A) k+ P' k; have hT: ∀ᶠ k:ℕ in atTop,‖Shine5 Z X k‖ ≤ (2*‖T‖)*Pig A k ∧ ‖ρ (Shine5 Z X k) - (-G.slopeConstant)‖ ≤ g k:=by
       have he':= eventually_all.mpr fun i=> rift (v:=X i) (hp i)
       filter_upwards [hu,hk,he'] with k hi ht hR; let v(p:ℕ×ℕ):= Roll k p X; let q:= Pig A k; let r:=barter A k
       have hz:Tendsto v b! (𝓝 (fun a=> hence Z (X a) k)):= tendsto_pi_nhds.mpr ht
       have hu:= h.nontrivial_color
       have hu: Nonempty G.ColorIndex:=by
          by_contra! he; haveI:IsEmpty G.ColorIndex:=he
          have h':Subsingleton G.Color:= ⟨fun x y=> by ext i; exact IsEmpty.false i|>.elim⟩; exact not_subsingleton_iff_nontrivial.mpr hu h'
       let a:= Classical.choice hu; let L(p:ℕ×ℕ):=r • (fun i=> Readout t i k p); let y(p:ℕ×ℕ)(i:Axis):=F.core (L p i)
       have hZ':∀ᶠ p:ℕ×ℕ in b!, ‖T (v p)‖ ≤ (2*‖T‖)*q ∧ ‖f (v p)-(-G.slopeConstant)‖ ≤ g k:=by
          filter_upwards [hi,(link_mesh hb).eventually_gt_atTop k,eventually_all.mpr hR] with p hu hN hR
          let Q:= t k p.1 p.2; let R:= C.path.rep p.1 p.2 k; let c:=(A).budget k;let z:= H! k
          have hm:R.p=c:= (P.wilson.represents _ _ k hN.le).vac
          obtain ⟨b',w,c',h'⟩:=hu.cover
          obtain ⟨he,hξ⟩:= brass a h h'.pay hu.ready.1 h'.solace (reachBW hu) hu.site (le_trans (by norm_num:5≤6) R.p.order_ge) (show _ from hu.age.thresh) Q.X (fun i=>hu.boat i)
          have hy: Revise R (fun i=> (Q.X i).x)=L p:=by unfold Revise; rw [hm];rfl
          have hZ:‖L p‖ ≤ q:=by rw [← hy]; exact he
          have h₁:‖y p‖ ≤ q:= (pi_norm_le_iff_of_nonneg (Zn.wake ..|>.le)).mpr fun i=> (cost_range F _).trans ((norm_le_pi_norm _ _).trans hZ)
          have h₂:‖v p - y p‖ ≤ loss A k:=by rw [norm_sub_rev, pi_norm_le_iff_of_nonneg (show 0 ≤ loss A k from Zn.wake ..|>.le)]; exact hR
          have hx₃: f (y p)=f (L p):=by unfold f; rw [MintR_eq]; change ρ (OrbitR _ (fun i=> _))= _; rw[orbit_core];rfl
          refine ⟨(T.le_opNorm _).trans ((mul_le_mul_of_nonneg_left (norm_le_norm_sub_add _ _ |>.trans (add_le_add h₂ h₁)) (norm_nonneg _)).trans ?_),?_⟩
          · have he: loss A k ≤ q:= Zn.wane z (by norm_num); linarith only [mul_le_mul_of_nonneg_left he (norm_nonneg T)]
          have hw:= lace f (v p) (y p) _ h₂; have hY := norm_sub_le_norm_sub_add_norm_sub (f (v p)) (f (y p)) (-G.slopeConstant)
          apply hY.trans (add_le_add hw ?_); rw[hx₃,← hy]; let t':=Loft.midPay a Q.J; apply (norm_sub_le_norm_sub_add_norm_sub _ (t'/12) _).trans; apply add_le_add hξ
          rw[← show Loft.landPay G/12=(- G.slopeConstant) from by unfold Loft.landPay;ring,← sub_div,norm_div, Real.norm_of_nonneg (by norm_num:0 ≤(12:ℝ))]; exact div_le_div_of_nonneg_right (hu.accurate a) (by norm_num)
       have hP:Tendsto (fun p=> T (v p)) b! (𝓝 (Shine5 Z X k)):= T.continuous.continuousAt.tendsto.comp hz
       exact ⟨le_of_tendsto hP.norm (hZ'.mono fun i h=>h.1), le_of_tendsto (((ρ.continuous.continuousAt.tendsto.comp hP).sub_const (-G.slopeConstant)).norm) (hZ'.mono fun i h=>h.2)⟩
    have he(k:ℕ)(hk:k≠0): Tendsto (fun j : ℕ=> ((H! j)^k)⁻¹) atTop (𝓝 0):= tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop hk).comp (hrate A h))
    have hG:Tendsto g atTop (𝓝 0):=by
        have hi:= Age_rate A (by norm_num: (-(1/4:ℝ)) <0) h; have hf:= (Age_rate A (by norm_num: (-(1:ℝ)) <0) h).const_mul (4*‖f‖); simpa only [zero_div,g, P',calorie,Zn.shock,loss,mul_zero,add_zero] using! ((hi.const_mul ‖f‖).add ((hf.add ((he 30 (by decide)).div_const 12)).add ((he 100 (by decide)).div_const 12)))
    refine ⟨2*‖T‖,by positivity, hT.mono (fun k hi=>hi.1),Metric.tendsto_nhds.mpr ?_⟩
    intro ε hε; filter_upwards[hT,hG.eventually (gt_mem_nhds hε)] with k hi hx; rw[dist_eq_norm]; exact hi.2.trans_lt hx
end YM.Trace.Slate
