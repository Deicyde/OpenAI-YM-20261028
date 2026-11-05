import YM.TraceExtension.Terrace.Peeking
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Terrace
open Function Filter Set Lattice RG Wilson Labels Source MergeProof MergeProof.Accent Extra.Histories Bid Zn
open Extraction Next.UVStress Next.Rank.Price MergeProof.East Further.CorrectedLift Ward Climb Analysis Work Weir
open Further.PhysicalPeriodLimitF933 Shunt PhysicalNext.Repeat.Quince PhysicalNext.Repeat.Legato.Bandage Push.GridApprox Cells Pressure
open Relay MeasureTheory AnalyticBridge VerifiedReset
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G} (P:C.Makes) (θ:PostT C.path.levels)(h:G.Simple)
set_option quotPrecheck false
local notation "A"=> C.path.levels
local notation "T!"=> C.path
-- caret Package includes louvres at (possibly translated) tiny good event.
structure Crown (C:Family G)(i N p:ℕ)(hp:summit C.path.levels i ≤ N)(f:Film G (C.side (summit C.path.levels i) p)) : Prop where
    cost : let k:= summit C.path.levels i; let t:= C.path.levels.clock.hatBeta k; let X:= Tau C.path.levels i; let B:=tilesAt C.S p ((stellar C.path.levels i).le.trans hp)
           ∃ (g: Config G (C.side k p)→ℂ)(Q: Support (C.side k p))(l:ℕ), Interior (Push.GridApprox.window 0 l) f∧ Interior (Push.GridApprox.window 0 l) g ∧ room C.path.levels i k l∧ (Q.card:ℝ) ≤ X 1000 ∧
             (∀ U,‖f U - g U‖ ≤ X 500000) ∧ (∀ U,Healthy (C.path.levels.clock.threshold k/16) Q U → ‖f U-g U‖ ≤ X (-500000)) ∧ B.rootTest (C.beta N p) (backTo C.path N p hp g) ≤ X (-1200000)
include θ P h
lemma stageCrown : ∀ᶠ i:ℕ in atTop, ∀ N p, let k:=summit (A) i; ∀ hp:k ≤ N,∀ u:Film G (C.side k p), Crown C i N p hp u→ ∀ g:Config G (C.side k p)→ℂ, (∀ U, ‖g U‖ ≤ Tau A i 150000)→ Interior (Push.GridApprox.window 0 (lensScope C 4)) g → room (A) i k (lensScope C 4)→ ∀ a b:Site (C.side i p), a≠b→
      ‖pew C.S ((stellar A i).le.trans hp) (C.beta N p) a b (backTo C.path N p hp u) (backTo C.path N p hp g)‖ ≤ Tau A i (-30000):=by
    let Q:= A; let u(i):= summit Q i; let x(i):=Q.clock.hatBeta (u i)
    have hQ : ∀ᶠ i in atTop,Real.exp (-2* (prism (x i):ℝ)) ≤ Tau (A) i (-1200000):=by
       filter_upwards [(hrate Q h|>.comp (Sstar Q)).eventually (hugeW 100000 (by norm_num)),(lrate Q h).eventually_ge_atTop 1] with i hx hv
       let k:=u i; let L:=Lyra Q k; have hK:i ≤ k:= (stellar Q i).le; have hL:1 ≤ L:= hv.trans (lypos Q h hK); let B:= Gate ((A).clock.hatBeta i); let y:= Gate (x i); have hb:B≤y:= pow_le_pow_left₀ (lira ..|>.le) (lypos Q h hK) _
       apply Real.exp_monotone; norm_num; change 120 *B ≤ _; have hx:100000*y*L ≤ (prism (x i):ℝ)/32:=hx
       have he: 0 ≤ y:= (gate_le _ (Q.fits.delayed k)).le
       linarith only [hx,mul_le_mul_of_nonneg_left hL he,he,hb]
    filter_upwards [hQ, (Sstar Q).eventually (expire P θ h), toll_small (x:=1) one_pos (sapTree h Q 3 (by norm_num))] with i hi hh hx N p k hn u' hv g hG hP he a b ht
    let H₀:= (stellar (A) i).le; let n:=C.side k p; let f:= Tau (A) i; let H':= tilesAt C.S p (H₀.trans hn)
    obtain ⟨w,P',l,hα,hZ,hL,hp,hz,hχ,hB⟩:= hv.cost; let j:=lensScope C 4; let β:= C.beta N p; let V:= backTo C.path N p hn u'; let W':= backTo C.path N p hn w; let U:= backTo C.path N p hn g; let F K:= pew C.S (H₀.trans hn) β a b K U
    have hδ : ‖F W'‖ ≤ f (-1200000)* f 150000:=by
        have hv : Interior (H'.chamber 0) W':=Broom i k N p H₀ hn w _ hZ hL
        have hW : Interior (H'.chamber 0) U:= Broom i k N p H₀ hn g _ hP he
        apply le_trans (pulpit C.S _ _ _ _ ht hv hW (seamless P N p)); have hu := root_sup H' β U hW (f 150000) (Tau_pos ..|>.le) (backTo_bound _ _ _ hn hP.borel _ hG); exact mul_le_mul hB hu (H'.root_nonneg ..) (Tau_pos ..|>.le)
    let e(t : Site (C.S.side i p)): Seat n := (1,anchor C.S p H₀ t); let y(x:Site (C.side i p))(g:Film G n):= g ∘ pull 1 (anchor C.S p H₀ x)
    let L:= u'-w; let R:= y a L*y b g
    have hr : Envelope R:=(show _ from Cask.envUmul ((cylinder_env (Next.UVStress.minus hα hZ)).comp_env (continuous_pull 1 _).measurable) ((cylinder_env hP).comp_env (continuous_pull 1 _).measurable))
    let u₁:= f (-500000)*f 150000; let u₂:= f 500000*f 150000; let M:= (Q.clock.threshold k)/16
    have hσ(t:Config G n):‖R t‖ ≤ u₂:= (norm_mul _ _).trans_le (mul_le_mul (hz _) (hG _) (norm_nonneg _) (Tau_pos ..|>.le)); have hp'(t: Config G n)(ht: Healthy M ((e a).spread P') t): ‖R t‖ ≤ u₁:= (norm_mul _ _).trans_le (mul_le_mul (hχ _ (Seat.healthy (e a) M P' t|>.1 ht)) (hG _) (norm_nonneg _) (Tau_pos ..|>.le))
    have hT: F (backTo C.path N p hn L)= Wilson.moment β (backTo C.path N p hn R):=by
        rcases le_or_gt j l with h|h
        · exact backProd i k N p H₀ hn a b ht L g l (Next.UVStress.minus hα hZ) (hP.enlarges (win_inc j l 0 h)) hL
        exact backProd i k N p H₀ hn a b ht L g j ((Next.UVStress.minus hα hZ).enlarges (win_inc _ _ 0 h.le)) hP he
    have hv' : ‖F (backTo C.path N p hn L)‖ ≤ u₁ +u₂*(f 1000)* f (-1200000):=by
       rw [hT]; apply (hh p N (show 0< summit .. from lt_of_le_of_lt (Nat.zero_le _) (stellar ..)) hn _ R u₁ u₂ hr (mul_nonneg (Tau_pos ..|>.le) (Tau_pos ..|>.le)) hσ hp').trans; apply add_le_add (le_refl _); apply mul_le_mul _ hi (Real.exp_pos _).le (show 0 ≤ u₂*f 1000 from mul_nonneg (mul_nonneg (Tau_pos ..|>.le) (Tau_pos ..|>.le)) (Tau_pos ..|>.le)); exact mul_le_mul_of_nonneg_left ((Nat.cast_le.mpr (Finset.card_image_le)).trans hp) (by unfold u₂;exact mul_nonneg (Tau_pos ..|>.le) (Tau_pos ..|>.le))
    change ‖F V‖≤ _; rw [show F V =F W'+F (backTo C.path N p hn L) from differ i k N p H₀ hn a b u' w g (cylinder_env hα) (cylinder_env hZ) (cylinder_env hP)]; apply (norm_add_le ..).trans; apply (add_le_add hδ hv').trans; have hp(s t:ℝ): f s*f t=f (s+t):= (Tau_add ..).symm; unfold u₁ u₂; rw [hp,hp,hp,hp,hp]
    have he₁ : f (-1200000+150000) ≤ f (-31000):= tau_mono _ _ (by norm_num); have he₂ : f (-500000+150000) ≤ f (-31000):= tau_mono _ _ (by norm_num); have he₃ : f (500000+150000+1000+ -1200000) ≤ f (-31000):= tau_mono _ _ (by norm_num); apply le_trans _ (c:=f (-30000)) (b:=3*f (-31000)); swap; · linarith only[he₁,he₂,he₃]
    exact (mul_le_mul_of_nonneg_right (show 3 ≤ f 1 from hx) (Tau_pos ..|>.le)).trans ((hp _ _).le.trans (tau_mono _ _ (by norm_num)))
end YM.Trace.Terrace
