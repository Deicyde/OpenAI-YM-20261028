import YM.TraceExtension.Terrace.Prism
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Terrace
open Function Filter Set Lattice RG Wilson Labels Source MergeProof MergeProof.Accent Extra.Histories Bid Zn
open Extraction Next.UVStress Next.Rank.Price Next.Rank.East MergeProof.East Further.CorrectedLift Ward Climb Analysis StressFlux
open Further.PhysicalPeriodLimitF933
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}
section Record
abbrev watch (P:Levels G)(a:ℝ)(k:ℕ):=Real.exp (a*Gate (P.clock.hatBeta k))
def Ticket(P:Levels G)(a:ℝ)(v:ℕ → ℝ):Prop:=∀ b:ℝ,a<b→∀ᶠ i:ℕ in atTop, 0≤v i∧v i≤watch P b i
variable {P:Levels G} {x:ℝ} {f g:ℕ →ℝ}
lemma ticket_exp (P:Levels G)(x:ℝ) : Ticket P x (watch P x):=by intro b hb; refine Eventually.of_forall fun i=> ⟨(Real.exp_pos _).le, Real.exp_monotone (mul_le_mul_of_nonneg_right hb.le (gate_le _ (P.fits.delayed i)|>.le))⟩
lemma sapTree (h:G.Simple)(P:Levels G)(c:ℝ)(hp:0 ≤ c):Ticket P 0 fun _=>c:=fun b hb=> ( (Real.tendsto_exp_atTop.comp ((grate P h).const_mul_atTop hb)).eventually_ge_atTop c).mono fun _ h=> ⟨hp,h⟩
lemma Ticket.prod {a b:ℝ} (h:Ticket P a f)(hp:Ticket P b g):Ticket P (a+b) (fun i=>f i*g i):=by
    intro c hc; let t:=(c-(a+b))/2; have ht:0 < t:=by unfold t;linarith
    filter_upwards [h (a+t) (by linarith),hp (b+t) (by linarith)] with i hi hj; exact ⟨mul_nonneg hi.1 hj.1,(mul_le_mul hi.2 hj.2 hj.1 (Real.exp_pos _).le).trans_eq (by unfold watch;rw[← Real.exp_add];congr 1; unfold t; ring)⟩
lemma Ticket.push (h:Ticket P 0 f)(hp:Ticket P 0 g): Ticket P 0 (fun i=> f i*g i):=by simpa only[zero_add] using h.prod hp
lemma Ticket.sum (hf:Ticket P x f)(hp: Ticket P x g)(h:G.Simple): Ticket P x (fun i=> f i+g i) :=by
    intro b hb; let y:=(x+b)/2; have hx:y>x:=by unfold y; linarith
    have hy:0 < b-y:=by unfold y; linarith
    filter_upwards [hf _ hx,hp _ hx,sapTree h P (2:ℝ) zero_le_two _ hy] with i hi hj hk
    exact ⟨add_nonneg hi.1 hj.1, (add_le_add hi.2 hj.2).trans ((two_mul _).symm.le.trans ((mul_le_mul_of_nonneg_right hk.2 (Real.exp_pos _).le).trans_eq (by unfold watch;rw [← Real.exp_add]; congr 1; ring)))⟩
lemma Ticket.pows (hf:Ticket P 0 f) (h:G.Simple)(p:ℕ): Ticket P 0 (fun i=>f i^p):=by induction p with
    | zero=> simpa only[pow_zero] using sapTree h P _ zero_le_one
    | succ p IH=> simp_rw[pow_succ];exact IH.push hf
lemma Ticket.mono (hf:Ticket P x f)(h:∀ᶠ i in atTop,0 ≤ g i∧g i ≤ f i): Ticket P x g:=by intro b hb;filter_upwards[h,hf _ hb] with i hi he using ⟨hi.1,hi.2.trans he.2⟩
lemma whither (hf:Ticket P x f)(h:G.Simple)(hx:x<0): Tendsto f atTop (𝓝 0):=by
    have he :=hf (x/2) (by linarith); exact squeeze_zero' (he.mono fun i h=> h.1) (he.mono fun i h=>h.2) (Real.tendsto_exp_atBot.comp ((grate _ h).const_mul_atTop_of_neg (show x/2<0 by linarith)))
lemma favorite (P:Levels G)(h:G.Simple): Ticket P 0 P.clock.hatBeta:=by
    intro b hb; filter_upwards [(hrate P h).eventually (exponent_gate b 1 0 hb)] with i hi; exact ⟨(bell ..).le, by simpa [watch] using! hi⟩
lemma stickK (P:Levels G)(h:G.Simple)(θ:PostT P): Ticket P 0 (fun i=>P.clock.hatBeta (summit P i)):= ((sapTree h P 2 zero_le_two).push (favorite P h)).mono ( (bond P h θ).mono fun i h=>⟨(bell ..).le,h.1⟩)
lemma LyreK (P:Levels G)(h:G.Simple): Ticket P 0 (Lyra P):=(favorite P h).mono (Eventually.of_forall fun i=>⟨(lira ..).le,Real.log_le_self (bell ..|>.le)⟩)
-- r / a_measure
abbrev tilt_cap (P:Levels G)(i:ℕ):= Next.Rank.Station.mag P (Next.Rank.Perch.y (P.clock.hatBeta i)) i
lemma titles (P:Levels G)(h:G.Simple): Ticket P 0 (tilt_cap P):=by
    intro b hb; filter_upwards[(lrate P h).eventually_ge_atTop 1,(hrate P h).eventually (gate_flex 3 (by decide) hb)] with i hP hB
    let x:=P.clock.hatBeta i; let y:= Lyra P i; let u:=Real.log y; have hp:0 ≤ u:=Real.log_nonneg hP; refine ⟨(Next.Rank.Station.mag_pos ..).le,?_⟩; unfold tilt_cap Next.Rank.Station.mag; change (Real.exp (u^2))^u ≤ _; rw[← Real.exp_mul]; apply Real.exp_monotone;apply le_trans _ hB; exact (show u^2*u=u^3 by ring).le.trans (pow_le_pow_left₀ hp (Real.log_le_self (zero_le_one.trans hP)) 3)
lemma hullK (P:Levels G)(K:Stock.Tabs P)(h:G.Simple)(θ:PostT P): Ticket P 0 (fun i=>P.S.a i/P.S.a (basin P K i)):= ((LyreK P h).pows h 6).mono ((Bgap P h θ K).mono fun i hi=>⟨(div_pos (P.S.a_pos _) (P.S.a_pos _)).le,hi.1⟩)
lemma stakeK {C:Family G}(K:Stock.Tabs C.path.levels)(h:G.Simple)(θ:PostT C.path.levels) : Ticket C.path.levels 0 (fun i=> stakes C i (basin _ K i)):=by
    let Q:= C.path.levels
    intro b hb; filter_upwards [liability _ h θ K,( (grate Q h).const_mul_atTop (half_pos hb)).eventually_ge_atTop 5, (hrate Q h).eventually (gate_flex 27 (by decide) (half_pos hb))] with i hi hv hp
    refine ⟨(Real.exp_pos _).le,Real.exp_monotone ?_⟩; change Lyra Q i^27≤_ at hp; linarith only[hi,hv,hp]
end Record
end YM.Trace.Terrace
