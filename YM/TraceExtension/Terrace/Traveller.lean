import YM.TraceExtension.Terrace.Au
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Terrace
open Function Filter Finset Set Lattice RG Wilson Labels Source MergeProof MergeProof.Accent Extra.Histories Bid Zn
open Extraction Next.Rank.Price Next.Rank.East MergeProof.East Further.CorrectedLift Ward Climb Analysis StressFlux Next.UVStress
open Further.PhysicalPeriodLimitF933 Next.Rank.Spindle Cells PhysicalNext.Repeat.Legato.Bandage Push.GridApprox
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G}
lemma cheap_theta (A:Levels G)(k:ℕ): ((A.budget k).threshold^ (2:ℕ))⁻¹ ≤ A.clock.hatBeta k:=by
    let t:=(A.budget k).threshold; let x:=A.clock.hatBeta k; have hp:0<x:=bell ..
    have hz : (Real.sqrt x)⁻¹ ≤ t := le_mul_of_one_le_right (inv_nonneg.mpr (Real.sqrt_nonneg x)) (Real.one_le_exp (sq_nonneg _)); have hr:0 < (Real.sqrt x):= Real.sqrt_pos.mpr hp
    change (t^ (2:ℕ))⁻¹≤_; exact (inv_anti₀ (pow_pos (inv_pos.mpr hr) _) (pow_le_pow_left₀ (inv_pos.mpr hr).le hz 2)).trans_eq (by rw[inv_pow,Real.sq_sqrt hp.le,inv_inv])
variable (h:G.Simple)(θ:PostT C.path.levels)(K:Stock.Tabs C.path.levels)
set_option quotPrecheck false
local notation "A"=> C.path.levels
local notation "T!"=> tilesAt C.S
open Relay
variable (H:C.Makes) {W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (ht:Scrim C W u ψ φ δ (fly C.path.levels) r D)(hM:Sceptre C W)
include H ht h K θ hM
local notation "V!"=> C.labels.level 5
-- OA budget funded directly from operators chosen at anchor; centers still observable.
lemma concert (m:ℕ): ∀ᶠ j:ℕ in atTop,let k:=summit C.path.levels j;let b:=C.S.a j;let t:=(A).clock.hatBeta k
    ∀ᶠ p:ℕ in atTop,∀ N:ℕ, k < N → ∀ (x:C.label 5), night V! x → (V!).coeffSize (columns C 5 k N p x) ≤ b^5*t^m → ∀ hj:j ≤ N, (tilesAt C.S p hj).rootTest (C.beta N p) (C.O N p x 0) ≤ Tau (A) j 5:=by
    let P:=C.path.levels; let t i:=(A).clock.hatBeta (summit P i); have htP(k):0<(A|>.budget k).threshold:= (P.budget k).threshold_pos
    have he:= (sapTree h P 2 zero_le_two).push ((stickK _ h θ).pows h (m+1))
    filter_upwards [toll_small (x:=1) one_pos he,journey h θ K H ht 5,open_budget P h θ K,spine_pitch C W h θ hM 5 le_rfl,eventually_ge_atTop (C.ref 5),(parts_rate (A) h).eventually (ge_mem_nhds (show (0:ℝ)<1 by norm_num))] with j hx hi hK hP hh hz k b β
    filter_upwards[hP] with p hP N hN x hn hL hm
    let i:=basin P K j; have hp(j')(hl:j≤ j')(h:j' ≤ k): night (C.labels.level 5) (columns C 5 j' N p x):= night_space C H ht (hh.trans hl) (h.trans hN.le) x hn
    apply hi _ _ hN x hm; have hs i'(hl : j ≤ i')(hc:i'≤k): (V!).coeffSize (spine C 5 i' N p x)= ((P.budget i').threshold^ (2:ℕ))⁻¹*(V!).coeffSize (columns C 5 i' N p x):=by
        unfold spine Cturn; rw [nights (V!) (hp i' hl hc),count_smul,Real.norm_of_nonneg]; have h:= htP i';positivity
    have he:=hP _ hN.le x (fun i' he hj=> night_grade (V!) (hp i' he hj) h) i (unwinds ..) hK.le
    let f:=(V!); let L:= f.coeffSize (columns C 5 k N p x); have hz':0 ≤ L:= Work.G08.size_nonneg ..
    have he': (V!).coeffSize (spine C 5 i N p x) ≤2* (V!).coeffSize (spine C 5 k N p x):=by
       have hr:part P j ≤1:=hz; linarith only [he,Work.G08.size_triangle (V!) (spine C 5 i N p x) (spine C 5 k N p x),mul_le_mul_of_nonneg_right hr (Work.G08.size_nonneg f (spine C 5 k N p x))]
    rw[hs i (unwinds ..) hK.le,hs k (stellar ..|>.le) le_rfl] at he'
    let J:=(P.budget i).threshold; have hR:0<J:=htP i; have hJ:J ≤1:=(P.budget i).threshold_le; have hJ': 1 ≤ (J^ (2:ℕ))⁻¹:= by have hH:= pow_le_one₀ hR.le hJ (n:=2); exact (inv_one (G:=ℝ)).symm.le.trans (inv_anti₀ (by positivity) hH)
    apply le_trans ((le_mul_of_one_le_left (Work.G08.size_nonneg ..) hJ').trans he'); have hθ:=mul_le_mul (cheap_theta P k) hL hz' (bell ..|>.le); refine le_trans (mul_le_mul_of_nonneg_left hθ zero_le_two) ?_; change 2*(β*(b^5*β^m))≤ _; apply le_trans _ (mul_le_mul_of_nonneg_left hx (pow_nonneg (C.S.a_pos j).le 5)); apply le_of_eq; change _=b^5*(2*β^(m+1)); ring
omit hM
-- ext w boot pairing + stem accuracy
lemma outside (d:ℕ)(hd:d≤5)(v:C.label d) : ∀ᶠ i in atTop,∀ N p (hN:summit (A) i < N),∀ (T0:Module.End ℂ (C.label d)),Tested C d i N p T0→∀ (b:ℝ),1 ≤ b→ b ≤ tilt_cap (A) i→
    let V:=ladd C b i N p d T0 v;let B:= summit (A) i;let f:= tilesAt C.S p ((stellar (A) i).le.trans hN.le); let X:=Tau (A) i; (∀ v:C.label d,Interior (f.chamber 0) (C.O N p v 0)) → f.rootTest (C.beta N p) (C.O N p V 0) ≤ X 5 ∧ ∃ g: Config G (C.side B p)→ℂ,(∀ x, ‖g x‖ ≤ X 150000) ∧ Interior (Push.GridApprox.window 0 (lensScope C d)) g ∧ room (A) i B (lensScope C d) ∧ Interior (f.chamber 0) (backTo C.path N p hN.le g) ∧ f.rootTest (C.beta N p) (backTo C.path N p hN.le g-C.O N p V 0) ≤ X (-300) :=by
    filter_upwards [journey h θ K H ht d,smithies h θ K H ht d,capacity_cost H d hd h θ v (1*Dust) (by norm_num),open_budget (A) h θ K] with i hE hF hX hK N p hN T0 hT b hp hq V B f X hf
    obtain ⟨g,hU,hg⟩:= hF N p hN V hf (hX N p hN.le T0 hT b hp hq _ (stellar ..|>.le) le_rfl)
    refine ⟨hE N p hN V _ (hX N p hN.le _ hT b hp hq _ (unwinds ..) hK.le),g, fun x=>(hU x).trans ?_,hg⟩
    have hp : (d:ℝ) ≤ 5:=by exact_mod_cast hd
    exact tau_mono (A) i (by linarith only [hp])
end YM.Trace.Terrace
