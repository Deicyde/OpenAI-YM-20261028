import YM.TraceExtension.Margin.Ansel
import YM.MergeProof.Almandine
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Margin
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open Next.Rank East
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Graces PhysicalNext.Repeat.Roost
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open Push.PriceCompiler WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset Planned.GuardedAtom Guard
open Shepherd StressFlux Perfect Loft Zn Shunt Wicket Turret Weir Terrace
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge}{Qp : Sheet G} {V: Rolls Qp} {θ:Protection V} {U: Delays θ}
def Acclaim (T: Levels G): Prop:= ∀ᶠ k:ℕ in atTop, StoreQ (Labels.frames G) (localSection G) (hol G) (T.params k) (T.clock.hatBeta k) ∧
   -- expense at measured theta
    let P:= T.params k; let x:=T.clock.hatBeta k; ∀ (w:ℝ),1 ≤ w → w ≤ Real.exp ((Terrace.prism x:ℝ)/32) →∀ (n:Side)(R:Rep G n)(Λ:ℝ), Age P x Λ R→∀ z:ℝ, Shepherd.tariff R (wingC R z P.width P.paths Λ) (2*hue x) ≤ 1 → ExpenseH P.paths Λ (Weir.smoke x) (Weir.hue x) 1 P.width x z w R TileNo (wheelQ x) (Terrace.prism x)
lemma honor (K:Levels G)(h:Acclaim K): auraQ K TileNo:= h.mono fun _ i=>i.2
lemma flows (U: Delays θ)(h:G.Simple): ∃ W:Delays θ,DelayLe U W∧∀ V:Delays θ,DelayLe W V→∀ (D:RG.Supply.Bar V)(I:Wait D)(A:Levels G), Paid I A→ Acclaim A:=by
   let K:= Labels.frames G; let H:=Next.Foundations.hol G; let L:=localSection G
   let P (i:ℕ)(x:ℝ):Prop:= StoreQ K L H (Qp.profile i) x ∧ (let P:= Qp.profile i; ∀ (w:ℝ),1 ≤ w → w ≤ Real.exp ((Terrace.prism x:ℝ)/32) →∀ (n:Side)(R:Rep G n)(Λ:ℝ), Age P x Λ R→∀ z:ℝ, Shepherd.tariff R (wingC R z P.width P.paths Λ) (2*hue x) ≤ 1 → ExpenseH P.paths Λ (Weir.smoke x) (Weir.hue x) 1 P.width x z w R TileNo (wheelQ x) (Terrace.prism x))
   have hp(j:ℕ):∀ᶠ x:ℝ in atTop,∀ i,StepStages j i→ P i x:= eventually_transitions j atTop _ (fun i _=> (taxes G (Qp.profile i) h K L H).and (priest G _ (l:=TileNo)))
   obtain ⟨y,-,hy,H⟩:= collect_upper U.betaEntry _ hp
   refine ⟨{U with betaEntry:=y},⟨hy,le_rfl,le_rfl,le_rfl⟩,fun W hw D I A h=> Eventually.of_forall ?_⟩
   intro i; rw [params_eq h i]; exact H _ _ ((hw.beta _).trans (h.pays i)) _ (step_paid A i)
variable {M : Metals G}{D:Rolls M.p}{A:Alloy M D}{X:Factor A}{B:Bolt A}{P:Family G}
section
lemma loop_gauge (S:Levels G)(i:ℕ)(hp:1000≤ S.clock.J i): S.clock.loopCap i ≤ humble (S.clock.hatBeta i):=by
    let x:=S.clock.hatBeta i; let f:=Wave 1 x; let v:= S.clock.theta (S.clock.J i);
    have he : v ≤ 1/1000:= (S.fits.thetaRange i|>.2).trans (by have ht : (1000:ℝ) ≤ (S.clock.J i:ℝ):=(by exact_mod_cast hp); rw[one_div]; exact inv_anti₀ (by norm_num) ht)
    rw [Calendar.loopCap,oracle]; change 2*f^v ≤ _; have hm : 1 ≤ f:=Zn.wok _ _ (by positivity)
    refine (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hm he) zero_le_two).trans_eq ?_; unfold f humble Wave Zn.RLog;rw [one_mul,← Real.exp_mul,mul_comm]; congr 2; rw [mul_comm]
lemma robes (V:Levels G)(h:supportQ V) : supportQ V:= h
lemma ancient (hk:Nest X B)(h:supportQ A.B.a)(hG:G.Simple):∀ᶠ i in atTop, ∀ (N p:ℕ), i<N → let U:= A.B.a; let S:=U.params i; Age S (U.clock.hatBeta i) (U.clock.loopCap i) ((Issue.trail B).rep N p i):=by
    let U:=A.B.a;filter_upwards [U.fits.deep.eventually_ge_atTop 1000,h] with i hi he N p hI U' P
    let R:=(Issue.trail B).rep N p i; let Y:= U.budget i; let x:=U.clock.hatBeta i
    have hz : U.clock.loopCap i ≤ humble x:=loop_gauge U i hi
    have hv:=(B.choice.represents N p i hI.le); have hB:R.p=Y:=hv.vac
    obtain ⟨l,t,Q,V,u,hu,hU,hY⟩:= (hk.held N i p hI).1; have hw:= (X.machine.passes hI V.knows).1
    have ha : (Issue.trail B).levels=U:=rfl; have hb:R.Lawful P.width P.paths (U.clock.loopCap i) (Weir.hue x) (Weir.smoke x):=by rw [show Weir.smoke x= _ from Harmony U i]; exact hv.good
    have hx:R.clip=P.clip:=hv.clip; have hM := hb.paths; have hm:= hM.two
    have he' : R.path.Bounds P.clip P.width P.paths (humble x):= hx ▸ ⟨hM.width, hM.rows,⟨hm.1,hm.2.1,hm.2.2.trans hz⟩,hM.three,hM.four,hM.invariant,hM.symTerms,hM.metric,hM.loopTerms,hM.loop_normal⟩
    have hy:R.beta ≤2*x:=hv.band.2
    refine ⟨⟨hx,hB ▸ rfl,he'⟩, hB ▸ rfl,hB ▸ rfl,hB ▸ rfl,hB ▸ Tanya U i, ?_, ?_, hb,hz,?_,?_⟩
    · rw [abs_of_pos (Overlay.beta_positive B.choice hI.le)]; exact hy.trans (by have h:=bell U i;linarith)
    · change Width R.p R.clip P.width; rw [hx,hB]; exact hw.width
    · change Decent R.clip R.p; rw[hB,hx]; exact hw.decent
    change 4 ≤ R.p.supportExponent; rw[hB]; exact he
end
end YM.Trace.Margin
