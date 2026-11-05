import YM.UVExtension.Gale.Foil
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Cloud
open Function Filter Set Real Lattice RG RG.Supply Wilson Precision Shoot Stock Org Input Extra.Histories Source Labels
open PhysicalNext PhysicalNext.Repeat Spire Orchard Lacing Eyelet
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Mallow Lotus Legato.Bandage Lacing.RoutesF MergeProof
open Planned.GuardedAtom Guard
open Push Push.AbsoluteSums
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open Pressure Pressure.Testing ConnectedActivityE6 Payroll Linden Guild
variable (G:Gauge)(s:Sheet G) (K:MapPrices) (X:Targets s K)(U:Expenses X)
-- cap reach.a.Coins terms L pay polynomial for all d≤j chosen before L does include target halo etc. clearance.
def Steep (F:ℕ→ℕ):Prop:= ∀ j i,StepStages j i →∀ (p:Side), F j≤p.val→ (∀ W μ a η ξ v q k o n, 0<W→0<μ→0 ≤ a →0≤ξ → ξ<(X j i).exp→0<v→(X j i).rate+v<η→η<0→ ∀ᶠ x in atTop,WorthP (X j i) W μ a x q k o p (betaF G x p ^v) ξ n) ∧ ∀ d≤j,24* coined (X j i) d ≤ p.val
include U
lemma snow: ∃ P:ℕ→ℕ, Steep G s K X P:=by
   choose p hp using fun i j=> lives (X i j) (U i j)
   let q(i j:ℕ):= ∑ k∈Finset.range (i+1), Nat.ceil (24*coined (X i j) k); let v i j:= p i j+ q i j
   refine ⟨fromMax v,fun i j h L hx=>?_⟩
   have ht:v i j≤ L.val:=(le_fromMax _ h|>.trans hx); constructor
   · intro W μ a η ξ v q k o n hW hm ha hξ h' hv H hA; exact hp i j L ((Nat.le_add_right ..).trans ht) W μ a q k n ξ v η o hW hm ha hξ h' hv H hA
   intro d hd; refine le_trans (Nat.le_ceil _) ?_; exact Nat.cast_le.mpr ((Finset.single_le_sum (f:=fun k=>Nat.ceil (24*coined (X i j) k)) (fun _ _=> Nat.zero_le _) (Finset.mem_range.mpr (Nat.lt_add_one_iff.mpr hd))).trans ((Nat.le_add_left ..|>.trans ht)))

variable {s K X U}{D:Rolls s}{Θ:Protection D}{F0:ℕ→ℕ}
omit U
include X
local notation "P"=> X
variable {G}
variable (Y:ℕ→ℝ)
-- use hY>0 at application from R.clock. buy condition β.ε
private def Slip (j i k:ℕ)(x:ℝ):= let L:=D.L j; let F:=(Labels.frames G).level k; let V:=s.profile i; let W:=s.profile j; let p:=Local.factor (hol G) (localSection G k) V.supportExponent (Next.Foundations.price G (max V.order V.power)); let q:=reflux (betaF G x L) (coined (X j i) 0) p (Blush.glyph x) (L.val^k:ℝ) (Push.Local.readPrice (hol G) F); Y j>0→ Mind F L V.order V.power (Doors.rate L) (Y j) q (q*(Real.exp W.supportExponent* title G W)) (shill x)
lemma atStake (j i k:ℕ): ∀ᶠ x in atTop,Slip (X:=X) (D:=D) Y j i k x:=by
   let L:=D.L j; let F:=(frames G).level k; let H:= Extra.Histories.Doors.rate L; let V:=s.profile i; let W:= s.profile j; let φ:=Push.Local.factor (hol G) (localSection G k) V.supportExponent (Next.Foundations.price G (max V.order V.power))
   let f(x):=reflux (betaF G x L) (coined (X j i) 0) φ (Blush.glyph x) (L.val^k:ℝ) (Local.readPrice (hol G) F); have hp: Tendsto (fun x=>f x / exp (shill x)) atTop (𝓝 0):= calling ..
   let a:=Motion.orbitCost F; let b:= ((F.extra+1:ℕ):ℝ); let t:= Local.turnCost V.order V.power; let G0:= Real.exp W.supportExponent*title G W; let g x:= f x*G0; let y:=Y j; let w:=y*(L.val:ℝ)^k; let e(x):=Real.exp (shill x); have hu:0<H:= Doors.rate_pos _
   have hg:Tendsto (fun x=>g x/e x) atTop (𝓝 0):=by
       simpa only [mul_zero,mul_div_assoc,g,mul_comm (f _)] using! hp.const_mul G0
   have he:Tendsto e atTop atTop:= Real.tendsto_exp_atTop.comp (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/100))
   have hP: Tendsto (fun x=> a*(b*g x+w)/e x) atTop (𝓝 0):=by
      simpa only [mul_zero,zero_add,mul_div_assoc,add_div] using! (((hg.const_mul b).add (he.const_div_atTop _)).const_mul a)
   by_cases hv: y>0; swap; · exact Eventually.of_forall fun x (hx:Y j >0)=> (hv hx).elim
   filter_upwards [hp.eventually (gt_mem_nhds hu), (hp.const_mul (a*b)).eventually (gt_mem_nhds (by simpa using hu)),(hp.const_mul t).eventually (gt_mem_nhds (by simpa using hu)), hP.eventually (gt_mem_nhds hu), (hg.const_mul t).eventually (gt_mem_nhds (by simpa using hv))] with x _ hK ht hA hQ
   have he:0<e x:= Real.exp_pos _
   intro hx; refine ⟨(div_le_iff₀ he).1 ?_,(div_le_iff₀ he).1 ?_,(div_le_iff₀ he).1 hA.le,(div_le_iff₀ he).1 ?_⟩
   · rw [mul_div_assoc]; exact hK.le
   · rw [mul_div_assoc]; exact ht.le
   rw [mul_div_assoc]; exact hQ.le
variable {w : Return.Wages} {l : ℕ→ℝ}
variable (R:PhysicalNext.Repeat.Register D U w l) (V: Delays Θ)
structure Leases (V: Delays Θ) : Prop where
    owns j i: StepStages j i→∀ x:ℝ,V.betaEntry j ≤ x→∀ k≤ i, Slip (X:=X) (D:=D) Y j i k x
    spend j i: StepStages j i→∀ x:ℝ,V.betaEntry j ≤ x→(s.profile i).supportExponent+2<(X j i).exp → (X j i).rate≤-(7/16:ℝ) → WorthP (X j i) (w j i) (R.μ j i) (R.c j i) x (s.profile i).order (s.profile i).power (R.o j i) (D.L j) (Payroll.hearts G (D.L j) x) ((s.profile i).supportExponent+2) 4
    hearty j i: StepStages j i → ∀ k≤j,24*Linden.coined (X j i) k ≤ (D.L j).val
include U
lemma hones (h:Steep G s K X F0)(hp:∀ j,F0 j≤ (D.L j).val):∃ V':Delays Θ, DelayLe V V' ∧ ∀ T':Delays Θ,DelayLe V' T'→ Leases (X:=X) Y R T':=by
   let f(j i:ℕ)(x:ℝ):= (s.profile i).supportExponent+2<(X j i).exp → (X j i).rate≤-(7/16:ℝ) → WorthP (X j i) (w j i) (R.μ j i) (R.c j i) x (s.profile i).order (s.profile i).power (R.o j i) (D.L j) (Payroll.hearts G (D.L j) x) ((s.profile i).supportExponent+2) 4
   have he(j i)(he:StepStages j i): ∀ᶠ x:ℝ in atTop,f j i x:=by
       by_cases hp': (s.profile i).supportExponent+2<(X j i).exp; swap; · exact Eventually.of_forall fun x hx=> (hp' hx).elim
       by_cases hZ:(X j i).rate≤ -(7/16:ℝ); swap; · exact Eventually.of_forall fun x h ht=> (hZ ht).elim
       obtain ⟨hr,hμ,ha,hH⟩:= R.consumes j i he; let y:=s.profile i
       exact (h j i he _ (hp j)|>.1 _ _ _ colorspeed _ Payroll.fillSpeed (s.profile i).order (s.profile i).power _ 4 hr hμ ha (add_nonneg (s.profile i).price_pos.le zero_le_two) hp' (by norm_num [fillSpeed]) (by unfold fillSpeed colorspeed; linarith only [hZ]) (by norm_num [colorspeed])).mono (fun x hx he h'=> hx)
   let T j i x:= f j i x ∧ ∀ k∈ Finset.range (i+1), Slip (X:=X) (D:=D) Y j i k x
   obtain ⟨v,-,hv,H⟩:= collect_upper V.betaEntry _ (fun j=>eventually_transitions j _ (T j) fun i hi=> (he j i hi).and ((Finset.range (i+1)).eventually_all.mpr (fun k _=> atStake Y (X:=X) (D:=D) j i k)))
   exact ⟨{V with betaEntry:=v},⟨hv,le_rfl,le_rfl,le_rfl⟩,fun p hp'=> ⟨fun i j hi x hx k hk=> (H _ x ((hp'.beta _).trans hx) j hi).2 k (Finset.mem_range.mpr (by omega)),fun j i he x hx=>(H _ x ((hp'.beta _).trans hx) i he).1,fun i j hi=> (h i j hi _ (hp _)).2⟩⟩
section calendar
omit X U
variable {P₀:Metals G} {D:Rolls P₀.p}{A:Alloy P₀ D} (R₀:Roost.Factor A) (C:ℕ→ℝ)(V₀:Leases C R₀.shape A.delay)
include V₀
lemma fabric (b:ℕ)(d:ℕ)(he:d ≤ A.B.a.clock.J b)(hc:0 < C (A.B.a.clock.J (b+1))): Buoy R₀ C d b:=by
    have ht:=V₀.owns _ _ (step_paid A.B.a b) _ (A.B.valid.pays b) _ he hc; unfold Buoy facing; simp only [Rain.jersey (A:=A) (m:=b)|>.1,Rain.jersey (A:=A) (m:=b)|>.2.1,Rain.jersey (A:=A) (m:=b)|>.2.2.1,Rain.jersey (A:=A) (m:=b+1)|>.2.2.1,Planned.GuardedAtom.authors,params_eq A.B.valid b,Push.PriceCompiler.beta_eq A.B.valid b,Complex.norm_pow,Complex.norm_natCast]; exact ht
lemma wiggles (h:∀ i j,(R₀.target i j).rate ≤ -(7/16:ℝ))(b:ℕ) : Guild.PriceS R₀ b:= V₀.spend _ _ (step_paid A.B.a b) _ (A.B.valid.pays b) (by let t:= A.B.a.clock.J b; let s:=A.B.a.clock.J (b+1); let Y:=(R₀.expense s t); have ht:=R₀.pledging.agenda s t (step_paid A.B.a b)|>.1; linarith [Y.first,Y.second,Y.worth]) (h ..)
end calendar
end YM.UVExtension.Cloud
