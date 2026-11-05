import YM.FullVolume.Glide.Clays
/-! One-step norms & betas. On Common orbit, not required balanced. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Lark.Glide
open Function Filter Set MeasureTheory Lattice RG Pressure RG.Shoot Wilson Precision RG.Supply Input Org
open Push Push.AbsoluteSums AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Song Geo
open ConnectedActivityE6
open Push.PriceCompiler Further.StrongStartup UniformSpace
open WilsonStartup Progress.DirectedRecipe Time UVNext.CouplingReset Roof
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{c f:Side}{X:Metals G}{D:Rolls X.p}{A:Alloy X D}{R:Roost.Factor A} {p m N n:ℕ}
open Muse Pass FullVolume.Urns FullVolume.Shadow FullVolume.Amp
variable {t ξ w d q:ℝ} {L:Lyrics R t t}
    (Y:Plato L q w d ξ)(O:Ops L N p)
-- layout norm at all periods does not forget Reads; val if proof.
local notation "Ω"=> A.B.a.clock.hatBeta
local notation "B"=> A.B.a
local notation "K"=> A.B.kin
namespace Window
open Contest
abbrev coats (O:Ops L N p)(P:Contest N p L)(i:ℕ) := gifts (dices Y O P) i
def draws (r: Contest N p L)(i:ℕ):= (r.trail i).beta
-- Ticket at same N.Actual permit.Vel. complete.Leb
variable {O} {U V:ℕ → ℝ} {T:Runup O U}{W:Runup O V} (hT:Cage O U N T)(hw:Cage O V N W)
include Y hT
lemma watts (hi:m < N): ‖price T m‖ ≤ stow A.B.a w m/2:=by -- fix
     rw [prime _ hi,stow,show (2:ℝ)*fn A.B.a m w/2=fn A.B.a m w from (by ring)]
     exact (compass Y O (h:=hi) (U (m+1),T.liftP (m+1) hi) (hT.moods _ hi) (T.valid ..)).2
include hw
lemma tickets (h:m<N): let y:=max (dist (U (m+1)) (V (m+1))) (dist (gifts T (m+1)) (gifts W (m+1))); dist (gifts T m) (gifts W m) ≤8*glint*y ∧‖price T m-price W m‖≤4*stow A.B.a w m*y:=by
    dsimp only; rw [lifts _ h.le,lifts _ h.le, prime _ h,prime _ h,lifts (m+1) h,lifts (m+1) h,hT.route m h h, hw.route m h h,stow,show (4:ℝ)*(2*fn A.B.a m w)= 8*fn A.B.a m w from (by ring)]
    exact curls Y O (h:=h) (U (m+1),T.liftP _ h) (hT.moods _ h) (T.valid ..) (V (m+1),W.liftP _ h) (hw.moods _ h) (W.valid ..)
omit hT hw
lemma pressing {t v:ℝ} (ht:mild (Ω m) t)(hv:mild (Ω m) v): brace A.B.a m * dist t v≤ ‖fromLambda (Ω m) t-fromLambda (Ω m) v‖:=by
    let a:= Ω m; let p:=normedWidth a; let b:=brace A.B.a m; have h' :0<b:= braceP Y _; unfold fromLambda
    have he: a*(p*t)^2-a*(p*v)^2=b*(t-v)*(p*t+p*v):=by unfold b brace Pass.salary p a; ring
    change b*dist t v≤ ‖a*(p*t)^2-a*(p*v)^2‖; rw [dist_eq_norm,he,norm_mul,norm_mul,Real.norm_of_nonneg h'.le]; exact le_mul_of_one_le_right (by positivity) (le_trans (by linarith [ht.1,hv.1] : (1:ℝ) ≤ p*t+p*v) (le_abs_self _)) -- unfold p
section limits
-- Balance data limits for ANY λ-cluster of ART. actual α read N→.
variable {u:ℕ→ℕ}{Q:∀ i,Ops L (u i) p}{P:∀ i,Contest (u i) p L} {f:ℕ→ℝ}{X':∀ i:ℕ,cloud A.B.a i p}{g:ℕ→ℝ}
structure Banked (P:∀ i, Contest (u i) p L)(Q:∀ i,Ops L (u i) p)(f:ℕ→ℝ)(X': ∀ i:ℕ, cloud A.B.a i p)(g:ℕ→ℝ):Prop where
    angles:∀ m:ℕ,Tendsto (fun i=> saga (P i) m) atTop (𝓝 (f m))
    fields:∀ m,Tendsto (fun i=> coats Y (Q i) (P i) m) atTop (𝓝 (X' m))
    earns:∀ m,Tendsto (fun i=> price (dices Y (Q i) (P i)) m) atTop (𝓝 (g m))
variable {Y} (he:Tendsto u atTop atTop) (h:Banked Y P Q f X' g)
include h he
lemma issued (m:ℕ): mild (Ω m) (f m):= isClosed_Icc.mem_of_tendsto ((h.angles m).const_mul _) ((he.eventually_ge_atTop m).mono fun i hi=> mildS Y (P i) m hi)
omit he in
lemma waveBound (m:ℕ): ‖X' m‖ ≤1/8:= le_of_tendsto' ((h.fields m).norm) fun i=> gems (T:=dices Y (Q i) (P i)) _
lemma palm (m:ℕ): Tendsto (fun i=>draws (P i) m) atTop (𝓝 (fromLambda (Ω m) (f m))):=by
    have hx:Continuous (fromLambda (Ω m)):=by unfold fromLambda; fun_prop
    exact (hx.continuousAt.tendsto.comp (h.angles m)).congr' ((he.eventually_ge_atTop m).mono fun i hi=>spoken Y (P i) m hi)
lemma pop (m:ℕ): ‖g m‖ ≤ stow A.B.a w m/2:= le_of_tendsto ((h.earns m).norm) ((he.eventually_gt_atTop m).mono fun i hi=>watts Y (cageM Y (Q i) (P i)) hi)
lemma trader {m:ℕ}{s:ℝ}(hr:Tendsto (fun n=> A.B.kin.alpha n m) atTop (𝓝 s)): fromLambda (Ω m) (f m)-fromLambda (Ω (m+1)) (f (m+1)) -s=g m:= by
    refine tendsto_nhds_unique (((palm he h m).sub (palm he h _)).sub (hr.comp he)) ((h.earns m).congr' ((he.eventually_gt_atTop m).mono fun i hi=>?_)); exact census Y (Q i) (P i) m hi
end limits
end Window
end YM.PhysicalNext.Repeat.Lark.Glide
