import YM.TraceExtension.Chart.Limits
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Over
open Function Filter Lattice RG Wilson Labels Source Extra.Histories Bid MergeProof.Accent MergeProof
open Extraction Next.Rank.Price Next.Rank.East MergeProof.East Further.CorrectedLift Climb Analysis Work
open MeasureTheory
open Further.PhysicalPeriodLimitF933 Shunt Weir PhysicalNext.Repeat.Legato.Bandage Push.GridApprox Cells
open Relay Pull Terrace Terrace.Glade Perfect Turret Margin Slate Shelves
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
open StressFlux Next.UVStress Margin
variable (Hδ:Moonlit C.path r (PhysicalNext.Repeat.Legato.Bandage.renal C.path.levels) u D)(hr:∀ᶠ i in atTop,2 ≤ r i)(hA:auraQ C.path.levels TileNo)
variable {L:PaceBook C}(hL:Rod t none (𝓛:Filter (ℕ×ℕ)) L)
variable {S:Table C.book}{J:Scaling S}{H:(Cells.standard C).Hierarchy}{V:∀ i,Vane C i}{Y:∀ d i:ℕ,(Cells.standard C).Field d→L[ℂ] C.label d}(hq:Gondola F H J 𝓛 V Y)
variable (H':S.Hierarchy)(HF:F.PointLimits C S) (hq': StarPath F H J H' 𝓛)
variable {S₁:DiffPlan S}{P₁:DiffPlan (Cells.standard C)} (hJ:S₁.Derivatives S)(hP:P₁.Derivatives (Cells.standard C)) (ho:P₁.Orientation H.spin)
variable {s:ℕ→ Bowl (C.labels.level 5) →L[ℝ] (TableOne H.spin)} (hY:Spun Z J V H s)
open Asymptotics
local notation "F!"=> Cells.standard C
local notation "P!"=> Stern V
variable (ho': S₁.Orientation H'.spin)(hc:CellHyp C F) {i:Bend} {P':PaceBook C}(hv:Rod t i (𝓛:Filter (ℕ×ℕ)) P') (he:Prosper V h H s)
section calculus
-- real scale absorption lemmas
variable {E F:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E][FiniteDimensional ℝ E] [NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F]
variable {f g:ℕ→ℝ}{X:ℕ→ E}
lemma invest {c:ℝ}(hc:0 ≤ c)(h:∀ᶠ i in atTop,|f i| ≤ c*g i)(hp:∀ᶠ i in atTop,0 ≤ g i)(hx:Tendsto (fun i=>g i • X i) atTop (𝓝 0)): Tendsto (fun i=>f i • X i) atTop (𝓝 0):=by
   apply tendsto_zero_iff_norm_tendsto_zero.mpr; refine squeeze_zero' (Eventually.of_forall fun i=>norm_nonneg _) ?_ (show Tendsto (fun i=>c*‖g i • X i‖) _ (𝓝 0) from by simpa using hx.norm.const_mul c)
   filter_upwards [h,hp] with i hi ht; rw[norm_smul,norm_smul,Real.norm_of_nonneg ht,← mul_assoc]; exact mul_le_mul_of_nonneg_right hi (norm_nonneg _)
lemma swim {s:ℕ→ E→L[ℝ] F}{K:E→L[ℝ] F}{x:E}(hs:Tendsto s atTop (𝓝 K))(hv:Tendsto X atTop (𝓝 x)) : Tendsto (fun i=> s i (X i)) atTop (𝓝 (K x)):= scoutR s K X x hs hv
lemma shady {s:ℕ→ E→L[ℝ] F}{K:E→L[ℝ] F}(hs:Tendsto s atTop (𝓝 K)){q:ℝ}(hx:0≤q)(h:∀ᶠ i in atTop, ‖X i‖ ≤ q*f i): ∃ c:ℝ,0≤c∧∀ᶠ i in atTop, ‖s i (X i)‖ ≤ c*f i:=by
   refine ⟨(‖K‖+1)*q,by positivity, ?_⟩; filter_upwards [hs.norm.eventually (ge_mem_nhds (lt_add_one _)),h] with i hi he
   exact ( (s i).le_opNorm _).trans ((mul_le_mul hi he (norm_nonneg _) (by positivity)).trans_eq (mul_assoc ..).symm)
lemma liftB {u:ℕ→ℝ}{μ:ℕ → E→ₗ[ℝ] ℝ} {C:ℝ}(hp:∀ᶠ i in atTop,∀ y,‖μ i y‖≤ C*‖y‖) (H:Tendsto (fun i=> u i • X i) atTop (𝓝 0)): Tendsto (fun i=>u i*μ i (X i)) atTop (𝓝 0):=by
   apply tendsto_zero_iff_norm_tendsto_zero.mpr; refine squeeze_zero' (Eventually.of_forall fun i=>norm_nonneg _) ?_ (show Tendsto (fun i=> C * ‖u i • X i‖) atTop (𝓝 0) from by simpa using H.norm.const_mul C); filter_upwards [hp] with i hi
   exact le_trans (by rw [map_smul];rfl : ‖u i*_‖ ≤ ‖μ i (u i • X i)‖) (hi _)
end calculus
variable (Qv:Tendsto (Stern V) atTop atTop)
include h
lemma timid (x:ℝ): ∀ᶠ k in atTop,AgeK A x k ≤ H! k:=by
    filter_upwards [(hrate A h).eventually ((ferry (waveM x)) 1 zero_lt_one)] with i hi; exact hi.2.trans (Real.rpow_one ..).le
include h hv P θ K ht hM hT hb hu hz hq H' HF hq' hJ hY ho' hc he
abbrev tub(Q:∀ i,Vane C i)(L:PaceBook C) (j:ℕ):= PillA H' L (Stern Q j)
abbrev BeamC (J:Scaling S)(V:∀ i,Vane C i)(Z:Arch C)(o:S₁.Orientation H'.spin) (j:ℕ) (X:PaceBook C):= Optics H' H S₁ o J V Z j (tub (Q:=V) H' X j)
lemma beater : Tendsto (fun j=>BeamC (H:=H) H' J V Z ho' j P') atTop (𝓝 (vega H.spin (BornZ i))):=by
   let f(k):= Shine5 Z P'.Z (P! k); let g(k):= s k (f k); let t(k):= Optics H' H S₁ ho' J V Z k (PillA H' P' (P! k))
   have hz': Tendsto (fun i=>t i - g i) atTop (𝓝 0):= by
        have hh:= gapC P h θ K ht hM hT hb hu hz hq H' HF hq' hJ hY ho' hc hv he 0; simpa only[t,g,f,pow_zero,one_smul,BeamC,tub] using! hh
   have hU:Tendsto f atTop (𝓝 (Vivid (Zᵣ) (BornZ i))):= ((continuous_snd.continuousAt.tendsto.comp (tiara P h hb hu hz hv))).comp ((Sstar (A)).comp hq.growth)
   have h₁:= swim (E:=Bowl (Zᵣ)) (F:=TableOne H.spin) he.alpha hU
   have hp₁:Tendsto g atTop (𝓝 (vega H.spin (BornZ i))):= h₁
   simpa only[t,BeamC,tub,zero_add, sub_add_cancel] using! hz'.add hp₁
-- µ certificate fields
structure PaymentR (s:ℕ→ Bowl (C.labels.level 5) →L[ℝ] TableOne H.spin)(h:G.Simple)(V:∀ i,Vane C i)(μ:ℕ→TableOne H.spin→ₗ[ℝ] ℝ) : Prop where
    lean : ∃ c:ℝ,0≤c∧∀ᶠ i in atTop,∀ y, ‖μ i y‖ ≤ c*‖y‖
    lead (ε:ℝ)(hε:0< ε): ∀ᶠ i in atTop,∀ y, ‖taxA A (Stern V i)*(μ i (s i y)- Lease Zᵣ h y)‖ ≤ ε*‖y‖
variable {μ:ℕ→TableOne H.spin→ₗ[ℝ] ℝ}(hr': PaymentR (H:=H) s h V μ)
include hr'
set_option maxRecDepth 4096 in
lemma mere : Tendsto (fun k=>taxA A (P! k) * (μ k (Optics H' H S₁ ho' J V Z k (tub H' V P' k))-rho h (bareVector (BornZ i)))) atTop (𝓝 0):=by
   let TT(k):=taxA A (P! k); let f:= Shine5 Z P'.Z; let U(i):= f (P! i); let V':= Vivid (Zᵣ) (BornZ i); let g(k):= s k (U k); let p(k):=Optics H' H S₁ ho' J V Z k (tub H' V P' k)
   have htQ:Tendsto (P!) atTop atTop:=(Sstar A).comp hq.growth; have hU:Tendsto U atTop (𝓝 V'):=by
       have hu:= continuous_snd.continuousAt.tendsto.comp (tiara P h hb hu hz hv); change Tendsto f atTop (𝓝 V') at hu; exact hu.comp htQ
   have he':Tendsto (fun k=> TT k • (p k-g k)) atTop (𝓝 0):=by
       let b i:= H! (P! i)^(1:ℕ); refine invest (E:=TableOne H.spin) zero_le_one (g:=b) ?_ (Eventually.of_forall (fun i=> pow_nonneg (bell ..|>.le) _)) (gapC P h θ K ht hM hT hb hu hz hq H' HF hq' hJ hY ho' hc hv he 1); filter_upwards [htQ.eventually (timid (C:=C) h (1/5))] with k hk; exact (abs_of_nonneg (Zn.wake ..|>.le)).trans_le (by unfold b;rw [one_mul,pow_one];exact hk)
   obtain ⟨q,Hq,hp⟩:= hr'.lean; let v:= Lease Zᵣ h; have hx := (liftB (E:=TableOne H.spin) hp he'); simp_rw [map_sub] at hx
   have hh :Tendsto (fun k=> TT k*(μ k (g k)-v (U k))) atTop (𝓝 0):=by
       apply Metric.tendsto_nhds.mpr; intro ε hε; let c:= ‖V'‖+1; have hc:0 < c:=add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one
       filter_upwards [hU.norm.eventually (gt_mem_nhds (lt_add_one _)), hr'.lead (ε/c) (div_pos hε hc)] with i hi hI; rw [dist_zero_right]; apply (hI (U i)).trans_lt; exact (mul_lt_mul_of_pos_left (show ‖U i‖<c from hi) (div_pos hε hc)).trans_eq (div_mul_cancel₀ _ hc.ne')
   have hY:= diadem P h hb hu hz hv |>.comp htQ; have hv':v V'=rho h (bareVector (BornZ i)):= leaseV ..
   have hm:= (hx.add hh).add hY; simp only[zero_add] at hm; exact hm.congr (fun k=>by change TT k*(μ k (p k)-μ k (g k))+TT k*(μ k (g k)-v (U k))+TT k*(v (U k)-v V')=TT k*_; rw [hv']; ring
       )
end YM.Trace.Over
