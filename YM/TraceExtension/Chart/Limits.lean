import YM.TraceExtension.Shelves.Lore
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
-- analytic servo: if coefficients satisfy orientation law prove alignment
abbrev CP:= Fin 2→ℝ
section edges

section
variable {E F:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] [NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F]
lemma wend (f: E→ₗ[ℝ] F) (W:ℕ → E→ₗ[ℝ] F) (hw:Bijective f) (hv:∀ x:E, Tendsto (fun i=> W i x) atTop (𝓝 (f x)) ):
    ∃ c:ℝ, 0≤ c ∧ ∀ᶠ i in atTop, Bijective (W i)∧∀ v: E, ‖v‖ ≤ c*‖W i v‖:=by
    let V:=LinearMap.toContinuousLinearMap f; let Uu(i):= LinearMap.toContinuousLinearMap (W i)
    have hx:Tendsto Uu atTop (𝓝 V):= fitV Uu V hv; let g:=LinearEquiv.ofBijective f hw; let L:= LinearMap.toContinuousLinearMap g.symm.toLinearMap; have hL:0≤ ‖L‖:= norm_nonneg _; let K:=‖L‖+1; have hk:0<K:=add_pos_of_nonneg_of_pos hL zero_lt_one
    refine ⟨2*K,by positivity,?_⟩; have hp:0 < 1/(2*K):=by positivity
    filter_upwards[ Metric.tendsto_nhds.mp hx (1/(2*K)) hp ] with i hi; rw[dist_eq_norm,norm_sub_rev] at hi; let v:= Uu i
    have hC(x):‖x‖≤ 2*K*‖v x‖:=by
       have he: ‖V x-v x‖ ≤ 1/(2*K)*‖x‖:= ((V-v).le_opNorm _).trans (mul_le_mul_of_nonneg_right hi.le (norm_nonneg _))
       have ht : ‖x‖ ≤ K*‖V x‖:= le_trans ((congr_arg norm (show x=L (V x) from (g.symm_apply_apply x).symm)).trans_le (L.le_opNorm _)) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by norm_num:0≤(1:ℝ))) (norm_nonneg _))
       have hz:= mul_le_mul_of_nonneg_left ((norm_le_norm_sub_add (V x) (v x)).trans (add_le_add_left he (‖v x‖))) hk.le
       have hy:(1/(2*K):ℝ)*K=1/2:=by field_simp
       linarith only [ht,hz,show ( (1/(2*K))*K)*‖x‖=(1/2:ℝ)*‖x‖ from congr_arg (· * ‖x‖) hy]
    have hw:Injective (W i):=by refine LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr fun w hw=> ?_); apply norm_le_zero_iff.mp; exact (hC w).trans_eq (by rw[show v w=0 from hw]; simp)
    exact ⟨⟨hw,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank g.finrank_eq).mp hw⟩,hC⟩
end
-- canonical two basis of vector output (under h.Simple).
abbrev vega (a:(standard C).RealSpin): (Fin 3→ℝ)→ₗ[ℝ] (TableOne a):= (Vbase a).comp ((vCard (Zᵣ)).toLinearMap)
abbrev Waft : CP→ₗ[ℝ] (Fin 3→ℝ):= (LinearMap.proj (0:Fin 2)).smulRight (Margin.azure false)+(LinearMap.proj (1:Fin 2)).smulRight (Margin.azure true)
lemma steppes (a:(standard C).RealSpin)(h:G.Simple)(w:Fin 3→ℝ): vega a w=0↔∃ c:ℝ,w=c • tribe:=by
    let p:= vCard (Zᵣ); have hx:Injective p:=(plate (Zᵣ)).symm.injective.comp (bareCoordinates h).injective
    change Vbase a (p w)=0 ↔ _; rw [Stem5_kernel _ h]; constructor
    · rintro ⟨c,hc⟩; refine ⟨c, hx ?_⟩; rw [hc,map_smul,show p tribe=_ from bust _]
    rintro ⟨c,hc⟩;rw [hc, map_smul]; exact ⟨c,by rw[show p tribe=Stem5 Zᵣ from bust _]⟩
lemma quill (a:(standard C).RealSpin)(h:G.Simple): Bijective ((vega a).comp Waft):=by
    let F:=vega a; refine ⟨LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr fun v hv=> ?_),?_⟩;
    · obtain ⟨c,hc⟩:=(steppes a h _).mp hv; let x:=v 0;let y:=v 1; have hp: c=0:=by have ht:=congr_fun hc 0; change x*0+y*0=c*1 at ht; linarith
      rw [hp,zero_smul] at hc; have hx: x=0:=by have hy:=congr_fun hc 2; change x*1+y*0=0 at hy; linarith
      have hy:y=0:=by have h:=congr_fun hc 1; change x*0+y*(1/4)=0 at h; linarith
      exact funext (Fin.forall_fin_two.mpr ⟨hx,hy⟩)
    intro x; obtain ⟨v,hv⟩:=Vbase_sure a x; have hu: Surjective (vCard (Zᵣ)):= (plate (Zᵣ)).symm.surjective.comp (bareCoordinates h).surjective; obtain ⟨w,hw⟩:=hu v; rw[← hw] at hv
    let y:CP:=![w 2-w 0,4*w 1+w 0]; refine ⟨y,?_⟩; change F (Waft y)=_; change F w=_ at hv; have he: Waft y=w - w 0 • tribe:=by
        funext i; fin_cases i
        · change (w 2-w 0)*0+(4*w 1+w 0)*0=w 0-w 0*1; ring
        · change (w 2-w 0)*0+(4*w 1+w 0)*(1/4)=w 1-w 0 *(-1/4); ring
        change (w 2-w 0)*1+(4*w 1+w 0)*0=w 2-w 0*1;ring
    rw[he,map_sub,hv,show F (w 0 • tribe)=0 from (steppes a h _).mpr ⟨_,rfl⟩,sub_zero]
end edges
end YM.Trace.Over
