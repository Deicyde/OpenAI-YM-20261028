import YM.TraceExtension.Slate.Phantom
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
open StressFlux Next.UVStress Margin
variable (Hδ:Moonlit C.path r (PhysicalNext.Repeat.Legato.Bandage.renal C.path.levels) u D)(hr:∀ᶠ i in atTop,2 ≤ r i)(hA:auraQ C.path.levels TileNo)
variable {L:PaceBook C}(hL:Rod t none (𝓛:Filter (ℕ×ℕ)) L)
variable {S:Table C.book}{J:Scaling S}{H:(Cells.standard C).Hierarchy}{V:∀ i,Vane C i}{Y:∀ d i:ℕ,(Cells.standard C).Field d→L[ℂ] C.label d}(hq:Gondola F H J 𝓛 V Y)
variable (H':S.Hierarchy)(HF:F.PointLimits C S) (hq': StarPath F H J H' 𝓛)
variable {S₁:DiffPlan S}{P₁:DiffPlan (Cells.standard C)} (hJ:S₁.Derivatives S)(hP:P₁.Derivatives (Cells.standard C)) (ho:P₁.Orientation H.spin)
variable {s:ℕ→ Bowl (C.labels.level 5) →L[ℝ] (TableOne H.spin)} (hY:Spun Z J V H s)
include h P hb hz
lemma washout (c:ℝ): Tendsto (fun i=>AgeK A c i * (Z.β i)⁻¹) atTop (𝓝 0):=by
   let P(i):= (A).clock.hatBeta i;let m(i):=AgeK A c i; let T:= Z.β; have he:Tendsto (fun i=> 2*(P i)^(-(1/2:ℝ))) atTop (𝓝 0):=by simpa using ((tendsto_rpow_neg_atTop (show 0 < (1/2:ℝ) by norm_num)).comp (hrate A h)).const_mul 2
   refine squeeze_zero' ?_ ?_ he
   · refine Eventually.of_forall fun i=>mul_nonneg (Zn.wake ..|>.le) (inv_nonneg.mpr (measured hb ‹_› hz i|>.le))
   filter_upwards [(hrate A h).eventually ((Weir.ferry (waveM c)) (1/2) (by norm_num))] with i hi; have ht: P i/2 ≤ T i:= (holds hb ‹C.Makes› hz i).1
   have hp:= measured hb ‹_› hz i; have hr:0<P i:=bell ..; change m i*(T i)⁻¹ ≤ _; apply le_trans (mul_le_mul hi.2 (inv_anti₀ (half_pos hr) ht) (inv_nonneg.mpr hp.le) (by positivity:0≤P i^(1/2:ℝ))); apply le_of_eq; rw [inv_div,mul_comm 2,Real.rpow_neg hr.le]; field_simp; rw [← sq, ← Real.sqrt_eq_rpow]; exact Real.sq_sqrt hr.le

variable (Pq : True := True.intro)
include hL hp hu
lemma aspiring : Tendsto (medium L X Z) atTop (𝓝 (Stem5 (Zᵣ))) ∧ Tendsto (fun k=> taxA (A) k * Lease Zᵣ h (medium L X Z k)) atTop (𝓝 0):=by
    obtain ⟨q,hq,hR,hV⟩:= penumbra P h hb hu hz hp; let f(k):=(Z.β k)⁻¹; let v:= Shine5 Z X; let w:= Shine5 Z L.Z
    have he:Tendsto (fun i=> f i • v i) atTop (𝓝 0):=by
       apply tendsto_zero_iff_norm_tendsto_zero.mpr; refine squeeze_zero' (Eventually.of_forall fun i=>norm_nonneg _) ?_ (g:=fun i=> q*(Pig A i*(Z.β i)⁻¹)) ?_
       · filter_upwards [hR] with i hi; have hp:f i ≥0:=inv_nonneg.mpr (measured hb P hz i|>.le); rw [norm_smul,Real.norm_of_nonneg hp]; exact (mul_le_mul_of_nonneg_left hi hp).trans_eq (by unfold f; ring)
       simpa [Pig] using! (washout P h hb hz (1/6)).const_mul q
    let y:= taxA (A); let ρ:=Lease Zᵣ h; have hx : Vivid (Zᵣ) (BornZ none)= -Stem5 (Zᵣ):=Vivid_z _
    have hv':ρ (Vivid (Zᵣ) (BornZ none))=0:=by rw[hx,map_neg, show ρ (Stem5 _)=0 from Lease_alive .., neg_zero]
    have hZ:= (continuous_snd.continuousAt).tendsto.comp (tiara P h hb hu hz hL); change Tendsto w atTop (𝓝 (Vivid (Zᵣ) (BornZ none))) at hZ; rw [hx] at hZ; constructor
    · have ht:= he.sub hZ; rw [zero_sub,neg_neg] at ht; exact ht
    have hv:Tendsto (fun k=> y k*ρ (w k)) atTop (𝓝 0):=by have hw:= diadem P h hb hu hz hL; simp_rw [show Lease (Zᵣ) _ (Vivid _ _)=_ from hv', sub_zero] at hw; exact hw
    have he1:= ((washout P h hb hz (1/5)).mul hV).sub hv; rw[zero_mul,sub_zero] at he1
    exact he1.congr (fun i=>by unfold medium; rw[map_sub,map_smul]; change _=_*(_*_-ρ (w i)); unfold y taxA v at *; rw [mul_sub,mul_assoc])
include Hδ ht hr hA θ K hM HF ho hY hJ hP hq' hq
lemma legacy (p:ℕ): Tendsto (fun i=> H! (Stern V i)^p • s i (medium L X Z (Stern V i))) atTop (𝓝 0):=by
    obtain ⟨t',ht'⟩:= hullage P h θ K ht hb hu hz hp Hδ hr hA hL hq
    exact small_means P h θ K ht hM hb H' HF hq hq' hY hz hJ hP ho t' _ ht' p (medium L X Z ∘ Stern V) (canal P ht hb hz hq L X)
lemma rungs : Prosper V h H s:=by
    let k:= Stern V; let x i:= (A).clock.hatBeta (k i); let g:= medium L X Z ∘ k
    obtain ⟨hx,he⟩:= aspiring P h hb hu hz hp hL; have hℓ : Tendsto k atTop atTop:= (Sstar A).comp hq.growth
    refine springs hz P hb ht hq hM θ h hY g (hx.comp hℓ) ?_ (he.comp hℓ)
    let F:=(A); apply tendsto_zero_iff_norm_tendsto_zero.mpr; have hb':= legacy P h θ K ht hM hb hu hz hp Hδ hr hA hL hq H' HF hq' hJ hP ho hY 1
    refine squeeze_zero' (Eventually.of_forall fun i=> norm_nonneg _) ?_ (show Tendsto _ _ _ from tendsto_zero_iff_norm_tendsto_zero.mp hb')
    filter_upwards [hℓ.eventually ((hrate F h).eventually ((ferry (waveM (1/5:ℝ))) 1 zero_lt_one))] with i hi; change ‖hueK F (k i) • ((s i (g i)).val:Axis→ (Cells.standard C).Field 5)‖ ≤ ‖(H! _ ^ (1:ℕ)) • ((s i (g i)).val:Axis→ (Cells.standard C).Field 5)‖; rw [norm_smul,norm_smul,pow_one,Real.norm_of_nonneg (show 0 ≤ hueK F (k i) from Zn.wake ..|>.le),Real.norm_of_nonneg (bell ..|>.le)]; exact mul_le_mul_of_nonneg_right (hi.2.trans (Real.rpow_one _).le) (norm_nonneg _)
end YM.Trace.Slate
