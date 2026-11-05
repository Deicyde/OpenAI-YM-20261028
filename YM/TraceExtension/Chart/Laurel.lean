import YM.TraceExtension.Chart.Dray
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
variable {Δ Ω:PaceBook C} (hΔ:Rod t (some true) (𝓛:Filter (ℕ×ℕ)) Δ) (hΩ:Rod t (some false) (𝓛:Filter (ℕ×ℕ)) Ω)
abbrev forceR(G:Gauge):= -G.slopeConstant/4
section
local notation "V0"=>KernelSpace H'.spin
local notation "K#"=> Optics H' H S₁ ho' J V Z
local notation "RQ!"=> RQ V
local notation "BQ!"=> BQ Z V
local notation "L#"=>tub H' V
-- pencil H free anti- and true scalar case.
def pollen(H':S.Hierarchy)(V:∀ i,Vane C i)(Δ Ω:PaceBook C)(k:ℕ): CP→ₗ[ℝ] KernelSpace H'.spin:=(LinearMap.proj (0:Fin 2)).smulRight (tub H' V Ω k)+(LinearMap.proj (1:Fin 2)).smulRight (tub H' V Δ k)
local notation "s#"=> pollen H' V Δ Ω
local notation "V#"=>TableOne H.spin
include P h θ K ht hT hM hb hu hz hp H' HF hq hq' hc ho' hP ho hJ hY he hL hr hA Hδ
include hΩ hΔ
lemma formulate : ∃ c:ℕ→ CP, ∃ C:ℝ,0 ≤ C∧ (∀ᶠ i in atTop, ‖c i‖ ≤ C* RQ! i ∧ Bijective ((K# i).comp (s# i)) ∧ BQ! i • K# i (L# L i)+ K# i (s# i (c i))=0)∧ Tendsto (fun i=> c i 1) atTop (𝓝 (forceR G)):=by
   let f:= fun i=> (K# i).comp (s# i); let g:= (vega H.spin).comp Waft; let p(i z):= K# i (L# z i); let t(i):=taxA A (P! i); let B:= BQ!
   have hp₁(k)(v:CP): f k v=v 0 • p k Ω+v 1 • p k Δ:=by unfold f; rw[LinearMap.comp_apply,show s# k v=v 0 • L# Ω k +v 1 • L# Δ k from rfl,map_add,map_smul,map_smul]
   have he₁(z:CP):g z=z 0 • vega H.spin (BornZ (some false)) + z 1 • vega H.spin (BornZ (some true)):=by unfold g; rw[LinearMap.comp_apply,show Waft z=z 0 • BornZ (some false)+ z 1 • BornZ (some true) from rfl,map_add,map_smul,map_smul]
   have ht₁:= beater P h θ K ht hM hT hb hu hz hq H' HF hq' hJ hY ho' hc hΩ he; have ht₂:= beater P h θ K ht hM hT hb hu hz hq H' HF hq' hJ hY ho' hc hΔ he
   obtain ⟨d,hD,h₃⟩:= wend (E:=CP) (F:=TableOne H.spin) g f (quill H.spin h) (fun z=> by simp_rw [hp₁,he₁]; exact (ht₁.const_smul (z 0)).add (ht₂.const_smul (z 1)))
   obtain ⟨x,hx,h₄⟩:= sizeQ' P h θ K ht hM hT hb hu hz hp Hδ hr hA hL hq H' HF hq' hJ hP ho hY ho' hc he
   let X(i):=B i • p i L; let c(k):= if h:Bijective (f k) then (LinearEquiv.ofBijective (f k) h).symm (-X k) else 0;let C':=d*x; have hp': 0 ≤ C':=mul_nonneg hD hx
   have hC: ∀ᶠ i in atTop, ‖c i‖ ≤ C'* RQ! i ∧ Bijective ((K# i).comp (s# i)) ∧ BQ! i • K# i (L# L i)+ K# i (s# i (c i))=0:=by
        filter_upwards[h₃,h₄] with i hi hk; have hz:f i (c i)= -X i:=by unfold c; rw[dif_pos hi.1];exact (LinearEquiv.ofBijective _ hi.1).apply_symm_apply _
        have ht:=hi.2 (c i); rw[hz,show ‖-X i‖=‖X i‖ from norm_neg (X i)] at ht; refine ⟨ht.trans ((mul_le_mul_of_nonneg_left hk hD).trans_eq (mul_assoc ..).symm),hi.1,?_⟩; change X i+ f i _= _; rw[hz,add_neg_cancel]
   obtain ⟨μ,w,hw,hW,hℓ⟩:= he.vote; have hm:PaymentR (H:=H) s h V μ:= ⟨⟨w,hw,hW⟩,hℓ⟩
   refine ⟨c,C',hp',hC,?_⟩; have hX:Tendsto (fun i=>μ i (X i)) atTop (𝓝 (- G.slopeConstant)):= transferX P h θ K ht hM hT hb hu hz hp Hδ hr hA hL hq H' HF hq' hJ hP ho hY ho' hc he hm
   have h₅(j):∀ᶠ i in atTop, |c i j| ≤ C'*t i:= hC.mono fun i hi=> (norm_le_pi_norm _ _).trans (hi.1.trans (mul_le_mul_of_nonneg_left (river_k ..) hp'))
   have hh : ∀ᶠ i in atTop,0≤ t i:= Eventually.of_forall fun i=>Zn.wake ..|>.le
   have hs:Tendsto (fun i=> t i*(μ i (p i Ω)-0)) atTop (𝓝 0):=by
        have he:= mere P h θ K ht hM hT hb hu hz hq H' HF hq' hJ hY ho' hc hΩ he hm; rw [show rho h (bareVector (BornZ (some false)))=0 from ?_] at he; exact he
        rw [rho_vector];norm_num[BornZ,azure]
   have ht:Tendsto (fun i=> t i*(μ i (p i Δ)+4)) atTop (𝓝 0):=by
        have he:= mere P h θ K ht hM hT hb hu hz hq H' HF hq' hJ hY ho' hc hΔ he hm; rw [show rho h (bareVector (BornZ (some true)))= -4 from ?_] at he; swap; · rw [rho_vector];norm_num[BornZ,azure]
        simpa only [sub_neg_eq_add] using! he
   have he : Tendsto (fun i=> c i 0*μ i (p i Ω)) atTop (𝓝 0):=by simp_rw [sub_zero] at hs; exact invest (E:=ℝ) (X:=fun i=>μ i (p i Ω)) hp' (h₅ 0) hh hs
   have hz:Tendsto (fun i=> c i 1*(μ i (p i Δ)+4)) atTop (𝓝 0):= invest (E:=ℝ) (X:=fun i=>μ i (p i Δ)+4) hp' (h₅ 1) hh ht
   have h₀:= ((hX.add he).add hz).div_const 4; rw[add_zero,add_zero] at h₀
   apply h₀.congr'; filter_upwards [hC] with i hi; have hP : X i+ f i (c i)=0:= hi.2.2
   have hv:= μ i|>.map_add (X i) (f i (c i)); rw[hP,map_zero,hp₁,map_add, (μ i).map_smul (c i 0) (p i Ω), (μ i).map_smul (c i 1) (p i Δ),smul_eq_mul,smul_eq_mul] at hv; linarith only[hv]
end
end YM.Trace.Over
