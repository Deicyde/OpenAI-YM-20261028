import YM.TraceExtension.Shelves.Sapphire
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Shelves
open Function Filter Lattice RG Wilson Labels Source Extra.Histories Bid MergeProof.Accent MergeProof
open Extraction Next.Rank.Price Next.Rank.East MergeProof.East Further.CorrectedLift Climb Analysis Work
open MeasureTheory
open Further.PhysicalPeriodLimitF933 Shunt Weir PhysicalNext.Repeat.Legato.Bandage Push.GridApprox Cells
open Relay Pull Terrace Terrace.Glade Perfect Turret Margin Slate
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
-- totalized Rank chart, matches actual core for all late i. Never assume rank bigger than paid.
def Optics(H₁:S.Hierarchy)(H₂:(Cells.standard C).Hierarchy)(S':DiffPlan S)(o:S'.Orientation H₁.spin)(J: Scaling S)(V:∀ i,Vane C i)(Z:Arch C)(i:ℕ): KernelSpace H₁.spin→ₗ[ℝ] TableOne H₂.spin:=by
    let U:= J.U i 5; by_cases h:Coherent H₂.spin H₁.spin 5 U; swap; · exact 0
    let s:= vectorMap (K:=spinQ H₁.spin) (R:=conjQ H₁.spin) (D:=spinQ H₂.spin) (T:=conjQ H₂.spin) (U.symm.toLinearMap.restrictScalars ℝ) (fun i x=> (flips h).signed i x) (fun x=> (flips h).stars x)

    exact crown Z J (Stern V) 5 i • (s ∘ₗ DSeed H₁ o)
include hq' in
lemma Optics_pay :∀ᶠ i in atTop,∀ B:KernelSpace H'.spin,∀ a:Axis, (Optics H' H S₁ ho' J V Z i B).val a=Hero J V Z 5 i (nabla S₁ B.val a):=by
    filter_upwards [hq'.units 5] with i hi B a
    unfold Optics; rw[dif_pos hi.1];rfl
include hb P hz ht hq h hY θ hM
include HF H' hc he hq' hu K hT hv hJ
lemma aprilA : ∀ᶠ i in atTop,∀ B:KernelSpace H'.spin, Optics H' H S₁ ho' J V Z i B=0 ↔ nabla S₁ B.val=0:=by
    filter_upwards [Optics_pay (Z:=Z) (V:=V) H' hq' ho'] with i hi B; let b:= crown Z J (Stern V) 5 i; have hb':0 < b:=mul_pos (measured hb P hz _) (pow_pos (J.positive i) 5);
    let p:= Optics H' H S₁ ho' J V Z i; constructor
    · intro hB; funext a; apply (J.U i 5).symm.injective; let U:= J.U i 5; change U.symm _=U.symm 0; rw [map_zero]; refine (smul_eq_zero.mp (show b • U.symm (nabla S₁ B.val a)=0 from ?_)).resolve_left hb'.ne'; change Hero J V Z 5 i (nabla S₁ B.val a)=0; rw[← hi B a,hB];rfl
    intro hy; apply Subtype.ext; funext a; rw [hi B a,hy, Pi.zero_apply,map_zero];rfl
abbrev PillA(H':S.Hierarchy)(L:PaceBook C)(k:ℕ) : KernelSpace H'.spin:= ⟨baron S L k, stitch_k H' L k⟩
lemma gapC(p:ℕ): Tendsto (fun k=> H! (P! k)^p • (Optics H' H S₁ ho' J V Z k (PillA H' P' (P! k))-s k (Shine5 Z P'.Z (P! k)))) atTop (𝓝 0):=by
   apply tendsto_subtype_rng.mpr; refine tendsto_pi_nhds.mpr fun a=>?_ ; refine (careers P h θ K ht hM hT hb hu hz hq H' HF hJ hY ho' hc hv he p a).congr' ?_
   filter_upwards [Optics_pay (Z:=Z) (V:=V) H' hq' ho'] with k hk; let g:= PillA H' P' (P! k); change H! (P! k)^p • _ = H! (P! k)^p • ((Optics H' H S₁ ho' J V Z k g|>.val a)-_); rw [hk]
end YM.Trace.Shelves
