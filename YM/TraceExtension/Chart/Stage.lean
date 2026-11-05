import YM.TraceExtension.Chart.Laurel
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
open Table Asymptotics
local notation "F!"=> Cells.standard C
local notation "P!"=> Stern V
variable (ho': S₁.Orientation H'.spin)(hc:CellHyp C F) {i:Bend} {P':PaceBook C}(hv:Rod t i (𝓛:Filter (ℕ×ℕ)) P') (he:Prosper V h H s)
variable {Δ Ω:PaceBook C} (hΔ:Rod t (some true) (𝓛:Filter (ℕ×ℕ)) Δ) (hΩ:Rod t (some false) (𝓛:Filter (ℕ×ℕ)) Ω)
local notation "K#"=> Optics H' H S₁ ho' J V Z
local notation "RQ!"=> RQ V
local notation "BQ!"=> BQ Z V
local notation "L#"=>tub H' V
local notation "s#"=> pollen H' V Δ Ω
local notation "V#"=>TableOne H.spin
local notation "V0"=>KernelSpace H'.spin
local notation "M#"=>Phase4 J V Z
abbrev FZone (G:Gauge):=Fin.cons (α:=fun _=>ℝ) 0 (BornZ none)
lemma FZone_c(G:Gauge): FZone G= -weyl:=by ext1 i; fin_cases i<;> simp[FZone,BornZ,weyl,tribe] <;> rfl
abbrev OScale(L:Register G): (Climb.Bel L).Field 4:= fromPol (Climb.Bel L) (square4 G)
lemma sum_delta : (∑ i:Axis, materialB C (some true) i i)=(4:ℝ) • OScale C.book:=by
    let L:= C.book; let S':=Bel L; let v:=BornZ (some true); let w:=Fin.cons (α:=fun _=>ℝ) 0 v
    change ∑ i:Axis,fromPol S' (stress G w i i)= _; rw [← map_sum]; unfold w; rw[mechanical_trace,map_smul]; change _= 4 • fromPol S' (square4 G); apply congr_arg (· • _); change 4*(0+4*((1:ℝ)/4))=_;norm_num
-- witness at every UV metric. trace of normalized unselected scaling.
def Year (J:Scaling S)(k:ℕ): S.Stress→ₗ[ℝ] (Cells.standard C).Stress:= ((J.r k)^(4:ℕ)) • transformed (J.U k 4).symm
lemma YearP(k:ℕ)(U:S.Stress): Phase4 J V Z k U=Year J k (BQ Z V k • U):=by
    ext1 i;ext1 j; let u:= crown Z J (Stern V) 4 k; let B:=BQ Z V k; change u • _= J.r k^(4:ℕ) • (J.U k 4).symm (B • U i j); let s:=(J.U k 4).symm; rw [show s _=_ from (s.toLinearMap.restrictScalars ℝ).map_smul B (U i j)]
    change u • s (U i j)= J.r k^(4:ℕ) • (B • s (U i j));rw [smul_smul,mul_comm _ B];rfl
lemma cornel(HE:KernelSpace H'.spin)(p:ℝ)(h:S₁.Orientation H'.spin): Conserved S₁ H'.spin HE.val ↔ nabla S₁ HE.val=0:=by rw [← linear_cons _ _ h];exact ⟨fun h=>congr_arg Subtype.val h,fun h=>Subtype.ext h⟩
variable (c:ℕ→ CP)(I:ℝ)(ht₁:0≤ I)(hK:∀ᶠ i in atTop,‖c i‖ ≤ I* RQ V i∧ BQ Z V i • Optics H' H S₁ ho' J V Z i (tub H' V L i)+ Optics H' H S₁ ho' J V Z i (pollen H' V Δ Ω i (c i))=0)(hI:Tendsto (fun i=> c i 1) atTop (𝓝 (forceR G)))
abbrev Cloak(H': S.Hierarchy)(V:∀ i,Vane C i)(L Δ Ω:PaceBook C)(c:ℕ→ CP)(Z:Arch C)(i:ℕ): KernelSpace H'.spin:= BQ Z V i • tub H' V L i + pollen H' V Δ Ω i (c i)
include P h θ K hM ht hT hb hu hz H' hJ hq hq' hP ho hc HF he hY hΔ hΩ hL ht₁ hK
variable (hω:Tendsto (Moment4 Z J V) atTop (𝓝 (Hill4 C)))
lemma serene : ∀ᶠ i in atTop,Conserved S₁ H'.spin (Cloak H' V L Δ Ω c Z i).val:= by
    have hy:= aprilA P h θ K ht hM hT hb hu hz hq H' HF hq' hJ hY ho' hc hL he; filter_upwards[hK,hy] with k hk he; rw [cornel H' _ 0 ho',← he]; unfold Cloak; rw[map_add,map_smul]; exact hk.2
include hω
lemma tweak(k:ℕ)(v:KernelSpace H'.spin):Year J k v.val= ((BQ! k)⁻¹:ℝ) • Phase4 J V Z k v.val:=by
    rw[YearP,map_smul, inv_smul_smul₀ (show BQ! k ≠ 0 from (measured hb P hz (P! k)).ne')]
lemma yields : Tendsto (fun i=>Year J i (Cloak H' V L Δ Ω c Z i).val) atTop (𝓝 (materialB C none)):=by
    let U L i:= (Phase4 J V Z i) (L# L i).val; let p:=BQ Z V; let q(n i):= (c i n)*(p i)⁻¹; let X(i):=(Cloak H' V L Δ Ω c Z i).val
    have hx(i): Year J i (X i)=U L i + (q 0 i • U Ω i + q 1 i • U Δ i):=by
        let n(D₀:PaceBook C):= Year J i (L# D₀ i).val; have hz(A':PaceBook C): n A'=(p i)⁻¹ • U A' i:= tweak P h θ K ht hM hT hb hu hz hL hq H' HF hq' hJ hP ho hY ho' hc he hΔ hΩ c I ht₁ hK hω i (L# A' i)
        change Year J i (p i • (L# L i).val+(c i 0 • (L# Ω i).val+c i 1 • (L# Δ i).val))=_; rw [map_add, ← YearP, map_add,map_smul, map_smul]; change _+(c i 0 • n Ω+c i 1 • n Δ)=_; rw [hz,hz,smul_smul, smul_smul]
    have hq₀(i): Tendsto (q i) atTop (𝓝 0) :=by
        apply tendsto_zero_iff_norm_tendsto_zero.mpr; let v:=Pig (A); have he := (washout P h hb hz (1/6)).comp ( (Sstar A).comp hq.growth); refine squeeze_zero' (Eventually.of_forall fun i=>norm_nonneg _) ?_ (show Tendsto (fun k=> I*(RQ! k*(BQ! k)⁻¹)) _ _ from ?_)
        · filter_upwards[hK] with k hk; rw [show q i k=(c k i)*(BQ! k)⁻¹ from rfl,norm_mul,Real.norm_of_nonneg (show 0 ≤ (BQ! k)⁻¹ from inv_nonneg.mpr (measured hb P hz _|>.le)), ← mul_assoc]; exact mul_le_mul_of_nonneg_right ((norm_le_pi_norm _ _).trans hk.1) (inv_nonneg.mpr (measured hb P hz _|>.le))
        simpa only [Pig,mul_zero] using! he.const_mul I
    have hi:= (hq₀ 0).smul (nearing_h P h ht hb hu hz hq H' hΩ hω); have hj:= (hq₀ 1).smul (nearing_h P h ht hb hu hz hq H' hΔ hω)
    have ht': Tendsto (U L) atTop (𝓝 (materialB C none)):= nearing_h P h ht hb hu hz hq H' hL hω
    have hu:= ht'.add (hi.add hj); simp only [zero_smul,add_zero] at hu; exact hu.congr (fun i=> (hx i).symm)
include hI
lemma blossoms : Tendsto (fun i=> BQ! i • ∑ j:Axis, (Year J i (Cloak H' V L Δ Ω c Z i).val) j j) atTop (𝓝 ((4*forceR G) • OScale C.book)):=by
    let U L i:= ∑ j:Axis, (Phase4 J V Z i (L# L i|>.val)) j j; let p:= BQ Z V; let x:= fun i=> H! (P! i) ^(1:ℕ)
    have hp(i):0≤x i:=pow_nonneg (bell ..|>.le) _; have hℓ:= Sstar A|>.comp hq.growth; let N:= (Cells.standard C).Field 4
    have hx:Tendsto (fun i=> p i • U L i) atTop (𝓝 0):=by refine invest (E:=N) zero_le_two (g:=x) (Eventually.of_forall (fun i=> ?_)) (Eventually.of_forall hp) (muteP P h θ K ht hM hT hb hu hz hq H' HF hL hω hc 1 (by simp)); change |Z.β (P! i)|≤2*x i; rw [abs_of_nonneg (measured hb P hz _|>.le : 0 ≤ p i)]; simpa only [x,pow_one] using dex hb P hz (P! i)
    have htR:= hℓ.eventually (timid (C:=C) h (1/6)); have hy:Tendsto (fun i=> c i 0 • U Ω i) atTop (𝓝 0):=by
         refine invest ht₁ ?_ (Eventually.of_forall hp) (muteP P h θ K ht hM hT hb hu hz hq H' HF hΩ hω hc 1 (by simp)); filter_upwards [hK,htR] with i hi hq; exact (norm_le_pi_norm (c i) 0).trans (hi.1.trans (mul_le_mul_of_nonneg_left (show RQ! i≤x i from hq.trans_eq (pow_one ..).symm) ht₁))
    have ht' : Tendsto (U Δ) atTop (𝓝 ((4:ℝ) • OScale C.book)):=by rw[← sum_delta (C:=C)]; exact tendsto_finsetSum _ (fun i _=> tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (nearing_h P h ht hb hu hz hq H' hΔ hω) i) i)
    have hz:= hx.add (hy.add (hI.smul ht')); rw [zero_add,zero_add,smul_smul,mul_comm] at hz
    refine hz.congr (fun i=> ?_); let X:=Cloak H' V L Δ Ω c Z i; let L₁:= L# L i;let Γ:= L# Ω i; let Δ':=L# Δ i
    have he : p i • Year J i X.val= p i • M# i L₁.val + (c i 0 • M# i Γ.val+c i 1 • M# i Δ'.val):=by
         rw[← show M# i X.val = p i • Year J i X.val from ?_]; swap; · rw [YearP,map_smul]
         change M# i (p i • L₁.val+(c i 0 • Γ.val+c i 1 • Δ'.val))=_; rw [map_add,map_add,map_smul,map_smul,map_smul]
    unfold U; change p i • (∑ j:Axis, (M# i L₁.val) j j)+(c i 0 • (∑ j:Axis, (M# i Γ.val) j j)+ c i 1 • (∑ j:Axis,(M# i Δ'.val) j j))= p i • ∑ j:Axis,Year J i X.val j j
    simp only [Finset.smul_sum]; simp_rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun j _=> (congr_fun (congr_fun he j) j).symm
end YM.Trace.Over
