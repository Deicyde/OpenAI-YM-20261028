import YM.FullVolume.Fares.Cost
/-!
 # after-L query Costs.Economics
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mallow
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {s : Sheet G} {K : MapPrices} {X : Targets s K} {D : Rolls s} {Θ : Protection D} {p : Expenses X} {u : Return.Wages} {l : ℕ→ℝ} {P : Teller G}

open Next.Scheduling.Clock Next.Scheduling.Instrument Progress.DirectedRecipe
open Legato.Campaign
open MergeProof MergeProof.Menu
open Muse Veil Ship Empire Extra.Histories
variable (L:Side)(Q:ConnectedActivityE6.Target G P)(μ x q:ℝ)
open Face Splint Matric FullVolume.Paint Tower Source
variable (R:Register D p u l) (X₀:ℕ→ℝ) (Θ₁:Luna.Tableau q 300) (v:ℕ→ℕ→ℝ)
abbrev priceS (X:RG.Stage):ℝ:=Real.exp X.supportExponent*Cub.title G X
abbrev fundsM (G:Gauge)(j d:ℕ)(v:ℕ→ℕ→ℝ)(i:((Labels.frames G).level d).Index):ℝ:= v d j *‖Size.axis ((Labels.frames G).level d) i‖ -- import
-- q implicit? in statements specify.
structure Snowy (j i:ℕ)(x:ℝ): Prop where
   up : Tariff (X j i) (D.L j) 1 (R.μ j i) x
   has : Tariff (stella (X j i)) (D.L j) 1 (R.μ j i) x
   rate : Daisy.poster (X j i) (D.L j) x≤ 1
   much : ((D.L j).val:ℝ)≤ x
   fame : Real.exp ((s.profile i).supportExponent+2) ≤ x
   stars (n): n ≤ j → Snow G (D.L j) n (R.μ j i) x q
   framesE (d):d ≤ j→ |priceE ((Labels.frames G).level d) (priceS (G:=G) (s.profile j)) (fundsM G j d v)|≤x
   framesK (d):d ≤ j→ |priceK Θ₁.price (X₀ j) (Doors.rate (D.L j)) (D.L j) ((Labels.frames G).level d) (fundsM G j d v)|≤ x
#print Snowy -- inspect param ordering
lemma snowstar (j i :ℕ) (h: StepStages j i) :∀ᶠ x in atTop,Snowy q R X₀ Θ₁ v j i x:=by
    have hu:= (R.consumes _ _ h).2.1
    have hp:Rate G (D.L j) ((X j i).rate/4) (Daisy.poster (X j i) (D.L j)):= Rate.power
    have hv := hp.below (by have hh:=(X j i).stop; linarith) 1 zero_lt_one
    filter_upwards [thaws (X j i) (D.L j) 1 _ hu, thaws (stella (X j i)) (D.L j) 1 _ hu,hv, eventually_ge_atTop ((D.L j).val:ℝ),eventually_ge_atTop (Real.exp ((s.profile i).supportExponent+2)),(eventually_all_finset (Finset.range (j+1))).mpr (fun n _=>snowfall (G:=G) (D.L j) n _ q hu), (eventually_all_finset (Finset.range (j+1))).mpr (fun d _=>eventually_ge_atTop |priceE ((Labels.frames G).level d) (priceS (G:=G) (s.profile j)) (fundsM G j d v)|), (eventually_all_finset (Finset.range (j+1))).mpr (fun d _=>eventually_ge_atTop |priceK Θ₁.price (X₀ j) (Doors.rate (D.L j)) (D.L j) ((Labels.frames G).level d) (fundsM G j d v)|)] with x hF ht he hs hP hN hq hΩ
    have hh n (h:n≤ j): n∈Finset.range (j+1):= Finset.mem_range.mpr (by omega)
    exact ⟨hF,ht,(le_abs_self _).trans he,hs,hP,fun n h=> hN n (hh n h),fun i h=> hq i (hh i h),fun i h=>hΩ i (hh i h)⟩
def Canyon (Z: Delays Θ):Prop:= ∀ j x,Z.betaEntry j≤ x→∀ i, StepStages j i→ Snowy q R X₀ Θ₁ v j i x
lemma voyage (V:Delays Θ) :∃ W:Delays Θ,DelayLe V W∧ ∀ Y:Delays Θ,DelayLe W Y→ Canyon q R X₀ Θ₁ v Y:= by
    let P j i x := Snowy q R X₀ Θ₁ v j i x; obtain ⟨x,-,hx,hP⟩:= collect_upper V.betaEntry _ fun j=>eventually_transitions j _ _ fun i hi=>show ∀ᶠ x in atTop,P j i x from snowstar q R X₀ Θ₁ v j i hi
    exact ⟨{V with betaEntry:=x},⟨hx,le_rfl,le_rfl,le_rfl⟩,fun Y hy j y he i hi=> hP j y ((hy.beta j).trans he) i hi⟩
end YM.PhysicalNext.Repeat.Mallow
#print axioms YM.PhysicalNext.Repeat.Mallow.voyage
