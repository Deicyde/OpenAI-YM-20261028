import YM.RG08.Plot.Brook
/-!
# Full arbitrary-frame supply from Masters, one presentation.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.RG08.Plot
open Filter Analysis Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect Work.F08 Push.AbsoluteSums Matrix
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Staffer PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Town Bands Pill Wings High PowerSeries Taste
open scoped BigOperators Topology Real ContDiff
variable {I J M:Type} {u:I→Windows}{n k i:ℕ}{X:Chain}{G:Gauge}{E e r d τ D j t l:ℕ}{ν:G.ColorIndex}{F:Labels.Frame G d}{Ω:SectionData F}{H:Hol G}{D':ChartRatio G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}{R:ℝ}{h:1/2≤R}{hD:d+1≤D}{T:Signals P Q E τ H Ω h hD}
variable {b:J→ Dial u}{V:M→ℕ}{p:List M}{U A:J→Native (Letter F)}
abbrev tribute (X:Chain)(b:J→Dial u) := fun i=>Dial.fee X (b i)
abbrev payableD (X:Chain)(b:J→Dial u):= fun i=> gain X.S (1/4) (b i).K (b i).N
def backing (b:J→Dial u)(U A:J→Native (Letter F))(P:J→ℝ)(X:Chain)(E:ℕ): Prop:= ∀ i≤ E,∀ a:Letter F,Tonic (tribute X b) P (payableD X b) (fun j=>coeff i (U j a)) (fun j=>coeff i (A j a))
-- uniformity ANY choices bank funded near these reference positions
section pulses
variable {A₀: M→ℕ} {hT:∀ i, A₀ i+1≤D}{W: ∀ i:M, Labels.Frame G (A₀ i)}{B':∀ i:M,SectionData (W i)} {Y:∀ i:M, Signals P Q E τ H (B' i) h (hT i)}
variable (X ν D')
def deckR (Y:∀ i:M, Signals P Q E τ H (B' i) h (hT i)) (U:∀ i:M,J→ Native (Letter (W i))) (b:J→ Dial u)(j:J)(i:M)(n:ℕ) := masters X ν D' (Y i) (b j).N (b j).K n (U i j)
variable {X ν D'} {A U: ∀ i:M,J→ Native (Letter (W i))}
lemma wave_scene (he:Tights T S ν D' u)(hv:∀ i∈p,Tights (Y i) S ν D' u)(U:∀ i:M,J→ Native (Letter (W i)))(b:J→ Dial u)(j:J): Scenes X ν D' (b j).K (b j).N p A₀ A₀ (deckR X ν D' Y U b j):= by
    have hk n (h:(b j).K ≤ n)(hx:n < (b j).N): Fair (dance X ν D' (b j).N n):= he.fair (High.appr (b:=b) ⟨j,n,h,hx⟩)
    refine ⟨hk,h,fun m hm n hh hk=> (mastery (b:=b) (hv _ hm) ⟨j,n,hh,hk⟩ _).1,fun m hm n hh hk=>?_⟩
    exact mast_step (b:=b) (hv m hm) ⟨j,n,hh,hk⟩ (U m j)
lemma wave_payment (he:Tights T S ν D' u)(hv:∀ i ∈ p,Tights (Y i) S ν D' u)(q:M→ J→ℝ)(hp:∀ i∈p,0≤q i)(hx:∀ i∈p,backing b (U i) (A i) (q i) X E)(k'):
    Fleece T b ν D' k' E p A₀ A₀ (deckR X ν D' Y U b) (deckR X ν D' Y A (rightT b)) q:= ⟨wave_scene he hv U b,wave_scene he hv A (rightT b),hp,fun i hi j hj r=> mastery_d (U:=U i) (V:=A i) (hv i hi) hj _ (hp _ hi) (hx _ hi) k', fun i hi j hj r=> (mastery_d (U:=A i) (V:=A i) (hv _ hi) hj _ (hp _ hi) (fun j hj a=> mateR ((hx _ hi j hj a).two)) k').first⟩
end pulses
end YM.RG08.Plot
