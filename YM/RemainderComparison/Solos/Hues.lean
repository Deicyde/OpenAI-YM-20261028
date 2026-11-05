import YM.RemainderComparison.Solos.Cheers
import YM.RemainderComparison.Creek.Ancient
/-!
# Loyalty to test address markings
 Needed only for uniform integrability near equality F.B.Flags. For all other uses
 preserve the real rendered leaves. `weight` is before probe restriction.
 Honors support, gauges and flags. Don't require a cost summable over tests.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Solos
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling OmitClusters AnalyticBridge.VerifiedReset
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {θ ι : Type} {R₀ : θ→Type*} [∀ i, NormedAddCommGroup (R₀ i)] [∀ i,NormedSpace ℝ (R₀ i)]
variable {α:Type*}{G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (H:Cash W x μ L Q o C T R) {q A B b e u v d L' Gp:ℝ}{j n k s J I:ℕ}(χ:Chi)
open Lyric Mosaic Sleet Serif Typeface
variable (M:ι→Portrait R α) (y:α)
-- place : all tags of leaf (empty if dormant)
variable (M:ι→Portrait R (Audited R₀)) (place :ι→ Finset θ)(Hpc: ∀ (U:Config G f) i, LinearP (place i) (fun a=> ((brand M a i).ingredient U)))
local notation "V'" z:max=> brand M z
open WickReps Flues Progress.DirectedRecipe
-- callbacks at ANY footprint ANY test value.
variable (y:Audited R₀)(l:ι→ℝ)(Z:Set ι)(ε:ℝ)
variable (N:Captain H j q d v u A b r B e n χ)
local notation "t'" => Pressure.temp x
local notation "Vy"=> brand M y
local notation "Lt"=> mapWord place
local notation "A₀"=> Creek.theater H χ M y l Z ε
local notation "L↑"=> Muse.sits Z l ε
include Hpc N
set_option maxHeartbeats 500000 in
lemma vacant (V:Config G c)(i:Sleet.Staff (brand M y) H) (hp:Healthy (Pressure.temp x) (reachability (H:=H) i.fst) V): ∀ᶠ z in 𝓝 V,PaperP (Lt ((etude Vy H χ i.1 i.2).letters)) (fun b=> ∏ j,toe (brand M b) H χ (i.1.2 j) (i.2 j) z):=by

    have hz(j): Healthy t' (H.smallAt (i.1.2 j)) V:= hp.mono_left (subset_biUnion_of_mem (H.smallAt ∘ i.1.2) (mem_univ j))
    filter_upwards [eventually_all.mpr (fun j=> city H χ M place Hpc y (i.2 j) N (i.1.2 j) (hz j))] with x hx; intro v 
    let P j:=Lt (i.2 j).val.val; let F j (v:Audited R₀):=toe (brand M v) H χ (i.1.2 j) (i.2 j) x
    have he : Lt ((etude Vy H χ i.1 i.2).letters)=∑ j,P j:= map_sum Lt (fun j=>(i.2 j).val.val) univ
    rw [he]; exact PaperP.stack Finset.univ P F (fun j _=> hx j) (he ▸ v)
omit N Hpc [∀ i,NormedSpace ℝ (R₀ i)] in
lemma arming(i: Sleet.Staff (brand M y) H)(P':Audited R₀)(V:Config G c) : ((A₀).solvent P' i V)=(etude Vy H χ i.1 i.2).stock L↑ * Lyric.string (brand M P') H χ i.1 i.2 V:=by
    -- definal maneuvers force pol type
    unfold Creek.theater; dsimp only; unfold Verse.emit;
    rw [show (etude (brand M P') H χ i.1 i.2).stock L↑=(etude Vy H χ i.1 i.2).stock L↑ from congr_arg ((fun q:Multiset ι=> (q.map L↑).prod)) (Creek.paper H χ M y P' l Z ε i).symm]; rfl
set_option maxHeartbeats 210000 in
lemma dew (V:Config G c)(i:Sleet.Staff (brand M y) H) (hp:Healthy (Pressure.temp x) ((A₀).halls i) V): ∀ᶠ z in 𝓝 V,PaperP (Lt ((A₀).marks i)) (fun b=> (A₀).solvent b i z):=by
    rw [Creek.point H χ M y l Z ε _] at hp
    have hz:=vacant H χ M place Hpc y N V i hp
    refine hz.mono fun x hx h=> ?_
    have hQ: (A₀).marks i=(etude Vy H χ i.1 i.2).letters:= Creek.paper H χ M y y l Z ε i
    simp_rw [fun p:Audited R₀=> arming H χ M y l Z ε i p x]; rw [hQ]; unfold Lyric.string
    exact LinearP.pitch _ (LinearP.pitch _ (hx (hQ ▸ h)))
lemma scene (V:Config G c) (p:H.Chapter) (s:Mosaic.Stone (brand M y) H p) : PaperP (Lt ( (panel Vy H χ p s).letters)) (fun b=>(Mosaic.panel (brand M b) H χ p s).utter V):=by
    cases p with
    | inl p => exact act_h H χ M place Hpc y s p.val V
    | inr p =>
        let S:Sleet.Staff Vy H:=⟨p,s⟩
        -- with LT=1 get value. Inspect.Ev flags
        change PaperP _ (fun b=> -Lyric.cut (brand M b) H χ p s V)
        let f b j:=act (brand M b) H χ V (p.2 j).val (s j)
        have he(b:Audited R₀): -Lyric.cut (brand M b) H χ p s V= -cadence H p*∏ j,f b j:= by rw [← Lyric.scripted (brand M b) H χ p s N V,neg_mul] -- edit args
        simp_rw [he]; intro hp; apply LinearP.pitch
        let P j:= Lt (s j).val.val; have hz : Lt ((panel Vy H χ (.inr p) s).letters)= ∑ j, P j:=map_sum Lt (fun j=> (s j).val.val) univ
        rw [hz]; exact PaperP.stack univ P (fun i b=>f b i) (fun j _=>act_h H χ M place Hpc y (s j) (p.2 j).val V) (hz ▸ hp)
lemma lush (V:Config G c) (p:H.Chainbook)(s:Mosaic.Scene (brand M y) H p): PaperP (Lt (parade Vy H χ p s).letters) (fun b=> (parade (brand M b) H χ p s).emit l V):=by
    let f:=fun (i:↥p.fst) (j:Slots H p i)=> (Mosaic.panel Vy H χ i.val (s i j)).letters
    have he (w:Audited R₀)(i:H.Chapter)(j:Stone Vy H i): (Mosaic.panel (brand M w) H χ i j).letters=(Mosaic.panel Vy H χ i j).letters:=by cases i<;> rfl
    have hz (i:↥p.fst) (j:Slots H p i) : PaperP (Lt (f i j)) (fun b=> (Mosaic.panel (brand M b) H χ i.val (s i j)).emit l V):=by intro h; unfold Verse.emit Verse.stock; simp_rw [he]; exact LinearP.pitch _ (scene H χ M place Hpc y N V i.val (s i j) h)
    have hs : Lt ((parade Vy H χ p s).letters)=∑ i,∑ j,Lt (f i j):=by rw [show (parade Vy H χ p s).letters=∑ i:↥p.fst,∑ j,f i j from rfl,map_sum]; simp_rw [map_sum]
    simp_rw [fun b:Audited R₀=> Mosaic.wheel (brand M b) H χ l p s V]; split_ifs
    · rw [hs]; apply PaperP.stack; intro i _ hi; simp_rw [div_eq_inv_mul]; exact LinearP.pitch _ (PaperP.stack univ _ _ (fun j _=> hz i j) hi)
    exact fun h=> LinearP.nil _
variable [Countable ι]
variable {R':Rep G f} (H':Cash W x μ L Q o C T R')(D:Match.Alliance H' H 1 0)(P':BudgetPoint) (E₀:ℕ→RegularAddress c)(V₀:ℕ → Config G c→ℝ)
local notation "K'" => kettle H χ M y l Z ε H' D E₀ V₀
local notation "Ω" => Flues.funnel H M y H' D
lemma radiant (i:ℕ)(V:Config G c): PaperP (Lt ((K').score i)) (fun b=> (K').glow b i V) := by
    by_cases hi:i∈ Set.range Ω
    · obtain ⟨j,rfl⟩:=hi; unfold Flues.kettle; dsimp only; simp_rw [Progress.DirectedRecipe.stuffed]
      exact lush H χ M place Hpc y L↑ N V _ j.snd
    unfold kettle; dsimp only; simp_rw [Progress.DirectedRecipe.blank Ω _ hi]; intro h; apply LinearP.nil
end YM.RemainderComparison.Solos
