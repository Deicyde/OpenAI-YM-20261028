import YM.RemainderComparison.Placement.Oak
/-!
 # Sound α AP capability from real census. All paintings independent of weather rewards.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Placement
open Function Filter Lattice RG Tree Wilson Finset Pressure
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Shell Census Raw Footprint Matter
open PhysicalNext.Repeat Deck Stellar Mint Poll Pond MeasureTheory ProbabilityTheory Greenbelt Lotus Sienna Fare
open Further.PhysicalPeriodLimitF933 Macrame
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Gas Ursell Trees Blaze March Lyric WickReps Creek Mosaic Merge Palette Typeface Harmonics
open AnalyticBridge VerifiedReset Next.Scheduling Extra.Iteration Song Aria Seedlings BoxOf
open Push.Uniform Lantern Portal Exchange Aux Germ Lapis Herbal Musicology Funk Orbits Breeze Nursery
variable {ι:Type} {G:Gauge} {P:Teller G}{f c: Side}{X:StepData c f} {U V:ℕ}
variable {T: Tube G X} {Q: ConnectedActivityE6.Target G P}
variable {t j k n r q e m :ℕ} {Z v x W a D μ B':ℝ}
variable {α:Type*}(R:BudgetPoint)(E:BudgetPoint) (β:ℝ)
local notation "G'"=> Pane.virgin T R β
variable {R₁: Rep G f}(s:α)(Ti:Tile G α q e D)(o:Site f)
local notation "kI"=> (fun V:Config G _=> Tile.read Ti o s V)
-- single marked slot amplitude.Book from one canonical invariant atom. sign identity run. rank receipts.Core.Any P.Final stamps.
abbrev plot : Eden f G Unit:=⟨Finset.univ,fun _=>q,fun _=>q,fun _=> kI⟩
local notation "V₁"=> Placement.plot s Ti o -- arguments order
lemma leaves (hp:0<β) : (V₁).groups β=kI:=by
    funext U; have he:0<gStep β ^ q:=pow_pos (Fare.gS _ hp).1 q
    simp [Eden.groups,Herbal.worn,mul_inv_cancel₀ he.ne'] -- multiplication
local notation "κ"=> (D*Real.exp (e:ℝ))
def interiorFee (G:Gauge)(q e:ℕ)(D:ℝ)(k:ℕ)(v:ℝ):ℝ:= (D*Real.exp (e:ℝ))*(1+ Herbal.prize k q G 1 v)
local notation "weight"=> Placement.interiorFee G q e D k v
lemma buys_plot (hp:0≤v)(hq:1≤n)(he:q≤ n)(h: Placement.interiorFee G q e D k v ≤ W)(hl:μ≤ q) : (V₁).Culture n k R.threshold v W μ :=by
    have hA:0≤D:= Placement.Tile.funds Ti s
    have hh:0≤ W:= le_trans (show 0 ≤ weight from (by unfold interiorFee; have h:= Herbal.prizes_pos (G:=G) (j:=q) (k:=k) hp zero_lt_one; positivity)) h -- correction
    refine ⟨hq,fun i _=> ⟨he,he,?_⟩,hh,fun i _=>hl⟩ -- occupancy defeq card unit
    let a:= Ti.stamp s
    let f : Unit→ℝ:=fun i=>1; let Qh (_:Unit):=a
    have he' : SumBudget (fun i:Unit=> |(1:ℝ)| *(Ti.stamp s).budget 1) κ:=by
        have hX : (Ti.stamp s).budget 1 ≤ D * Real.exp (↑e):=by
            unfold RG.Atom.budget; rw [one_mul]; gcongr; exact Ti.bound s; exact Ti.length s
        refine ⟨fun i=>by unfold RG.Atom.budget RG.Atom.magnitude; positivity,(hasSum_fintype _).summable,?_⟩
        simpa only [abs_one,one_mul,tsum_fintype,Fintype.sum_unique] using! hX -- edits
    have hp : Herbal.Sect (Herbal.club Qh (fun _=>o) f (fun _=>1)) R.threshold (q) k v weight:= aSect Qh _ f _ zero_lt_one he' R hp fun _=>Ti.gauge s -- rank . not field
    rw [show (V₁).oil _ = Herbal.club Qh (fun _=>o) f (fun _=>1) from ?_]; exact Herbal.climbed hp R.threshold_pos.le h
    funext U; unfold Herbal.club; rw [tsum_fintype,Fintype.sum_unique]; unfold f; rw [one_mul,Lattice.pull_one]; rw [show Lattice.translate (0:Site _) U=U from funext fun i=>by simp [Lattice.translate] ]; rfl
section shape
variable [Countable ι] (hβ:0<β) (t:α)(P':ι→Tile G α q e D) (u:ι→Site f)
set_option quotPrecheck false
local notation "Z₁"=> Placement.file G' e ι
local notation "pM"=> Placement.plants G' t P' hβ u
local notation "l0"=> (fun _ :ι=> (1:ℝ))
local notation "ψ"=> Musicology.barren f G Unit
local notation "E'"=> (fun i:ι=> Placement.plot s (P' i) (u i))

lemma still_vac : (Z₁).activities.E=0:=by
    funext i; unfold Placement.file Dove.arcadia Dove.fair; simp only [Function.comp_apply]
    cases Placement.numbers ι f i <;> rfl -- implicit ? no args in lemma type missing T
lemma onlyVac : (Z₁).activities.K=0:=rfl
lemma wall_vac (U:Config G f): (Z₁).activities.additive R U=0:=by
    unfold Activities.additive; simp only [Activities.regularOccurrence,Placement.still_vac]; simp [masked]
lemma ground : Herbal.Terrain Z₁ T R ψ (Typeface.brand pM s) l0 E' :=by
    refine ⟨rfl,rfl,rfl,rfl,fun _=>rfl, fun i=>⟨_,Placement.wings_sig ..⟩,fun i _=> ?_,fun i U h=>?_⟩ -- edit
    · unfold Herbal.Eden.groups; rw [Placement.wall_vac]; simp [Musicology.barren]
    let he:= (Placement.planted G' t P' hβ u i).inputs s
    rw [Typeface.photo,he]; change ((Placement.plot _ _ _).groups β U) = masked R.threshold (neighbors e _) (Tile.read _ _ _) U * 1; rw [Placement.leaves (hp:= hβ), mul_one,masked_eq _ _ _ _ (show Healthy R.threshold _ U from (by unfold Healthy; rw [h]; simp))] -- hp implicit?
end shape
end YM.RemainderComparison.Placement
