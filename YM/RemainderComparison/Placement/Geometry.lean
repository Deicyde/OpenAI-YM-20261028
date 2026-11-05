import YM.RemainderComparison.Placement.View
/-!
 Transporting the center and in-cell offsets for a single ACTUAL page.
 Keep every requested address even at coinciding MARK points. License here is
 about input registrations, not the (independent) output forecast.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Placement
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Shell Census Raw Footprint Matter
open PhysicalNext.Repeat Deck Stellar Mint Poll Pond MeasureTheory ProbabilityTheory Greenbelt Lotus Sienna Fare
open Further.PhysicalPeriodLimitF933 Macrame
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Gas Ursell Trees Blaze March Lyric WickReps Creek Mosaic Merge Palette Typeface Harmonics
open AnalyticBridge VerifiedReset Next.Scheduling Extra.Iteration Song Aria Seedlings BoxOf
variable {G : Gauge} {f c F C L: Side}{P:Teller G} {q e j k N u r:ℕ}
variable {ι:Type} [Countable ι] {α:Type*}{A:ℝ}
variable (R:Rep G f)(R':Rep G F)
set_option quotPrecheck false
local notation "R_"=> Placement.file R e ι
local notation "Rh"=> Placement.file R' e ι
local notation "p"=> R.p
variable (v:α) (D:ι→ Tile G α q e A) (o o':ι→Site f)(d:ι→Site F)
variable (hp:0 < R.beta) (hg:0<R'.beta)
local notation "W" j:max=> Placement.plants R v D hp j
local notation "M₀" => Placement.plants R v D hp o
local notation "M₁" => Placement.plants R v D hp o'
local notation "M₂"=> Placement.plants R' v D hg d
variable (i:ι)
variable {V₀:Patch}{hC: C.val=c.val*N} {hh:F.val = C.val*V₀.L.val}{h:f.val=c.val*V₀.L.val}{X:KernelChoices}
local notation "Q"=> stepped X h
local notation "J"=> stepped X hh
local notation "Vt"=> decreed h
local notation "Vh"=> decreed hh
variable {T:Tube G (stepped X h)}{Y:Tube G (stepped X hh)}{S:ConnectedActivityE6.Target G P} {s κ μ Γ β t C₀ :ℝ}{K:Target.Order G μ}
set_option quotPrecheck false
local notation "ξ"=> Deck.Mint.width S.halo (radiusB β) e
local notation "TS"=> Timbre.trumpets
variable (V: Cash μ β t L S K Γ T (Placement.file R e ι))
variable (Z : Cash μ β t L S K C₀ Y (Placement.file R' e ι))
variable (b:Finset ι)(x:Site c) (y:ℝ)(l:ι→ℝ)
local notation "p₀"=> Placement.silent V
local notation "pE"=> Placement.silent Z
-- travel from larger-period synthetic stamped admissions to both lenders.
-- offsets X' fixed. preserved R sized. No payouts assumed through previous full program.
variable (hC) (hv: 2 ≤ c.val) (hy:4<f.val) (ht: R.p=R'.p)(hz:R'.path=R.path)(hw:R.beta=R'.beta)
variable (hT:Y=Deck.re T)
local notation "F_"=> Lace.project (h:=h) (H:=hh) hC hv
local notation "fE"=> (F_).high.cut
local notation "fL"=> (F_).low.cut
local notation "d₀"=> (fE ∘ d)
local notation "M₃"=> Placement.plants R v D hp d₀
variable (hu: 2*(2*r+3)<c.val) (hH: 2*(r+Deck.Mint.width S.halo (radiusB β) (radiusB β))<c.val)
variable (hd: u+Deck.Mint.width S.halo (radiusB β) e ≤ r)
variable (hZ:∀ i'∈b, separation 0 ((decreed hh).parent (d i')) ≤ u)
variable (hx:∀ i∈b,o i= (Lace.project (h:=h) (H:=hh) hC hv).high.cut (d i)+(decreed h).embed x)
include hv hy ht hu hH hZ hx hd hw hz hT
variable (π:R.activities.Moves 1 ((decreed h).embed x))
include π
lemma ports (n:ℕ) : BoxOf.Port hC hv Z V M₂ M₀ v (Timbre.trumpets Z) (Timbre.trumpets V) b b x r n l l Set.univ Set.univ 0 0 1:=by
    have hX(i:↥b):= Placement.filing R R' v D d₀ d hp hg i.val hy ht (hc:= Deck.fineP h hh hC) rfl -- projection correct? hc=fI
    have he : Aria.Wears hC hv Z V 0 pE p₀:= ⟨rfl,fun _ i=> i.elim,fun _ i=>i.elim⟩
    have hA : Aria.Scheduled hC hv Z V M₂ M₃ 0 r pE p₀ (0:Site C) b b (Equiv.refl _) := by
        refine ⟨fun i=> ⟨⟨_,Placement.wings_sig R' v D d hg i.val,fun _ i=> i.elim⟩,⟨_,Placement.wings_sig R v D d₀ hp i.val,fun _ i=> i.elim⟩⟩,fun i=> (hX i).1,fun i a U=>(hX i).2 _ _,?_, (Placement.augments R' v D d hg).injOn,(Placement.augments R v D d₀ hp).injOn⟩
        intro i hi j hj; apply (neighbors_mem ..).2; exact (separation_triangle _ ((decreed hh).parent (d i)) _).trans ((add_le_add (hZ i hi) ((neighbors_mem ..).1 (Placement.watching R' v D d hg i Z hj))).trans hd)
    have hy(i:ι)(hi:i∈b): separation 0 ((stepped X h).ratio.parent (d₀ i)) ≤ u :=by
        let A : Site C :=(decreed hh).parent (d i); change _ ≤ _; rw [show _=(F_).low.cut A from (show (Q).ratio.parent _= _ from ?_)] -- test
        · exact le_trans (show separation 0 (_:Site c) ≤ separation (0:Site C) _ from (map_zero (Macrame.splitter (Deck.divides hC))) ▸ Deck.less (Deck.divides hC) (0:Site C) A) (hZ _ hi)
        exact (F_).position (d i)
    have hv := Aria.passage hC hv Z V (show _ from hT) (show (Rh).path=(R_).path from hz) (show (Rh).p=(R_).p from ht.symm) (show (Rh).beta=(R_).beta from hw.symm) M₂ M₀ v 0 r pE p₀ he (by omega) hH b b (Equiv.refl _) M₃ x _ (Placement.transports R v D o d₀ hp V b x π hx hy hd) l Set.univ l Set.univ 0 0 1 n hA (by simp only [one_mul]) -- order inspect
    rw [quiet_score,quiet_score] at hv; exact hv
omit hv hy ht hu hH hZ hx hd hw hz hT π
-- shape profile stencil from offset world. Different appointments.Per.Per.C. root NO gauge permission required for transport. offsets using parent with canonical lift.U.Mark retains rank and repetitions.
structure Center (B:Side) (ι:Type) where
    coarseOff : ι→ Cover
    interior : ι→ Site B
namespace Center
variable (V:Placement.Center V₀.L ι)
-- bin.Site C.
omit [Countable ι] in
def atCore (hh:F.val=C.val*V₀.L.val)(x:Site C) (i:ι) : Site F:=
   (decreed hh).assemble (x+Lattice.wrap C (V.coarseOff i), V.interior i)
include hC hv
omit [Countable ι] in
lemma landing : (F_).high.cut (atCore V hh 0 i) + (decreed h).embed x= atCore V h x i:=by
   unfold atCore; rw [zero_add, (F_).regions]; simp_rw [show (F_).low.cut (wrap C (V.coarseOff i))= _ from (Macrame.branch (Deck.divides hC) _)]; unfold Ratio.assemble; dsimp only; rw [show (Vt).embed (x+_) = (decreed h).root x+ _ from (decreed h).root.map_add ..]; rw [Ratio.root_embed,Ratio.root_embed]; unfold Lace.r; abel
omit hC hv
omit [Countable ι] in
lemma reaches (he:∀ j,(V.coarseOff i j).natAbs≤ r) (hh:F.val=C.val*V₀.L.val) : separation (0:Site C) ((Vh).parent (atCore V hh 0 i)) ≤ r:=by
    unfold atCore; rw [Ratio.assemble_parent]; change separation 0 ((0:Site C) + wrap C (V.coarseOff i)) ≤ r
    rw [zero_add,separation_comm,separation,sub_zero]; exact Finset.sup_le fun b _=> (Lattice.Corona.lap ..).trans (he b)
end Center
omit [Countable ι] in
def history (h:f.val=c.val*V₀.L.val)(i:Site c): Placement.Center V₀.L ι:=
   ⟨fun j=> Lattice.lift ((decreed h).parent (o j)-i), (decreed h).residue ∘ o ⟩
local notation "𝓒"=> Placement.history o h x -- arg check
omit [Countable ι] in
lemma authentic (h): Center.atCore (Placement.history (V₀:=V₀) o h x) h x i=o i:=by
    unfold Center.atCore history; rw [wrap_lift]; simp only [add_sub_cancel]; exact Ratio.unpack_at ..
omit [Countable ι] in
lemma visits (h) (he: separation x ((decreed h).parent (o i))≤ u): ∀ j,((Placement.history (V₀:=V₀) o h x).coarseOff i j).natAbs ≤ u:= by
    rw [separation_comm] at he
    unfold separation at he; exact fun j=>(component_le ..).trans he
end YM.RemainderComparison.Placement
