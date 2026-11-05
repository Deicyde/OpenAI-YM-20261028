import YM.FullVolume.E6.Geared
/-! E6 Layout steps full volume.Epoch. Keep Records by exact tags.Canvas.Read.F. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Lim
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration PhysicalNext.Repeat Greenbelt Match Song Refrain
open Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open UVNext.CouplingReset Animals Progress.DirectedRecipe Ovens
open Stationary Stationary.Shade Stationary.Beacon Laurent Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {P : Teller G} {S : StepData c f} {F : Forest S.ratio}
open Matrix Window Progress.StationaryScenes Green Census Control Flux FullVolume.Shadow
open Gate Frond Vine Mask
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {φ: Filter ℕ}{J: Ultrafilter ℕ}{Q:ConnectedActivityE6.Target G P}{W x μ C₀ a b e ℓ v :ℝ}{o:Target.Order G W}
    {Λ: Era G S}{U:ℕ→ E→ Config G c}{Z: Draft F G} {K H:ℕ→ Epoch Λ}{j:ℕ}{p:E}
-- Common fixed masks for ALL hard inspections via Era. Mutable arguments steered.
variable [FiniteDimensional ℝ E]
namespace Draft
variable (H₀:∀ n,Cash W x μ L Q o C₀ (K n).tubes (K n).kin)(hQ: ∀ n,Promo Q o j x v ℓ a Z.χ (K n).tubes)
   (hz:Z.Paid Q o x) (h:Finish J K H)(he:∀ᶠ i in (J:Filter ℕ), Mode (U i) p j v)(ht:∀ᶠ i in (J: Filter ℕ), Z.Viable (U i p))
include hz H₀
set_option quotPrecheck false
local notation "D" => fun n y=> (Z.paints (K n) (U n y))
local notation "D'" => fun n y=> (Z.paints (H n) (U n y))
lemma gangU (h:∀ᶠ i in φ, Z.Viable (U i p)): ∀ᶠ n in φ,Allow ((D n p).plate) (along S) (tubularPrice G L) o.eta o.gap o.ample:= h.mono fun n hn=> licenses hz _ (H₀ n) _ hn -- call
include he ht h
-- recurring blank.Key costs
lemma downer : ∀ᶠ n in (J:Filter ℕ), Z.pearl.Viable (1:Config G c) := Eventually.of_forall fun n=> (D n p).bowed (temp_nonneg _)
lemma blankScale : ∀ᶠ n in (J:Filter ℕ), Allow (D n p|>.blank.plate) (along S) (tubularPrice G L) o.eta o.gap o.ample:=by
    exact Eventually.of_forall fun n=> ((H₀ n).laws.data.localP F (D n p|>.blank) hz.1 hz.2 ((D n p).bowed (temp_nonneg _))).sails.scale
lemma blankWing : Buds J j p (fun n y=> (D n y).blank.plate) (fun n y=> (D' n y).blank.plate):=by
    exact plume (E:=E) (U:=fun n y=>1) (V:=fun n y=>1) h (Quincy.standards (p:=fun _=>1) J) Z.pearl
lemma charges (i) : Frill J j p (fun n y=> (D n y).condensation i) (fun n y=> (D' n y).condensation i):=
     ((planets (blankWing H₀ hz h he ht) (blankScale H₀ hz h he ht) o.f (Coat.frames G S (radiusB Z.x)) i).sub (planets (plume h (scaleG he) Z) (gangU H₀ hz ht) o.f (Coat.frames G S (radiusB Z.x)) i)).via (contDiff_id.div_const 2)
open Itinerary
lemma wastes (n i) : Buds J j p (fun k y=> (D k y).finale n i) (fun k y=> (D' k y).finale n i):=by
    have hp:= plume h (scaleG he) Z; by_cases hi:i ≤ n
    · have hd:= relate H₀ hz h (scaleG he) ht
      simp only [Coat.finale, hi, ↓reduceIte]; exact fun i k=> (((hp.pairs hd i k).sub (Frill.still _)).neg)
    simp only [Coat.finale,hi,↓reduceIte]; exact hp
variable {u u':ℕ→E→Directions G f}{z z':ℕ→ E→ Air f G}
lemma circles (hp:Frill J j p z z')(b: Ledger f 2): Frill J j p (fun n y=> (D n y).qunique (z n y) b) (fun n y=> (D' n y).qunique (z' n y) b):=
    ((Frill.still _).times (Frill.buds Finset.univ fun i _=> (pointed hp (b.2.1,i)).times (Frill.buds Finset.univ fun i' _=> ((Buds.sticky _ _ (wastes H₀ hz h he ht _)) i i').times (pointed hp (_,i')))))
-- group chart gentry all arguments. extension
omit H₀ hz h he ht in
lemma lamps (i:Bond f) (he:Frill J j p u u')(b:ℝ) : Frill J j p (fun n y=> (D n y).cone b (u n y) i) (fun n y=> (D' n y).cone b (u' n y) i):=by
    let w:G.Color→ℝ:=fun x=> Z.χ.innerShare (b*(D 0 p).t) ‖x‖; refine (he.cross i).via (Q:=w) ?_; unfold w Chi.innerShare; simp_rw [div_pow]; exact (Z.χ.smooth.of_le (show (j:WithTop ℕ∞)≤ ∞ from WithTop.coe_le_coe.mpr le_top)).comp ((contDiff_norm_sq ℝ).div_const _)
omit h he ht in
private lemma gearC (i:Bond f) : let X:=Z.paints (K 0) (1:Config G c); ContDiff ℝ (↑j) (fun u=> X.gentry Q.table o.a u i):=by
    intro X; apply contDiff_iff_contDiffAt.mpr; intro x'; let u:=2*o.a; let τ:=Q.table
    have hp:= (H₀ 0).laws.data; have hw:0< X.t:=show 0<Pressure.fiery G Z.x S.patch.L from hz.1.symm ▸ hp.room.fiery
    have hv:0<u*X.t:= mul_pos (mul_pos (by norm_num) o.large) hw
    have hh: 2*u*X.t< τ.radius:=by
        rw [show 2*u=4*o.a from by unfold u; ring, show X.t=_ from (show X.t= Pressure.fiery G x L from by change Pressure.fiery G Z.x S.patch.L=_; rw [hz.1,hp.funds.length_eq])]; exact hp.covers
    by_cases hk: ‖x' i‖ ≤ 2*u*X.t
    · apply ContDiffAt.mul
      · unfold Coat.cone Chi.innerShare; simp_rw [div_pow]; refine ((Z.χ.smooth.of_le (show (j:WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).comp ?_).contDiffAt; exact ((contDiff_norm_sq ℝ).comp (contDiff_pi.mp contDiff_id i)).div_const _
      have hr: x' i∈Metric.ball (0:G.Color) τ.radius:= Metric.mem_ball.mpr (by rw [dist_zero_right]; exact hk.trans_lt hh)
      exact (((Q.table_exists.germ (x' i) hr).log (Q.table_exists.pos _ hr).ne').of_le (le_top)).comp _ (f:=fun y : Directions G f=> y i) (contDiffAt_pi.mp contDiffAt_id i)
    apply (contDiffAt_const (c:=(0:ℝ))).congr_of_eventuallyEq
    filter_upwards [((continuous_apply i).tendsto x').norm.eventually (lt_mem_nhds (lt_of_not_ge hk))] with x hx
    have he: X.cone u x i=0:= by by_contra he; exact (show 2*u*X.t < ‖x i‖ from hx).not_ge (X.amount hv _ _ he)
    change X.cone u x i*_=0; rw [he,zero_mul]
omit h he ht in
lemma gears (hu:Frill J j p u u')(i:Bond f): Frill J j p (fun n y=> (D n y).gentry Q.table o.a (u n y) i) (fun n y=> (D' n y).gentry Q.table o.a (u' n y) i):= hu.via (gearC (j:=j) H₀ hz i)
-- contour.Spin Stamp curves
open Polar
include hQ
lemma rowsP (he':Frill J j p u u')(hv:Frill J j p z z')(i:ChainIndex f): Frill J j p (fun n y=> Polar.spins (D n y) o.a (K n).kin (u n y) (z n y) i) (fun n y=>Polar.spins (D' n y) o.a (H n).kin (u' n y) (z' n y) i):=by
    let M:=Coat.frames G S (radiusB Z.x)
    have hA:= plume h (scaleG he) Z; have hx:= gangU H₀ hz ht
    have hF i : Frill J j p (fun n y=> Polar.patch (D n y) o.a (u n y) i) (fun n y=> Polar.patch (D' n y) o.a (u' n y) i):=by
         by_cases hk:(D 0 p).Hot i
         ·
           refine (lamps (Z:=Z) (U:=U) (K:=K) (H:=H) i he' (2*o.a)).alter (Eventually.of_forall fun n=> Eventually.of_forall fun y=> (if_pos (show (D n y).Hot i from hk)).symm) (Eventually.of_forall fun n=> Eventually.of_forall fun y=> (if_pos (show (D' n y).Hot i from hk)).symm)
         refine (Frill.still _).alter (Eventually.of_forall fun n=> Eventually.of_forall fun y=> (show Polar.patch _ _ (u n y) i=1 from if_neg (show ¬(D n y).Hot i from hk)).symm) (Eventually.of_forall fun n=>Eventually.of_forall fun y=> (if_neg (show ¬(D' n y).Hot i from hk)).symm)
    rcases i with i | i | i | i | i
    · exact ((thought hA hx o.f M i).neg.via (contDiff_id.div_const 2))
    · exact ((thought (blankWing H₀ hz h he ht) (blankScale H₀ hz h he ht) o.f M i).via (contDiff_id.div_const 2))
    · exact ((sphinx hA hx o.f M i).via (contDiff_id.div_const 2))
    · exact (hF i).times (Frill.buds Finset.univ fun k _=> (pointed hv _).times (harry H₀ hQ hz h he ht (i,k)))
    exact ((hF i.2.1).times (hF _)).times (circles H₀ hz h he ht hv i)
end Draft
end YM.ConnectedActivityE6.Lim
