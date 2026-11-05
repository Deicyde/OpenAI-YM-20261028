import YM.FullVolume.E6.Bronze
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
open FullVolume.Neptune Flux Shield Eider Packets Polar
variable {M: Bank}(I:Depot Q o x μ L C₀ K) (T:Depot Q o x μ L C₀ H){χ: Chi}(R:∀ n, Station M χ (I n) j)(P':∀ n,Station M χ (T n) j)
namespace Draft
open Stained
variable (h:Sweep K)(he:Sweep H)(hM:Mirror K H)(hJ:(J:Filter ℕ)≤ atTop)
include I T R P' h he hM hJ
variable [FiniteDimensional ℝ E]
lemma levers (m:(I 0).ThinP)(hv:∀ n,Healthy (Pressure.temp x) ((I 0).smallAt m) (U n p))(hp:∀ n, Mode (U n) p j M.v):
     Frill J j p (fun n y=>March.leaflet (I n) χ (U n y) m) (fun n y=> March.leaflet (T n) χ (U n y) m):=by
    refine (Frill.still _).times (Frill.buds (Finset.univ : Finset (Reserve S)) fun i _=>?_)
    let X n:= prism (K n).tubes x χ o.K (U n p) (allot i); let Y n:= prism (H n).tubes x χ o.K (U n p) (allot i)
    let Z:= m.val
    let f n (s:E):=shelter (vary (X n) (U n s)) W o.a Z (K n).kin Q.table Q.halo
    let g n (s:E):=shelter (vary (Y n) (U n s)) W o.a Z (H n).kin Q.table Q.halo
    refine Frill.alter (F:=f) (H:=g) ?_ (Eventually.of_forall fun n=> Filter.EventuallyEq.symm (rainbow (X:=X n) Z (R n|>.N.oboe) rfl rfl rfl m.property.2 (hv n) (hp n) rfl)) (Eventually.of_forall fun n=> Filter.EventuallyEq.symm (rainbow (X:=Y n) Z (P' n|>.N.oboe) rfl rfl rfl m.property.2 (hv n) (hp n) rfl))
    by_cases hh: Ac.Spark (I 0).supportP Z ∧ troupe (K 0).tubes (K 0).kin Q.halo (radiusB x) Z
    swap
    · exact (Frill.still (0:ℝ)).alter (Eventually.of_forall fun n=> Eventually.of_forall fun s=> (if_neg hh).symm) (Eventually.of_forall fun n=>Eventually.of_forall fun s=> (if_neg hh).symm)
    let a := (Fintype.card S.Choices:ℝ)⁻¹
    let M' := podium S G ((I 0).unionP Z) (radiusB x)
    let F n (s:E) k:=bars M' (((preps (vary (X n) (U n s)) (roster Z)).taggedL k)) Z (K n).kin Q.table W o.a Q.halo; let A n (s:E) k:=bars M' (((preps (vary (Y n) (U n s)) (roster Z)).taggedL k)) Z (H n).kin Q.table W o.a Q.halo
    refine ((Frill.still a).times (Frill.buds Finset.univ (F:=F) (H:=A) fun k _=>?_)).alter (Eventually.of_forall fun n=> Eventually.of_forall fun s=> (show f n s=a*∑ i,F n s i from ?_).symm) (Eventually.of_forall fun n=> Eventually.of_forall fun s=> (show g n s=a*∑ i,A n s i from ?_).symm)
    swap; · exact if_pos hh
    swap; · exact if_pos hh
    let F' n s:= bars M' (vary ((planted (X n) Z).taggedL k) (U n s)) Z (K n).kin Q.table W o.a Q.halo; let A' n s:= bars M' (vary ((planted (Y n) Z).taggedL k) (U n s)) Z (H n).kin Q.table W o.a Q.halo
    refine Frill.alter (F:=F') (H:=A') ?_ (Eventually.of_forall fun n=> Eventually.of_forall fun s=> Blaze.spices Z (I n) (X n) rfl _ _ (show Agrees _ (U n s) (U n s) from fun _ _ _=> rfl) (hv n) m.property.2 k) (Eventually.of_forall fun n=> Eventually.of_forall fun s=> Blaze.spices Z (T n) (Y n) rfl _ _ (show Agrees _ (U n s) (U n s) from fun _ _ _=> rfl) (hv n) m.property.2 k)
    obtain ⟨q,hq⟩:= carded I R (coined _ _ R h).choose_spec; obtain ⟨q',hq'⟩:=carded T P' (coined _ _ P' he).choose_spec; obtain ⟨v,hk⟩:= hq.value.bound
    have h₀ : Frill J j p F' F':= glance (v:=v) (a:=1) (Eventually.of_forall fun n=> (hq.steady n (allot i) ((planted (X n) Z).taggedL k) rfl rfl rfl rfl Z (hv n) E (U n) p (hp n) rfl).climb (budget_single (hk n) _) le_rfl)
    let Q' n:=mount (allot i) G x (U n p) χ k Z o.K
    exact ⟨h₀.seer,Eventually.of_forall fun n=> (hq'.steady n (allot i) ((planted (Y n) Z).taggedL k) rfl rfl rfl rfl Z (hv n) E (U n) p (hp n) rfl).smooth,fun j hj=>(h₀.feel j hj).time ((verse (Υ:=Q') I T R P' (fun _=> ⟨rfl,rfl⟩) (fun _=>rfl) (fun _=>rfl) hp Z j hj hv h he hM).mono_left hJ)⟩
end Draft
end YM.ConnectedActivityE6.Lim
