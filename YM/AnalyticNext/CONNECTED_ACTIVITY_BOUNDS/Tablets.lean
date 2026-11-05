import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Embargo

/-!
# One chart support and true mask protections through the packet

Constants r subselection to satisfy both `LocalRatio` and the producer
inverse prices. Hold at secondary scale u on F's smallest stencil.
Gamma broad width B^17 t, pays all estimated centers even where larger
than constant * t. This is for hit/smallness, doesn't assert later
polynomial losses in E-low-grade-rescaling are affordable at earlier L.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Aff
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Bloch Turn
open Matrix Work.F03 Progress.StationaryScenes Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.AbsoluteSums Tree Next.Fluctuations Finset Win Rates
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f} {T : Tube G S}

section

structure Choice (N : ChartRatio G) (r : ℝ) : Prop where
  h : LocalRatio N
  pos : 0<r
  mail : r ≤ N.radius
  law : LocalH.Geom G (G.lieExp '' Metric.ball 0 r) (Metric.ball 0 r)



def holdSize (G : Gauge) (D : Patch) (x : ℝ) := allowance G D x 1 1
def chartSize (G : Gauge) (D : Patch) (x : ℝ) := allowance G D x 1 17

lemma pos_size (G : Gauge) (D : Patch) : ∀ᶠ x : ℝ in atTop, 0 < fiery G x D.L ∧
    0 < holdSize G D x ∧ holdSize G D x ≤ chartSize G D x := by
  filter_upwards [(Work.E09.betaF_growth G D.L).eventually (eventually_gt_atTop 0),
    Work.E01.radiusB_tendsto.eventually_ge_atTop 1, Rates.widen G D 1 (by decide : 1≤17)] with x hx hv hp
  have hx : 0 < fiery G x D.L := Work.E09.temp_pos hx
  exact ⟨hx,by unfold holdSize allowance pieces; positivity,hp⟩

-- product over active only, window held frozen constant. ψ defined
-- even when broad guard evaluated separately in optional background.
variable (x : ℝ) (D : Patch)

def broad (q : Chi) (a : G.Color) := q.innerShare (chartSize G D x) ‖a‖
def ψ (q : Chi) (a : G.Color) := q.innerShare (2*chartSize G D x) ‖a‖





def prorated (q : Chi) (N : ChartRatio G) (a : G.Color) := broad x D q a*N.J a



end

namespace Mint
variable {F : Forest S.ratio} {A : Stores S} {x : ℝ} (Y : Mint T F A x)

-- `a` positive real array BEFORE suppressing inactive or before
-- changing variables. `only` is projection onto all selected bonds.

def build (a : ArrayR G f) := install A F (radiusB x) Y.V Y.Y a

def only (_Y : Mint T F A x) (a : ArrayR G f) : ArrayR G f := fun i =>
    if i.1 ∈ activeB A F (radiusB x) then a i else 0

def chambers (p : Stores S) (N : ChartRatio G) (a : ArrayR G f) :=
    ∏ i∈ padB p (304*radiusB x) ∩ activeB A F (radiusB x), prorated x S.patch Y.q N (lie a i)

def road (a : ArrayR G f) := lie (Y.sh + Y.only a)

-- don't re-read frozen as Z
lemma on_active (a : ArrayR G f) (p : Bond f) (hp : p∈ activeB A F (radiusB x)) : Y.road a p = lie a p ∧
    Y.build a p = increment (replica S.ratio Y.V) (lie a) p := by
  have hi : p∉F.trunks := (mem_filter.mp hp).2.1
  constructor
  · ext i
    change Y.sh (p,i)+ Y.only a (p,i)=_; rw [show Y.sh (p,i)=0 from plateau_zero ..,zero_add]; exacts [if_pos hp,hp]
  unfold build install; rw [show F.drape _ p = _ from F.off_tree _ ⟨p,hi⟩]; exact if_pos hp

lemma on_trunk (a : ArrayR G f) (p : Bond f) (hp : p ∈ F.trunks) :
    Y.road a p=0 ∧ Y.build a p=increment (replica S.ratio Y.V) (Y.road a) p := by
  have hh : p ∉ activeB A F (radiusB x) := by simp [activeB,hp]
  have he : Y.road a p=0 := by
    unfold road only sh fixed real; ext i; simp [lie,hp,hh]
  have hf : replica S.ratio Y.V p=1 := if_pos (F.trunk_internal hp)
  exact ⟨he,(real_tree A F _ Y.V Y.Y a p hp).trans (by simp [increment,he,hf])⟩



lemma roads (a : ArrayR G f) (i : Pos S) (he : i ∈ choosing A (radiusB x))
    {P : Teller G} (hT : P.Funds S T) :
    descend (Y.actions a) i = Real.sqrt weight •
      (target T (till x) (temp x) i Y.k Y.V (replica S.ratio Y.V) + derivative T (till x) i Y.V (Y.road a)) := by
  have ha : Y.D *ᵥ a = Y.D *ᵥ (Y.only a) := by
    funext i
    unfold Matrix.mulVec dotProduct
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold only; split
    next => rfl
    next h => dsimp only; simp [Y.activeD i j h]
  have hi := summit i Y.V T A F x (Y.only a) hT he (fun j hj => if_neg hj)
  let L := elongate x Y.V i hT
  have hd : derivative T (till x) i Y.V (Y.road a) = L (lie Y.sh) + L (lie (Y.only a)) :=
    map_add L (lie Y.sh) (lie (Y.only a))
  ext j
  change Y.actions a (i,j)=_
  rw [actions,Pi.add_apply, ha]
  unfold origin zeroed; simp only [he, ↓reduceIte]
  rw [as_applied _ _ hT,hd]
  simp only [PiLp.smul_apply,PiLp.add_apply]
  rw [show (Y.D *ᵥ Y.only a) (i,j)=(Real.sqrt weight • L (lie (Y.only a))) j from congr_arg (fun u : G.Color => u j) hi]
  simp only [PiLp.smul_apply]; unfold L; change _=_*(_+(_+_)); ring_nf; rfl
end Mint
end YM.AnalyticNext.ConnectedActivity.Aff
