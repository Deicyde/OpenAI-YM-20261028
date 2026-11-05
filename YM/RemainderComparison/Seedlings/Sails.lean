import YM.RemainderComparison.Seedlings.Thaw
import YM.RemainderComparison.Seedlings.Calm
import YM.RemainderComparison.Seedlings.Frost
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Seedlings
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Shell Census Raw Footprint Matter
open PhysicalNext.Repeat Deck Stellar Mint Poll Pond MeasureTheory ProbabilityTheory Greenbelt Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Gas Ursell Trees Blaze March Lyric WickReps Creek Mosaic Merge Palette Typeface Harmonics
variable {G : Gauge} {c f L: Side} {P:Teller G} {D: RG.Stage} {R:Rep G f}
variable {ι:Type}{α:Type*}{S:StepData c f}{T:Tube G S}{Z:Finset (Head S)}{J:ConnectedActivityE6.Target G P}{o': ℝ}
variable {W p a μ :ℝ}{x : ℝ} {o:Target.Order G W}
   (X:ι→Portrait R α)(y:α)(H:Cash W x μ L J o a T R)
variable (b:Finset ι)
namespace BoxOf
variable (E:BoxOf H) (x₁:Site c)(r n:ℕ)
local notation "X₁"=>brand X y
local notation "U"=>Sleet.Staff (brand X y) H
local notation "rX"=> (neighbors r x₁)

local notation "P₀"=> hub X y H b E x₁ r n
variable {C F:Side} {R': RG.Rep G F} {S':StepData C F}{δ:Type}{T': Tube G S'} {u:ℝ}
variable (I:Cash W x μ L J o u T' R') (Y:δ→ Portrait R' α) (b':Finset δ)(E':BoxOf I) (x₂: Site C)
local notation "Q₀"=> hub Y y I b' E' x₂ r n
local notation "Z₁"=>brand Y y
local notation "U'"=>Sleet.Staff (brand Y y) I
local notation "rY"=>neighbors r x₂

-- lean implicit
variable (K: Warp (S:=S) b b' (S':=S'))
variable {H X y b E r n I Y b' E' x₁ x₂ K}
variable (hp: Boot X y H b E x₁ r n I Y b' E' x₂ K)
-- query functions.Boot sym independent. Proof ensures arity boots and mark transport even on rotations.M.Home flag veneers.
namespace Boot
include hp
-- tower roll actual for arbitrary Boot with Meridian.T.C views irrespective weights labels; call migrations & rotations.B.Fp
variable (χ:Chi)(l:ι→ℝ)(Gm:Set ι)(b₁:ℝ)(U₀:Config G c)(l':δ→ℝ)(Δ:Set δ)(b₂:ℝ)(V:Config G C)(d:ℝ)
variable (hm: ∀ (s:Sleet.Staff (Typeface.brand X y) H)(hs:BoxOf.Marvel X y H b E (k:=n) (r:=r) x₁ s) (x':α), (Creek.theater H χ X y l Gm b₁).solvent x' s U₀= d * (Creek.theater I χ Y y l' Δ b₂).solvent x' (hp.flora s hs) V)
local notation "T₀"=> Creek.theater H χ X y l Gm b₁
local notation "T₁"=> Creek.theater I χ Y y l' Δ b₂
include hm
set_option quotPrecheck false
lemma dotted (u:α) : pool X y H b E x₁ r n χ l Gm b₁ u U₀=d * pool Y y I b' E' x₂ r n χ l' Δ b₂ u V:=by
    rw [period,period, Finset.mul_sum, ← sum_attach,←sum_attach (words Y y I b' E' r n x₂)]
    refine Finset.sum_bij (fun i _=> hp.tell i) (fun i _=> mem_attach ..) (fun _ _ _ _ h=> hp.bij_tell.1 h) (fun i _=>?_) (fun i _=> hm i.val ((BoxOf.shine ..).1 i.2) u)
    obtain ⟨j,h⟩:= hp.bij_tell.2 i; exact ⟨j,mem_attach ..,h⟩
lemma cruise (u:α): flagsCollected X y H b E r n χ l Gm b₁ u x₁ U₀=d* flagsCollected Y y I b' E' r n χ l' Δ b₂ u x₂ V:=by
    rw [BoxOf.bound,BoxOf.bound]; unfold trophy; rw [Finset.mul_sum,← Finset.sum_attach,← Finset.sum_attach (fieldWork (X:=Y) (y:=y) (H:=I) x₂ E' b' r n)]; refine Finset.sum_bij (fun i _=> hp.forestal i) (fun i _=>mem_attach ..) (fun _ _ _ _ h=> hp.bij_fore.1 h) ?_ ?_
    · intro i h; obtain ⟨j,h⟩:=hp.bij_fore.2 i; exact ⟨j,mem_attach ..,h⟩
    intro i hi; let p:= i.val; let p':=(hp.forestal i).val; change subsidies X y H x₁ p * (T₀).solvent u p U₀=d*(subsidies Y y I x₂ p'*(T₁).solvent u p' V)
    have ht:= (BoxOf.shine X y H b E _).1 (show p∈ _ from (BoxOf.adopt x₁ E b r n i).2); have hh:= ht
    rw [show _*_= _ from congr_arg (subsidies X y H x₁ p * ·) (show (T₀).solvent u p U₀= d*(T₁).solvent u p' V from hm p hh u), mul_left_comm _ d, show subsidies X y H x₁ p=subsidies Y y I x₂ p' from ?_]
    have hx : x₁∈ Sleet.Base X₁ H p:= (mem_filter.mp i.prop).2; have hy : x₂∈ Sleet.Base Z₁ I p':=(mem_filter.mp (hp.forestal i).prop).2; unfold subsidies; rw [if_pos hx,if_pos hy,show _=_ from (show (Sleet.Base Z₁ I p').card=_ from hp.cardReach p hh)]

omit hp hm
end Boot
section Rotation
variable (X Y H y) -- shadow earlier
variable (Y':δ→Portrait R α) (b b' E x₁ r n)(sd:Signed)(i:Site c)(w:R.activities.Moves sd (S.ratio.embed i)) (E₁: BoxOf H) (p:↥b≃↥b')
variable (ht:Shifting X y H b E x₁ r n Y' b' E₁ w p)
local notation "xt"=> Lattice.affine sd i x₁
variable (χ:Chi)(l:ι→ℝ)(Gm:Set ι)(b₁:ℝ)(u:α)(l':δ→ℝ)(Δ:Set δ)(b₂:ℝ)(V:Config G c)
local notation "Lt"=> Muse.sits Gm l b₁
local notation "L₁"=> Muse.sits Δ l' b₂
variable {d:ℝ}(hz: RG.flags (Pressure.temp x) V=∅)(hP:(∏ i∈ b,Muse.sits Gm l b₁ i)=d*∏ i∈b',Muse.sits Δ l' b₂ i)
variable (hYo: Bloom H χ)
include ht hYo hP hz
lemma season :
    pool X y H b E x₁ r n χ l Gm b₁ u (pull sd i V)=d * pool Y' y H b' E₁ xt r n χ l' Δ b₂ u V ∧
    flagsCollected X y H b E r n χ l Gm b₁ u x₁ (pull sd i V)=d* flagsCollected Y' y H b' E₁ r n χ l' Δ b₂ u xt V:=by
   have hg:= buoy X y H b E x₁ r n Y' b' E₁ w _ ht; obtain ⟨Q,N,h⟩:= hYo.grant
   have hm (s:Sleet.Staff (brand X y) H)(hs:Marvel X y H b E (k:=n) (r:=r) x₁ s) (x':α): (Creek.theater H χ X y l Gm b₁).solvent x' s (pull sd i V)=d * (Creek.theater H χ Y' y l' Δ b₂).solvent x' (hg.flora s hs) V:= Harmonics.moor H χ X Y' y s _ l l' Gm Δ b₁ b₂ w (airborne X y H b E x₁ r n Y' b' E₁ w _ ht s hs) N V hz _ d (hg.consonant Lt L₁ d s hs hP)
   exact ⟨hg.dotted χ l Gm b₁ _ l' Δ b₂ V d hm u,hg.cruise _ _ _ _ _ _ _ _ _ _ hm u⟩
end Rotation
end BoxOf
end YM.RemainderComparison.Seedlings
