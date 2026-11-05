import YM.RemainderComparison.Seedlings.Motion
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
open Turn
variable {d:ℝ}{δ:Type} (Y:δ→Portrait R α)(b':Finset δ)(E':BoxOf H){s:Signed}{i:Site c}(w:R.activities.Moves s (S.ratio.embed i))
local notation "x₂"=> Lattice.affine s i x₁
local notation "Z₁"=> brand Y y
variable (W': ↥b≃↥b')
structure Shifting :Prop where
   light : (nearby H E x₁ r n).image (Turn.badge R w) = nearby H E' (Lattice.affine s i x₁) r n
   marks (q:↥b) : (∃ j,(X q.val).wing=Wing.logKey j)∧ ∀ j:α, Leaf.route w (Typeface.brand X j q.val) = Typeface.brand Y j (W' q).val
   reach (q:↥b) : H.supportP (Palette.sign (Typeface.brand X y) S q.val)⊆ neighbors r x₁
variable (ht:Shifting X y H b E x₁ r n Y b' E' w W')
-- Lean declaration type paid marks.H coverage anchored

def yaw : Warp (S:=S) b b' (S':=S):=⟨Turn.badge R w,W',Lattice.affine s i⟩
local notation "K"=> yaw _ _ w W' -- params
include ht
lemma buoy : Boot X y H b E x₁ r n H Y b' E' (x₂) (yaw b b' w W'):=by
   have hl q : Palette.sign Z₁ S (W' q).val = Turn.badge R w (Palette.sign X₁ S q.val):=by unfold sign; rw [← (ht.marks q).2 y]; exact Leaf.cardRoute .. -- implicit
   have hB p : H.supportP (Turn.badge R w p)= (H.supportP p).image (StepData.sendSites s i):= Turn.insignia T R w (J.halo) (radiusB x) p
   refine ⟨(Turn.badge R w).injective.injOn,?_,fun i hi=> (ht.marks ⟨i,hi⟩).1,(StepData.sendSites s i).injective.injOn, (circle_wind s i x₁ r).symm,rfl,fun i _ j _=>(by dsimp only [yaw]; simp [Lattice.affine]),ht.light,?_,ht.reach,fun i _=>hB i,hl⟩
   · intro i' hi; obtain ⟨z,hz⟩:= (ht.marks (W'.symm ⟨i',hi⟩)).1; have hu := congr_arg Leaf.turn ((ht.marks (W'.symm ⟨i',hi⟩)).2 y)
     refine ⟨w.ep z,?_⟩; rw [Equiv.apply_symm_apply] at hu; exact hu.symm.trans (congr_arg (Wing.labelRoute w) hz)
   intro j; let p:= W'.symm j; rw [show _ =_ from (congr_arg (fun p:↥b'=> sign Z₁ S p.val) (W'.apply_symm_apply j)).symm.trans (hl p),hB, circle_wind]; exact image_subset_image (ht.reach p)
variable (v:Sleet.Staff (Typeface.brand X y) H) (hv: Marvel X y H b E (k:=n) (r:=r) x₁ v)
set_option quotPrecheck false
local notation "Tt" => buoy X y H b E x₁ r n Y b' E' w W' ht
local notation "D'"=> (Tt).flora v hv
lemma airborne : Harmonics.Wake H X Y y v D' w:=by
    let p:= Tt; refine ⟨v.1.fst,v.1.snd,(D').1.snd,v.2,(D').2,rfl,rfl,fun s=>⟨?_,?_⟩⟩
    · change _= Equiv.finsetCongr _ _; rw [Equiv.finsetCongr_apply,Finset.map_eq_image]; rfl
    intro r; have h {x y:Team R}(hp:x.own=y.own): x=y:=by cases x; cases y; congr
    apply h; unfold team Team.route; dsimp only
    let X':=brand X r; let Y':=brand Y r; ext i; constructor
    · intro hi; obtain ⟨j,hj,rfl⟩:= mem_image.mp hi; obtain ⟨w,hw,rfl⟩:= (p.marks_reach v hv s _).1 hj; exact mem_image.mpr ⟨_, mem_image_of_mem X' hw,(ht.marks w).2 r⟩
    intro hi; obtain ⟨l,hl,rfl⟩:= mem_image.mp hi; obtain ⟨k,hk,rfl⟩:=mem_image.mp hl; let w':↥b:=⟨k,hv.fair.located s hk⟩; refine mem_image.mpr ⟨(W' w').val, (p.marks_reach v hv s _).2 ⟨w',hk,rfl⟩, ((ht.marks w').2 r).symm⟩
end BoxOf
end YM.RemainderComparison.Seedlings
