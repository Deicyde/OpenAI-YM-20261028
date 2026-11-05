import YM.RemainderComparison.Seedlings.Motion
import YM.RemainderComparison.Apo.Star
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

variable (χ:Chi)(l:ι→ℝ) (Gm:Set ι)(p₁:ℝ) (V:Config G c)
local notation "Tt"=> theater H χ X y l Gm p₁
local notation "Mk"=> glints X y H b E r n
local notation "Mr"=> words X y H b E r n x₁
local notation "Mz"=> fieldWork (X:=X) (y:=y) (H:=H) x₁ E b r n

def subsidies (x:Site c) (i:U):ℝ := if x∈ Sleet.Base (brand X y) H i then ((Sleet.Base (brand X y) H i).card:ℝ)⁻¹ else 0
local notation "Sb" => subsidies X y H
lemma fee (i:U) : ∑ x,Sb x i=1:=by
    let F:= Sleet.Base _ H i; have hf:F.Nonempty:= by unfold F; apply Finset.Nonempty.mono (subset_biUnion_of_mem (H.smallAt ∘ i.1.2) (mem_univ none)) (i.1.2 _).2.1
    have hP: #(univ.filter fun i=> i∈F) = #F:=congr_arg Finset.card (by ext j; simp)
    have h:(#F:ℝ)≠0:= by exact_mod_cast hf.card_pos.ne'
    change (∑ x, if x∈F then (#F :ℝ)⁻¹ else 0)=_; rw [← sum_filter,sum_const,hP]; rw [nsmul_eq_mul,mul_inv_cancel₀ h]
def weights : (Tt).Basis Mk r:=by
    refine ⟨fun x=> Sb x, fun i h=>?_,fun i _=>fee _ _ _ _,fun x i hi hx=>?_⟩
    · unfold subsidies; split <;> positivity
    rw [Creek.point]; apply ((blink ..).1 hi).transit x; exact by_contra fun ht=> hx (if_neg ht)
variable (u:α)
def trophy (V:Config G c):=∑ i∈fieldWork (H:=H) (X:=X) (y:=y) x₁ E b r n,Sb x₁ i*(Tt).solvent u i V
def flagsCollected := (Tt).sector u Mk (weights X y H b E r n χ l Gm p₁)
lemma bound : flagsCollected X y H b E r n χ l Gm p₁ u x₁= trophy X y H b E x₁ r n χ l Gm p₁ u:=by
    funext V; unfold trophy; symm
    change _= ∑ i∈Mk,(weights X y H b E r n χ l Gm p₁).support x₁ i * (Tt).solvent u i V -- f suppressed RHS
    change _= ∑ i∈Mk,Sb x₁ i * (Tt).solvent u i V; exact sum_subset (filter_subset ..) (fun i hi hx=>mul_eq_zero_of_left (if_neg (fun hp=>hx (mem_filter.mpr ⟨hi,hp⟩))) _)
def pool := Apo.slab (Tt) Mr u
lemma period (V:Config G c) : pool X y H b E x₁ r n χ l Gm p₁ u V= ∑ i∈Mr,(Tt).solvent u i V:= rfl
structure Bloom (X:Cash W x μ L J o a T R)(χ:Chi): Prop where
    grant : ∃ (k:ℕ) (U':Muse.Pad X k χ),Cascade.Heroes X U'.S.N.conduit U'.S.A U'.S.B U'.S.n
variable (h: Bloom H χ)
include h
lemma locality (i:U) : LocalOn (Sleet.Base X₁ H i) ((Tt).solvent u i):=by
   obtain ⟨k,K',h⟩:= h.grant; have hh: LocalOn (Sleet.Base (brand X y) H i) (string (brand X u) H χ i.1 i.2):= (Lyric.expense (brand X u) H χ (Lyric.rocketing _ _ _ _ h) i.1 i.2).1
   intro j v hp; exact congr_arg (_ * ·) (hh j v hp)
lemma applause : LocalOn rX (trophy X y H b E x₁ r n χ l Gm p₁ u):=by
    intro a b ht; refine sum_congr rfl fun i hi=> congr_arg (_ * ·) (locality X y H χ l Gm p₁ u h i _ _ (agrees_mono ht ?_))
    exact show Sleet.Base X₁ H i⊆ rX from ((blink ..).1 (mem_filter.mp hi).1).transit _ (mem_filter.mp hi).2
lemma polar : LocalOn rX (pool X y H b E x₁ r n χ l Gm p₁ u):=fun _ _ ht=>sum_congr rfl fun i hi=> locality _ _ _ _ _ _ _ _ h i _ _ (agrees_mono ht ((BoxOf.shine X y H b E _).1 hi).roam)
end BoxOf
end YM.RemainderComparison.Seedlings
