import YM.RemainderComparison.Seedlings.Palate
import YM.RemainderComparison.Breeze.Baskets
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
variable (b:Finset ι) -- aimed marks. vac b=∅, BOTH films use turns of chosen pages, some may share WKey
local notation "Y"=>brand X y
local notation "MΓ"=> Sleet.Staff (brand X y) H
local notation "B"=> radiusB x
namespace BoxOf
variable (E:BoxOf H) {F': Finset ι}{k n r q d m:ℕ} {s:Sleet.Staff (Typeface.brand X y) H}{Z:Set ι}{F G':Set ℕ}{V:Set (Sleet.Staff (Typeface.brand X y) H)}
local notation "SΓ"=> (Palette.sign (Typeface.brand X y) S)
local notation "S₀"=> (Sleet.Base (brand X y) H)
-- Round vacancy all-arities≤queries . No aperture directional bonds yet.
def regional (X:Support c) (n:ℕ):=∀ s∈X,X⊆neighbors n s
structure Aura (p:MΓ):Prop where
   beginF : E.Eligible H X y b k p
   transit : regional (Sleet.Base (brand X y) H p) r
-- CAREFUL parser k/r unknown implicit
structure Marvel (z:Site c)(p:MΓ): Prop where
   fair : E.Eligible H X y b k p
   roam : Sleet.Base (brand X y) H p⊆ neighbors r z

def glints (r k :ℕ): Finset MΓ := ((candles X y H b E k).subset (show {p:MΓ| Aura (k:=k) (r:=r) X y H b E p} ⊆ _ from fun p h=>(show Aura (k:=k) (r:=r) X y H b E p from h).beginF)).toFinset

def words (r k :ℕ)(z:Site c): Finset MΓ := ((candles X y H b E k).subset (show {p:MΓ| Marvel (k:=k) (r:=r) X y H b E z p} ⊆ _ from fun p h=>(show Marvel (k:=k) (r:=r) X y H b E z p from h).fair)).toFinset
local notation "A₀"=> BoxOf.glints X y H b E
local notation "P₀"=> BoxOf.words X y H b E
lemma blink : s∈ A₀ r k ↔ Aura X y H b E (k:=k) (r:=r) s := Set.Finite.mem_toFinset _
lemma shine (x:Site c) : s∈ P₀ r k x ↔ Marvel X y H b E (k:=k) (r:=r) x s := Set.Finite.mem_toFinset _
lemma stars_for (r:ℕ) : Monotone (A₀ r):=by
    intro i j h p hp; obtain ⟨hf,hk⟩:= (blink X y H b E).1 hp; exact (blink ..).2 ⟨hf.suffices h,hk⟩
lemma marks_for (r:ℕ) (z:Site c): Monotone fun i=>P₀ r i z:=by
    intro i j h p hp; obtain ⟨hf,hk⟩:= (shine X y H b E z).1 hp; exact (shine X y H b E z).2 ⟨hf.suffices h,hk⟩
variable (χ:Chi)(l:ι→ℝ)(Gm:Set ι)(B':ℝ)
local notation "Tt"=> Creek.theater H χ X y l Gm B'
local notation "w"=> Creek.Academy H χ X y l Gm B'
local notation "bk" => (Lyric.page (brand X y) H)
-- synopsis cardinal.V mark tally for any projections
lemma grace (he:Eligible H E X y b k s) : (Tt).marks s=b.val:=by
    have hx:= (Creek.rounds H χ X y l Gm B' s).mpr he.leaves; rw [← Multiset.dedup_eq_self.mpr hx, ← Multiset.toFinset_val, Creek.issued,he.atlas]
lemma admittance (he:Eligible H E X y b k s)(hl:b.card≤ n) : (s ∈ w n ∧ bk s.1 s.2=b):=by
    have ht:=BoxOf.grace X y H b E χ l Gm B' he; refine ⟨⟨?_,?_⟩,he.atlas⟩
    · unfold Verse.load; rw [ht]; exact (Multiset.card_le_card (Multiset.filter_le ..)).trans hl
    rw [ht]; exact b.nodup.filter _
variable {δ:Type}
-- core grabs before Alarms
lemma urged (hp:E.Grant H F G')(p:MΓ)(hk : p∈w k) (hg : Muse.virgin (brand X y) H χ Gm p.1 p.2) (ht:¬ Halo.dyed (brand X y) H G' p.1 p.2)
   (h: ∃ r:α,Sleet.Nordic (Typeface.brand X r) H p.1 p.2 F k q (n*(radiusB x)) ∧ ∃ V, Lyric.string (Typeface.brand X r) H χ p.1 p.2 V≠0) (hr:Sleet.cortex J.halo (radiusB x) k q n ≤ r) :
    let b:=Lyric.page (Typeface.brand X y) H p.1 p.2
    b.card ≤ k ∧ (∀ i∈ b,i∈Gm ∧ ∃ j:ℕ,(X i).wing=Wing.logKey j ∧ ¬ Sleet.cloudy R (n*(radiusB x)) j∧ ((Y i).crest.image S.ratio.parent)⊆S₀ p) ∧ ∃ m,Aura X y H b E (k:=m) (r:=r) p:=by
    intro b; obtain ⟨hz,hS⟩:= choir H χ X y l Gm B' hk hg
    obtain ⟨r',hQ,U,hX⟩:=h
    have hs:= Sleet.plate (brand X r') H p.1 p.2 F hQ
    have he i (hi:i∈ b) : i∈ Gm := by
       have hh : i∈(Tt).marks p:= (leaves H χ X y l Gm B' p i).2 hi; rw [← accord H χ X y l Gm B' hg] at hh; exact (Multiset.mem_filter.mp hh).2
    refine ⟨?_,fun i hi=>⟨he i hi,hQ.anchors i hi⟩,?_⟩
    · have hf := hk.1; unfold Verse.load at hf; rw [Creek.accord H χ X y l Gm B' (z:=p) hg,hS] at hf; exact hf
    have hv(k':Option (Fin p.1.fst))(j)(hj:j∈ (p.1.2 k').val\(p.2 k').reach) : ∀ᶠ n:ℕ in atTop,j∈E.heads n:=by
       suffices h:∃ n,j∈E.heads n by
          obtain ⟨n,hq⟩:=h; exact (eventually_ge_atTop n).mono fun k h=> E.ascends h hq
       rcases hQ.birds k' j hj with ⟨b,rfl,hT⟩|⟨i,hi,-,rfl⟩; exact hp.sees b hT
       have hE : i∉ G':= fun h=>ht ⟨k',_,⟨i,h,rfl⟩,hj⟩
       exact hp.buds _ hi hE (stirred X r' H i p k' hj U χ hX)
    obtain ⟨m,hm,hF⟩:= ((eventually_all.mpr (fun i=> (eventually_all_finset _).mpr (fun j=>hv i j))).and (eventually_ge_atTop p.1.1)).exists
    exact ⟨m,⟨hF,rfl,hz,fun i=>(Lyric.grown (brand X r') H χ p.1 p.2 U hX).2.1 i|>.2.2,fun i j hj=> hm i j hj⟩,fun i hi x hx=> (neighbors_mem ..).2 (((neighbors_mem ..).1 (hs i hi hx)).trans hr)⟩
end BoxOf
end YM.RemainderComparison.Seedlings
