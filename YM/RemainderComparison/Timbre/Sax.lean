import YM.RemainderComparison.Timbre.Down
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Timbre
open Seedlings
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter
open PhysicalNext.Repeat Deck Stellar Mint Poll Pond MeasureTheory ProbabilityTheory Greenbelt Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F L₀:Side} {P : Patch} {M : ℕ} {K : Teller G}
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q:KernelChoices} {hC : C.val=c.val*M} {he:2 ≤ c.val}
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {T: Tube G (stepped Q h)} {T': Tube G (stepped Q H)} {p : ℝ} {E: Forest (stepped Q h).ratio} {E':Forest (stepped Q H).ratio}
    {R:RG.Rep G f} {R':RG.Rep G F}
local notation "B" => radiusB p

variable (hC he) (I:Team R) (I':Team R')
variable {Z:Site C}{n:ℕ} {a W K₀ v : ℝ} {J : ConnectedActivityE6.Target G K} {o : ConnectedActivityE6.Target.Order G W}
    (C' : Cash W p a L₀ J o K₀ T' R') (c' : Cash W p a L₀ J o v T R) (hq : T'= re T)
    (ht : R'.path=R.path) (hx : R'.p=R.p) (hb:R'.beta=R.beta) (V:Molecule (stepped Q H))(U:Molecule (stepped Q h))
variable {hC he I I' V U}
variable (χ:Chi)
open Gas Ursell Trees Blaze March Lyric WickReps Creek Mosaic Merge Palette Typeface
open Harmonics
open BoxOf
variable {ι δ:Type}{α:Type*}(X:ι→Portrait R' α) (Y₁:δ→Portrait R α)(y:α)
local notation "X₁"=>brand X y
variable (hC he)
local notation "Z₁" => brand Y₁ y
variable (K':BoxOf C') (D':BoxOf c') (b:Finset ι)(b':Finset δ)
variable (x:Site C) (r n:ℕ)(W' : Warp («S»:= stepped Q H) b b' (S':=stepped Q h))
set_option quotPrecheck false
local notation "uₓ"=> (L).low.cut x

-- lexical elements only, geometry fields to see any mask & enforcers. port.X.No cost expected.
variable {hC he}
-- music sector.Crew.Card.Vac Warp support only.Now ensure width.
def bag (hC:C.val=c.val*M)(he:2≤c.val) (q:Head (stepped Q H)): Head (stepped Q h):= if h': q∈ Set.range (Mint.disc (stepped Q H)) then Mint.disc (stepped Q h) (verse_down (Lace.project (h:=h) (H:=H) hC he) h'.choose) else Opacity.key (stepped Q h) 0
set_option quotPrecheck false
local notation "L'"=> (Lace.project (h:=h) (H:=H) hC he)
local notation "Z'"=> (trumpets C')
local notation "D''"=> (trumpets c')
variable (hC he)
lemma pile (i:Music C F): bag (h:=h) hC he (Mint.disc (stepped Q H) i)= Mint.disc (stepped Q h) (verse_down (L') i):=by
    have hp: disc (stepped Q H) i∈Set.range (Mint.disc (stepped Q H)):=⟨i,rfl⟩; unfold bag; rw [dif_pos hp,(disc (stepped Q H)).injective hp.choose_spec]
lemma cheaper (j:Music C F): Meadow.held (verse_down (L') j)=Meadow.held j:=by rcases j with j|j|j|j <;> rfl
-- archelight.F. Power.Alive enlarge only for proof existence aperture's birth.
variable (hc:2*(r+Mint.width J.halo (radiusB p) (radiusB p))<c.val)
local notation "V₀"=> nearby C' Z' x r n
local notation "U₀"=> nearby c' D'' ((L').low.cut x) r n
local notation "pF"=> bag (h:=h) (H:=H) (Q:=Q) hC he
include C' c' ht hc
lemma snack : Set.InjOn (pF) (↑V₀)∧ (V₀).image (pF)= U₀:=by
    let P:= L'; have hz : 0< B:= lt_of_lt_of_le (by norm_num) c'.laws.data.room.sight.1
    have h𝒩 : (neighbors r x).image (L').low.cut=neighbors r ((L').low.cut x):=(Deck.inclined hC r x).symm
    constructor
    · intro i hi j hj hp; obtain ⟨i,rfl⟩:= knock C' n i (mem_filter.mp hi).1; obtain ⟨j,rfl⟩:= knock C' n j (mem_filter.mp hj).1; rw [pile,pile] at hp
      have hx (i) (hi:Mint.disc (stepped Q H) i∈V₀): separation x (pace Y i)≤ r:= (neighbors_mem ..).1 ((mem_filter.mp hi).2 (Mint.centered J.halo B B hz i Y T' R' (((Timbre.chants C' n i).1 (mem_filter.mp hi).1).2)).1)
      refine congr_arg _ ( (nest_mint (hC:=hC) (he:=he) (h:=h) (H:=H) (Q:=Q)).point hc x i j ((hx i hi).trans (Nat.le_add_right ..)) ((hx j hj).trans (Nat.le_add_right ..)) ((Mint.disc (stepped Q h)).injective hp))
    ext i; constructor
    · intro he; obtain ⟨j,hJ,hB⟩:=mem_image.mp he; obtain ⟨j,rfl⟩:= knock C' n j (mem_filter.mp hJ).1; have hh:= Meadow.contempt hC (by assumption) ht (I':=C') (I:=c') j
      subst i; rw [pile]; apply mem_filter.mpr; refine ⟨?_,?_⟩; · rw [chants,cheaper,← hh.1]; exact (chants C' n j).1 (mem_filter.mp hJ).1
      rw [hh.2,← h𝒩]; exact image_subset_image (mem_filter.mp hJ).2
    intro hi; obtain ⟨i,rfl⟩:= knock c' n i (mem_filter.mp hi).1
    obtain ⟨j,h,hj⟩:= (nest_mint (hC:=hC) (he:=he) (h:=h) (H:=H) (Q:=Q)).esc x i
    obtain ⟨hiP,he'⟩:= (chants c' n i).1 (mem_filter.mp hi).1
    have hz' : separation x (pace Y j)≤ r:=hj.trans_le <| (neighbors_mem ..).1 ((mem_filter.mp hi).2 (Mint.centered J.halo B B hz i S T R he').1)
    have hN:= Meadow.contempt hC he ht (I':=C') (I:=c') j; have hy: Mint.verse R'.path j≤ B:=(hN.1.trans (congr_arg (verse R.path) h)).trans_le he'
    refine mem_image.mpr ⟨(disc (Y) j),mem_filter.mpr ⟨(Timbre.chants C' _ _).2 ⟨?_,hy⟩,?_⟩, (pile _ _ _).trans (congr_arg _ h)⟩
    · exact (show Meadow.held j=Meadow.held i from (cheaper (h:=by assumption) (H:=H) hC he j).symm.trans (congr_arg Meadow.held h)).trans_le hiP
    intro z hz''; have hc' : z∈neighbors (r+Mint.width J.halo B B) x:=by exact (neighbors_mem ..).2 ((separation_triangle _ (pace Y j) _).trans (Nat.add_le_add hz' ((neighbors_mem ..).1 ((Mint.centered J.halo B B hz j Y T' R' hy).2 hz''))))
    have hf : P.low.cut z∈ (neighbors r x).image P.low.cut:= by rw [show (neighbors r x).image P.low.cut=_ from h𝒩]; apply (mem_filter.mp hi).2; rw [← h,hN.2]; exact mem_image_of_mem _ hz''
    obtain ⟨j,hj,hp⟩:=mem_image.mp hf
    have he:j∈neighbors (r+Mint.width J.halo B B) x:=(neighbors_mem ..).2 (((neighbors_mem ..).1 hj).trans (Nat.le_add_right ..))
    exact (show j=z from Meadow.garden hC x hc he hc' hp) ▸ hj
omit C' c' ht hc
include C' c' ht hc
lemma frigid : ∃ V: Warp (S':=stepped Q h) («S»:=stepped Q H) (∅:Finset ι) (∅:Finset δ), Folding hC he C' c' X Y₁ y Z' D'' ∅ ∅ x r n V:= by
    obtain ⟨hP,hV⟩:= snack hC he C' c' ht x r n hc; refine ⟨⟨pF, Equiv.equivOfIsEmpty ..,(L').low.cut⟩, ?_⟩
    refine ⟨?_,hV,rfl,fun i=>isEmptyElim i,fun i=> isEmptyElim i,fun i=>isEmptyElim i,?_⟩
    · simpa only [BoxOf.hub,image_empty,union_empty] using! hP
    intro i hi; obtain ⟨k,rfl⟩:= Timbre.knock _ _ i (mem_filter.mp hi).1; exact Or.inl ⟨k,rfl,pile .., ((chants C' n k).1 (mem_filter.mp hi).1).2⟩
end YM.RemainderComparison.Timbre
