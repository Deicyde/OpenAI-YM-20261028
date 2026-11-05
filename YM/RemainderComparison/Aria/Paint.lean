import YM.RemainderComparison.Aria.Scores
/-! # Dual projection to coincide before exposures

 Symmetry & correspondence are not conclusions about all x in the Family.
 Require prescriber/encoder to supply compatible rosters on chosen copy layouts.
 Below folds unmasked primitive readings without assuming an estimate at
 real physical step. Uses these ONLY on eligible looks.W.Marker.A.Cap.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Aria
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter
open PhysicalNext.Repeat Deck Stellar Mint Poll Pond MeasureTheory ProbabilityTheory Greenbelt Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F L₀:Side} {P : Patch} {M D' : ℕ} {K : Teller G}
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q:KernelChoices} {hC : C.val=c.val*M} {he:2 ≤ c.val}
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {T: Tube G (stepped Q h)} {T': Tube G (stepped Q H)} {p : ℝ} {E: Forest (stepped Q h).ratio} {E':Forest (stepped Q H).ratio}
    {R:RG.Rep G f} {R':RG.Rep G F}
local notation "B" => radiusB p
variable (hC he)
variable {Z:Site C}{n:ℕ} {a W K₀ v : ℝ} {J : ConnectedActivityE6.Target G K} {o : ConnectedActivityE6.Target.Order G W}
    (C' : Cash W p a L₀ J o K₀ T' R') (c' : Cash W p a L₀ J o v T R) (hq : T'= re T)
    (ht : R'.path=R.path) (hx : R'.p=R.p) (hb:R'.beta=R.beta) (V:Molecule (stepped Q H))(U:Molecule (stepped Q h))
open Gas Ursell Trees Blaze March Lyric WickReps Creek Mosaic Merge Palette Typeface Harmonics Seedlings BoxOf
variable {ι δ:Type}{α:Type*}(X:ι→Portrait R' α) (Y₁:δ→Portrait R α)(u:α)
local notation "X₁"=>brand X u
local notation "Z₁" => brand Y₁ u
variable {I:Type}
variable (k r:ℕ) (X': Score C' I k) (Y': Score c' I k) (z:Site C)
set_option quotPrecheck false
local notation "ψ" => Score.pose C' k X'
local notation "η" => Score.pose c' k Y'
local notation "lT"=> Score.wake C' k n X'
local notation "Lt"=> Score.wake c' k n Y'
local notation "q"=> (Lace.project (h:=h) (H:=H) hC he)
local notation "Lq"=> (Lace.project (h:=h) (H:=H) hC he).low.cut
local notation "aZ" => (X'.index)
local notation "A"=> (Y'.index)
local notation "U₀" => (Score.wake C' k n X').filter fun i=> C'.supportP i⊆neighbors r z
local notation "V₀" => (Score.wake c' k n Y').filter fun i=> c'.supportP i⊆neighbors r (Lq z)
local notation "U₁" => (BoxOf.nearby C' (Timbre.trumpets C') z r n)
local notation "V₁" => (BoxOf.nearby c' (Timbre.trumpets c') (Lq z) r n)

-- lexical E authentications. Does not need tolerance.Co.Tx contact covered.Owner. Mark pins.P.W.Big Arena.
structure Wears : Prop where
   reads : X'.book= Y'.book
   inherits s i n : i∈X'.book n→ (R.activities.reg (Y'.index ((Lace.project (h:=h) (H:=H) hC he).low.cut s,i))).support=((R'.activities.reg (X'.index (s,i))).support).image (Lace.project (h:=h) (H:=H) hC he).high.cut
   paid s i n : i∈X'.book n → ∀ V:Config G f,Healthy R.p.threshold (R.activities.reg (Y'.index ((Lace.project (h:=h) (H:=H) hC he).low.cut s,i))).support V → R'.activities.E (X'.index (s,i)) ((Lace.project (h:=h) (H:=H) hC he).high.links V)=R.activities.E (Y'.index ((Lace.project (h:=h) (H:=H) hC he).low.cut s,i)) V
-- combine household
local notation "Hc"=> Score.scoreCalling C' k X'
local notation "Hf"=> Score.scoreCalling c' k Y'
def reprieve (t':Head Y) : Head S:= Function.extend (Hc) (fun i:Site C×I=> Hf ((Lq) i.1,i.2)) (Timbre.bag hC he) t'
local notation "p₀"=> reprieve hC he C' c' k X' Y'
lemma reads (s:Site C)(j:I): p₀ (Hc (s,j))= Hf ((Lq) s,j) := (Hc).injective.extend_apply ..
lemma logKey {c f:Side} (S':StepData c f)(i)(j:Music c f): Opacity.key S' i≠ Mint.disc S' j:= by
    rcases j with j|j|j|j <;> cases j <;> intro ht <;> simp [Opacity.key,Mint.disc,Mint.album,Mint.note] at ht
lemma rocks (i:Music C F): p₀ (Mint.disc (Y) i)= Mint.disc (S) (verse_down (q) i):= by
     rw [reprieve,Function.extend_apply' _ _ _ ?_]; exact Timbre.pile ..
     rintro ⟨x,hx⟩; exact Aria.logKey (Y) _ _ hx
local notation "Xq"=> Lq z
variable (hv: Wears hC he C' c' k X' Y')
variable (hc:2*(r+k+3)<c.val)
include hc hv
lemma matchUp (n:ℕ)(s:Site C)(i:I)(hS : i∈ X'.book n): c'.supportP (Hf (Lq s,i))=(C'.supportP (Hc (s,i))).image (Lq):=by
    apply Harmonics.mold (h:=h) (H:=H) hC he T T' (Wing.logKey (Y'.index (_,i))) (Wing.logKey (X'.index (s,i))) (hv.inherits s i n hS) -- replace h✝
    exact lt_of_lt_of_le (by omega : 4 < c.val) (by rw [h]; exact Nat.le_mul_of_pos_right _ P.L.pos)
lemma learns : Set.InjOn (p₀) (↑U₀) ∧ (U₀).image (p₀)= V₀:=by
    let p:=Lq
    have hF:2*(r+k)<c.val:=by omega
    have he' s i (h: Hc (s,i)∈ U₀): s∈neighbors r z:=by
        obtain ⟨x,hx,h'⟩:=mem_map.mp (mem_filter.mp h).1; have h':x=(s,i):=(Hc).injective h'; subst x; exact (mem_filter.mp h).2 ((X'.advice s i n (mem_product.mp hx).2).1)
    constructor
    · intro i hi j hj hp; obtain ⟨⟨v,kθ⟩,hv,rfl⟩:= mem_map.mp (show i∈ Score.wake C' k n X' from (mem_filter.mp hi).1) -- k shadow
      obtain ⟨⟨y,a⟩,hy,rfl⟩:= mem_map.mp ((mem_filter.mp hj).1)
      rw [reads,reads] at hp
      have he'':(p v,kθ)=(p y,a):=(Hf).injective hp
      refine congr_arg (Hc) (Prod.ext ?_ (show kθ=a from congr_arg Prod.snd he'')); exact Meadow.garden hC z (by omega : 2*r<c.val) (he' _ _ hi) (he' _ _ hj) (congr_arg Prod.fst he'') -- Hc notation k shadow.Hue
    ext i; constructor
    · intro h; obtain ⟨t',ht,rfl⟩:= mem_image.mp h; obtain ⟨⟨s,j⟩,hS,rfl⟩:=mem_map.mp ((mem_filter.mp ht).1)
      rw [reads]; have hp:= (mem_product.mp hS).2
      exact mem_filter.mpr ⟨mem_map_of_mem _ (mem_product.mpr ⟨mem_univ _,hv.reads ▸ hp⟩),show _ from (by rw [matchUp hC he C' c' k r X' Y' hv hc n _ _ hp,show neighbors r ((Lq) z)=(neighbors r z).image Lq from Deck.inclined hC r z]; exact image_subset_image (mem_filter.mp ht).2)⟩
    intro ht; obtain ⟨⟨y,a⟩,hy,rfl⟩:=mem_map.mp ((mem_filter.mp ht).1); have ha:= (mem_product.mp hy).2
    let s:= Deck.rise (Deck.divides hC) z y; have hp:Lq s=y:=dawns ..; have hx': s∈neighbors r z:= (neighbors_mem ..).2 ((Deck.climb (Deck.divides hC) z y).trans_le ((neighbors_mem ..).1 ((mem_filter.mp ht).2 (Y'.advice y a n ha|>.1))))
    refine mem_image.mpr ⟨Hc (s,a),mem_filter.mpr ⟨mem_map_of_mem _ (mem_product.mpr ⟨mem_univ _,hv.reads.symm ▸ ha⟩),?_⟩,?_⟩; swap;· rw [reads,hp]
    intro i hi; have he' : i∈neighbors (r+k) z:= (neighbors_mem ..).2 ((separation_triangle _ s _).trans (Nat.add_le_add ((neighbors_mem ..).1 hx') ((neighbors_mem ..).1 ((X'.advice s a n (hv.reads.symm ▸ ha)|>.2) hi))))
    have hL: Lq i ∈ neighbors r (p z):=by
       apply (mem_filter.mp ht).2; rw [← hp, matchUp hC he C' c' k r X' Y' hv hc n _ _ (hv.reads.symm ▸ ha)]; exact mem_image_of_mem _ hi
    have hN:= Deck.inclined hC r z
    obtain ⟨j,hj,hθ⟩:= mem_image.mp (show Lq i∈ (neighbors r z).image Lq from hN ▸ hL)
    have hz' : j∈neighbors (r+k) z:= (neighbors_mem ..).2 (((neighbors_mem ..).1 hj).trans (by omega))
    exact Meadow.garden hC z hF hz' he' hθ ▸ hj
end YM.RemainderComparison.Aria
