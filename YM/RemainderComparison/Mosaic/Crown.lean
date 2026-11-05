import YM.RemainderComparison.Mosaic.Shuttle

/-!
# Uniform forced-book pricing, before gluing duplications
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Mosaic
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling OmitClusters
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι : Type}
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R)(H:Cash W x μ L Q o C T R) {q A B b e u v d L':ℝ}{j n k s J:ℕ}(χ:Chi)
open Lyric
variable (N:Captain H j q d v u A b r B e n χ)
open Verse
local notation "B₀" => tile M H χ
local notation "E₀" => etude M H χ
local notation "A₀" => panel M H χ
local notation "L₀" => jewel M H χ
local notation "P₀" => parade M H χ

local notation "sx"=> radiusB x
variable (l:ι→ℝ)
local notation "X'" => Daisy.swing Q L μ R.beta x C
open Mixed

def bite (m:ℕ)(p:Molecule S)(i:Drums M S):ℝ:= if H.ticketsP 0 m 0 p ∧ i.reach⊆p then (∏j∈i.val,wages M l j)*∏j∈p\i.reach,H.text j else 0
local notation "bt" => bite M H l
variable (hr:∀ i,0≤ l i)
include hr
lemma venture (p:Molecule S)(m:ℕ)(hm:m ≤ Cash.numP p)(U:Config G c)(i:Drums M S):
    ‖(B₀ p i).emit l U‖ ≤ bt m p i:=by
   unfold bite; split
   next h=>
     have hz:= act_norm M H χ p i U h.2
     let c:=∏ j∈i.val,l j; have ht: 0≤ c:= prod_nonneg fun j _=>hr j
     change ‖c*_‖ ≤ _; rw [norm_mul, Real.norm_of_nonneg ht]; apply (mul_le_mul_of_nonneg_left hz ht).trans_eq
     rw [Palette.worth]; unfold c Palette.wages;rw [Finset.prod_mul_distrib,mul_assoc]
   next h=>
     letI : Nonempty (Forest S.ratio):=Tree.select S.ratio S.patch.odd_side
     by_contra hn; apply h; have hx : act M H χ U p i ≠0:= right_ne_zero_of_mul (norm_pos_iff.mp (lt_of_not_ge hn))
     obtain ⟨hv,he⟩:= present M H χ U i p (F:=Classical.ofNonempty) hx; exact ⟨⟨he.1,Nat.zero_le _,hm,H.positive_volume p⟩,hv⟩

def kronor (p:H.fragrances)(i:Syllable M H p):ℝ:= ‖cadence H p‖ * ∏ j, bt 0 (p.snd j).val (i j)
def pay : (p:H.Chapter)→Stone M H p→ℝ
 | .inl p, j => bt 1 p.val j
 | .inr p, j => kronor M H l p j

def Bank (p:H.Chainbook)(w:Scene M H p):ℝ:= if H.Fresh p∧ Ac.Spark H.bookFoot p.fst then ∏ i,(∏ j,pay M H l i.val (w i j))/(↑((p.snd i+1).factorial):ℝ) else 0
include N
lemma drinks (p:H.fragrances)(w:Syllable M H p)(U:Config G c): ‖(L₀ p w).emit l U‖ ≤ kronor M H l p w:=by
   unfold kronor; rw [stencil M H χ N l, norm_mul, norm_prod]; exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun i _=>norm_nonneg _) (fun i _=> venture M H χ l hr _ 0 (Nat.zero_le _) U _)) (norm_nonneg _)
lemma campers (p:H.Chapter)(w:Stone M H p)(U:Config G c): ‖(A₀ p w).emit l U‖ ≤ pay M H l p w:=by
   rcases p with p|p
   · exact venture M H χ l hr _ 1 (Cash.forced_cost p.val p.prop.2) U _
   have he : (A₀ (Sum.inr p) w).emit l U= -(L₀ p w).emit l U:= mul_neg ..
   rw [he,norm_neg]; exact drinks M H χ N l hr p w U
lemma camping (p:H.Chainbook)(w:Scene M H p)(U:Config G c): ‖(P₀ p w).emit l U‖ ≤ Bank M H l p w:=by
   rw [wheel]; unfold Bank; split
   next h =>
     have hh : H.Fresh p∧ Ac.Spark H.bookFoot p.1 := ⟨h.1,h.2.1⟩; rw [if_pos hh, norm_prod]; apply Finset.prod_le_prod (fun _ _=>norm_nonneg _); intro i _; rw [norm_div,norm_prod, Real.norm_of_nonneg (by positivity : 0≤(↑((p.snd i+1).factorial):ℝ))]; exact div_le_div_of_nonneg_right (Finset.prod_le_prod (fun _ _=>norm_nonneg _) (fun j _=>campers M H χ N l hr _ _ U)) (by positivity)
   next h=>
     rw [norm_zero]; split
     next h=> exact prod_nonneg (fun i _=> div_nonneg (prod_nonneg fun j _=> (norm_nonneg _).trans (campers M H χ N l hr _ _ U)) (by positivity))
     next=> exact le_rfl

-- finite sum over decorations pays first in Vote.price
variable [Fintype ι]
omit N
include χ
lemma fare_cost (p:Molecule S)(m k:ℕ)(h:m≤Cash.numP p) : ∑ i:Drums M S, bt m p i ≤ tune M H l m k p:=by
  unfold Palette.tune Mixed.selected
  by_cases hp:H.ticketsP 0 m 0 p
  · rw [if_pos (show Allowed S Q.halo sx X' H.birth (ConnectedActivityE6.lengths T R) 0 m 0 p from hp)]
    have he : (∑ i:Drums M S, bt m p i)=∏ i∈p,Palette.toll M H l i:=by
       unfold Palette.toll; rw [Tickets.expanded]; refine sum_congr rfl fun i _=> ?_; unfold bite; simp only [hp,true_and]
    have hz : ∀ i,Palette.toll M H l i= Mixed.costs S Q.halo sx (steamP S (Q.costs L μ R.beta x C)) (pitch M H l) i := by
       intro i; rcases i with i|i
       · unfold Palette.toll Tickets.extra; rw [sum_eq_zero, add_zero]; · rfl
         intro j _; exact if_neg (fun h=> by have hf:=(show .inr _ = Palette.sign M S j from Daisy.sparkPath ..).trans h; contradiction)
       unfold Palette.toll Tickets.extra Cash.text Mixed.costs Palette.pitch Tickets.extra
       dsimp only [Sum.elim]; simp_rw [← show ∀ j, (.inr (Palette.mark M (c:=c) j):Head S)=Palette.sign M S j from fun j=> Daisy.sparkPath ..]; simp only [Sum.inr.injEq]
    unfold Mixed.Price; simp_rw [← hz]; rw [← he]; apply le_mul_of_one_le_right ?_ (show 1 ≤ (1+H.shapeW p)^k from one_le_pow₀ (le_add_of_nonneg_right (H.positive_volume p)))
    exact sum_nonneg fun i _=> (norm_nonneg _).trans (venture M H χ l hr p m h (1:Config G c) i) -- include χ
  rw [if_neg (show ¬Allowed S _ _ X' _ _ _ m _ p from hp)]; exact (sum_eq_zero (fun i _=> if_neg (show ¬(H.ticketsP 0 m 0 p ∧ (i:Drums M S).reach⊆p) from fun hx=>hp hx.1))).le

set_option quotPrecheck false
local notation "p₁"=> fun i:H.ThickP=> tune M H l 1 0 i.val
variable (n)
lemma tickets (p:H.fragrances) : ∑ w:Syllable M H p, kronor M H l p w ≤ lace M H l n p:=by
   let g (j) i:= bt 0 (p.snd j).val i
   let K' j:= tune M H l 0 n ((p.2 j).val); let k:= ‖cadence H p‖
   change (∑ w:Syllable M H p,k*∏ i,g i (w i)) ≤ _
   rw [← Finset.mul_sum,← Fintype.prod_sum g,show lace M H l n p=k*∏ i,K' i from ?_]
   · exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun i _=> Finset.sum_nonneg (fun j _=>(norm_nonneg _).trans (venture M H χ l hr _ _ (Nat.zero_le _) (1:Config G c) j))) (fun i _=> fare_cost M H χ l hr _ _ n (Nat.zero_le _))) (norm_nonneg _)
   unfold lace k cadence clusters; rw [Real.norm_eq_abs,abs_div,abs_of_nonneg (by positivity:0≤(↑((p.fst+1).factorial):ℝ))]; unfold K'; ring
lemma ferries (p:H.Chapter) : ∑ w:Stone M H p, pay M H l p w ≤ grade H.seam (fun i:H.ThinP=>tune M H l 0 n i.val) p₁ p:=by
    rcases p with p|p
    · exact fare_cost M H χ l hr _ _ _ (Cash.forced_cost p.val p.prop.2)
    exact tickets M H n χ l hr p
variable {n}
include N
lemma paradise (p:H.Chainbook) : ∑ w:Scene M H p, Bank M H l p w ≤ bold M H l n p:=by
   unfold bold; split
   next h=>
    unfold Bank Multiple.manyW; simp_rw [if_pos h]; let g (i:↥p.fst)(w:Slots H p i→Stone M H i.val):=(∏ j,pay M H l i.val (w j))/(↑((p.snd i+1).factorial):ℝ)
    change (∑ w:Scene M H p, ∏ i,g i (w i)) ≤ _; rw [← Fintype.prod_sum g]
    have h₁ (i) (j):0 ≤ pay M H l i j:=(norm_nonneg _).trans (campers M H χ N l hr _ j 1)
    refine Finset.prod_le_prod (fun i _=>sum_nonneg (fun j _=> div_nonneg (prod_nonneg fun i _=>h₁ _ _) (by positivity))) (fun i _=>?_)
    unfold g; rw [← sum_div, ← Fintype.prod_sum (fun (_:Slots H p i) j=>pay M H l i.val j), Finset.prod_const,card_univ,Fintype.card_fin]
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (sum_nonneg (fun _ _=>h₁ _ _)) (ferries M H n χ l hr _) _) (by positivity)
   next h=> unfold Bank; simp_rw [if_neg h,sum_const_zero]; exact le_rfl
end YM.RemainderComparison.Mosaic
