import YM.MergeProof.Limb
import YM.RemainderComparison.Lyric.Cadenza
import YM.RemainderComparison.Mosaic.Words

/-!
# Polished RECON data

One lemma before limits. Explicit signed polynomial retained.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Mosaic
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι : Type}
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R)(H:Cash W x μ L Q o C T R) {q A B b e u v d L':ℝ}{j n k s J:ℕ}(χ:Chi)
open Lyric
variable (N:Captain H j q d v u A b r B e n χ)
open Verse
lemma exhibit {α d:Type}(p:Finset α)(u:α→Multiset d)(r:d→ℝ): ((∑ i∈p,u i).map r).prod=∏ i∈p,((u i).map r).prod:=by
   induction p using Finset.induction_on with
   | empty=>simp
   | @insert i p hi ih=>rw [Finset.sum_insert hi,Finset.prod_insert hi,Multiset.map_add,Multiset.prod_add,ih]
lemma holds {α d:Type}(p:Finset α)(u:α→Multiset d)(i:d) : i∈ (∑ j∈p,u j)↔∃ j∈p,i∈u j:=by
   induction p using Finset.induction_on with
   | empty=>simp
   | @insert j p hp ih=>simp [Finset.sum_insert hp, ih]

-- Retains full real evaluation including ALL masked tests
-- Source-specific formal encoding in ink (owner adapts precisely), real survey.
-- books.vignette

def raw (p:Drums M S): Verse ι (Config G f):= ⟨p.val.val,(team M p).cicada⟩

def tile (p:Molecule S)(i:Drums M S):Verse ι (Config G c):= ⟨i.val.val,fun U=> act M H χ U p i⟩

def etude (p:H.fragrances)(w:Syllable M H p): Verse ι (Config G c):=
  ⟨∑ i,(tile M H χ (p.2 i).val (w i)).letters,string M H χ p w⟩

def jewel (p:H.fragrances)(w:Syllable M H p):Verse ι (Config G c):=
  {(etude M H χ p w) with utter:= cut M H χ p w}
-- K deformation costs keep all rails
abbrev Stone (z:H.Chapter) := (Sum.rec (motive:=fun _=>Type) (fun _=>Drums M S) (fun s=>Syllable M H s) z)

noncomputable instance stage [Fintype ι](z:H.Chapter):Fintype (Stone M H z):= by cases z with
  | inl s=> exact inferInstanceAs (Fintype (Drums M S))
  | inr s=> exact inferInstanceAs (Fintype (Syllable M H s))
noncomputable instance seat [Countable ι](z:H.Chapter):Countable (Stone M H z):=by cases z with
  | inl s=> exact inferInstanceAs (Countable (Drums M S))
  | inr s=> exact inferInstanceAs (Countable (Syllable M H s))

def panel : (p:H.Chapter)→Stone M H p→ Verse ι (Config G c)
 | .inl p,j => tile M H χ p.val j
 | .inr z,i => {(jewel M H χ z i) with utter:=-cut M H χ z i}

-- prefer structured Π Π for decompositions
abbrev Slots (p:H.Chainbook)(j:↥p.fst):= Fin (p.snd j+1)
abbrev Scene (p:H.Chainbook):= (j:↥p.fst)→ Slots H p j → Stone M H j.val

local notation "B₀" => tile M H χ
local notation "E₀" => etude M H χ
local notation "A₀" => panel M H χ
local notation "L₀" => jewel M H χ

def sealing (i:H.Chainbook) (V : Config G c):= H.Fresh i ∧ Ac.Spark H.bookFoot i.1 ∧ H.statesPool V i

def parade (p:H.Chainbook) (w:Scene M H p):Verse ι (Config G c):=
  ⟨∑ i, ∑ j:Slots H p i,(A₀ i.val (w i j)).letters, fun V=> if sealing H p V then ∏ i,(∏ j:Slots H p i,(A₀ i.val (w i j)).utter V)/(↑((p.snd i+1).factorial):ℝ) else 0⟩
local notation "P₀" => parade M H χ

variable (l:ι→ℝ)
lemma pieces (p:H.fragrances)(w:Syllable M H p) : (E₀ p w).stock l=invests M H p w l:=by unfold Verse.stock etude; rw [exhibit]; rfl
include N
lemma embarks (p:H.fragrances)(w:Syllable M H p)(U:Config G c): (L₀ p w).utter U = cadence H p * ∏ i,(B₀ (p.2 i).val (w i)).utter U:= (scripted M H χ p w N U).symm
lemma stencil (p:H.fragrances)(w:Syllable M H p)(U:Config G c) : (L₀ p w).emit l U=cadence H p*∏ i,(B₀ (p.2 i).val (w i)).emit l U:=by
   unfold Verse.emit; rw [show (L₀ p w).stock l= _ from pieces M H χ l p w, prod_mul_distrib,embarks M H χ N]; exact mul_left_comm ..

omit N in
lemma wheel (p:H.Chainbook)(w:Scene M H p)(U:Config G c): (P₀ p w).emit l U= if sealing H p U then ∏ i,(∏ j,(A₀ i.val (w i j)).emit l U) / (↑((p.snd i+1).factorial):ℝ) else 0:=by
   unfold Verse.emit Verse.stock parade; dsimp only; rw [mul_ite,mul_zero]; split; next=>
      simp_rw [exhibit,prod_mul_distrib]
      rw [← prod_mul_distrib]; apply prod_congr rfl; intro i _; rw [mul_div_assoc]
   rfl

variable [Fintype ι]
lemma canon (p:H.fragrances)(U:Config G c): H.trainedMill (Palette.color M H χ U l) p=∑ w:Syllable M H p,(L₀ p w).emit l U:=by
   rw [Lyric.chorus M H χ p N]; refine sum_congr rfl (fun i _=>?_); exact congr_arg (·*_ ) (pieces M H χ l p i).symm
lemma portrays (p:H.Chapter)(U:Config G c): H.cologneMill (Palette.color M H χ U l) p= ∑ i:Stone M H p,(A₀ p i).emit l U:=by
   rcases p with p|p
   · rfl
   rw [show H.cologneMill _ _=-H.trainedMill (Palette.color M H χ U l) p from rfl,canon M H χ N,← sum_neg_distrib]; refine sum_congr rfl fun i _=> (mul_neg ..).symm
lemma voyage (p:H.Chainbook)(U:Config G c): H.smilesMill U (Palette.color M H χ U l) p=∑ w:Scene M H p,(P₀ p w).emit l U:=by
   unfold Cash.smilesMill;simp_rw [wheel]; split
   next h =>
    have he:sealing H p U:=h
    unfold Multiple.manyW; simp_rw [if_pos he, portrays M H χ N]
    let f (i:↥p.fst) s:= (A₀ i.val s).emit l U
    let g (i:↥p.fst) (a: Slots H p i → Stone M H i.val):=(∏ j,f i (a j))/(↑((p.snd i+1).factorial):ℝ)
    have hg (i:↥p.fst) : (∑ s, f i s)^(p.snd i+1)/(↑((p.snd i+1).factorial):ℝ)= ∑ a,g i a:=by
       rw [show (∑ s,f i s)^(p.snd i+1) = ∏ _ : Slots H p i,∑ s,f i s from (by simp [Slots]), Fintype.prod_sum (fun (_:Slots H p i) s=>f i s),sum_div]
    change (∏ i:↥p.fst, (∑ s,f i s)^(p.snd i+1)/(↑((p.snd i+1).factorial):ℝ))= _; simp_rw [hg]; exact Fintype.prod_sum g
   next h=> symm; exact sum_eq_zero (fun _ _=> if_neg (show ¬sealing H p U from h))
end YM.RemainderComparison.Mosaic
