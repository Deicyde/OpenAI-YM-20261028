import YM.UVExtension.Wren.Legs
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Wren
open Filter Function Metric Set RG Lattice Pressure Wilson Precision Exterior Push.AbsoluteSums Finset ConnectedActivityE6
open Push Bloch Next.Fluctuations Blaze March Channel SliceRows Work.E03 Work.F03 Reward Laurent Tree
open Push SectorMeasure
open Pressure.Stores Pressure.Tube Scroll
open Progress.StationaryScenes Green Control Window Census Pulse Itinerary Coat Poll Pond AnalyticBridge.RelativeLogdet
open Blaze.Frond Steady
open scoped BigOperators Topology InnerProductSpace ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n c f L :Side}{S:StepData c f} {ι α β κ:Type}{v:Filter ι} {P:BudgetPoint}
variable {qq: Filter κ} {T:ι→Tube G S} {w:ℝ} {X:Teller G}
    {Q: ConnectedActivityE6.Target G X} {U:Target.Order G w} {R:ι→ Rep G f}
    {s δ q η r W C B V f' a g u D' ψ Y ζ:ℝ} {k l:ℕ} {χ:Chi}
open Matrix MeasureTheory WithLp Shield
open Span Oriented Vine PhysicalNext.Repeat PhysicalNext.Repeat.Match PhysicalNext.Repeat.Greenbelt Wick
open Polar Silica Shield Score Flux Matter Ursell Gas Trees Multiple Refrain

-- Captain leases come together with Score width for all L large and at any calendar.
-- restored K. Grammar exact; use no cut beyond duct yet.
namespace Sheets
lemma tunes (S:Finset κ)(g:κ→ι→α→ℝ)(h:∀ i∈S,Tune v (g i)): Tune v (fun n x=> ∏ i∈S,g i n x) := by
    induction S using Finset.induction with
    | empty => simp only [Finset.prod_empty]; exact Tune.constant (fun _=>1) 1 tendsto_const_nhds
    | insert i s hi hP=> simp_rw [prod_insert hi]; exact (h i (mem_insert_self ..)).mul (hP fun i hi=> h _ (mem_insert_of_mem hi))
lemma boil (R:ι→ κ→ α→ℝ)(h:Transit v R): Transit v (fun n j X=> manyW (fun z=> R n z X) j):=by
    obtain ⟨a,ha,hR⟩:=h.rain; obtain ⟨r,hr⟩:=ha.books; refine ⟨⟨_,ha.repetitions,(hr.and hR).mono fun n hn x V=>?_⟩,fun i=> ?_⟩
    · unfold manyW; rw [norm_prod]; refine Finset.prod_le_prod (fun _ _=>norm_nonneg _) fun i _=> ?_; rw [norm_div,norm_pow]; rw [Real.norm_of_nonneg (by positivity : 0 ≤ (↑((x.2 i+1).factorial):ℝ))]; exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hn.2 _ _) _) (by positivity)
    apply tunes; intro j hj; exact (h.meters _).cont (F:=fun x=> x^(i.2 j+1)/(↑((i.2 j+1).factorial):ℝ)) (by fun_prop)
end Sheets
namespace Choir
variable {H:∀ i:ι,Cash w s q L Q U C (T i) (R i)} (p:Choir v T H k χ)(h:StableR v R)
open Badge Song Strata Gala Concert Graph
variable (j:ι)(P:BudgetPoint)(hp:P.threshold=temp s)(hu:P.order ≤ k)
variable [NeBot v][v.IsCountablyGenerated]

def candid n (m:(H j).Chainbook):= leaf _ _ (p.stirs h j n) m
def lilies n m (V:Config G c):= (H n).smilesPool χ V (p.candid h j n m)
lemma autumn (n m V): lilies p h j n m V=
    if (H j).Fresh m ∧ Ac.Spark (H j).bookFoot m.1∧ (H j).statesPool V m then manyW (fun i=>spritz p h j n i V) m else 0:=by
    let z:= p.candid h j n m --
    obtain ⟨hx,hK,hL,hq⟩ := panels (p.stirs h j n) m
    unfold lilies Cash.smilesPool Cash.statesPool candid; rw [hx,hK, ← hL, ← hq]; split
    · exact (Match.cashes (Badge.tongs _ _ (p.stirs h j n)) (fun i=> p.spritz h j n i V) _ (fun i=> rfl) m).symm
    rfl
include hp hu
lemma numeric : Transit v (p.lilies h j):= by
    let f n i (x:Config G c):= (p.spritz h j n i x); let Q(m:(H j).Chainbook) (V:Config G c): Prop:= (H j).Fresh m ∧ Ac.Spark (H j).bookFoot m.1∧ (H j).statesPool V m
    refine ((Sheets.boil f (splashes p h j _ (fun i=> Beam.see (H j) i) P hp hu)).masks Q).fade (Eventually.of_forall fun i m=> funext fun V=>?_)
    rw [autumn]

omit hp hu
-- using SELF when base cash= guide. Any X is certified having units=...

def helm (i:ι): Match.Alliance (H i) (H i) 1 0 := staple rfl rfl rfl
-- tongs need leafSelf argument
lemma tow (i:ι)(m:(H i).Chainbook): (helm (H:=H) i).tongs m=m := leaf_self (H i).unionP m
include h
lemma dues (n:ι)(i:Leaf (H j))(V:Config G c): fuse (H n) (helm (H:=H) n) χ (Badge.numa (p.stirs h j n) (.inl i)) V=p.lilies h j n i.val V:=by
    let t:= Badge.leafO (p.stirs h j n) i; exact congr_arg ((H n).smilesPool χ V) (tow (H:=H) n t.val)
def toxin (n:ι)(i:Annual (H j)) (V:Config G c):= fuse (H n) (helm (H:=H) n) χ (Badge.numa (p.stirs h j n) i) V
include hp hu
lemma memories :Transit v (p.toxin h j):=by
    let f n (i:Leaf (H j)) V:= lilies p h j n i.val V; let g (n:ι)(i:Blank (c:=c)) (V:Config G c):= (0:ℝ)
    refine (((p.numeric h j P hp hu).many (fun i:Leaf (H j)=> i.val) Subtype.val_injective (fun i (x:Config G c)=> x)).merge (show Transit v g from Transit.zero)).fade (Eventually.of_forall ?_)
    intro n; exact Sum.rec (motive:=fun i:Annual (H j)=> Sum.elim (f n) (g n) i= toxin p h j n i) (fun i=> Eq.symm (funext fun V=> dues p h j n i V)) (fun i=> rfl)
include p j
lemma stars (d:ι→ℝ): Transit v (fun n i V=> (plusone (H n) (helm (H:=H) n) χ (d n)).hardRead i V) :=by
    apply ((memories p h j P hp hu).many (badge (H j)) (badge _).injective (fun _ (x:Config G c)=>x)).fade; filter_upwards with n i; funext V
    exact Eq.symm (congr_arg (fun l: Annual (H n)=> fuse (H n) (helm (H:=H) n) χ l V) (seats (p.stirs h j n) i))
end Choir
end YM.UVExtension.Wren
#print axioms YM.UVExtension.Wren.Choir.stars
