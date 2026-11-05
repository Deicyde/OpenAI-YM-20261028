import YM.UVExtension.Wren.Rhapsody
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
-- K contents. cologne read, any V. Output labels on Leaf, HEq. Series of powers in ℓ¹, tight.
namespace Choir
variable {H:∀ i:ι,Cash w s q L Q U C (T i) (R i)} (p:Choir v T H k χ)(h:StableR v R)
open Badge Song Strata Gala Concert Graph
variable (j:ι)(D:(H j).fragrances→ RegularAddress c) (hd:∀ m,(D m).support=perf (H j) m) (P:BudgetPoint)(hp:P.threshold=temp s)(hu:P.order ≤ k)
variable [NeBot v] [v.IsCountablyGenerated]

def stings (i:ι)(b:Molecule S)(V:Config G c):= (H i).spawn χ V b
-- with prices OR p purchase, output
include p h j
lemma stunners :Transit v (stings (H:=H) (χ:=χ)):=by
    obtain ⟨B,hB⟩:= Polish.delegates p.laws h (p.sails j).position.le
    letI : Nonempty (Tree.Forest S.ratio):=Tree.select S.ratio S.patch.odd_side
    let w:=(Fintype.card (Greenbelt.Reserve S):ℝ); have hw: 0<w:= by unfold w; positivity
    let g i b V (v:Greenbelt.Reserve S) := (H i).emerging (prism (T i) s χ U.K V (Greenbelt.allot v)) b
    have hA : ∀ᶠ n in v,∀ j V (z:Greenbelt.Reserve S), ‖g n j V z‖≤ B n j:= hB.laws.mono fun i hi j V z=> (hi j _ _ rfl rfl rfl).1
    obtain ⟨r,hr⟩:=hB.swift.books; refine ⟨⟨B,hB.swift,?_⟩,fun j'=> ?_⟩
    · filter_upwards [hA] with i hi j V; change ‖w⁻¹*∑ k,g i j V k‖≤_; rw [norm_mul, Real.norm_of_nonneg (by positivity : 0≤ w⁻¹)]; apply (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (sum_le_sum (g:=fun _=> B i j) (fun x _=> hi j V x))) (inv_nonneg.mpr hw.le)).trans_eq; rw [sum_const,nsmul_eq_mul,card_univ,inv_mul_cancel_left₀ hw.ne' (B i j)]
    have he(x): Tune v (fun i V=> g i j' V x):= by
       apply Tune.spans ⟨_,(hA.and hr).mono (fun n h V=> (h.1 _ V x).trans (budget_single h.2 _))⟩; intro Y
       obtain ⟨B,Z,H⟩:= Polish.entrance p.laws (p.sails j).position.le h
       let K:=pathD Y x; -- trans syntax
       refine (Polish.traversed p.laws wig K h (p.sails j).position.le B Z H j').shimmy ?_
       filter_upwards with i; funext b; cases b <;> rfl
    have hz := Tune.term Finset.univ (fun x i V=> g i j' V x) (fun i _=>he i)
    exact (Tune.constant (fun _=> w⁻¹) w⁻¹ tendsto_const_nhds).mul hz
include hp hu hd
lemma silhouette : Transit v (fun n i (U:Config G c)=> - (H n).trainedPool χ U (p.casts h j n i)):=by
   let y x:= (D x).support; let w m n U:= masked P.threshold (y m) (rings p h j n m) U
   obtain ⟨q,hq,ht⟩:=p.harvest h j D hd P hp hu
   have he(i): Tune v (fun n U=> -(w i n U)):=by
       let Y:= (sonnets p h j D hd P hp hu).invests.meters i
       let p' (U:Config G c): Prop:= Healthy P.threshold (y i) U
       obtain ⟨⟨r,hr⟩,hh⟩:=Y; refine ⟨⟨max r 0,?_⟩,?_⟩
       · filter_upwards [hr] with n hi U; rw [norm_neg]; unfold w; by_cases hz:p' U
         · rw [masked_eq _ _ _ _ hz]; exact (hi (⟨U,hz,[],by simp,by simp⟩)).trans (le_max_left ..)
         rw [masked_ne _ _ _ _ hz,norm_zero]; exact le_max_right ..
       intro ε hε; filter_upwards [hh ε hε] with n hi X; rw [neg_sub_neg,norm_sub_rev]; unfold w; by_cases hx:p' X
       · rw [masked_eq _ _ _ _ hx, masked_eq _ _ _ _ hx]; exact hi ⟨X,hx,[],by simp,by simp⟩
       rw [masked_ne _ _ _ _ hx,masked_ne _ _ _ _ hx,sub_zero,norm_zero]; exact hε.le
   have hk m n X:(H n).trainedPool χ X (casts p h j n m)=w m n X:=by
       have hg:= congr_fun ((p.sails n).gloryBudget (casts p h j n m) P hp hu).1 X; apply Eq.trans hg; unfold w y; rw [hd, ←p.landscapes h j m n]; rfl -- rewrite
   obtain ⟨r,hr⟩:=hq.books; simp_rw [hk]; refine ⟨⟨q,hq,?_⟩,he⟩
   filter_upwards [ht,hr] with n hn hx j U; rw [norm_neg]; unfold w; by_cases hz:Healthy P.threshold (y j) U
   · rw [masked_eq _ _ _ _ hz]; exact hn j ⟨U,hz,[],by simp,by simp⟩
   rw [masked_ne _ _ _ _ hz,norm_zero]; exact hx.1 _

omit hp hu hd
omit h p j in
private lemma comm(i: Molecule S→Support c)(m: Molecule S→Support c)(u:i=m)(p): (dried _ _ u p).val=p.val:=rfl -- omit p etc

def atlas (n:ι)(k:(H j).Chapter):= tongs _ _ (p.stirs h j n) k
def spritz (n:ι)(k:(H j).Chapter) (V:Config G c):= (H n).colognePool χ V (p.atlas h j n k)
def fog (n:ι)(k:(H j).ThickP) (V:Config G c):= (H n).spawn χ V k.val

private lemma frosted (n:ι)(k:(H j).ThickP)(V:Config G c): fog (H:=H) j n k V (χ:=χ)= (p.spritz h j n (.inl k) V):=by
   have hT: (dried _ _ (p.stirs h j n) k).val=k.val:= comm _ _ (p.stirs h j n) k
   exact congr_arg ((H n).spawn χ V) hT.symm
include hd hp hu
lemma splashes : Transit v (p.spritz h j):=by
   let f n (m:(H j).ThickP) V:= fog (H:=H) (χ:=χ) j n m V ; let g n (m:(H j).fragrances) (U:Config G c):= - (H n).trainedPool χ U (p.casts h j n m)
   have hf : Transit v f := (p.stunners h j).many (fun x:(H j).ThickP=> x.val) Subtype.val_injective (fun _=>id)
   have ht(z:ι):∀ (i:(H j).Chapter), Sum.elim (f z) (g z) i=p.spritz h j z i:= Sum.rec (fun i=> funext (fun V=> p.frosted h j z i V)) (fun i=> rfl) -- motive
   exact (hf.merge (p.silhouette h j D hd P hp hu)).fade (Eventually.of_forall ht)
end Choir
end YM.UVExtension.Wren
#print axioms YM.UVExtension.Wren.Choir.splashes
