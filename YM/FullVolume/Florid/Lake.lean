import YM.FullVolume.Florid.Mast
import YM.FullVolume.Florid.Tend
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Empire.Imago
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider Reserves Brush Metric Foramen Gate Tablet
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat PhysicalNext.Repeat.Alabaster FullVolume.Ray Daisy Lotus
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G} {W : ℝ}
variable {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W} {R : RG.Rep G f}
    {x₀ μ C:ℝ} {H : Cash W x₀ μ L Q o C T R}
    {v s t b δ A n B : ℝ} {j k : ℕ}
variable {F : Tree.Forest S.ratio} {i η r q u d L' A' f':ℝ} {K:ℕ} {χ:Chi}
open Lyre Jams
set_option quotPrecheck false
variable {U:Tune H v δ} (M:Lyre U j u d r A' χ A b L' K)
open Merge Tickets Merge.Palette Lyre Tune
namespace Crew
-- authentic epochs.affine Camera geometry. φ held input hats all.FULL.Reached.
variable {A:Type}[Fintype A](V:A→Mill U)
open Daisy PhysicalNext.Repeat.Greenbelt PhysicalNext.Repeat.Jams Ovens
variable (p:Tickets (sign (faces V) S))
local notation "V₁"=> Merge.Palette.team (faces V) p
local notation "Λ"=>U.pole
local notation "T₀"=> radiusB x₀
local notation "Q'" => Empire.stella Q
variable {ν α:ℝ} {s:Lyre.Signal 0} (hc:Clear Q L μ ν x₀ v s)(hr: Lyre.Clarity H 0 C δ ν)(hσ:Margin G L x₀ α δ)(hv:2≤v)
variable (X:Coat T F)(he:X.x=x₀)(ht:X.width=o.K)
variable (i:Molecule S)
local notation "f₀"=> U.plainP s ν
local notation "f₁"=> U.totalP s ν
local notation "d" => pleas V p α ν s i
variable (Cy:A→ℝ)(hh:∀ i,0≤Cy i)
local notation "A₀"=>accountK V Cy s
open Merge Switch FullVolume.Ray.Weigh
open Gas Ursell Trees Multiple Letter OmitClusters
set_option quotPrecheck false
abbrev stock (χ:Chi) (x:Config G c) (l:ℝ) (b:Finset A) (t:sun)(i:Molecule S):=Palette.vote (facesT V t) (U.beams t (U.lay t.property)) χ Cy i x l b
def scales (x: Config G c) (χ:Chi) (t:sun)(p:Tickets (sign (faces V) S)) (i:Molecule S) := Palette.act (facesT V t) (U.beams t (U.lay t.property)) χ x i (shift V t p)
lemma scape (x:Config G c)(t:sun)(p:Tickets (sign (faces V) S)) (b:Finset A)(i:Molecule S)(l:ℝ): (∏ j∈(Crew.shift V t p).val, Palette.ways Cy l b j)* scales V x χ t p i=Switch.click p.val ((∏ j∈p.val,Cy j) * tea V p χ x t i) l b:=by
   rw [amplitudes];change Switch.click p.val (∏ j∈p.val,Cy j) l b * tea V p χ x t i=_; unfold Switch.click; split_ifs<;>ring
lemma colorK (χ:Chi)(P: Config G c)(k:Molecule S) (x:sun)(t:ℝ)(b:Finset A) : stock V Cy χ P t b x k=∑ p : Tickets (sign (faces V) S),Switch.click p.val ((∏ j∈p.val,Cy j)*tea V p χ P x k) t b:=by
    unfold stock Palette.vote Palette.color; rw [← Equiv.sum_comp (Crew.shift V x)]; exact Finset.sum_congr rfl fun i _=> Crew.scape V _ P x _ b k t
include V hh hc hr hv hσ
variable (χ)
lemma harbor (l:ℕ)(hL:l ≤ Cash.numP i): Strung (fun t:sun=>fun U x b=> stock V Cy χ U x b t i) (v/2) (laude V Cy l α ν s i):=by
   let F p(t:sun) (u:Config G c):= (∏ j∈(p:Tickets (sign (faces V) S)).val,Cy j)*tea V p χ u t i
   let g p:=fun t:sun=> fun u:Config G c=> Switch.click (p: Tickets (sign (faces V) S)).val (F p t u); let a p:= (∏ j∈(p: Tickets (sign (faces V) S)).val,Cy j)* salves V i l p α ν s
   have hx(p): Strung (g p) (v/2) (a p):=by
      have ht:0≤ ∏ j∈(p:Tickets (sign (faces V) S)).val,Cy j:=prod_nonneg (fun i _=>hh i); refine Strung.radius (by linarith) (mul_nonneg ht (silver ..)) (fun j=>?_) _
      have h:= (costsK V p hc hr hσ hv i l hL χ j).scale (∏ j∈p.val,Cy j); rw [Real.norm_of_nonneg ht] at h; exact h
   have he: (fun t:sun=>fun U x b=> stock V Cy χ U x b t i)=∑ i,g i:=by funext t U x b; rw [colorK]; simp only [Finset.sum_apply];rfl
   rw [he];apply Strung.assembly _ g a (by linarith) (fun i _=>hx i)
local notation "Ax" => fun i=> laude V Cy 0 α ν s (i:H.ThinP).val
local notation "Ay" => fun i=> laude V Cy 1 α ν s (i:H.ThickP).val
-- canonical amber over ANY aligned shots (same recipe); no dependent conv headaches.
local notation "Pp" => stock V Cy χ
abbrev songK (t:sun)(x:Config G c)(q:H.fragrances)(y:ℝ)(z:Finset A):= H.trainedMill (Pp x y z t) q
abbrev grading (Cy:A→ℝ) (α ν:ℝ)(s:Lyre.Signal 0) (i:H.fragrances):= Ursell.clusters H.seam (fun i=> laude V Cy 0 α ν s i.val) i.2
omit hh hc hr hv hσ
lemma operates {t:sun}(P: Config G c)(Y:Cash W x₀ μ L Q o C T (U.notes t.val))(D:PhysicalNext.Repeat.Match.Alliance H Y 1 0)(he:D.units=Equiv.refl _)(p:H.fragrances)(x:ℝ)(y: Finset A): songK χ V Cy t P p x y=Y.trainedMill (fun i=> vote (facesT V t) Y χ Cy i P x y) (D.furrow p):=by
    refine Match.sale _ _ _ D.sec (fun i=>?_) _; have hx : (D.bearing i).val=i.val:=(show D.units i.val=i.val from (by rw [he]; rfl)); change _=vote (facesT V t) Y χ Cy (D.bearing i).val P x y; rw [hx]; rfl
include V hh hc hr hv hσ
lemma columnK (x:H.fragrances) : Strung (fun t u=>songK χ V Cy t u x) (v/2) (grading V Cy α ν s x):=by
   let z:= (x.1+1).factorial; let a:=coefficient H.seam x.2/(z:ℝ); let f i(t:sun)(U:Config G c)u b:=Pp U u b t (x.snd i).val
   have he: (fun t (u:Config G c)=> songK χ V Cy t u x)= a • (∏ i,f i):=by
     funext t U r b; simp only [Pi.smul_apply,Finset.prod_apply, smul_eq_mul]; unfold songK Cash.trainedMill Gas.term a;change coefficient H.seam x.snd*(∏ i,f i t U r b)/(z:ℝ)= _; ring
   rw [he]; have hv := Strung.winds Finset.univ f _ (show 1≤v/2 by linarith) (fun i _=> harbor χ V hc hr hσ hv (x.2 i).val Cy hh _ (Nat.zero_le _)); apply (hv.train a).tame; rw [Real.norm_eq_abs]; unfold grading clusters a; rw [abs_div, abs_of_pos (show 0<(z:ℝ) by positivity)];apply le_of_eq; unfold z; ring
-- Scent.Final ledger supp -> trophy flags
abbrev boon (x:H.Chapter)(t:sun)(u:Config G c) (y:ℝ)(v:Finset A) := H.cologneMill (Pp u y v t) x
abbrev spine (t:sun)(x:H.Chainbook)(U:Config G c)(p:ℝ)(q:Finset A):= H.smilesMill U (Pp U p q t) x
abbrev price_ch (Cy:A→ℝ)(α ν:ℝ)(s:Lyre.Signal 0):= grade H.seam (fun i=> laude V Cy 0 α ν s i.val) (fun i : H.ThickP=> laude V Cy 1 α ν s i.val)
lemma roses (x:H.Chapter):Strung (boon χ V Cy x) (v/2) (price_ch V Cy α ν s x):=by
    rcases x with i|i; · exact harbor χ V hc hr hσ hv i.val Cy hh 1 (Cash.forced_cost i.val i.2.2)
    let F(t:sun)(u:Config G c):= Crew.songK χ V Cy t u i
    have h:= (columnK χ V hc hr hσ hv Cy hh i).train (-1); rw [norm_neg,norm_one,one_mul] at h
    rw [show boon χ V Cy (Sum.inr i)=(-1:ℝ) • F from ?_];exact h
    ext t u x b; change -F t u x b=-1* F t u x b; ring
abbrev tokens (Cy:A→ℝ)(α ν:ℝ) (s:Lyre.Signal 0) (i:H.Chainbook):= if H.Fresh i∧ Ac.Spark H.bookFoot i.1 then manyW (price_ch V Cy α ν s) i else 0
lemma bluff (x:H.Chainbook): Strung (fun t=> spine χ V Cy t x) (v/2) (tokens V Cy α ν s x):=by
    have hp: 1≤ v/2:=by linarith
    let P:= Crew.price_ch V Cy α ν s; let n(i:↥x.1):=x.2 i+1; let e(i:↥x.1):ℝ:=((n i).factorial:ℝ)⁻¹; let f(i:↥x.1):= e i • ((boon χ V Cy i.val)^(n i)); let g:= ∏ i,f i
    unfold tokens; split
    next hx=>
       have ht: (fun t=> spine χ V Cy t x) = fun t U=> if H.statesPool U x then g t U else 0:=by
           funext t U y q; unfold spine Cash.smilesMill;by_cases he: H.statesPool U x;swap;· rw [if_neg he,if_neg (fun h=> he h.2.2)];rfl
           rw [if_pos he,if_pos ⟨hx.1,hx.2,he⟩]; unfold g; simp only [Finset.prod_apply]
           apply prod_congr rfl; intro i _; change (Crew.boon χ V Cy i.val t U y q)^(n i)/(n i).factorial=e i*(Crew.boon χ V Cy i.val t U y q)^(n i); unfold e; ring
       rw [ht]; apply Strung.cloud; unfold manyW;apply Strung.winds _ f _ hp; intro i _; refine ((roses χ V hc hr hσ hv Cy hh _).rolls (n i)|>.train (e i)).tame (le_of_eq ?_); rw [Real.norm_of_nonneg (show 0≤e i from (by unfold e; positivity))]; unfold e n; ring
    next hx=>
    suffices ht:(fun t=> spine χ V Cy t x)=0 by rw [ht]; exact Strung.none hp
    funext t u i b; exact if_neg (fun h=> hx ⟨h.1,h.2.1⟩)
omit hh hc hr hv hσ
lemma cabin {t:sun}(P: Config G c)(Y:Cash W x₀ μ L Q o C T (U.notes t.val))(D:PhysicalNext.Repeat.Match.Alliance H Y 1 0)(he:D.units=Equiv.refl _)(p:H.Chainbook)(x:ℝ)(y: Finset A): Crew.spine χ V Cy t p P x y= Y.smilesMill P (fun i=> vote (facesT V t) Y χ Cy i P x y) (D.tongs p):=by
    unfold spine Cash.smilesMill; refine if_congr (and_congr (D.sap _) (and_congr (D.splint _) ?_)) (Match.cashes _ _ _ (fun i=> ?_) _) rfl
    · have he:pull (1:Signed) (0:Site c) P=P:= pull_id P; have hx:= D.festoon P p; rwa [he] at hx
    rcases i with i|i; · exact congr_arg (fun p=> vote (facesT V t) Y χ Cy p P x y) (show i.val=D.units i.val from (by rw [he]; rfl))
    exact congr_arg Neg.neg (operates χ V Cy P Y D he i x y)
end Crew
end YM.ConnectedActivityE6.Empire.Imago
