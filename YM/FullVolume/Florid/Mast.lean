import YM.FullVolume.Florid.Hats
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
def salves (i : Molecule S)(l : ℕ)(p:Tickets (sign (faces V) S)) (α ν:ℝ)(s:Lyre.Signal 0) := if H.ticketsP 0 l 0 i ∧ p.reach⊆i then 2*pleas V p α ν s i else 0
lemma tide (t:sun)(hx:X.B=radiusB x₀): standsIn X R Q.halo i=standsIn X (U.notes t) Q.halo i:=by
    have hp:= t.property; have he:= U.seats _ (U.lay hp); unfold standsIn claimed; apply propext
    rw [hx]; refine and_congr ?_ (and_congr (U.troupe_hold t (U.lay hp) i) ?_)
    · rw [show areas R T Q.halo T₀=areas (U.notes t) T Q.halo T₀ from U.arena t (U.lay hp)]
    change _= _ ↔ _= _; have hp:= congr_fun (U.stage t (U.lay hp)) i;
    change _ ∩ H.unionP i=_ ↔ _ ∩ _=_; rw [hp]; exact Iff.rfl
variable (l:ℕ)(hl:l ≤ Cash.numP i)
lemma silver : 0≤ salves V i l p α ν s:=by unfold salves; split; exact mul_nonneg zero_le_two (coinsP V p i); rfl
include V hc hr hv hσ hl X ht he
set_option maxHeartbeats 520000 in
lemma hopesK : Scout (v/2) (phraseS fun t:sun=> (hat V p t).bloom X W o.a Q.table Q.halo i) (salves V i l p α ν s):= by
   have hT: X.B=T₀:=congr_arg _ he; have hP:1 ≤ v/2:=by linarith
   have hr'(J:S.Choices) (hg:p.reach⊆i) : Scout (v/2) (phraseS fun t:sun=> (hat V p t).tithe ((planted X i).taggedL J) (Matter.own i) W o.a Q.table Q.halo i) (2*d) := by
     refine ((ballot V p hc hr hσ ((planted X i).taggedL J) he ht (planted_valid X i) i hg _).recovery hP (by linarith)).enlarged ?_; rw [show (1-v/2/v)⁻¹=2 by field_simp; ring_nf]
   by_cases hg:p.reach⊆i; swap; · refine ((Scout.still hP (0:ℝ)).enlarged (by rw [norm_zero]; exact silver ..)).replace fun t h=>?_ ;let t':sun:=⟨t,h⟩; change 0=phraseS _ _; rw [show phraseS _ t=_ from phrased _ t']; exact ((hat V p t').bloom_off X i (by rw [shotU]; exact hg)).symm
   let f i' x:= phraseS (fun j:sun=> Team.tithe (hat V p j) ((planted X i).taggedL i') (Matter.own i) W o.a Q.table Q.halo i) x
   by_cases hK: standsIn X R Q.halo i; swap; · apply ((Scout.still hP (0:ℝ)).enlarged (by rw [norm_zero]; exact silver ..)).replace; intro t h; let t':sun:=⟨t,h⟩; change 0=phraseS _ _; rw [show phraseS _ t= _ from phrased _ t']; exact (if_neg (fun hp=>hK ((tide (U:=U) X i t' hT).symm ▸ hp))).symm
   have hS: Ac.Spark H.supportP i:= (show Ac.Spark (areas R T Q.halo (radiusB x₀)) i from hT ▸ hK.1)
   rw [salves, if_pos ⟨⟨hS,Nat.zero_le _,hl,H.positive_volume _⟩,hg⟩]; refine (likely_scout U hc hr hσ hv f (fun i=> hr' i hg)).replace fun t hh=> ?_
   let t':sun:=⟨t,hh⟩; rw [show phraseS _ t= _ from phrased _ t']; unfold Team.bloom; dsimp only; rw [if_pos (show standsIn X (U.notes t) Q.halo i from tide (U:=U) X i t' hT ▸ hK)]; apply congr_arg likely; funext i; exact phrased _ t'
omit he ht X
local notation "E"=> Tune.ports U
abbrev tea (q:Chi)(P:Config G c)(t:sun)(i:Molecule S) := (hat V p t).lotus T x₀ q o.K W o.a Q.table Q.halo P i
lemma costsK (χ : Chi)(P : Config G c): Scout (v/2) (phraseS fun s:sun=> tea V p χ P s i) (salves V i l p α ν s):=by
   letI : Nonempty (Forest S.ratio):= Tree.select S.ratio S.patch.odd_side; let f (t:sun)(q:Greenbelt.Reserve S):= Team.bloom (hat V p t) (prism T x₀ χ o.K P (Greenbelt.allot q)) W o.a Q.table Q.halo i
   exact likely_scout U hc hr hσ hv (fun q:Greenbelt.Reserve S=>phraseS (fun t=> f t q)) (fun q=> hopesK V p hc hr hσ hv _ rfl rfl i l hl)
-- Budget aggregation for hot. expose ALL Packs. single oracle pays via salves * WHEN rootHalo.Applier.PPPPδ. sign.
omit V hc hr hv hσ hl
variable (Cy:A→ℝ)(hh:∀ i,0≤Cy i)
local notation "Fz"=>U.receipt s (H.alarms * topStorm S.patch)
abbrev accountK (s:Lyre.Signal 0) := U.receipt s (H.alarms * topStorm S.patch) + Tickets.extra (Palette.mark (c:=c) (faces V)) (Palette.wages (faces V) Cy)
local notation "A₀"=>accountK V Cy s
def laude (V:A→Mill U) (Cy:A→ℝ) (a:ℕ)(α ν:ℝ)(s:Lyre.Signal 0)(i:Molecule S):= ∑ p:Tickets (sign (faces V) S), (∏ j∈p.val,Cy j) * salves V i a p α ν s
variable (Y: Mixed.Accounts S Q.halo (radiusB x₀) (Daisy.swing (stella Q) L μ R.beta x₀ ν) H.birth (accountK V Cy s) (ConnectedActivityE6.lengths T R) (steamP S ((Empire.stella Q).costs L μ R.beta x₀ ν)))
variable (hA:(Daisy.swing (stella Q) L μ R.beta x₀ ν).Buy S.patch.L Q.halo (radiusB x₀))
include V hh
lemma crestK : 0≤ laude V Cy l α ν s i:= Finset.sum_nonneg fun p _=> mul_nonneg (prod_nonneg fun j _=> hh _) (silver ..)
include Y hA
lemma foes (l : ℕ): Ac.Hit H.unionP (radiusB x₀) (laude V Cy l α ν s) (Q.exp-α) (2*(Daisy.swing Q' L μ 1 x₀ 0).ceiling 0 0 l 0) := by
    let Z:=sign (faces V) S; let φ:= Palette.wages (faces V) Cy; let f:= Daisy.swing (stella Q) L μ R.beta x₀ ν; let V₀:= (A₀)
    let k:= steamP S ((Empire.stella Q).costs L μ R.beta x₀ ν); let F:= Mixed.costs S Q.halo (radiusB x₀) k V₀
    let T:= Mixed.selected S Q.halo T₀ f H.birth V₀ (ConnectedActivityE6.lengths T R) k 0 0 l 0 -- T shadow
    have hp(i:Head S): F i=(f₁ i)+Tickets.extra Z φ i:=by
       rcases i with i|i
       · unfold Tickets.extra; rw [sum_eq_zero,add_zero]; rfl
         intro j _; exact if_neg (fun h=> by have hf:=(show .inr _ = Z j from Daisy.sparkPath ..).trans h; contradiction)
       unfold F V₀ Tune.totalP Tune.sheet Mixed.costs;dsimp only [Sum.elim];simp only [Crew.accountK,Pi.add_apply]; apply congr_arg₂ HAdd.hAdd rfl
       unfold Tickets.extra; simp_rw [← show ∀ j, (.inr (Palette.mark (faces V) (c:=c) j):Head S)=Z j from fun j=> Daisy.sparkPath ..]; simp only [Sum.inr.injEq];rfl
    have hz(i):laude V Cy l α ν s i= 2*Real.exp (α*coverNumber T₀ (H.unionP i))*T i:=by
       by_cases he:H.ticketsP 0 l 0 i
       · have he'(p:Tickets Z): (∏ j∈p.val,Cy j)*salves V i l p α ν s=2*Real.exp (α*coverNumber T₀ (H.unionP i))*(if p.reach ⊆ i then (∏ j∈p.val,φ j)*∏ j∈i\p.reach,f₁ j else 0):=by
            unfold salves; by_cases hz:p.reach⊆i; swap; · rw [if_neg (fun h=>hz h.2),if_neg hz,mul_zero,mul_zero]
            rw [if_pos hz,if_pos ⟨he,hz⟩]; unfold pleas; rw [worth]; unfold φ wages; rw [prod_mul_distrib]; ring
         unfold T Mixed.selected laude; rw [if_pos (show Mixed.Allowed _ _ _ f _ _ 0 l 0 i from he),Mixed.Price,pow_zero,mul_one]; simp_rw [he']; rw [← mul_sum]; change _=_* ∏ j∈i,F j; simp_rw [hp, Tickets.expanded Z]; congr!
       unfold T Mixed.selected laude; rw [if_neg (show ¬ Mixed.Allowed _ _ _ f _ _ 0 l 0 i from he),mul_zero]; apply sum_eq_zero fun j _=> ?_; rw [salves,if_neg (fun h=>he h.1),mul_zero]
    intro i
    have ht':= Mixed.mixed_hit S Q.halo (radiusB x₀) f H.birth V₀ _ k hA Y 0 0 l 0
    have hx: Ac.Hit H.unionP T₀ T Q.exp _:= ht'
    convert! budget_scale zero_le_two (hx i) using 1; ext j; split
    next h=> rw [hz,show Q.exp* ↑(coverNumber T₀ (H.unionP j))=α* ↑(coverNumber T₀ (H.unionP j))+(Q.exp-α)* ↑(coverNumber T₀ (H.unionP j)) from (by ring),Real.exp_add]; ring
    next h=>rw [mul_zero]
end Crew
end YM.ConnectedActivityE6.Empire.Imago
