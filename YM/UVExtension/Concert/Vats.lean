import YM.UVExtension.Concert.Aperture
import YM.UVExtension.Wick.Kilt

set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Concert
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Blaze Shell Channel SliceRows Control Window Census Green Mask Pulse Itinerary Coat Footprint Raw Poll Pond
open Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill
open Packets Art Silica Shield Eider Flux Hues Rotation Matter
open Lamppost Wick Wick.Bower MeasureTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff ENNReal InnerProductSpace Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {Z : ChartRatio G}
variable (X : Coat T F) {R : RG.Rep G f} {u v s a : ℝ}
open Animals Reserves Gas Ursell Trees Multiple Letter OmitClusters
variable {ι : Type} [Fintype ι]
variable {x y γ W μ δ e b B C u D d r q' A v' g w b' Y' n:ℝ} {K l j : ℕ} {χ:Chi} {Q : YM.ConnectedActivityE6.Target G P}
    {o : Target.Order G W} {H : Cash W x μ L Q o a T R} {V : ι→ Juice G f}
open March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt Wick
variable (hF:Festa Q L H V w g){q:Q.rate≤γ}{hk:γ<0}(Y:Festa.Pavilion H V g γ v d q hk) (hi:0≤Q.exp-d)
    (J : (d:Canvas (betaF G x L) w ι)→ Cash W x μ L Q o a T (freshen d R V)) (U:Config G c) (χ: Chi)
-- forced entry on common dictionary
open Match Refrain

def grain (H:Cash W x μ L Q o a T R)(V:ι→ Juice G f) (i:Molecule S)(z:Vines ι):ℂ:=
  (Fintype.card (Greenbelt.Reserve S):ℂ)⁻¹*∑ j, Wick.bubble H V (prism T x χ o.K U (Greenbelt.allot j)) i z
include Y hF hi
lemma grainL (i:Molecule S)(he:(H.unionP i).Nonempty): Bumps (aperture hF).span (grain U χ H V i) := by
  intro E f hE he' hg; exact (DifferentiableOn.fun_sum (fun i' (_:i'∈Finset.univ)=> hF.stems (X:=prism T x χ o.K U (Greenbelt.allot i')) rfl rfl Y he hi E f hE he' hg)).const_mul _
omit Y hi hF in -- need hF
lemma grainR (_K:Festa Q L H V w g) (t:Canvas (betaF G x L) w ι) (i:Molecule S) : grain U χ H V i (hoist t.val)= ↑((J t).spawn χ U i):= by
  unfold grain Cash.spawn poolA likely; push_cast; apply congr_arg _; apply Finset.sum_congr rfl; intro j hj; exact _K.real_money (X:=prism T x χ o.K U (Greenbelt.allot j)) rfl rfl i _ t.2
omit hi
lemma grainS (z:Vines ι)(hz:z∈ parade (betaF G x L) g)(l:ℕ):∃ b : Molecule S→ℝ, (∀ i, 0≤b i) ∧ Ac.Hit H.unionP (radiusB x) b (Q.exp-d) ((stalk Q q hk).quantum L μ x 0 0 l 0) ∧ ∀ U i,l ≤ Cash.numP i → ‖grain U χ H V i z‖≤ b i:=by
  letI:= Tree.select S.ratio S.patch.odd_side; obtain ⟨b,h,hc,hg⟩:= hF.canthus Y hz l
  refine ⟨b,h,hc,fun U i hi=>?_⟩; unfold grain; rw [norm_mul,norm_inv,Complex.norm_natCast]; have hx j:= hg _ (prism T x χ o.K U (Greenbelt.allot j)) rfl rfl i hi
  refine (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (sum_le_sum (fun j _=> hx j))) (by positivity)).trans_eq ?_; rw [Finset.sum_const,card_univ,nsmul_eq_mul,inv_mul_cancel_left₀ (by positivity)]

omit Y hF
-- Letters, promised spectra.
def juiceK (H:Cash W x μ L Q o a T R)(V:ι→ Juice G f)(z:Vines ι)(j:H.Chapter) : ℂ := j.elim (fun j=> grain U χ H V j.val z) (fun j=> -((coefficient H.seam j.2:ℂ) *(∏ i, grain U χ H V (j.2 i).val z) / ((j.1+1).factorial:ℂ)))
def tonic (H:Cash W x μ L Q o a T R)(V:ι→ Juice G f)(z:Vines ι)(i: Annual H):ℂ:=
    i.elim (fun i=> let p:= i.val; if H.Fresh p ∧ Ac.Spark H.bookFoot p.1 ∧ H.statesPool U p then ∏ t:↥p.1, juiceK U χ H V z t.val^(p.2 t+1) / ↑((p.2 t+1).factorial) else 0) (fun _=>0)
include hF
lemma drinkR (t:Canvas (betaF G x L) w ι)(i:H.Chapter): juiceK U χ H V ((aperture hF).call t) i= ↑((J t).colognePool χ U ((fleet t J H).editor i)):=by
  rcases i with i|i
  · exact grainR J U χ hF t i.val
  let X := fleet t J H
  change -(_*_/_)=(↑(-(Gas.term (J t|>.seam) _ (X.furrow i))):ℂ)
  unfold Gas.term; rw [← Match.weighs _ X.sec i]; push_cast; apply congr_arg Neg.neg; refine congr_arg (·/ _) ?_; apply congr_arg _; exact Finset.prod_congr rfl fun k _=> grainR J U χ hF t (i.snd k).val
lemma tonicR (t:Canvas (betaF G x L) w ι) (i: Annual H): tonic U χ H V ((aperture hF).call t) i= ↑(Refrain.fuse H (fleet t J H) χ i U):=by
  let X:= fleet t J H; rcases i with i|i; swap; · exact Complex.ofReal_zero.symm
  let p:= i.val; let r:=X.tongs p; let Y:= J t
  change (if H.Fresh p ∧ Ac.Spark H.bookFoot p.1 ∧ H.statesPool U p then _ else _)= ((Y.smilesPool χ U r:ℝ):ℂ)
  have h: H.statesPool U p ↔ Y.statesPool U r:=by have hx:= X.festoon U p; rw [pull_one,show Lattice.translate (0:Site c) U=U from funext fun i=> by simp [Lattice.translate]] at hx; exact hx
  rw [X.sap p,X.splint,h]; unfold Cash.smilesPool; split_ifs with hp; swap; · simp
  unfold manyW; push_cast; refine Fintype.prod_equiv (Match.tallyVip X.editor p.1) _ _ fun i=>?_
  have hh : (X.tongs p).2 (tallyVip X.editor p.1 i)=p.2 i := Match.numbers X.editor p i; rw [show r.snd _=_ from hh]; rw [drinkR]; rfl
include Y hi
lemma drinkH (i:H.Chapter): Bumps (aperture hF).span (fun z=> juiceK U χ H V z i):= by
  rcases i with i|i
  · exact grainL hF Y hi U χ _ i.2.1
  intro E f ht hm hg; exact (((DifferentiableOn.fun_finsetProd (fun j (_:j∈Finset.univ)=> grainL hF Y hi U χ _ (i.snd j).2.1 E f ht hm hg)).const_mul _).div_const _).neg
lemma tonicH (i: Annual H): Bumps (aperture hF).span (fun z=> tonic U χ H V z i):=by
  rcases i with i|i
  · let p := i.val
    intro E f hE hv ht
    by_cases hm : H.Fresh p ∧ Ac.Spark H.bookFoot p.1∧ H.statesPool U p
    · refine (DifferentiableOn.fun_finsetProd (fun t (_:t∈(Finset.univ:Finset (↥p.1)))=> ((drinkH hF Y hi U χ t.val E f hE hv ht).pow (p.2 t+1)).div_const (↑((p.2 t+1).factorial):ℂ))).congr (fun i hi=> if_pos hm)
    exact (differentiableOn_const (𝕜:=ℂ) _).congr (fun i hi=> if_neg hm)
  intro E f _ _ _; exact differentiableOn_const _
end YM.UVExtension.Concert
