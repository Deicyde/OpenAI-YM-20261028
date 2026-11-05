import YM.FullVolume.Florid.Payee
import YM.MergeProof.Wreath
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
abbrev faces : A→Leaf R:= fun i => (V i).pole
abbrev facesT (t:sun): A → Leaf (U.notes t):=fun i=> (V i).flies t
local notation "V₀"=>faces V
local notation "Vx" =>facesT V
lemma face_wing (s:sun): sign (facesT V s) S=sign (faces V) S:=funext fun i=> congr_arg (Wing.badge · S) ((V i).kind s)
def shift (s:sun) : Tickets (sign (faces V) S)≃ Tickets (sign (facesT V s) S):= Equiv.subtypeEquivRight (fun i=>by rw [face_wing])
variable (p:Tickets (sign (faces V) S))
local notation "V₁"=> Merge.Palette.team V₀ p
abbrev hat (t:sun) := Merge.Palette.team (facesT V t) (shift V t p)
lemma shotK(t:sun) : (hat V p t).weight=(team (faces V) p).weight:=by
   unfold hat; rw [worth,worth]; exact prod_congr rfl (fun i _=> (V i).prices t)
lemma shotU(t:sun): (hat V p t).signs S=p.reach:=by
    simp only [hat,label,Tickets.reach];change Finset.image (sign (facesT V t) S) p.val=_;rw [face_wing]
-- marks exactly V.crest multiple. zero allowed.NE.
lemma fleeting {i:Molecule S} (h:p.reach⊆ i): blaze (i\p.reach)=blaze i:=by
    ext j; simp only [blaze,mem_toRight]; refine ⟨fun h=> (Finset.mem_sdiff.mp h).1,fun h=> Finset.mem_sdiff.mpr ⟨h,?_⟩⟩
    rintro ht; obtain ⟨q,hq,hx⟩:=mem_image.mp ht; have hx: Sum.inr (Daisy.sparkling c f (V q|>.pole.turn))=Sum.inr (.inr (.inr j)):= (sparkPath ((V q).pole.turn) S).trans hx
    cases he:(V q).pole.turn <;> rw [he] at hx <;> simp [sparkling] at hx
lemma stays_put (X:Coat T F)(t:sun)(k:A)(w:Directions G f): (facesT V t k).paidU X o.a w=(V k).pole.paidU X o.a w:=by
   unfold Leaf.paidU Leaf.fond; rw [show (facesT V t k).ingredient=(V k).pole.ingredient from (V k).reps t];simp_rw [Wing.badge_area]; rw [show ((facesT V t k).turn.support _)= _ from (V k|>.crests t)] <;> rfl
lemma headK (X:Coat T F) (t:sun) (w:Directions G f): (hat V p t).paidU X o.a w=(V₁).paidU X o.a w:=by
    let K:=shift V t p; let J:= (facesT V t); unfold Team.paidU hat team
    rw [prod_image,prod_image];
    · exact prod_congr rfl (fun i _=> stays_put V _ t i _)
    · exact fun _ hx _ hy h=>p.property hx hy (congr_arg (fun i:Leaf R=> i.turn.badge S) h)
    exact fun i hx j hy h => K.property hx hy (congr_arg (fun i:Leaf _=> i.turn.badge S) h)
local notation "Λ"=>U.pole
local notation "T₀"=> radiusB x₀
local notation "msg"=> V₁
variable {ν α:ℝ} {s:Lyre.Signal 0} (hc:Clear Q L μ ν x₀ v s)(hr: Lyre.Clarity H 0 C δ ν)(hσ:Margin G L x₀ α δ)(hv:2≤v)
variable (X:Coat T F)(he:X.x=x₀)(ht:X.width=o.K)(hx:X.manifest)
variable (i:Molecule S)(hg:p.reach⊆i)
def pleas (α ν:ℝ) (s:Lyre.Signal 0) (i:Molecule S):= Real.exp (α*coverNumber (radiusB x₀) (H.unionP i)) * (V₁).weight * ∏ j∈ i\p.reach, U.totalP s ν j
local notation "f₀"=> U.plainP s ν
local notation "f₁"=> U.totalP s ν
local notation "d" => pleas V p α ν s i
lemma coinsP:0 ≤ d := by
   unfold pleas; rw [← U.swell]; exact mul_nonneg (mul_nonneg (Real.exp_pos _).le ((V₁).profit)) (mul_nonneg (prod_nonneg fun _ _=> U.propense _) (pow_nonneg H.pos _))
variable (l: Finset ℕ)
def blush (t:sun)(y:F.Slice G × Air f G):=(hat V p t).into X W o.a Q.table l Q.halo i (y.1, U.pole.flow t • y.2)
include V X hc hr he ht hx hg
lemma wright (y:F.Slice G× Air f G): Scout v (phraseS fun t:sun=> blush V p X i l t y) ((X.catastrophe o.ξ R.beta (blaze i)).indicator (fun _=> (msg).weight * ∏ j∈i\p.reach,f₀ j) y.2):=by
   let Z:= X.wrapY y.1
   let f(t):= U.content X l (i\p.reach) t y
   let a:=(V₁).paidU Z o.a (Z.liftA R.beta y.2)
   have hX:= U.gains X l (i\p.reach) hc hr he ht hx y
   rw [fleeting V p hg] at hX
   refine ((hX.scale a).enlarged ?_).replace (fun t h=>?_) -- auth.1
   · let Y:= X.catastrophe o.ξ R.beta (blaze i);by_cases hp:y.2∈Y; swap; · rw [Set.indicator_of_notMem hp,Set.indicator_of_notMem hp,mul_zero]
     rw [Set.indicator_of_mem hp,Set.indicator_of_mem hp]; exact mul_le_mul_of_nonneg_right (Team.coin ..) (prod_nonneg fun i _=> U.propense _)
   let t':sun:=⟨t,h⟩; let u:= U.pole.flow t • y.2; let F':= U.notes t; simp only [show phraseS _ t= _ from phrased _ t']
   unfold blush Team.into Team.premium; dsimp only; rw [shotU,if_pos hg]
   apply congr_arg₂ (·*·) _ rfl
   rw [headK (p:=p)]; apply congr_arg ((V₁).paidU Z o.a); change Z.liftA _ _=Z.liftA F'.beta u;have hc : Z.manifest:=hx
   rw [shine Z (he.symm ▸ (U.beams t (U.lay h)).laws.data.room) hc, shine Z (he.symm ▸ H.laws.data.room) hc]; -- P ambiguous
   unfold u; rw [← U.pitch t (U.lay h)]; exact (moving (U.seats t (U.lay h)) Z _).symm
include hσ
lemma ballot : Rebar v (phraseS fun t:sun=> (hat V p t).tithe X l W o.a Q.table Q.halo i) d:= by
  let μ':=(F.order G).prod X.dice; let I:= Lyre.stampD (H:=H) i;let J:=lensS I G
  let a (t:sun) (y:F.Slice G × Air f G):=markL X y.2 I (U.pole.flow t) * blush V p X i l t y
  let D:= (1+δ)^J.card; let T':=(V₁).weight*∏ j∈i\p.reach,f₀ j; let Y:= X.catastrophe o.ξ R.beta (blaze i); let W'(y : F.Slice G × Air f G):= Y.indicator (fun _=>D*T') y.2
  let hH:= H.laws.data; have hV: X.relating.PosDef := (hH.localP F X he ht hx).sails.fullC
  have hs(t:sun) : Integrable (a t) μ' ∧ Team.tithe (hat V p t) X l W o.a Q.table Q.halo i=∫ y,a t y ∂μ':=by
    have hz:= U.lay t.property;let K:= U.beams t hz; let B:= K; let Hx:= Mill.bankHere X K he
    have hh : J = podium S G (K.unionP i) X.B:= by unfold J I Lyre.stampD; rw [Flux.chargedU,U.stage t hz,show X.B= T₀ from congr_arg _ he]
    let f:= (hat V p t).into X W o.a Q.table l Q.halo i; have hP:=Team.tip (hat V p t) X l Hx ht hx i
    exact root_lens X J hV (show StronglyMeasurable f from hP.1.meas.stronglyMeasurable) (by
       intro u v h w; let Y':=X.wrapY w; change Team.premium _ _ _ _ _ _ _ _ _= _; rw [hh] at h; exact Team.concur _ Y' _ Y' ⟨Village.refl Y' _,(observe _).mp h,fun _ _=>Iff.rfl⟩ Hx.laws.data.room Q.buys (show _⊆ K.unionP i from (by change ground (U.notes t) T Q.halo Y'.B i ⊆ _; rw [show Y'.B=T₀ from congr_arg _ he]; exact Finset.Subset.refl _)) Hx.laws.intake
       ) hP.2.1 (U.pole.flow t) (zero_lt_one.trans_le (U.pole.moves _ hz|>.1))
  have hm : MeasurableSet Y:= Poll.sounded ..;have hX: Integrable W' μ' := ((MeasureTheory.integrable_const _).indicator hm).comp_snd _
  have hh (y): Scout v (phraseS fun t:sun=> a t y) (W' y):=by
     have h:= ((U.glass_w X I _ hV).multiplies (wright V p hc hr X he ht hx i hg l y)).replace (g:=phraseS fun t:sun=> a t y) (by intro t h;let t':sun:=⟨t,h⟩;simp_rw [show phraseS _ t=_ from phrased _ t']; rfl); apply h.enlarged
     by_cases hy : y.2∈Y
     · unfold W';rw [Set.indicator_of_mem hy,Set.indicator_of_mem hy]
     unfold W';rw [Set.indicator_of_notMem hy,Set.indicator_of_notMem hy,mul_zero]
  refine ⟨U.normed,coinsP V p _,fun w t he₁=>?_⟩
  let T y:= Jams.mix w (fun i₀:sun=> a i₀ y); have ht:0≤ t := (norm_nonneg _).trans (he₁ 0)
  have hf' (i:↑sun) : Integrable (fun x=> w i • a i x) μ':= ((hs i).1).smul (w i)
  have hu : Integrable T μ':= integrable_finsetSum _ (fun i _=>hf' i)
  rw [mix_made,show Jams.mix w _= ∫ y,T y ∂ μ' from ?_]; swap
  · unfold T mix; rw [integral_finsetSum _ (fun i _=> hf' i)]; apply sum_congr rfl; intro y hy; dsimp only; rw [integral_smul (w y), (hs y).2]
  apply (norm_integral_le_integral_norm _).trans
  apply (integral_mono hu.norm (hX.const_mul t) (fun i=> ?_)).trans; swap;· exact mix_d _ (by exact he₁) (hh i)
  rw [integral_const_mul]; apply mul_le_mul_of_nonneg_left _ ht
  have hy': (∫ p,W' p ∂μ')= X.dice.real Y*(D*T'):=by
    have he(i:F.Slice G) : ∫ z,W' (i,z) ∂X.dice=X.dice.real Y*(D*T'):= integral_indicator_const _ hm
    unfold μ'; rw [integral_prod _ hX]; simp_rw [he,integral_const,probReal_univ,one_smul]
  rw [hy']; unfold pleas; rw [← U.swell, fleeting V p hg]
  have h': X.dice.real Y ≤ H.alarms^(blaze i).card:= ((H.quotes F X he ‹_› hx).2.2.2 (blaze i)).1; have hD:D≥0:=by unfold D; have he := U.pole.full.2.2; positivity
  have hu:0≤ T':= mul_nonneg ((V₁).profit) (prod_nonneg fun i _=> U.propense _)
  have hx: (1:ℝ) ≤ 1+δ:=le_add_of_nonneg_right (U.pole.full.2.2)
  let f:= Real.exp (α*coverNumber T₀ (H.unionP i)); have hZ:D≤f:= (pow_le_pow_right₀ hx (show J.card≤2*J.card from (by omega))).trans (hσ.painter hH.funds.length_eq (H.unionP i) (U.pole.full.2.2))
  exact (mul_le_mul h' (mul_le_mul_of_nonneg_right hZ hu) (mul_nonneg hD hu) (pow_nonneg H.pos _)).trans_eq (by unfold f T'; ring)
end Crew
end YM.ConnectedActivityE6.Empire.Imago
