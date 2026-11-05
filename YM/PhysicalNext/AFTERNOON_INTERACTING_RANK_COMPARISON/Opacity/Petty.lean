import YM.Extra.MULTISOURCE_BOUNDS.Merger
import YM.Further.THRESHOLD_SOURCE_RESTART.Series
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Desk
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Plotter
import YM.PhysicalNext.RECURSIVE_SECANTS_079.Masses



/-!
# Regrade pointwise meter+rents and present Plate to actual Grip

Support-only roll. All zero-order; not prescription for analytic
purchasing after markings. Retains sums of local ℝ exps to exponentiate,
two headings (core and other) with ONE hit budget, Γ gap not a single
V-only normalizer. Sensor inflation independent later. Does not assume
occupancy away motions beyond Sparkle. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Pump
open Function Lattice RG Pressure Pressure.Tube Pressure.Stores Tree Wilson
open Matrix Finset PhysicalGuard7f546.Curved Next.SectorChange Precision AnalyticBridge.LocalGaussianLaws Filter
    SectorTools.PhysicalGaussianSwitch AnalyticBridge.RelativeLogdet MeasureTheory
    Push.SectorMeasure Push.SectorMeasure.Presented Push.SectorMeasure.Oriented Native Gaussian GaugeRoute
    AnalyticBridge.MarginalMultiplier3b1d PatchReads Rows Wisps Display Display.Docking Display.Sew Pot Push.AbsoluteSums RecursiveSecants079.BothSides
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {c f : Side} {G : Gauge} {S : StepData c f} {P : Teller G} {v : Dyed G S} {B : ℕ} {x W t e d g : ℝ} {p q : Pilot G S x}
variable {F H : Pilot G S x→ℝ}
def Petty (v : Dyed G S) (W : ℝ) (B : ℕ) (e T : ℝ) (X : Pilot G S x→ℝ):=
   ∃ (f: Glade c→ Pilot G S x→ℝ) (b:Glade c→ℝ),(∀ i,Pulled (f i) i.val) ∧ Ac.Hit (fun i:Glade c=>i.val) B b e T ∧ (∀ i,0≤b i)∧ (∀ i p,Matched p →|f i p|≤b i) ∧∀ p,Matched p → v.Playing W p → X p=∑ i,f i p
namespace Petty
lemma across (h : Petty v W B e d F) (hp : d≤ g) : Petty v W B e g F:= by
  obtain ⟨f,b,hp',ha,h⟩:=h; exact ⟨f,b,hp',fun i=>budget_loosen (ha i) hp,h⟩
lemma plus (h : Petty v W B e t F) (hp : Petty v W B e d H) : Petty v W B e (t+d) (fun i=>F i+H i):=by
  obtain ⟨f,b,hf,hb,hN,h1,h2⟩:=h; obtain ⟨g,a,hg,ha,hK,hP,hH⟩:=hp
  exact ⟨fun i p=> f i p+g i p,_,fun i=> (hf i).plus (hg i),hit_plus hb ha,fun i=>add_nonneg (hN i) (hK i),fun i p h=>(abs_add_le ..).trans (add_le_add (h1 i p h) (hP i p h)),fun i h k=> (congr_arg₂ HAdd.hAdd (h2 i h k) (hH i h k)).trans (sum_add_distrib ..).symm⟩
lemma traded (h : Petty v W B e d F) (he : ∀ p, Matched p → v.Playing W p → H p=F p) : Petty v W B e d H := by
  obtain ⟨f,b,hz,h,hV,hU,hX⟩:=h; exact ⟨f,b,hz,h,hV,hU,fun p a b=> (he p a b).trans (hX p a b)⟩
section
variable {ι : Type} [Countable ι] {L : ι→ Pilot G S x→ℝ} {Y : ι→ Support c} {b : ι→ℝ}
    (hl : ∀ i, Pulled (L i) (Y i)) (hY:∀ i,(Y i).Nonempty) (hs : ∀ i,0≤b i) (hb : Ac.Hit Y B b e t) (he : 0≤e)
include hl hY hs hb he
lemma accepts (h : ∀ i p,Matched p→ |L i p| ≤ b i) : Petty v W B e t (fun p=>∑' i,L i p):=by
  let X i : Glade c := ⟨Y i,hY i⟩; let ξ (g:ι→ℝ) (i : Glade c):= ∑' j:{j// X j=i},g j.val
  have hf := Further.ThresholdSourceRestart.hit_summable he hs hb hY
  have hx (g:ι→ℝ) (hg : Summable g) : ∑ i,ξ g i=∑' i,g i:= by rw [←tsum_fintype (L:=.unconditional _)]; exact (hg.hasSum.tsum_fiberwise X).tsum_eq
  have hT i:0≤ξ b i:= tsum_nonneg fun j=> hs _
  have ha p (hp:Matched p): Summable (fun i=>|L i p|):= hf.of_nonneg_of_le (fun i=>abs_nonneg _) fun i=>h i p hp
  refine ⟨fun i p=> ξ (fun j=>L j p) i,ξ b,fun i=>Pulled.countable (fun j:{j//X j=i} => (hl j.val).mono (le_of_eq (show Y j.val = i.val from congr_arg Subtype.val j.property)) ),?_,hT,?_,fun p hp _=> (hx _ (Summable.of_norm (ha p hp))).symm⟩
  · intro k; let w i:= if k∈Y i then b i*Real.exp (e*coverNumber B (Y i)) else 0
    have hK (i : Glade c) : (if k∈i.val then ξ b i*Real.exp (e*coverNumber B i.val) else 0)=ξ w i:= by
      unfold ξ; have hj (j:{j// X j=i}):Y j.val=i.val:= congr_arg Subtype.val j.property
      unfold w; simp_rw [hj]; split
      next hv=> exact (tsum_mul_right ..).symm
      next hv=> exact tsum_zero.symm
    refine budget_finite (fun i=>hK i|>.symm ▸ tsum_nonneg (fun j=> (hb k).1 (_:ι))) ?_
    change (∑ i:Glade c,if k∈i.val then _ else _)≤_
    simp_rw [hK,hx w (show Summable w from (hb k).2.1)]; exact (hb k).2.2
  intro i p hp
  have hm : Summable (fun j:{j// X j = i} => ‖L j.val p‖):= (ha p hp).subtype _
  exact (norm_tsum_le_tsum_norm hm).trans (hm.tsum_le_tsum (fun j=>h j.val p hp) (hf.subtype _))
lemma receives (h :∀ i p,Matched p → v.Playing W p → |L i p| ≤ b i) : Petty v W B e t (fun p=>∑' i,L i p):= by
  let ν i p:= max (-(b i)) (min (b i) (L i p))
  have hh:Petty v W B e t (fun p=>∑' i,ν i p):= by -- shadow rename below
    refine accepts (fun i=> (hl i).twine ((continuous_const.max (continuous_const.min continuous_id)).measurable)) hY hs hb he ?_
    intro i p hp; exact abs_le.mpr ⟨le_max_left ..,max_le (neg_le_self (hs i)) (min_le_left ..)⟩
  refine hh.traded (fun p hp he=> tsum_congr fun i=>?_)
  unfold ν; obtain ⟨a,b⟩:= abs_le.mp (h i p hp he); rw [min_eq_right b,max_eq_right a]
lemma acceptsList [Fintype ι] (h :∀ i p,Matched p → v.Playing W p → |L i p| ≤ b i) : Petty v W B e t (fun p=>∑ i,L i p):= by
  simpa only [tsum_fintype] using receives hl hY hs hb he h
end
end Petty
lemma issue_invoice {κ C η u : ℝ} (h : Chips v P W x) (hf : Physical.Certified S v.things x κ C η u)
    (Q : Core S x→ Pilot G S x→ℝ) (hq : ∀ i,Pulled (Q i) (acre i)) (h₁ : ∀ i,Opaque (Q i)) (ht : t≤1) (he : 0≤e)
    (h₂ : ∀ p i,Matched p→ Q i p≤ g*i.val.shares) (hP : ∀ p,Matched p→ v.Playing W p→ v.spoolLift p=(∑ i∈owners p.key x,Q i p)+F p) (hp : Petty v W B e t F) :
    ∃ M : Plate v x W,(∀ i p,Matched p → M.base i p ≤ g * i.val.shares) ∧
       ∃ b:Glade c →ℝ,(∀ i,0 ≤ b i)∧ Ac.Hit (fun i:Glade c=> i.val) B b e (2*t)∧∀ i p,Matched p→ |Real.exp (M.aux i p)-1|≤b i:= by
  obtain ⟨f,b,hL,hx,hk,hV,H⟩:= hp
  have hy i : Opaque (f i):=⟨_,hV i⟩
  obtain ⟨s,i,j,k,y,hR⟩:=h.lawful
  let M:Plate v x W:= brushes Q f hq hL h₁ hy (fun p hp hP'=> by rw [hP p hp hP',H p hp hP']) h.boost hf h.paths h.clips h.data h.arc_pos h.inner hR h.beta h.tall
  let Y (i:Glade c):=∑ e:Wheel c,cash_at c*b (((routes c).dial e).symm i)
  have hv : Ac.Hit (fun i:Glade c=>i.val) B Y e t:= liquidate (routes c) hx
  have hY (i:Glade c):0≤ Y i:= Finset.sum_nonneg (fun k _=>mul_nonneg (cash_pos _).le (hk _))
  refine ⟨M,fun i p hs=>?_,fun i=>Y i+Y i,fun i=> add_nonneg (hY i) (hY i),fun i=> budget_loosen (hit_plus hv hv i) (by linarith only),?_⟩
  · apply fill_upper scope Q hq h₁ i p hs
    intro z v; apply le_trans (h₂ _ _ ((hs.signed z).bright v))
    suffices hi : (hoop S x z i).val.shares=i.val.shares by change g* (↑((hoop S x z i).val.shares))≤_; rw [hi]
    rw [← Packets.seeds_card,← Packets.seeds_card]; exact (Finset.card_map .. ).symm.trans (congr_arg Finset.card (turnSeeds z i.val).symm)
  intro i p hp; have hl : |M.aux i p| ≤ Y i := bill_saving (routes c) _ hL hV p hp i
  apply le_trans (Real.abs_exp_sub_one_le (hl.trans ((hit_one hv he hY i i.property).trans ht))) (by linarith only [hl])
end YM.PhysicalNext.InteractingRank.Pump
