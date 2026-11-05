import YM.FullVolume.Luna.Cuts
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Luna
open Function Filter Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Empire
open FullVolume.Ray
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Next.Foundations Jams YM.Source Labels
section basics
open YM.Source Extra.Histories
variable {G:Gauge}{n:Side}{ι:Type*}{B:BudgetPoint}{X:Support n}{o:Site n}{p q r s t v:ℝ}
abbrev Brill (B:BudgetPoint)(X:ι→ Support n)(x:ι→ ℝ)(e v:ℝ):= SumBudget (fun i=>Real.exp (e*coverNumber B.B (X i))*x i) v
lemma br_add {X:ι→Support n} {y z:ι→ℝ}(h:Brill B X y p q)(hp:Brill B X z p r):Brill B X (y+z) p (q+r):=by
   unfold Brill; simp_rw [Pi.add_apply,mul_add]; exact Local.sumBudget_add h hp
lemma br_scale {X:ι→Support n} {y:ι→ℝ}(h:Brill B X y p q)(hp:0≤r):Brill B X (r • y) p (r*q):= by
   unfold Brill; simp_rw [Pi.smul_apply,smul_eq_mul,mul_left_comm _ r]; exact Local.sumBudget_mul_left h hp
lemma br_zero (B:BudgetPoint){X:ι→Support n}(e:ℝ):Brill B X 0 e 0:=by unfold Brill; simp_rw [Pi.zero_apply,mul_zero]; exact Local.sumBudget_zero le_rfl
lemma br_fin {X:ι→ Support n}{U:Type*}(T:Finset U) (x:U→ι→ℝ)(a:U→ℝ)(h:∀ u, Brill B X (x u) p (a u)):Brill B X (∑ u∈T,x u) p (∑ u∈T,a u):=by
  induction T using Finset.induction_on with
  | empty=> simp; exact br_zero ..
  | insert i T hi hv=> rw [sum_insert hi,sum_insert hi]; exact br_add (h i) hv
lemma saneF {s:ℝ}{x: Config G n→ℂ}: s • x=(s:ℂ) • x:=funext fun _=> (Complex.real_smul)
lemma sandR {f:Config G n→ℂ} (h:B.Regular X f)(s:ℝ):B.Regular X (s • f):=by rw [saneF]; exact regular_smul _ h
lemma sandF (s:ℝ){f:Config G n→ℂ} {a:ℝ}(h:B.supBounds o X f a): B.supBounds o X (s • f) (|s| *a):=by
   rw [saneF,show |s|=‖(s:ℂ)‖ from by simp [Real.norm_eq_abs] ]; exact bound_smul _ h
lemma sumAr {U:Type*}(T:Finset U)(f:U→ Config G n→ℂ)(he:∀ i,B.Regular X (f i)): B.Regular X (∑ i∈T,f i):=by
   induction T using Finset.induction_on with
   | empty => simpa only [sum_empty] using (regular0 B X (0:Site n)).1
   | insert i T hi hv => rw [sum_insert hi]; exact regular_add (he i) hv
lemma paneR {f:sun → Config G n→ℂ}(w:Rung)(h:∀ z,B.Regular X (f z)):B.Regular X (mix w f):= sumAr _ _ (fun i=> sandR (h i) _)
lemma sumBounds {U:Type*}(T:Finset U)(f:U→ Config G n→ℂ)(a:U→ℝ)(h:∀ i,B.Regular X (f i))(he:∀ i,B.supBounds o X (f i) (a i)): B.supBounds o X (∑ i∈T,f i) (∑ i∈T,a i):=by
   induction T using Finset.induction_on with
   | empty => simpa only [sum_empty] using (regular0 ..).2 -- ambiguous
   | insert i T hi hv => rw [sum_insert hi,sum_insert hi]; exact bound_add (h i) (sumAr _ _ h) (he i) hv
structure Wires (B:BudgetPoint)(o:Site n)(X:ι→ Support n)(f:sun→ ι→ Config G n→ℂ)(p e v:ℝ): Prop where
   lamps: ∃ r, Brill B X r e v ∧ (∀ i,0 ≤ r i) ∧ ∀ i:ι,∀ w:Rung,∀ a,Stripe w p a→B.supBounds o (X i) (mix w (fun t=> f t i)) (a * r i)
-- raw first tier: reservesMass
abbrev Chand (B:BudgetPoint)(o:Site n)(X:ι→Support n)(f:ι→ Config G n→ℂ)(e v:ℝ):Prop:=∃ r,Brill B X r e v ∧∀ i,B.supBounds o (X i) (f i) (r i)
variable {X:ι→Support n}{f:sun→ι→ Config G n→ℂ}
namespace Wires
lemma leaner (h:Wires B o X f p r v)(hh:v ≤ q):Wires B o X f p r q:= by obtain ⟨b,hb,hA⟩:=h.lamps; exact ⟨b,Local.sumBudget_mono hb hb.1 le_rfl hh,hA⟩
lemma takes (h:Wires B o X f p r v){w:Rung}(hh:Stripe w p s): Chand B o X (mix w f) r (s*v):=by
   obtain ⟨b,hb,hA,hY⟩:=h.lamps; exact ⟨s • b, br_scale hb (stripe_pos hh), fun i=>by rw [mix_eval]; exact hY _ _ _ hh⟩
variable {k:ℕ}(T:Tableau q k)
lemma squeeze {p v:ℝ}(hr:q ≤ p)(h:Wires B o X f p r v)(hx:∀ x,Chand B o X (f x) r t)(hf:∀ x i, B.Regular (X i) (f x i)):Wires B o X f q r (T.price*t+T.liftT p*v) := by
   choose b hb hB using fun i=> hx (T.p i); obtain ⟨a,hA,ha,hK⟩:= h.lamps
   let K(i):=T.u i • b i; let Z:=∑ i,K i
   have ht i:Brill B X (K i) r (T.u i*t):=br_scale (hb i) (T.hp i)
   have hY:T.price*t=∑ i,T.u i*t:=sum_mul ..; have hZ(n):0≤ Z n:=by unfold Z; rw [Finset.sum_apply]; exact sum_nonneg (fun i _=>mul_nonneg (T.hp _) (hB i n).1)
   let s:= T.liftT p; let e : ι→ℝ := s • a
   have hs:0≤ s:=by unfold s Tableau.liftT;have h:= T.sane; have hq:= T.wide; have hp:0≤p:=(by linarith); positivity
   refine ⟨Z+e,br_add (hY.symm ▸ br_fin univ K _ ht) (br_scale hA hs),fun i=>add_nonneg (hZ i) (mul_nonneg hs (ha i)), fun i w η hv=>?_⟩
   let V x:= f x i; have hU:= paneR (X:=X i) (w-T.cuts w) (fun x=> hf x i); have hy:= T.lapse hr hv
   have hp:B.supBounds o (X i) (mix (T.cuts w) V) (η*Z i):=by
      have hN:= Jams.incomes k T.p w V
      rw [show mix (T.cuts w) V=_ from hN]; unfold Z; rw [Finset.sum_apply,mul_sum]
      refine sumBounds univ _ (fun j=>η*K j i) (fun j=> sandR (hf _ _) _) (fun j=> ?_)
      have hb := mul_le_mul_of_nonneg_right (T.use _ _ hv j) (hB j i).1
      apply Local.bound_weaken (sandF _ (hB _ i)) (hb.trans_eq ?_); change η*T.u j*b j i= η*(T.u j*b j i); ring
   rw [T.splitK w]; refine Local.bound_weaken (bound_add (paneR _ (fun x=>hf x i)) hU hp (hK _ _ _ hy)) (le_of_eq ?_); change η*Z i+η*s*a i=η*(Z i+s*a i);ring
end Wires
end basics
end YM.PhysicalNext.Repeat.Luna
