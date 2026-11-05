import YM.FullVolume.Luna.Bulks
import YM.FullVolume.Glitz.RockG
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
open YM.Source Planned.GuardedAtom Labels -- Angles
open Guard MergeProof MergeProof.Matric Extra.Histories
open YM.PhysicalNext.Repeat.Roof
open YM.Source Planned.GuardedAtom Labels MergeProof MergeProof.Matric Extra.Histories Guard
variable {G:Gauge}{n:Side}{ι:Type*}{B:BudgetPoint}{X:ℕ→Support n}{o:Site n}{p q r s t u v a b c:ℝ}
variable {S:ℕ→Support n}{d k:ℕ}{F:Labels.Frame G d}{C: SectionData F}{Y:Hol G}{R:sun→RG.Rep G n}
local notation "zr"=> Config G n→ℂ
variable {x:ℕ}
-- Pointwise recovery when q large. Do not differentiate along masks.
section
lemma leaf_stripes (T:sun)(hp:1≤p): Stripe (Finsupp.single T 1) p 1:=fun i=>by
   rw [← mix_id (f:=fun y:ℝ=> (y/p)^i), ← combo_eq, combo,Finsupp.linearCombination_single]; simp only [one_smul,norm_pow]; exact pow_le_one₀ (norm_nonneg _) (ratio_le hp T.property)
-- q/v costs controlled; allow even p=2 into Price.Clock. use poly recovery
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E]{A:sun→E}
abbrev Dims (A:sun→E) (p q:ℝ): Prop:= ∀ w:Rung,∀ t,Stripe w p t→ ‖mix w A‖≤ t*q
lemma Dims.beasts (h:Dims A p q)(hs:1≤t)(ht:t<p): Scout t (phraseS A) ((1-t/p)⁻¹*q):=by
   have hx : 1≤p:= hs.trans ht.le; have hP:0≤q:=by simpa [Jams.mix] using (h 0 1 (fun i=> by simp [FullVolume.Ray.trace]: Stripe 0 p 1))
   apply Rebar.recovery _ hs ht; exact ⟨hx,hP,fun w v hh=>mix_made A ▸ h _ _ hh⟩
lemma Dims.values (h : Scout p (phraseS A) q): Dims A p q:=fun _ _ hh=> mix_d A hh h
end
variable (Z:Support n){P:BudgetPoint}{f:sun→ Config G n→ℂ}(w:Rung)(hX:P.order≥d) (h:∀ i,P.Regular Z (f i))
include h hX
lemma aids : Local.residual Y C 0 Z P.threshold (mix w f)= mix w (fun i=> Local.residual Y C 0 Z P.threshold (f i)):=by
   let g:= Local.presented C (0:Site n) P.threshold; let Y' i:= Local.weighted Y F 0 Z P.threshold (f i)
   have hQ : g (Local.weighted Y F 0 Z P.threshold (mix w f))= mix w (fun i=> g (Y' i)):=by rw [projL Z w hX h]; unfold mix; simp_rw [aspect,saneF,map_sum,map_smul]; rfl -- h order check
   change mix w f - g (Local.weighted Y F 0 Z _ _) = mix w (fun i=> f i-g (Y' i)); rw [hQ]; unfold mix; simp only [smul_sub,sum_sub_distrib]
lemma benefits : Local.rebate Y C 0 Z P.threshold (mix w f)=mix w (fun i=>Local.rebate Y C 0 Z P.threshold (f i)):=by
   let r i:= Local.residual Y C 0 Z P.threshold (f i); let g := Local.maskLinear (G:=G) P.threshold (Local.joint C 0 Z);
   let z i:= Local.weighted Y F 0 Z P.threshold (f i); let p:= Local.primary C (0:Site n) P.threshold; let s:= Local.maskLinear (G:=G) P.threshold Z
   change s (mix w f)-p (Local.weighted Y F 0 Z _ _)-g (Local.residual Y C 0 Z _ _)= mix w (fun i=> s (f i)- p (z i)- g (r i))
   rw [aids Z w hX h,projL Z w hX h]; unfold mix; simp_rw [aspect,saneF,map_sum,map_smul,smul_sub,sum_sub_distrib]; rfl
omit h hX
variable {M:sun→Push.Local.Raw F n} (hp:∀ i,(R i).p=B)
variable (ht:Local.Readable Y C B n u)
variable {A:sun→ Coefficient F n} (hh:∀ i, ∃ T: Berths (R i).p (R i).activities (fun j=> Local.joint C 0 (X j)), A i=mint T (M i) Y)
variable {hs:ℝ} (hY:∀ i, (M i).Format 0 X (R i))
local notation "Φ"=> Local.factor Y C B.supportExponent u
local notation "λ!"=>Motion.orbitCost F
local notation "ξ"=> Local.turnCost B.order B.power
set_option quotPrecheck false
local notation "Ω"=>B.supportExponent+2
local notation "fM"=> fun i:sun=> (M i).bulk
local notation "Z'"=> fun i=> Local.joint C (0:Site n) (X i)
def Flames (Y:Hol G)(C:SectionData F)(B:BudgetPoint)(X:ℕ→Support n)(M:sun→Push.Local.Raw F n)(t:sun)(i:ℕ):= Push.Local.rebate Y C (0:Site n) (X i) B.threshold ((M t).bulk i)
local notation "E"=> fun t i=> Flames Y C B X M t i
structure RollsUp {G:Gauge}{n:Side}{ι:Type*} (B:BudgetPoint)(X:ι→Support n)(s:sun→ι→ Config G n→ℂ)(p e b :ℝ):Prop where
   funds : ∃ a, Brill B X a e b ∧∀ i U, Scout p (phraseS (fun t=> s t i U)) (a i)
variable (hq:1≤q)(hz:q<p)
local notation "k'"=> (1-q/p)⁻¹
variable (hw:Wires B 0 X (fun i=>(M i).bulk) p (B.supportExponent+2) a)
include hw hh hY hp ht
lemma pot : Wires B 0 (fun i=> Local.joint C 0 (X i)) (fun t=> (A t).regular) p (B.supportExponent+2) (Φ*a) ∧ ∃ f, Brill B (fun i=> Local.joint C (0:Site n) (X i)) f (B.supportExponent+2) (Φ*a) ∧∀ i,0 ≤ f i∧∀ (U:Config G n),Dims (fun t=>Flames Y C B X M t i U) p (f i):=by
   obtain ⟨c,hc,hr,h⟩:=hw.lamps
   let f i:=Local.atomPrice Y F u*c i; have he i:0≤f i:=mul_nonneg (zero_le_one.trans (Local.atomPrice_ge_one _ _ ht.nonneg)) (hr _)
   have hp' :Brill B (fun i=> Local.joint C (0:Site n) (X i)) f Ω (Φ*a):= Local.sumBudget_mono (Local.sumBudget_mul_left hc (zero_le_one.trans (alphapos ht))) (fun i=>mul_nonneg (Real.exp_pos _).le (he _)) (fun i=>Local.price_join C Y 0 ((hY tip).origin _) ht.sound ht.nonneg (hr _)) le_rfl
   let Z(w:Rung)(i:ℕ):= mix w (fun t=>(M t).bulk i); have hV(t₁ i):B.Regular (X i) ((M t₁).bulk i):=(hp t₁) ▸ ((hY t₁).regular i)
   have hg w η (hz:Stripe w p η) i:= Local.charge_atom (0:Site n) ht (paneR w (fun t=>hV t i)) (h i _ _ hz)
   have hA i t: (A t).regular i=Local.residual Y C 0 (X i) B.threshold ((M t).bulk i):=by
     obtain ⟨T,hT⟩:= hh t; rw [hT]; change Local.residual Y C 0 (X i) (R t).p.threshold _= _; rw [hp]
   refine ⟨⟨f,hp',he,fun i z η hz=> ?_⟩,f,hp',fun i=>⟨he i,fun U w η hw=>?_⟩⟩
   · simp_rw [hA,← aids (X i) z ht.order (fun t=>hV t i)]; unfold f; rw [mul_left_comm]; exact (hg z η hz i).1
   have hx(U): (mix w (fun t=>Flames Y C B X M t i U))= Local.rebate Y C 0 (X i) B.threshold (Z w i) U:=by
      rw [benefits (X i) w ht.order (fun i'=> hV i' i),mix_eval]; rfl
   rw [hx]; exact ((hg w η hw i).2 U).trans_eq (by unfold f; ring)
lemma descent (hq:1≤q)(hz:q<p) : Wires B 0 (fun i=> Local.joint C 0 (X i)) (fun t=> (A t).regular) q (B.supportExponent+2) (Φ*a) ∧ RollsUp B (fun i=> Local.joint C 0 (X i)) (fun t i=> Flames Y C B X M t i) q Ω (k'*(Φ*a)):=by
   obtain ⟨⟨r,hr,hp,ht⟩,a,hb,hA⟩:= pot hp ht hh hY hw; have hx : 0≤k':= inv_nonneg.mpr (sub_nonneg.mpr ((div_le_one (by linarith : 0<p)).2 hz.le))
   exact ⟨⟨r,hr,hp,fun i w η he=> ht i w η (Jams.stripe_down he (by linarith) hz.le)⟩, ⟨k' • a,br_scale hb hx,fun i U=> ((hA i).2 U).beasts hq hz⟩⟩
end YM.PhysicalNext.Repeat.Luna
