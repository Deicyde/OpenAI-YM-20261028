import YM.FullVolume.Luna.Terms
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
open YM.Source Planned.GuardedAtom Labels MergeProof MergeProof.Matric Extra.Histories Guard Jams
variable {G:Gauge}{n:Side}{ι:Type*}{B:BudgetPoint}{X:ι→Support n}{o:Site n}{p q r s t u v a b c:ℝ}
variable {S:ℕ→Support n}{d k:ℕ}{F:Labels.Frame G d}{C: SectionData F}{Y:Hol G}{R:sun→RG.Rep G n}
local notation "zr"=> Config G n→ℂ
section
-- adding general Scout algebra new for complex transfers
lemma goes_complex {f:ℝ→ℝ} (h:Scout p f q):Scout p (fun i=>(f i:ℂ)) q:=by
  obtain ⟨hp,b,hb,h⟩:=h
  refine ⟨hp,(fun i=>(b i:ℂ)),?_,fun i hi=>?_⟩; simpa only [Complex.norm_real] using hb
  refine (Complex.ofRealCLM.hasSum (h i hi)).congr_fun ?_; intro i; exact (map_smul Complex.ofRealCLM _ _).symm
lemma mult {f g:ℝ→ℂ}(h:Scout p f c) (hv:Scout p g s): Scout p (fun i=>f i*g i) (c*s):=by
  obtain ⟨hp,b,hb,hk⟩:=h; obtain ⟨r,hr,he⟩:=hv.scored
  let K {A:Type} [CommRing A] (b r:ℕ→A) n:=∑ x∈antidiagonal (n:ℕ),b x.1*r x.2
  let L (b r:ℕ→ℝ) n:=K b r n
  have hs (b r:ℕ→ℂ) (h:Summable (fun i=> ‖b i‖)) (hv:Summable (fun i=>‖r i‖)):HasSum (K b r) ((∑' i,b i)*∑' i,r i):=by
    rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm h hv]
    exact (summable_norm_sum_mul_antidiagonal_of_summable_norm h hv).of_norm.hasSum
  have ha (b r:ℕ→ℝ) (h:Summable (fun i=> ‖b i‖)) (hv:Summable (fun i=>‖r i‖)):HasSum (L b r) ((∑' i,b i)*∑' i,r i):=by
    rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm h hv]
    exact (summable_norm_sum_mul_antidiagonal_of_summable_norm h hv).of_norm.hasSum
  refine ⟨hp,K b r,?_,fun i hi=>?_⟩
  · let u n:= ‖b n‖; let v n:= ‖r n‖; have hu:0≤u:=fun _=>norm_nonneg _; have ht:0≤v:=fun _=>norm_nonneg _
    have hP := ha u v ((show Summable u from hb.2.1).norm) ((show Summable v from hr.2.1).norm)
    have hx: SumBudget (L u v) (c*s):= ⟨fun n=> Finset.sum_nonneg (fun i _=> mul_nonneg (hu _) (ht _)), hP.summable, hP.tsum_eq.trans_le (mul_le_mul hb.2.2 hr.2.2 (tsum_nonneg ht) ((tsum_nonneg (g:=u) hu).trans hb.2.2))⟩
    refine budget_mono hx (fun i=>norm_nonneg _) (fun i=>(norm_sum_le ..).trans ?_)
    unfold L K; exact (Finset.sum_le_sum fun x _=> (norm_mul ..).le)
  let z:=i/p
  let u n:= z^n • b n; let v n:= z^n • r n
  have hz: ‖z‖≤1:=ratio_le hp hi
  have h:=hs u v (at_flight z hz hb).2.1 (at_flight z hz hr).2.1
  change HasSum (fun n=> z^n • _) (f i*g i); rw [← (show HasSum u (f i) from hk _ hi).tsum_eq, ← (show HasSum v (g i) from he _ hi).tsum_eq]
  refine h.congr_fun fun n=> ?_; unfold K; rw [smul_sum]; apply sum_congr rfl; intro j hj
  dsimp only [u,v]; rw [Complex.real_smul,Complex.real_smul,Complex.real_smul,← mem_antidiagonal.mp hj,pow_add];push_cast;ring
lemma cartload {ι:Type*}(hp:1≤p)(z:Finset ι){f:ι→ℝ→ℂ}{b:ι→ℝ}(h:∀ i∈z,Scout p (f i) (b i)): Scout p (fun t=>∏ i∈z,f i t) (∏ i∈z,b i):=by
   induction z using Finset.induction_on with
   | empty=> simpa using (Scout.still hp (1:ℂ))
   | insert i T hi hv=> simp_rw [prod_insert hi]; exact mult (h _ (mem_insert_self ..)) (hv fun i hi=> h i (mem_insert_of_mem hi))
-- roll up by fibers preserve shape
lemma fanF {K:Type*}{Y:K→Support n}{f:sun→ι→ Config G n→ℂ}(hp:1≤p)(hs:0 ≤ s)(z:ι→K)(h:RollsUp B (Y∘z) f p s v):RollsUp B Y (fun t i U=> MergeProof.cram z (fun x=> f t x U) i) p s v :=by
   obtain ⟨b,hb,h⟩:= h.funds; let c i:= Real.exp (s * coverNumber B.B (Y (z i)))* b i
   have hi i:0≤ b i:= (h i 1).nonneg; let q k:=cram z b k
   have he k: Real.exp (s*coverNumber B.B (Y k))* (q k)= cram z c k:=by
      unfold q MergeProof.cram;rw [← tsum_mul_left]; apply tsum_congr; intro i;unfold c; rw [i.property]
   have hZ:Summable b:= (show Summable c from hb.2.1).of_nonneg_of_le hi (fun i=>le_mul_of_one_le_left (hi _) (Real.one_le_exp (mul_nonneg hs (by positivity))))
   have hw:= heavy z (show Summable c from hb.2.1)
   refine ⟨q,?_, fun i U=>?_⟩
   · unfold Brill; simp_rw [he]; exact ⟨fun i=> tsum_nonneg (fun j=>mul_nonneg (Real.exp_pos _).le (hi j.val)),hw.summable,hw.tsum_eq.trans_le hb.2.2⟩
   exact Scout.infinite (a:=fun j:{j//z j=i}=> b j.val) (c:=q i) ⟨fun j=>hi _,hZ.comp_injective Subtype.val_injective,le_rfl⟩ hp (fun j=>h j.val U)
lemma addsUp {f g:sun→ι→ Config G n→ℂ}{y:ι→Support n}(hf:RollsUp B y f p a q)(hg:RollsUp B y g p a s):RollsUp B y (fun i=>f i+g i) p a (q+s):=by
   obtain ⟨x,hx,hf⟩:=hf.funds; obtain ⟨y,hy,hg⟩:=hg.funds; exact ⟨x+y,br_add hx hy,fun i U=>(hf i U).pair (hg i U)⟩
end
open RG
variable (Z:Support n)
local notation "R'"=> (R tip)
local notation "β"=> B.supportExponent
variable (hh:∀ t,(R t).activities.forced=(R tip).activities.forced)(hR:∀ i,(R i).p=B)
variable (hp:1≤p)(hv:league (Local.patch (R tip).activities) B.B (fun t=>(R t).activities.K) B.supportExponent p a)
include hp hv hh
open Local
-- output trace in barcode, not individual labels. input any response f(scope) in supports, anchored already.
section terms
variable {f:sun→Response G n}(hf:RollsUp B id f p (B.supportExponent+2) b)
set_option quotPrecheck false
-- id defeq on Quote helper. Win for S flap.
local notation "Z"=> fun i:sun=>hook (R i).activities B.threshold (f i)
include hf
lemma estuary (ha:0≤a) (ht:hitWidth B*a≤1): RollsUp B Prod.fst (fun i:sun=> MergeProof.hook (R i).activities B.threshold (f i)) p (B.supportExponent) (hitWidth B*a*b):=by
  let A:= (R tip).activities; obtain ⟨x,hx,hY⟩:= hv; have he i:0 ≤ x i:= (hY i 1).nonneg
  obtain ⟨y,hy,hf⟩:= hf.funds; have hw i:0≤ y i:= (hf i 1).nonneg; let D:=Local.Letters A (fun i:Support n=>i)
  let u(v:Support n):= mergePrice B a v (y v); have hz:SumBudget u (Local.hitWidth B*a*b):=by
     apply Local.sumBudget_mono (Local.sumBudget_mul_left hy (mul_nonneg (zero_le_one.trans (width_one_le B)) ha)) (fun i=> Local.mergePrice_nonneg _ _ ha (hw _)) (fun i=> ?_) le_rfl
     exact price_meeting ha ht (hw _) i
  have hX p: SumBudget (fun i=> if p∈Local.patch A i then B.mass (Local.patch A i) (x i) else 0) a:= by
     have hh:= hx p; change SumBudget (fun i=> if p∈ _ then _ else _) a at hh
     convert hh using 2 with i;split; exact mul_comm ..; rfl
  let v (i:D):= fusionBox A i.1 i.2.val
  let t (i:D):= y i.1*∏ j∈i.2.val,x j
  let g (s:sun)(i:D)(U:Config G n):=f s i.1 U*grasp (R s).activities B.threshold i.fst i.2.val (v i) U
  have hN t i:(fun p=> Local.patch (R t).activities p) i=Local.patch A i:=by change ((R t).activities.forced i).support=_;rw [hh]
  have hP t i (s:Finset ℕ): Packs (R t).activities i s ↔ Packs A i s:=by
     have he: Local.patch (R t).activities=Local.patch A:=funext fun i=>hN t i; -- structure packs.prop not ext
     exact ⟨fun ⟨h,hp,hQ⟩=>⟨h,(by unfold Separate; rw [← he]; exact hp), fun u hu=> by rw [← he]; exact hQ u hu⟩,fun ⟨h,hp,hQ⟩=>⟨h,(by unfold Separate; rw [he]; exact hp),fun u hu=> by rw [he]; exact hQ u hu⟩⟩
  have hd(t:sun)(i:D) : fusionBox (R t).activities i.1 i.2.val=v i:=by unfold fusionBox v; unfold Local.patch Local.flagsFor; rw [hh]; rfl
  have hv' : RollsUp B (Prod.fst ∘ v) g p B.supportExponent (Local.hitWidth B*a*b):=by
     refine ⟨t,?_,fun i U=>?_⟩
     · apply Local.sumBudget_sigma (a:=u) (fun i=>?_) hz
       exact Local.packBudget i (hw i) he hX
     have hA(s:sun):g s i U=f s i.1 U*(if (v i).1∩flags B.threshold U=(v i).2 then ∏ j∈i.2.val,((R s).activities.K j U:ℂ) else 0):=by unfold g grasp; have hf:= (hP s i.1 i.2.val).2 i.2.property; rw [hd]; split_ifs <;> first| rfl| grind
     let P'(s:ℝ)(j:ℕ):ℂ:= ((R (pinch s)).activities.K j U:ℂ)
     have hY' := cartload (f:=fun j s=>P' s j) hp i.2.val (b:=x) (fun j _=> goes_complex (hY j U))
     by_cases hx:(v i).1∩flags B.threshold U=(v i).2; · exact (mult (hf i.1 U) hY').replace (fun s _=>(show g (pinch s) i U= _ from (hA _).trans (congr_arg ((f (pinch s) i.1 U)*·) (if_pos hx))).symm)
     apply Scout.replace ((Scout.still hp (0:ℂ)).enlarged ?_) (fun s hs=>?_)
     · rw [norm_zero]; exact mul_nonneg (hw _) (prod_nonneg fun j _=> he j)
     change 0=g (pinch s) i U; rw [hA,if_neg hx,mul_zero]
  have hW:= fanF hp B.exponent_pos.le v hv'
  obtain ⟨z,hZ,hG⟩:=hW.funds; refine ⟨z,hZ,fun i U=> (hG i U).replace ?_⟩
  intro s hs; let l:=pinch s; -- sum regroup. finite supp p. f.x and portion.S. Need hz σ summability
  let k (j:D):=if v j=i then g l j U else 0
  obtain ⟨e,hhx,hV⟩:= hv'.funds; have he (j:D): ‖k j‖≤ Real.exp (B.supportExponent * coverNumber B.B ((v j).1))*e j:=by
     unfold k; have h:= hV j U; have hp:= h.held l.property; rw [phrased] at hp
     split; exact hp.trans (le_mul_of_one_le_left h.nonneg (Real.one_le_exp (mul_nonneg B.exponent_pos.le (by positivity))));exact norm_zero.trans_le (hhx.1 _)
  have hK: Summable k := hhx.2.1.of_norm_bounded he
  change MergeProof.cram v (fun j=>g l j U) i= ∑ p:Support n,f l p U*MergeProof.portion (R l).activities B.threshold p i U
  rw [MergeProof.expand_eq]; change ∑' i,k i=_; rw [hK.tsum_sigma,tsum_fintype]; refine sum_congr rfl fun x _=>?_ -- support i per index.D structure abbrev recognized
  let A':=(R l).activities; let f'(z:Finset ℕ):= f l x U*grasp A' B.threshold x z i U
  have hy (j:Local.Pack A x): k ⟨x,j⟩= f' j.val:=by
       unfold k; let u':D:=⟨x,j⟩; split
       next hh=>change g l u' U=_; unfold g; change v u'=i at hh;rw [hh]
       next hh=>
         unfold f' grasp; rw [if_neg (fun h=> hh ((hd l u').symm.trans h.2.1)),mul_zero]
  simp_rw [hy]; unfold MergeProof.portion; rw [←tsum_mul_left]; exact tsum_subtype_eq_of_support_subset (s:={u|Packs A x u}) (f:=f') (by intro j hj; by_contra h; apply hj; unfold f' grasp; rw [if_neg (fun H=>h ((hP _ _ _).1 H.1)),mul_zero])
end terms
end YM.PhysicalNext.Repeat.Luna
