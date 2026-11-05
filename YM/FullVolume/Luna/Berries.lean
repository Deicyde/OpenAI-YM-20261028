import YM.FullVolume.Luna.Rings
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
-- pieces retained & rebate Hart.Field and Frame
variable {X: ℕ→Support n} {M:sun→ Push.Local.Raw F n} {A:sun→ Coefficient F n}
variable (hk:∀ i,(R i).p=B)
variable (hO:∀ i,(R i).activities.forced=(R Jams.tip).activities.forced)
variable (ht:Local.Readable Y C B n u)
variable (hs:∀ i,(M i).seed=0)
variable (hh:∀ i, ∃ T: Berths (R i).p (R i).activities (fun j=> Local.joint C 0 (X j)), A i=mint T (M i) Y)
variable {xL:F.Coeff} (hf:∀ i,Graces.Effort C (R i) Y X (M i) xL u a b v)
variable (hp:0<a)
local notation "Φ"=> Local.factor Y C B.supportExponent u
local notation "λ!"=>Extra.Histories.Motion.orbitCost F
local notation "ξ!"=> Local.turnCost B.order B.power
set_option quotPrecheck false
local notation "U₀"=> R Jams.tip
local notation "B!"=> (Real.sqrt a)
local notation "R'"=> (R Jams.tip).activities
local notation "k!"=> Local.patch (U₀).activities
variable (p0:p≥1) (hq:p<q)(T:Tableau q k) (hY:q≤r)
variable {α μ σ:ℝ}
variable (hz:Wires B 0 X (fun i=>(M i).bulk) r (B.supportExponent+2) t) (hA:RollsUp B (Local.patch (R Jams.tip).activities) (fun i=>(M i).forced) p B.supportExponent α) (hK:league (Local.patch (R tip).activities) B.B (fun i=> (R i).activities.K) B.supportExponent p μ)
variable {Ψ C₁ D E:ℝ} (hT:∀ i,(R i).Lawful Ψ C₁ D E a) (hS:∀ i, Keeper (R i).p (R i).activities) (hP:∀ i, cart (hS i)=cart (hS Jams.tip))
-- overhead in probes! genuine ℓ¹ after final graph
section hooks
local notation "n!"=> fun i=>closeK (hS i) (A i)
local notation "Z!"=> fun i=> MergeProof.coda C Y 0 X (M i) (R i)
local notation "Y!"=>fun i=> Local.joint C (0:Site n) (X i)
variable {y:ℝ} {z':sun→Support n→ Config G n→ℂ}
include hk hO hT hp
include hf ht hh
include p0 hq hY hz
omit hT in
lemma prev : Wires B 0 (fun i=> Local.joint C 0 (X i)) (fun t=> (A t).regular) p (B.supportExponent+2) (Φ*(T.price*(v/(ξ! *Φ))+T.liftT r*t)) ∧ RollsUp B id (fun i=> MergeProof.coda C Y 0 X (M i) (R i)) p (B.supportExponent+2) ((1-p/q)⁻¹*(Φ *(T.price*(v/(ξ! *Φ))+T.liftT r*t))):= by
    have hr t i:B.Regular (X i) ((M t).bulk i):=hk t ▸ (hf t).choose_spec.choose_spec.choose_spec.1.regular i
    obtain ⟨h,hY⟩:= descent hk ht hh (fun i=> (hf i).choose_spec.choose_spec.choose_spec.1) (hz.squeeze T hY (fun z=> (upright hk ht hh hf hp z).2.1) hr) p0 hq
    refine ⟨h,?_⟩
    have hx:= fanF (Y:=id) p0 (add_nonneg B.exponent_pos.le (by norm_num : (0:ℝ)≤2)) (fun i=> Local.joint C (0:Site n) (X i)) hY
    have hW i j V: coda C Y 0 X (M i) (R i) j V= cram (Y!) (fun x=> Flames Y C B X M i x V) j:=by unfold MergeProof.coda; rw [hk]; rfl
    obtain ⟨a,ha,hU⟩:= hx.funds; exact ⟨a,ha,fun i U=> by simp_rw [hW]; exact hU i U⟩
omit hz hY hq
include hA hK
lemma halos (h : RollsUp B id (fun i=> MergeProof.coda C Y 0 X (M i) (R i)) p (B.supportExponent+2) y)(h₁:0≤μ)(h₂:Local.hitWidth B*μ≤1):RollsUp B Prod.fst (fun i=> profile (R i).activities (A i).forced) p B.supportExponent (α+Local.hitWidth B*μ*y):=by
    let uQ i:=MergeProof.profile (R i).activities (M i).forced; let f:=barcode R'; let s i:= MergeProof.hook (R i).activities B.threshold (Z! i)
    have hg i:MergeProof.profile (R i).activities (A i).forced= uQ i+s i:=by
        obtain ⟨T,hT'⟩:= hh i; obtain ⟨q,r,v,hp',ht',-⟩:= hf i
        rw [hT']; have he:= budgetProfile T ht' hp' (hk i ▸ ht : Local.Readable Y C (R i).p n u) (hT i) (Real.sqrt_pos.mpr hp); -- u shadows
        rw [he];change uQ i+MergeProof.hook _ (R i).p.threshold _=uQ i+s i; refine congr_arg (fun x=>uQ i+MergeProof.hook (R i).activities x (Z! i)) (?_); rw [hk]
    have he : RollsUp B Prod.fst uQ p B.supportExponent α:=by
        have ha:= fanF (Y:=Prod.fst) p0 B.exponent_pos.le f hA; obtain ⟨z,hz,hZ⟩:= ha.funds
        have hh (i):barcode (R i).activities= f:=by unfold barcode; rw [hO]; rfl
        unfold uQ MergeProof.profile; simp_rw [hh];exact ⟨z,hz,hZ⟩
    simp_rw [hg]; exact addsUp he (estuary hO p0 hK h h₁ h₂)
end hooks
section stock
include hk
lemma stoked (k:ℝ)(y:ℝ)(ha:1≤k)(hP:∀ i, cart (hS i)= cart (hS tip))(h:RollsUp B Prod.fst (fun i=> MergeProof.profile (R i).activities (A i).forced) k B.supportExponent y):RollsUp B (Local.patch (R tip).activities) (fun i=> (closeK (hS i) (A i)).2.2) k B.supportExponent y:=by
   let e:=cart (hS tip); let f:=Local.patch R'
   obtain ⟨r,hr,hC⟩:= h.funds; let x:=extend e (fun i=>r i.val) 0; have hz p:x (e p)=r p.val:=e.injective.extend_apply ..; have ha' i (hi:i∉Set.range e):x i=0:=extend_apply' _ _ _ hi
   have he k:f (e k)= k.val.fst:=congr_arg Prod.fst (cardK (hS tip) k)
   refine ⟨x,?_,fun i U=>?_⟩
   · apply Local.sumBudget_pass e
     · change SumBudget (fun i=> Real.exp (B.supportExponent*coverNumber B.B (f (e i)))*x (e i)) y
       simp_rw [he,hz]; exact Local.sumBudget_subtype _ hr
     intro i hi; rw [ha' _ hi,mul_zero]
   let φ j:= (closeK (hS j) (A j)).2.2
   by_cases hh:i∈Set.range e
   · obtain ⟨i,rfl⟩:=hh; rw [hz]; have hp j:φ j (e i)= MergeProof.profile (R j).activities (A j).forced i.val:=by rw [show e= _ from (hP j).symm]; exact stowed ..
     change Scout k (phraseS fun j=> φ j _ U) _; simp_rw [hp];exact hC _ _
   rw [ha' _ hh]; have h(j): φ j i=0:= MergeProof.pit _ _ (by rw [hP j]; exact hh); change Scout k (phraseS fun j=> φ j i U) _; simp_rw [h];exact (Scout.still ha (0:ℂ)).enlarged norm_zero.le
omit hk
lemma costEd (hc:∀ z, (A z).support=(A tip).support)(he:(A tip).Format 0 Y (U₀))(hr : Wires B 0 (A tip).support (fun i=>(A i).regular) p q r): Wires B 0 (mapSeat) (fun i=>(closeK (hS i) (A i)).2.1) p q r:=by
   let e:=Matric.tongue (A tip).support
   obtain ⟨x,hx,hv,hQ⟩:= hr.lamps
   let y:=extend e x 0; have hy p:y (e p)=x p:=e.injective.extend_apply ..; have ha' i (hi:i∉Set.range e):y i=0:=extend_apply' _ _ _ hi; have he i:mapSeat (e i)=(A tip).support i:=Matric.leased _ he _
   let z(i):=(closeK (hS i) (A i)).2.1; have ha t i:z t i=extend e (A t).regular 0 i:=by change liveE (A t) i=_; unfold liveE; rw [hc]
   refine ⟨y,?_,fun i=> ?_,fun i w η hp=>?_⟩
   · apply Local.sumBudget_pass e
     · change SumBudget (fun i=> _*y (e i)) _; simp_rw [he,hy]; exact hx
     intro i hi; rw [ha' i hi,mul_zero]
   · by_cases h:i∈ Set.range e; obtain ⟨i,rfl⟩:=h; rw [hy]; exact hv _
     rw [ha' _ h]
   change B.supBounds 0 _ (mix w (fun t=> z t i)) _; simp_rw [ha]; by_cases h:i∈Set.range e; obtain ⟨i,rfl⟩:=h; rw [hy,he];simp_rw [e.injective.extend_apply]; exact hQ _ _ _ hp
   simp_rw [ha' _ h,extend_apply' _ _ _ h,Pi.zero_apply,mul_zero]; rw [show mix w _=(0:Config G n→ℂ) from mix_z _]; exact (regular0 ..).2
end stock
include hk ht hh hs hf hz hA hK p0 hO hT hp hq hY hP
lemma confect (ht': Local.hitWidth B*μ ≤ 1):let y:= T.price*(v/(ξ! *Φ))+T.liftT r*t; let z:= (1-p/q)⁻¹*(Φ*y); let U: sun→ Pin F n:=fun i=>closeK (hS i) (A i)
    (∀ z:Rung,∀ η,Stripe z q η→ λ! * F.coeffSize (mix z fun i=> (U i).1-xL) ≤ η*(T.price*b+T.liftT r*(λ! *(Φ*t)))) ∧ Wires B 0 mapSeat (fun i=>(U i).2.1) p (B.supportExponent+2) (Φ*y) ∧ RollsUp B (Local.patch (R tip).activities) (fun i=>(U i).2.2) p B.supportExponent (α+Local.hitWidth B*μ*z) ∧ RollsUp B id (fun i=> MergeProof.coda C Y 0 X (M i) (R i)) p (B.supportExponent+2) z :=by
   intro y z U; have hr : ∀ i, (A i).support=(fun j=> Local.joint C 0 (X j)):=by intro i; obtain ⟨T,hT⟩:=hh i; rw [hT]; rfl
   have he : (A tip).Format 0 Y (U₀):= by obtain ⟨T,hT'⟩:=hh tip; rw [hT']; exact usage T ((hf tip).choose_spec.choose_spec.choose_spec.1) (hT _) (hk tip ▸ ht)
   have hm:= muscles hk ht hh hs hf hp T hY hz
   obtain ⟨hy,H⟩:=prev hk hO ht hh hf hp p0 hq T hY hz; have hκ:=halos hk hO ht hh hf hp p0 hA hK hT H (budget_nonneg (hK.choose_spec.1 (0:Site n))) ht'
   exact ⟨hm,costEd hS (fun i=>(hr i).trans (hr tip).symm) he ((hr tip).symm ▸ hy),stoked hk hS p _ p0 hP hκ,H⟩
end YM.PhysicalNext.Repeat.Luna
