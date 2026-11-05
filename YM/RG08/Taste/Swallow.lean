import YM.RG08.Taste.Counter
/-!
# Kforms top W, matched stencil and rate paid in the SAME clock
including arbitrary $q$ powers. Normalize offshell. State at both cutoffs to reuse in other tests.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.RG08.Taste
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Pill Matrix PowerSeries Drift Pivot
open scoped BigOperators Topology Real ContDiff
open Wings Summit
variable {I J W:Type} {u:I→Windows}{w:J→ShoreP u}{X:Chain}{G:Gauge}{E e r d τ D j t n k m l :ℕ}{R:ℝ}{F:Labels.Frame G d}{Ω:SectionData F}{ν:G.ColorIndex}{D':ChartRatio G}{H:Hol G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}
variable {h:1/2≤R}{hD:d+1≤D} {T:Signals P Q E τ H Ω h hD}{T':Aperture G P k E τ d D R}{U V:J→ BoardU D R G} {p q:J→ℝ}
section fiscal
variable {A B:W→ Row (Loc G 1) (Loc G 1)}{U V:W→ EnvelopeU D R G (r+2)}{Y Z: W→Loft F}{M N:W → Letter F→ ℝ}{C δ ρ y p: W→ℝ}
lemma offer_jib (hP: ∀ i,Plaque (A i) (C i*p i))(hp:Weighed y C)(hu:Card k y ρ U 1): Card k y (p*ρ) (fun i=>jib none (A i) (U i)) 1 := by
    obtain ⟨B,hB,H⟩:=hu.money; refine ⟨_,(Weighed.constant y (norm_nonneg (batting r))).times (hp.times hB),fun i=>?_⟩
    simp only [Pi.mul_apply]; rw [show _*(C i*B i)*(p i*ρ i)=‖batting r‖*((C i*p i)*(B i*ρ i)) by ring]
    apply sew_cis _ zero_le_one; apply Ink.scale; apply Ink.pour _ _ (tailp zero_le_one); apply budget_mono (budget_scale (hP i|>.1) (H i)) (fun i=> mul_nonneg (zero_le_one.trans (tailp zero_le_one _)) (norm_nonneg _))
    intro z; rw [mul_comm (C i*p i)]; change tailP k 1 (stems z) * ‖tuneS (A i) none z • U i z‖ ≤ _; rw [norm_smul]; refine (mul_le_mul ?_ (mul_le_mul_of_nonneg_right ((hP i).2 ..) (norm_nonneg _)) (by positivity) (zero_le_one.trans (tailp (k:=k) zero_le_one z))).trans_eq ?_
    · simp only [tailP,  one_mul]; gcongr; exact (stems_le (stem1 z)).trans (stems_le z)
    change tailP k 1 z * _= (tailP k 1 z * _)*_; ring
lemma twix (hA : ∀ i,Plaque (A i) (C i))(hB:∀ i,Plaque (B i) (C i))(hM:∀ i,Plaque (A i-B i) (C i*δ i))(he:Weighed y C)(hP:Audience y)(hU:Drum k y δ ρ U V 1) : Drum k y δ ρ (fun i=>jib none (A i) (U i)) (fun i=>jib none (B i) (V i)) 1:= by
    have hh i: Plaque (A i) (C i*(1:W→ℝ) i):= by rw [Pi.one_apply,mul_one]; exact hA _
    have hz i: Plaque (B i) (C i*(1:W→ℝ) i):=by rw [Pi.one_apply,mul_one]; exact hB _
    refine ⟨by simpa only [one_mul] using offer_jib hh he hU.first,by simpa only [one_mul] using offer_jib hz he hU.second,?_⟩
    let M i:= jib none (A i) ((U-V) i); let N i:=jib none (A i-B i) (V i); rw [show _-_ = M+N from funext fun i=>?_]; swap
    · simp only [Pi.sub_apply,Pi.add_apply,M,N,phil_less (hA i) (hU.first.even zero_le_one i) (hU.second.even zero_le_one i),phil_bet (hU.second.even zero_le_one i) (hA i) (hB i)]; abel
    have hp:= offer_jib hh he hU.funds; rw [one_mul] at hp; exact hp.more (offer_jib (A:=A-B) hM he hU.second) zero_le_one hP
lemma draw (h:Lying y δ Y Z)(hx:∀ a,Tonic y ρ δ (fun i=> M i a) (fun i=> N i a))(hT:Audience y)(hp:0 ≤ δ)(hP:0≤ρ)(a:Letter F): Tonic y ρ δ (fun i=> (Y i *ᵥ M i) a) (fun i=> (Z i *ᵥ N i) a) := by unfold mulVec dotProduct; exact Tonic.sums _ (fun j _=> (hx j).timesL (h a j) hT hP hp) hT
end fiscal
section
variable (he:Tights T S ν D' u)(b:Offer w) (hU:∀ i,Marvel τ (U i))(ht:∀ i,Lank (U i))
local notation "𝕍" => remnant ν D' T b U
include he hU ht
lemma vol_p (i:Wall w 0): Marvel τ (𝕍 i)∧Lank (𝕍 i):= by
   have hp:= (barriers ν D' T b U he hU ht).zone i; obtain ⟨hT,H⟩:=edge_crew (phase0 ν D' T b i) (offerUp ν D' T b U i) (he.firs _|>.toBoards) he.hh; unfold remnant; rw [sub_eq_add_neg,←neg_one_smul ℝ]; exact ⟨choir_plus hp.hU (choir_weight hT _), lank_add hp.paid (lank_wt H _)⟩
lemma v_pot (i:Wall w 0): let Y i:= vCook b T i (𝕍 i)
    Y i = (breathP ν D' T b i) *ᵥ Y (foothold i):= by intro Y; refine skit_b ν D' T b i he (fun i=> ?_); unfold Y; rw [v_steps ν D' T b U i he hU ht]; exact vCook_tex ν D' T b i _ (vol_p he b hU ht i.roof|>.1) (vol_p he b hU ht i.roof|>.2) he -- arg order?
omit he hU ht in
lemma vCook_cut (N i)(U V:BoardU D R G)(hp:Marvel τ U)(he:Marvel τ V)(hu:Lank U)(hv:Lank V): upside (U-V) (fires X G N i) τ H F = upside U (fires X G N i) τ H F-upside V (fires X G N i) τ H F:= by
    let M:= fires X G N i; obtain ⟨B,_,P⟩:= portion G X.kernel.penalty_pos (X.adm i)
    have hP:Plaque M B:= P _|>.1; ext1 j
    let g (U:BoardU D R G):= frisk M (U 0) τ (slot j)
    change invest H (g (U-V)) j=invest H (g U) j-invest H (g V) j
    have hX (U:BoardU D R G)(h:Marvel τ U): Toute (g U):= (show Gold (g U) from gold_sum fun i _=> golden_terraces X.kernel.penalty_pos (X.adm _) (W:=U 0) (fun _=> sober_vetted h) ..).toToute
    rw [show g (U-V)=g U-g V from (Finset.sum_congr rfl fun i _=> wick_more (hp.hem 0) (he.hem 0) hP i (slot j)).trans (Finset.sum_sub_distrib _ _)]
    exact Pivot.invest_less H j (polished_sum (fun i _=>pol_front hP (hu 0) i _)) (polished_sum (fun i _=>pol_front hP (hv 0) i _)) (hX U hp) (hX _ he)
omit hU ht in
lemma vCook_basis (i: Wall w 0)(V:Native (Letter F)): vCook b T i (edgeBook (phase0 ν D' T b i) V)=oven X ν D' H Ω (d.le_succ.trans hD) h (b.N i.a) i.i *ᵥ (fun j=>coeff 0 (V j)):= by
    let z := b.part i; let B: Session (Letter F):= Matrix.of fun j _=> V j; let P:=edgeBook (phase0 ν D' T b i) V
    have ht:= he.firs z; have hP:= edge_crew _ V ht.toBoards (le_refl d)
    funext j; let M:= fires X G z.N z.i
    obtain ⟨A,_,g⟩:= portion G X.kernel.penalty_pos (X.adm z.i)
    change invest H (frisk M (P 0) τ (slot j)) j= _
    rw [← wick_carry (U:=P 0) (fun i hi=> not_ne_iff.mp (mt (hP.1.cap 0 i) (by omega))) (M:=M) (g _|>.1) he.hh]
    exact flare_out (M:=B) j j ht X.kernel.penalty_pos (X.adm z.i) (X.history z.N z.i)
end
end YM.RG08.Taste
