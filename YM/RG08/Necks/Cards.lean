import YM.RG08.Necks.Jade
/-! # Independent one-step with reset. Oracle assembled later from normalized end-cut data.
 Emits Y fore and leak and assesses dual. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Necks
open Forms Function Finset Jetty Lattice Isles Pert.Bulk Stationary Spar Camera Glyph Filter Laurent RG Precision Exterior Skiff Trickle Weald Hatch Carrel Quarry Steam
open Planned.PrimaryIntegral295 Place Film Labels Source Source.Drops WardBin Parts Flint Lagoon Yurt Next.Free Atrium Trill Clef
open scoped Classical ContDiff BigOperators Topology ENNReal
variable {G:Gauge}{n m d p l e k c:ℕ}{σ τ μ V Q B C δ η a b W:ℝ}{P:Patch}{K:KernelChoices}
local notation "A"=>Loc G 1
local notation "E"=> Ed G Cover
-- Independent data already pinned as part of unmarked step.
structure Crew (G:Gauge)(P:Patch)(K:KernelChoices) where
 fine : Bed
 behind:Bed
 diff : P.Branches K G
 champ : Mount.Castle G
 ratio : ChartRatio G
 wake : ℕ→ℝ
 agree : Foyer P K fine behind champ ratio
namespace Crew
def move (T:Crew G P K):=Mount.inlet T.diff T.champ T.ratio
def house (T:Crew G P K)(d l:ℕ)(X:GrainS E):=Lagoon.bustle P K T.fine T.champ T.ratio T.diff d l X
def cast (T:Crew G P K)(d:ℕ)(X:GrainS E):=Yurt.forecast P K T.fine X d
def gift (T:Crew G P K)(d l:ℕ)(X:GrainS E):= scene P K T.diff T.fine T.champ T.ratio d l X
def land (T:Crew G P K)(d l:ℕ)(X:GrainS E):= Clef.film T.wake (T.house d l X)
lemma living (T:Crew G P K){d l:ℕ}(D:ℕ)(X:GrainS E)(hx:Folk D l X): Folk D l (T.land d l X):=by obtain ⟨h,k⟩:=Lagoon.Lobby P K T.fine T.behind T.champ T.ratio T.diff T.agree d X hx.inlet hx.outlet T.wake; exact ⟨h,k⟩
def string (T:Crew G P K)(d l:ℕ)(X:GrainS E)(e n:ℕ):Pack n E:= T.gift d l X e n+ ∑ i∈range e,Nacre.dues T.wake i n e • T.house d l X i n
end Crew

structure Warmth (η δ W:ℝ)(e n d:ℕ)(C T:Crew G P K):Prop where
 hR:C.ratio=T.ratio
 tooth : Sepals G P K η W δ C.fine T.fine C.move T.move e
 glow:(P.L.val:ℝ)^d≤ W
 reset (i j r:ℕ):i ≤ e → j < i →  r ≤n → |Nacre.dues C.wake j r i| ≤ W∧|Nacre.dues T.wake j r i|≤ W∧|Nacre.dues C.wake j r i-Nacre.dues T.wake j r i|≤W*δ
-- Sings cameras across all strict positions earlier & throughput for this n before brim. supply common at finer height τ meeting consumer h.
variable {Q R: Crew G P K}
lemma Warmth.prices (he:Warmth η δ W e n d Q R){i r:ℕ}(hi:i≤e)(hr:r≤n):Warmth η δ W i r d Q R:=⟨he.hR,by have hh:=he.tooth; unfold Crew.move at *; rw [←he.hR] at hh ⊢;exact shrunk hh hi,he.glow,fun j k c hk ht hv=>he.reset _ _ _ (hk.trans hi) ht (hv.trans hr)⟩
-- paired strict. **B0** for n=e target. arbitrary Qual volume. earlier & throughput.
lemma portFee (n e l:ℕ):∃ J:ℝ→ℝ,Wage J ∧ ∀ {G:Gauge}{P:Patch}{K:KernelChoices}{Q R:Crew G P K}{σ η W δ:ℝ}{D d:ℕ},Warmth η δ W e n d Q R → ∀{S S':GrainS (Ed G Cover)}(hk:0<η),η≤1→∀{h:0<σ},η*Carrier.unitStep P.L≤σ→∀{B T:ℝ},0≤B→0≤T→Folk D l S→Folk D l S'→
   (∀ i r,r≤l+i→(i<e∨i=e∧n<r)→ Dyad (stance _) D h B δ (S i r) (S' i r))→ Dyad (stance _) D h T δ (S e n) (S' e n) →
 let U:=Q.cast d S e n;let U':=R.cast d S' e n
 let M:=Q.land d l S e n;let M':=R.land d l S' e n
 let N:=Q.string d l S e n;let N':=R.string d l S' e n
 let x:=Q.cast d S' e n
 ; Dyad (stance _) D hk (J W*T) δ U U' ∧ Dyad (stance _) D hk (J W*B) δ N N' ∧ M=U+N ∧ M'=U'+N' ∧ U-x=Q.cast d (S-S') e n ∧ Sings (stance _) D hk (x-U') (J W*T*δ):=by
 choose c hc H using fun i=> stress_price n i l
 let L(r:ℝ):= c e r +∑ i∈range e,2*r*(2*c i r)
 refine ⟨L,(hc e).add (Wage.sum _ _ (fun i _=>(((Wage.constant 2 (by norm_num)).mul Wage.input).mul ((Wage.constant 2 (by norm_num)).mul (hc i))))),?_⟩
 intro G P K Q R σ η W δ D d hw S S' hk hx h ht B T hB hT hF hF' hv hV u u' M M' N N' x
 have hδ:=hw.tooth.gift;have hW:0≤W:=zero_le_one.trans hw.tooth.base
 have hu(i):0≤ c i W:=(hc i).nn hw.tooth.base
 have h₀:c e W≤L W:=le_add_of_nonneg_right (Finset.sum_nonneg fun i _=>by have h:=hu i; positivity)
 have he(i:ℕ)(hi:i<e):Dyad (stance _) D hk ((2*c i W)*B) δ (Q.house d l S i n) (R.house d l S' i n):=by
    -- Q & R diff branch may NOT same hp definition! P.Branches type is Prop? verify.
    have hr:= (hw.prices hi.le le_rfl).tooth
    unfold Crew.move at hr;rw [←hw.hR] at hr
    have hY:Dyad (stance _) D h B δ (S i n) (S' i n):=by
       by_cases hn:n≤l+i;exact hv i _ hn (Or.inl hi)
       rw [show S i n=0 from Classical.not_not.mp (fun he=>hn (hF.inlet.lit i n he)),show S' i n=0 from Classical.not_not.mp (fun he=>hn (hF'.inlet.lit i n he))];exact (Dyad.zero hδ).mono hB
    obtain ⟨h0,h1,h2,h3,-⟩:=H i hr hk hx ht hB hB hF hF' (fun a r hz hp=>hv a r hz (by omega)) hY hw.glow
    unfold Crew.house;rw [←hw.hR,h2,h3]; exact (h0.add h1).mono (le_of_eq (by ring))
 have hR:=hw.tooth; unfold Crew.move at hR;rw [←hw.hR] at hR
 obtain ⟨h0,h1,h2,h3,hu',ht'⟩:= H e hR hk hx ht hB hT hF hF' hv hV hw.glow
 have hU: u=(Yurt.forecast P K Q.fine S d) e n:=rfl;have hO:=show u'=Yurt.forecast P K R.fine S' d e n from rfl
 have hT':c e W*T≤ L W*T:=by gcongr
 have hx(i:ℕ)(hi:i∈range e):= (he i (mem_range.mp hi)).livery (hw.reset e i n le_rfl (mem_range.mp hi) le_rfl).1 (hw.reset _ _ _ le_rfl (mem_range.mp hi) le_rfl).2.1 (hw.reset _ _ _ le_rfl (mem_range.mp hi) le_rfl).2.2
 refine ⟨h0.mono hT', ?_, ?_, ?_, hu',ht'.mono le_rfl le_rfl (fun _=>le_rfl) (mul_le_mul_of_nonneg_right hT' hδ) ⟩
 · unfold N N' Crew.string; unfold Crew.gift; rw [←hw.hR]
   apply (h1.add (Dyad.sum (range e) (C:=fun i=> 2*W*((2*c i W)*B)) hx hδ)).mono
   unfold L;apply le_of_eq;rw [add_mul,sum_mul];congr 1;apply sum_congr rfl;intro i _;ring
 · unfold M Crew.land Clef.film N Crew.string Crew.gift;rw [sum_range_succ,Nacre.due_self,one_smul,add_comm, Crew.house,h2,add_assoc];rfl -- unification rfl?
 unfold M' Crew.land Clef.film N' Crew.string Crew.gift;rw [sum_range_succ,Nacre.due_self,one_smul,add_comm, Crew.house,←hw.hR,h3,add_assoc];rfl
end YM.RG08.Necks
