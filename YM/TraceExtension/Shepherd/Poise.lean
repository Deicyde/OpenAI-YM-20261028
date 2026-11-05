import YM.TraceExtension.Shepherd.Purse
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Trace.Shepherd
open RG Wilson Lattice Source AnalyticBridge VerifiedReset Finset Ac MergeProof Cask Function Pressure Next.Fluctuations PathData Extra.Iteration Push.AbsoluteSums Extra.Multi StressFlux MeasureTheory
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical ContDiff
variable {G:Gauge}{n:Side} (R:Rep G n)(x:Site n)(d:Step)
local notation "X"=> Config G n
local notation "θ"=> R.p.threshold
def stunt (v:G.El→ G.El)(U:Config G n)(j:G.El):= StressFlux.modify x d (v j) U
def field (m:ℕ)(U:X):= R.v*Fintype.card (Site n)+∑ i : {p:Support n//coverNumber R.p.B p  ≤  m}, stockC R i.val U
lemma crewField {σ A v δ u:ℝ}(hp:R.Lawful σ A v δ u)(H:Geo.Width R.p R.clip σ)(m:ℕ)(U:X): R.exponent U= field R m U+∑ i:SheetL R m, stockC R i.val U:=by
    rw [shores R hp H U,field,add_assoc]; refine congr_arg₂ (· + ·) rfl ?_; let a(p:Support n):=coverNumber R.p.B p  ≤  m; have hh(j:Support n):¬ a j ↔ m < coverNumber R.p.B j:=not_le
    -- avoid inst precision
    let Y:= Equiv.subtypeEquivRight hh; rw [← Y.sum_comp (fun i:SheetL R m=> stockC R i.val U)]; exact (Fintype.sum_subtype_add_sum_subtype a _).symm
variable {σ A v δ u:ℝ}(h:R.Lawful σ A v δ u)(H:Geo.Width R.p R.clip σ)(hv:WilsonStartup.Decent R.clip R.p)(he:4 ≤ R.p.supportExponent) (m:ℕ)
include h
lemma crew_pull (s:Seat n) : field R m ∘ s.view=field R m:=by
    let F(P: Support n):=s.spread P; have hx: Injective F:=image_injective (f:=affine s.1 s.2) (fun _ _ hz=> s.1.act_injective (add_right_cancel hz)); let Q:={p:Support n//coverNumber R.p.B p  ≤  m}; have hp(p : Support n) : coverNumber R.p.B (F p)=coverNumber R.p.B p:= Seat.visit_count (p:=R.p) ..; let f(i:Q): Q:= ⟨F i.val,(hp _).symm ▸ i.property⟩; have ht: Injective f:=fun i j he=>Subtype.ext (hx (show F i.val=F j.val from congr_arg Subtype.val he))
    funext U; unfold field; simp only[Function.comp_apply]; refine congr_arg₂ (· + ·) rfl ?_; let e:= Equiv.ofBijective f ⟨ht,Finite.injective_iff_surjective.mp ht⟩
    exact Fintype.sum_equiv e _ _ (fun i=> congr_fun (stock_turn R h _ _) _|>.symm)
include H hv he
lemma floated (P:Support n):Envelope (stockC R P):=by
   obtain ⟨b,hb,ht⟩:= cans R h H (by linarith); exact ⟨(stock_pay R h _ hv).1,_,fun i=> (hb P).2 i⟩
lemma froth : Envelope (field R m):= Envelope.add (Envelope.const _) (Envelope.sum univ (fun p:{p:Support n//coverNumber R.p.B p ≤  m}=>stockC R p.val) (fun i=> floated R h H hv he _))
variable (J:Config G n→ G.El →ℂ)(ν:G.El→ G.El)
def spur (U:X)(j:G.El):= J (stunt x d ν U j) j
def aura (U:X)(j:G.El):ℝ:= field R m (stunt x d ν U j)-field R m U
def rink (U:X)(j:G.El):ℂ:= spur x d J ν U j*(Real.exp (aura R x d m ν U j):ℂ)
abbrev SBook (P:Support n):= x∈P∧coverNumber R.p.B P ≤  m
abbrev EBook:= {P:Support n//SBook R x m P}
def trio (i:EBook R x m)(U:X)(j:G.El):ℂ:= if spur x d J ν U j = 0 then 0 else ↑(Real.exp (stockC R i.val (stunt x d ν U j)-stockC R i.val U)-1)
def braid (p:Finset (EBook R x m))(U:X)(j:G.El):ℂ:= spur x d J ν U j* ∏ i∈p,trio R x d m J ν i U j
structure ProofC (P:Support n)(D:ℝ):Prop where
   env : Envelope (Function.uncurry J)
   eye j: LocalOn P (fun U=> J U j)
   gear (g:Site n→G.El) U j: J (Lattice.gauge g U) (g x*j)=J U j
   charm U j:J U j ≠0 → Healthy (R.p.threshold/4) {x} U
   turns i j: ν (i*j) = i*ν j*i⁻¹
   price (j):G.chord (ν j) ≤ D
   less : 8*D ≤ R.p.threshold
   borel : Measurable ν
variable {P:Support n}{D:ℝ}
variable (w: ProofC R x J ν P D)
include w
lemma actsD (U:X) (j:G.El)(hx: spur x d J ν U j ≠ 0): flags θ (stunt x d ν U j)=flags θ U∧ Brink R D U (stunt x d ν U j):= by
   obtain ⟨hp,h⟩:= smallC x d (ν j) R D (w.price j) w.less U (w.charm _ _ hx); exact ⟨hp.symm,h⟩
omit H he
lemma fills (U:X) (j:G.El): (∑ v : Finset (EBook R x m), braid R x d m J ν v U j)= rink R x d m J ν U j:=by
   by_cases hx:spur x d J ν U j=0
   · simp[rink,hx,braid]
   have hz:= (smallC x d (ν j) R D (w.price j) w.less U (w.charm _ _ hx)).1
   let W:= stunt x d ν U j; let q(P:Support n):= stockC R P W-stockC R P U
   have hδ: aura R x d m ν U j=∑ i:EBook R x m,q i.val:=by
       unfold aura field; rw[add_sub_add_left_eq_sub,← sum_sub_distrib]; let s:={p:Support n// coverNumber R.p.B p ≤  m}; let f:=fun p:s=>q p.val
       let e(i:EBook R x m):s:=⟨i.val,i.property.2⟩
       change ∑ i:s,f i=_; rw [← sum_subset (subset_univ (univ.image e)) ?_,sum_image]; rotate_left
       · intro p _ hp; have hu : x ∉ p.val:= fun h=> hp (mem_image.mpr ⟨⟨_,h,p.property⟩,mem_univ _,Subtype.ext rfl⟩); apply sub_eq_zero.mpr; symm; exact (stock_pay R h p.val hv).2.2 _ _ (modify_off x d _ p.val U hu) (congr_arg (p.val∩·) hz)
       · exact (show Injective e from fun i j hh=>Subtype.ext (congr_arg (fun i:s=>i.val) hh)).injOn
   unfold braid; rw [← mul_sum,← Finset.powerset_univ,←prod_one_add,rink,hδ,Real.exp_sum,Complex.ofReal_prod]; refine congr_arg (_ *·) (prod_congr rfl (fun p _=>?_)); unfold trio; rw [if_neg hx]; unfold q W; push_cast; ring
end YM.Trace.Shepherd
