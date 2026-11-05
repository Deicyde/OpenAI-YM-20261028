import YM.TraceExtension.Shepherd.Stack
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Trace.Shepherd
open RG Wilson Gauge Lattice Source AnalyticBridge VerifiedReset Finset Ac MergeProof Cask Function Pressure Next.Fluctuations PathData Extra.Iteration Push.AbsoluteSums Extra.Multi
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical ContDiff
variable {G:Gauge}{n:Side}(R:Rep G n)
local notation "W!"=> R.path
local notation "b!"=> R.p.threshold
local notation "M!"=> R.p.B
local notation "d!"=> R.p.supportExponent
variable {σ A v δ t:ℝ}(h:R.Lawful σ A v δ t)(H:Geo.Width R.p R.clip σ)
lemma sloop (t:Barley): 0∈ fort R t:=by
    rcases t with a|i
    · exact a.small_home ..
    apply mem_image.mpr; exact ⟨0,mem_insert_self ..,by simp⟩
lemma rawHit {F:Barley→ℝ}{u:ℝ}(he:∀ i,0 ≤ F i)(hx:SumBudget (fun i=> F i * Real.exp (d!*coverNumber M! (fort R i))) u): Hit (boothC R ∘ Sum.inl) M! (fun i:Seat n × Barley=> VerifiedReset.factor*F i.2) (d!-1) (Fintype.card Signed * siteFactor M! * (VerifiedReset.factor*u)):=by
   let g(x:Seat n):= x.2; let q(i:Seat n×Barley):Finset (Seat n) := {i.1}
   have hp:Occupancy g (Fintype.card Signed):=by
      intro i; refine le_trans (card_le_card_of_injOn (t:=@univ Signed _) Prod.fst ?_ ?_) (by rw [card_univ])
      · exact fun j _=> mem_univ _
      intro j hj k hk he; exact Prod.ext he ((mem_filter.mp hj).2.trans (mem_filter.mp hk).2.symm)
   apply root_hit (mode:=q) hp (fun i=>mul_nonneg VerifiedReset.factor_pos.le (he i.2)) (mul_nonneg VerifiedReset.factor_pos.le ((tsum_nonneg hx.1).trans hx.2.2)) (fun p _=>⟨p.1,mem_singleton_self _,?_⟩); swap
   · change p.1.2 ∈ Seat.spread p.1 (fort R p.2); exact p.1.reg _ (sloop R p.2)|>.anchor
   intro x; let v(y:Seat n×Barley):= if x∈q y then Real.exp ((d!-1+1)*coverNumber M! (boothC R (.inl y)))*(VerifiedReset.factor*F y.2) else 0; let f(i:Barley):= VerifiedReset.factor*(F i* Real.exp (d!*coverNumber M! (fort R i)))
   have ht': SumBudget f (VerifiedReset.factor*u):= budget_scale VerifiedReset.factor_pos.le hx
   have ht:∀ i:Barley,v (x,i)= f i:= by
      intro i; unfold v; simp only[sub_add_cancel]; rw [if_pos (show _ from mem_singleton_self x)]; unfold f; rw [show boothC R (.inl (x,i))= Seat.spread x (fort R i) from rfl,Seat.visit_count]; ring
   convert! (show SumBudget v (factor*u) from ?_) using 1
   · funext i; dsimp only[comp_apply,v]; split_ifs<;>rfl
   refine Budget.certify (fun i=> ?_) (fun s=>?_)
   · change 0 ≤ v i; unfold v; split; exact mul_nonneg (Real.exp_pos _).le (mul_nonneg VerifiedReset.factor_pos.le (he _));exact le_rfl
   let z:=s.filter (fun i:Seat n × Barley=> i.1=x); calc
     _ = ∑ i∈ z,v i:=by apply Eq.symm; refine Finset.sum_subset (filter_subset ..) ?_ ; intro i hi h; exact (show v i=0 from if_neg (fun he=> h (mem_filter.mpr ⟨hi,(mem_singleton.mp he).symm⟩)))
     _ = ∑ i∈ z.image Prod.snd,f i:=by
       rw [sum_image]; refine sum_congr rfl (fun i hi => by obtain ⟨j,t⟩:=i; obtain rfl:= (mem_filter.mp hi).2; exact ht t)
       exact fun i hi j hj he=> Prod.ext ((mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm) he
     _ ≤ _:=Budget.cap ht' _
lemma regHit {F:ℕ→ℝ}{u:ℝ} (hs:R.activities.EBound R.p u)(he:∀ i,0 ≤ F i)(hx:∀ x:Site n, SumBudget (fun i=> if (R.activities.reg i).site=x then R.p.mass (boothC R (.inr i)) (F i) else 0) u): Hit (boothC R ∘ Sum.inr) M! F (d!-1) (siteFactor M!*u):=by
   rw [show siteFactor M! = ((1:ℕ):ℝ)*siteFactor M! by norm_num]
   refine root_hit (mode:=fun i=> {(R.activities.reg i).site}) (o:=@id (Site n)) (μ:=1) (Occupancy.of_injective injective_id) he (Planned.GuardedAtom.sumBudget_credit (hx 0)) (fun i _=> ⟨_,mem_singleton_self _,(R.activities.reg i).anchor⟩) ?_
   intro i; simp only[mem_singleton,sub_add_cancel, Function.comp_apply]; simpa only[eq_comm] using! hx i
lemma hitting {I J:Type*} (f:I→Support n) (g:J→ Support n) (F:I⊕J→Support n)(hh:F ∘ Sum.inl=f)(hz:F ∘ Sum.inr=g) (p₁:I→ℝ)(p₂:J→ℝ) (M:ℕ) {e t u:ℝ}(hp:Hit f M p₁ e t)(hq:Hit g M p₂ e u): Hit F M (Sum.elim p₁ p₂) e (t+u):=by
    rw [← hh] at hp;rw[←hz] at hq; exact fun i=> Cost.sum (hp i) (hq i)
lemma pass_hit {I:Type*} (s:I→Support n)(f:I→ℝ)(d:ℕ){e u:ℝ}(hs: Hit s d f e u)(h:Summable f): Hit id d (cram s f) e u:=by
    intro i
    let v j:= if i∈s j then f j*Real.exp (e*coverNumber d (s j)) else 0
    have he : Summable v:= (hs _).2.1
    have hz (j: Support n): (if i∈j then cram s f j*Real.exp (e*coverNumber d j) else 0)=cram s v j:=by
       split
       next H=> unfold cram; rw [← tsum_mul_right];exact tsum_congr fun l=>by unfold v; rw [l.property,if_pos H]
       next H=> exact Eq.symm ((tsum_congr (fun l:{x//s x=j}=> show v l.val=0 from if_neg (fun ht=> H (l.property ▸ ht)))).trans tsum_zero)
    have h' := heavy s he; change SumBudget (fun j : Support n=> if i∈j then _ else 0) _; simp only[id_eq]; rw [funext hz]; exact ⟨fun j=> tsum_nonneg fun k=> (hs _).1 _,h'.summable,h'.tsum_eq.trans_le (hs i).2.2⟩
end YM.Trace.Shepherd
