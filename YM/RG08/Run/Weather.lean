import YM.RG08.Run.Load
/-! # Strict costs polynomial moments. Cutoff variation relative to ANY exposure size. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Run
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door
open scoped BigOperators Topology Real ContDiff Classical
variable {I E : Type}{α β : I→Type}{r s D τ n i k e : ℕ}[NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E]
variable {F V:∀ i,Rooted E (α i) (r+2)}{A H:∀ i,Rooted E (α i) (r+1)} {W K:∀ i, Row (α i) (α i)}{S S':∀ i,Screed E (α i)}{M M':∀ i, Canticle (α i)}
variable {y σ w v δ b c ρ: I→ℝ}{U T : ∀ i,Shale (α i) (s+1)}
lemma rain_c (h:Card k y ρ F v)(hk:0≤v)(hb:SafeRow y b K w)(hp:∀ i,0<w i)(he:0≤b): Card k y (b*ρ) (fun i=>jib none (K i) (F i)) v:= by
    obtain ⟨B,hB,H⟩:=h.money; obtain ⟨A,hA,H'⟩:=hb; refine ⟨_,((Weighed.constant y (norm_nonneg (batting r))).times hA).times hB,fun i=> Ink.raise (jib_cis (H i) (hk i) (H' i) (hp i) (mul_nonneg (hA.positive _) (he _))) ?_⟩; simp only [Pi.mul_apply]; exact le_of_eq (by ring)
lemma rainy (h: Audience y)(hp:0≤v)(ht:∀ i,0<w i)(hx:0≤δ)(hk:RowBoth y δ K W w)(hF:Drum k y δ ρ F V v): Drum k y δ ρ (fun i=> jib none (K i) (F i)) (fun i=>jib none (W i) (V i)) v := by
   have h1 : 0 ≤ (1:I→ℝ):= fun _=>zero_le_one
   constructor
   · simpa only [one_mul] using rain_c hF.first hp hk.fresh ht h1
   · simpa only [one_mul] using rain_c hF.second hp hk.again ht h1
   let A i:=jib none (K i-W i) (F i); let B i:=jib none (W i) (F i-V i)
   rw [show _-_ = A+B from funext fun i=>?_]; · refine Card.more (U:=A) (rain_c hF.first hp hk.moves ht hx) ?_ hp h; simpa only [Pi.sub_apply,one_mul] using rain_c hF.funds hp hk.again ht h1
   have hw:=hk.again.status ht i; have hu:= hF.first.even hp i; unfold A B; simp only [Pi.sub_apply,Pi.add_apply,jib_kern none hu (hk.fresh.status ht _) hw,jib_less none hu (hF.second.even hp i) hw]; abel
lemma summit_c (h:Card k y ρ A v)(hg:0≤v)(hu:v≤1)(ht:∀ i,0<w i)(hv:Voucher y b U w)(hc:0≤c)(hk:SafeRow y c K w)(hp:Weighed y (fun i=>utter k (w i))): Card k y (b*c*ρ) (fun i=>clasp (K i) (A i) (U i)) v := by
   obtain ⟨B,hB,H⟩:=h.money; obtain ⟨p,hP,hx⟩:=hk; obtain ⟨C,hC,H'⟩:=hv
   refine ⟨_,(Weighed.constant y (norm_nonneg (syl r s))).times (((Weighed.constant y (show 0≤(((s+1:ℕ):ℝ)^k) by positivity)).times (hp.times hP)).times (hB.times (hp.times hC))),fun i=> Ink.raise (clasp_cis (H i) (H' i) (hx i) (mul_nonneg (hP.positive i) (hc i)) (hg i) (hu i) (ht i)) (le_of_eq ?_)⟩; simp only [Pi.mul_apply]; ring
lemma summative (h : Audience y)(hk : RowBoth y δ K W w)(hF : Drum k y δ ρ A H v)(hx:0≤v)(hh:v≤1)(ht : ∀ i,0<w i)(he:Weighed y (fun i=>utter k (w i)))(hv : Both y δ U T w)(hp:0≤δ): Drum k y δ ρ (fun i=> clasp (K i) (A i) (U i)) (fun i=> clasp (W i) (H i) (T i)) v:= by
   have h1 :0≤ (1:I→ℝ):=fun _=>zero_le_one
   constructor
   · simpa only [one_mul] using summit_c hF.first hx hh ht hv.fresh h1 hk.fresh he
   · simpa only [one_mul] using summit_c hF.second hx hh ht hv.again h1 hk.again he
   let B i:= clasp ((K-W) i) (H i) (T i); let C i:= clasp (K i) ((A-H) i) (T i); let D i:= clasp (K i) (A i) ((U-T) i)
   have hB: Card k y (δ*ρ) B v:= by simpa only [one_mul] using summit_c hF.second hx hh ht hv.again hp hk.moves he
   rw [show _-_ = B+C+D from funext fun i=>?_]; · refine Card.more (U:=B+C) (hB.more ?_ hx h) ?_ hx h; exacts [by simpa only [one_mul] using summit_c hF.funds hx hh ht hv.again h1 hk.fresh he,by simpa only [mul_one] using summit_c hF.first hx hh ht hv.moves h1 hk.fresh he]
   have hV:= hF.second.even hx i; have hQ:= hk.fresh.status ht i; have hA:= hF.first.even hx i; have hz:=(hv.again.choose_spec.2 i).summable (ling_one (ht i).le); simp only [B,C,D,Pi.add_apply,Pi.sub_apply]
   rw [clasp_debit hV hz hQ (hk.again.status ht _),clasp_balance hA hV hz hQ,clasp_income hA ((hv.fresh.choose_spec.2 i).summable (ling_one (ht _).le)) hz hQ]; abel
-- no `V V` infinite moment requirement for one-step costs (projection separate)
variable [∀ i,Fintype (α i)]
lemma aurora (h:Audience y)(hv:∀ i,0<w i)(hp:0≤δ)(he:RowBoth y δ K W w) (hk:∀ i,Decked (M i))(hk':∀ i,Decked (M' i))(hS:∀ i e r,Tidy (S i e r))(hS':∀ i e r,Tidy (S' i e r))(hT:∀ i e r,Tunable (M i e r))(hT':∀ i e r,Tunable (M' i e r))
    (hA:∀ m≤n,∀ j≤e,∀ k, Both y δ (fun i=> Refrain (K i) (M i) none m j k) (fun i=>Refrain (W i) (M' i) none m j k) w)
    (hδ:0≤v)(hV:v≤1)(hm:Weighed y (fun i=>utter k (w i)))
    (hM:∀ i j,awaits n e r i j→ Drum k y δ ρ (fun v=> S v i j) (fun v=> S' v i j) v) :
    Drum k y δ ρ (fun i=> murmur none (K i) (M i) (S i) n e r) (fun i=>murmur none (W i) (M' i) (S' i) n e r) v:= by
  induction n using Nat.caseStrongRecOn generalizing e r with
  | zero=> simp_rw [murmur]; exact hM e r (Or.inr ⟨rfl,by simp⟩)
  | ind n ih=>
   have Hx i:= he.fresh.status hv i; have Hy i:=he.again.status hv i
   simp_rw [murmur_step]; refine Drum.weight (U:=fun i=>_) (V:=fun i=>_) (Drum.more (U:=fun i=> jib none _ _) (V:=fun i=>jib none _ _) (A:=fun i=>_) (B:=fun i=>_) (rainy h hδ hv hp he (ih _ le_rfl (fun k hk d hd j=>hA k (by omega) d hd j) fun i j hv=> hM i j (by unfold awaits at *; split_ifs at * <;>omega))) ?_ hδ h) _
   let R (S : ∀ i, Screed E (α i)) (Q : ∀ i,Row (α i) (α i))(F : ∀ i, Canticle (α i)) (b a:ℕ×ℕ)(i):= Quire.hymn (Q i) (murmur none (Q i) (F i) (S i) b.1 a.1) (Refrain (Q i) (F i) none b.2 a.2) r
   refine Drum.group (wheel n) h hδ (F:=fun b i=>∑ a∈wheel e,R S K M b a i) (H:=fun b i=>∑ a∈wheel e,R S' W M' b a i) (fun b hb=> Drum.group (wheel e) h hδ (F:=R S K M b) (H:=R S' W M' b) fun c hk''=>?_)
   unfold R Quire.hymn; have hb:= mem_antidiagonal.mp hb; have hQ:=mem_antidiagonal.mp hk''
   refine Drum.group (wheel r) h hδ (F:=fun (v:ℕ×ℕ) i=>grant r (clasp (K i) _ _)) (H:=fun v i=>grant r (clasp (W i) _ _)) fun a ha=> ?_
   by_cases hf:c.1<e
   · exact Drum.grantor (summative h he (ih b.1 (by omega) (fun m hm d hd k=>hA m (by omega) d (by omega) k) (e:=c.1) (r:=a.1+1) fun i j he=> hM i j (Or.inl (by unfold awaits at he; omega))) hδ hV hv hm (hA b.2 (by omega) c.2 (by omega) _) hp) r
   rw [show c.2=0 by omega]
   have hx(i)(j k : ℕ) : Refrain (K i) (M i) none j 0 k=0 := not_ne_iff.mp (fun g=> (Nat.lt_irrefl _ ((treble_reel (Hx i) (hT i) (hk i) g).1.1)))
   have hy(i)(j k : ℕ) : Refrain (W i) (M' i) none j 0 k=0 := not_ne_iff.mp (fun g=> (Nat.lt_irrefl _ ((treble_reel (Hy i) (hT' i) (hk' i) g).1.1)))
   simp_rw [hx,hy, fun i=>clasp_stop (s:=a.2) ((quiet_tidily (Hx i) (hT i) (hS i) none b.1 c.1 (a.1+1)).pens) (Hx i), fun i=>clasp_stop (s:=a.2) ((quiet_tidily (Hy i) (hT' i) (hS' i) none b.1 c.1 (a.1+1)).pens) (Hy i),grant_zero]; exact Drum.zero
end YM.RG08.Run
