import YM.RG08.Door.Token
/-! # Normalized exponent tube -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Door
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade
open scoped BigOperators Topology Real Classical
variable {I E : Type}{α β : I→Type}{r s D τ n i e : ℕ}[NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E]
variable {P X : ∀ i,Rooted E (α i) r}{F V:∀ i,Rooted E (α i) (r+2)}{A H:∀ i,Rooted E (α i) (r+1)} {W K:∀ i, Row (α i) (α i)}{S S':∀ i,Screed E (α i)}{M M':∀ i, Canticle (α i)}
variable {y σ w v δ b c : I→ℝ}{U T : ∀ i,Shale (α i) (s+1)}
lemma Twill.granting (h : Twill y δ P X v) (n:ℕ):Twill y δ (fun i=> grant n (P i)) (fun i=>grant n (X i)) v := by
  unfold grant; split; next hn=> subst r; exact h
  exact Twill.zero
lemma jib_z (h: SafeRow y b K σ)(hp:0≤σ)(hv:0 ≤ w)(hh:Tin y δ F w)(he:0≤b): Tin y (b*δ) (fun i=> jib none (K i) (F i)) w := by
  obtain ⟨A,hA,hx⟩:=h; obtain ⟨B,hB,H⟩:=hh.serves; refine ⟨_, ((Weighed.constant y (norm_nonneg (batting r))).times hA).times hB,fun i=> Ink.raise (jib_print (H i) (hv i) (hx i) (hp i) (mul_nonneg (hA.positive i) (he i)) _) (le_of_eq ?_)⟩; simp only [Pi.mul_apply]; ring
lemma jib_pair (h : Audience y)(hp : RowBoth y δ K W v)(hF : Twill y δ F V w)(hv:∀ i,0<v i)(hw:0 ≤ w)(hx:0≤δ): Twill y δ (fun i=> jib none (K i) (F i)) (fun i=>jib none (W i) (V i)) w:= by
  have he:0≤ v:= fun i=>(hv i).le
  have hz:0≤(1:I→ℝ):= fun _=>zero_le_one
  constructor
  · simpa only [one_mul] using jib_z hp.fresh he hw hF.one hz
  · simpa only [one_mul] using jib_z hp.again he hw hF.two hz
  let A i:=jib none (K i-W i) (F i); let B i:=jib none (W i) (F i-V i)
  rw [show _ - _ = A+B from funext fun i=> ?_]
  · exact Tin.plus (F:=A) (by simpa only [Pi.sub_apply,mul_one] using jib_z hp.moves he hw hF.one hx) (by simpa only [Pi.sub_apply,one_mul] using jib_z hp.again he hw hF.goes hz) h
  have ht:=hp.again.status hv i; have he:=hF.one.solo hw i; simp only [A,B, Pi.add_apply,Pi.sub_apply]; rw [jib_kern none he (hp.fresh.status hv _) ht,jib_less none he (hF.two.solo hw i) ht]; abel
lemma clasp_z (h : SafeRow y b K v)(hh : Tin y δ A ((s+1:ℕ) • w))(hx:0≤w)(he: s • w ≤ v)(hb: Voucher y c U w)(hp:0≤b) : Tin y (b*δ*c) (fun i=> clasp (K i) (A i) (U i)) w:= by
  obtain ⟨B,hB,H⟩:= h.soften he; obtain ⟨a,ha,ht⟩:= hh.serves; obtain ⟨e,hE,he⟩:=hb
  refine ⟨_, ((Weighed.constant y (norm_nonneg (syl r s))).times (hB.times ha)).times hE,fun i=> Ink.raise (clasp_cost (A:=a i*δ i) (hx i) ?_ (he i) ?_ (mul_nonneg (hB.positive i) (hp i))) (le_of_eq ?_)⟩
  exact show Quire.Lit (A i) _ (a i*δ i) from by simpa only [Pi.smul_apply,nsmul_eq_mul] using ht i
  · simpa only [Pi.smul_apply,nsmul_eq_mul] using H i
  simp only [Pi.mul_apply]; ring
lemma clasp_pair (h : Audience y)(hp : RowBoth y δ K W v)(hF : Twill y δ A H ((s+1:ℕ) • w))(hx:0≤w)(he:s • w ≤ v)(hδ: 0 ≤ δ)(hv:∀ i,0<v i)(hh : Both y δ U T w) : Twill y δ (fun i=>clasp (K i) (A i) (U i)) (fun i=> clasp (W i) (H i) (T i)) w:= by
  have hz : 0 ≤ (1:I→ℝ):= fun _=>zero_le_one
  constructor
  · simpa only [mul_one] using clasp_z hp.fresh hF.one hx he hh.fresh hz
  · simpa only [mul_one] using clasp_z hp.again hF.two hx he hh.again hz
  let B i:= clasp ((K-W) i) (H i) (T i); let C i:= clasp (K i) ((A-H) i) (T i); let D i:= clasp (K i) (A i) ((U-T) i)
  have hB : Tin y δ B w := by simpa only [mul_one] using clasp_z hp.moves hF.two hx he hh.again hδ
  have hC : Tin y δ C w:= by simpa only [one_mul,mul_one] using clasp_z hp.fresh hF.goes hx he hh.again hz
  rw [show _-_ = (B+C)+D from funext fun i=> ?_]
  · exact Tin.plus (hB.plus hC h) (by simpa only [one_mul] using clasp_z hp.fresh hF.one hx he hh.moves hz) h
  have ht := nsmul_nonneg hx (s+1); have hH:= hF.two.solo ht i; have hQ:= hp.fresh.status hv i; have hA:= hF.one.solo ht i; have hz:=(hh.again.choose_spec.2 i).summable (ling_one (hx i)); simp only [B,C,D,Pi.add_apply,Pi.sub_apply]
  rw [clasp_debit hH hz hQ (hp.again.status hv _),clasp_balance hA hH hz hQ,clasp_income hA ((hh.fresh.choose_spec.2 i).summable (ling_one (hx _))) hz hQ]; abel
-- min calls through windows D. `snug` just enough.
-- NOTE murmur (tau top mark) and variants none regulator
variable [∀ i,Fintype (α i)]
def snug (τ e n : ℕ):ℕ := (τ+e+2)^n -- pays grad stitch/jibs
lemma snug_p {τ e i : ℕ} : 0< snug τ e i := by unfold snug; positivity
lemma snug_b (h:i≤n) (hp:D ≤ e)(hx:s+1 ≤ τ+e+2) : snug τ D i * (s+1) ≤ snug τ e (n+1) := by unfold snug; rw [pow_succ]; gcongr; omega
def awaits (n e r i j:ℕ) := i<e ∨ i=e ∧ if n=0 then r ≤ j else r < j
lemma murmur_f (h : Audience y)(hv:∀ i,0<v i)(hp:0≤δ)(he : RowBoth y δ K W v) (hk:∀ i,Decked (M i))(hk':∀ i,Decked (M' i))(hS:∀ i e r,Tidy (S i e r))(hS':∀ i e r,Tidy (S' i e r))(hT:∀ i e r,Tunable (M i e r))(hT':∀ i e r,Tunable (M' i e r)) (hc:∀ i,Fits τ (S i))(hc':∀ i,Fits τ (S' i))
    (hA:∀ m≤n,∀ j≤ e,∀ k, Both y δ (fun i=> Refrain (K i) (M i) none m j k) (fun i=>Refrain (W i) (M' i) none m j k) v)
    (hδ:0≤w)(hV: snug τ e n • w ≤ v)
    (hM : ∀ i j, awaits n e r i j→ Twill y δ (fun v=> S v i j) (fun v=> S' v i j) v) :
    Twill y δ (fun i=>murmur none (K i) (M i) (S i) n e r) (fun i=>murmur none (W i) (M' i) (S' i) n e r) w := by
  induction n using Nat.caseStrongRecOn generalizing e r w with
  | zero=> simp_rw [murmur]; apply (hM e r (Or.inr ⟨rfl,by simp⟩)).soften; simpa only [snug,pow_zero,one_smul] using hV
  | ind n ih=>
   have Hx i:=he.fresh.status hv i; have Hy i:=he.again.status hv i
   by_cases hn:r ≤ τ+e
   swap; · simp_rw [show ∀ i,murmur none (K i) (M i) (S i) (n+1) e r=0 from fun _=> not_ne_iff.mp fun g=> hn (murmur_degree (Hx _) (hT _) (hk _) (hS _) (hc _) g).1,show ∀ i,murmur none (W i) (M' i) (S' i) (n+1) e r=0 from fun _=> not_ne_iff.mp fun g=> hn (murmur_degree (Hy _) (hT' _) (hk' _) (hS' _) (hc' _) g).1]; exact Twill.zero
   have Hu : snug τ e n • w ≤ v := by refine le_trans (smul_le_smul_of_nonneg_right ?_ hδ) hV; exact show snug τ e n ≤ _ from by simpa only [Nat.reduceAdd, mul_one] using snug_b (τ:=τ) (s:=0) (le_refl n) (le_refl e) (by omega)
   simp_rw [murmur_step]; refine Twill.weight (F:=fun i=>_) (H:=fun i=>_) (Twill.plus (F:=fun i=>jib none _ _) (H:=fun i=>jib none _ _) (V:=fun i=> _) (U:=fun i=>_) (jib_pair h he ?_ hv hδ hp) ?_ h) _ h
   · exact ih _ le_rfl (fun m hm d hd k=>hA m (by omega) d hd k) hδ Hu fun i j hv=> hM i j (by unfold awaits at *; split_ifs at * <;> omega)
   let R (S : ∀ i, Screed E (α i)) (Q : ∀ i,Row (α i) (α i))(F : ∀ i, Canticle (α i)) (b a:ℕ×ℕ)(i):= Quire.hymn (Q i) (murmur none (Q i) (F i) (S i) b.1 a.1) (Refrain (Q i) (F i) none b.2 a.2) r
   refine Twill.sums (wheel n) (f:=fun b i=>∑ a∈wheel e,R S K M b a i) (g:=fun b i=>∑ a∈wheel e,R S' W M' b a i) h (fun b hb=> Twill.sums (wheel e) (f:=R S K M b) (g:=R S' W M' b) h fun c hk''=>?_)
   unfold R Quire.hymn; have hb:= mem_antidiagonal.mp hb; have hQ:=mem_antidiagonal.mp hk''
   refine Twill.sums (wheel r) (f:=fun (v:ℕ×ℕ) i=>grant r (clasp (K i) _ _)) (g:=fun v i=>grant r (clasp (W i) _ _)) h fun a ha=> ?_
   -- grip slot d
   have hr:= mem_antidiagonal.mp ha
   by_cases hf:c.1 < e
   · have hR : snug τ c.1 b.1 • ((a.2+1) • w)≤ v:=by rw [← mul_smul]; exact le_trans (smul_le_smul_of_nonneg_right (snug_b (by omega) (by omega) (by omega)) hδ) hV
     have hm : (a.2+1) • w ≤ v := le_trans (show _ ≤ snug .. • _ from ?_) hR
     · refine Twill.granting (clasp_pair h he (ih b.1 (by omega) (fun m hm d hd k=>hA m (by omega) d (by omega) k) (nsmul_nonneg hδ _) hR (r:=a.1+1) fun i j he=> hM i j (Or.inl (by unfold awaits at he; omega))) hδ ((smul_le_smul_of_nonneg_right (Nat.le_succ _) hδ).trans hm) hp hv ((hA b.2 (by omega) c.2 (by omega) _).soften (le_trans ?_ hm))) r
       simpa only [one_smul] using smul_le_smul_of_nonneg_right (show 1≤a.2+1 by omega) hδ
     · simpa only [Nat.succ_eq_add_one, Nat.zero_add,one_smul] using smul_le_smul_of_nonneg_right (Nat.succ_le_of_lt (snug_p (τ:=τ) (e:=c.1) (i:=b.1))) (nsmul_nonneg hδ (a.2+1))
   rw [show c.2=0 by omega]
   have hx(i)(j k : ℕ) : Refrain (K i) (M i) none j 0 k=0 := not_ne_iff.mp (fun g=> (Nat.lt_irrefl _ ((treble_reel (Hx i) (hT i) (hk i) g).1.1)))
   have hy(i)(j k : ℕ) : Refrain (W i) (M' i) none j 0 k=0 := not_ne_iff.mp (fun g=> (Nat.lt_irrefl _ ((treble_reel (Hy i) (hT' i) (hk' i) g).1.1)))
   simp_rw [hx,hy, fun i=>clasp_stop (s:=a.2) ((quiet_tidily (Hx i) (hT i) (hS i) none b.1 c.1 (a.1+1)).pens) (Hx i), fun i=>clasp_stop (s:=a.2) ((quiet_tidily (Hy i) (hT' i) (hS' i) none b.1 c.1 (a.1+1)).pens) (Hy i),grant_zero]; exact Twill.zero
end YM.RG08.Door
