import YM.RG08.Creek.Root
import YM.RG08.Arcade.Key
/-! # Exponential capacities from Payments. Transport of absolute and reannouncement without assumed accidental alignment. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Lyt
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Pill Matrix PowerSeries
open scoped BigOperators Topology Real ContDiff Classical
open Wings Summit
variable {X:Chain}{κ: KernelChoices}{G:Gauge}{E J:Type}{D d k t n τ s e i j r:ℕ}{σ θ p : J→ℝ}{w':ℝ}{T:Labels.Frame G d}{H:SectionData T}{P:KPrices κ}{g:KGate P}{Q:Lending G κ}{hp:1/2≤w'}{hD:d+1 ≤ D}{h:Hol G}{M:Signals P Q e τ h H hp hD}
-- Pre width narrowing (post signal run uses Ledger prices). Compatible same arrays Q: not requiring schedule circular.
set_option maxHeartbeats 500000 in
lemma narrow_l (M:Signals P Q e τ h H hp hD)(v:ℕ→ℝ)(hv:∀ i,0<v i)(he:∀ i, v i ≤ M.wi i): ∃ N:Signals P Q e τ h H hp hD,N.wi=v ∧ N.vi=M.vi∧N.cost=M.cost:=by
   choose U hh using fun i j r=> manExp (G:=G) (K:=κ) (P:=P) (j:=j) (Z:=expQ T (M.cost j i)) hp hD (hv j) (hv i) ((he i).trans (M.rose i)) (expQ_pos T (zero_le_one.trans (M.admits j i))) r
   let w i:= v i / ((τ+e+1:ℕ):ℝ); have hw i:0<w i:= div_pos (hv _) (by positivity)
   obtain ⟨L,hL⟩:=Creek.brook_gates hw M.vi
   let A i j:=(range (τ+e+1)).sup (U i j); let B j:= max (max (A j j) (A (j-1) j)) (L j)
   refine ⟨⟨v,M.vi,M.cost,B,hv,fun i=> le_trans ?_ (M.ores i),M.arcs,fun i=>(he _).trans (M.rose _),M.admits,fun i j X hx hz hp=>hL _ _ X ((le_max_right ..).trans hp),?_,M.posts⟩,rfl,rfl,rfl⟩
   · simp only [nsmul_eq_mul]; exact mul_le_mul_of_nonneg_left (he i) (Nat.cast_nonneg _)
   intro i j X hi hj hp r hv; refine hh _ _ r X hi hj ((le_sup (s:=range (τ+e+1)) (b:=r) (f:=U i j) (by simp; omega)).trans (le_trans (le_trans ?_ (le_max_left ..)) hp)) -- by simpa?
   change A i j ≤ max _ _; by_cases h:i=j; · rw [h]; exact le_max_left ..
   rw [show j-1 = i by have hp:= X.mono; have he:= X.narrow; omega]; exact le_max_right ..
section voucher
variable [NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E]{Y:J→Type}{y δ w:J→ℝ}{U:∀ i,Rooted E (Y i) r}
lemma tin_sm (h:Tin y δ U w)(he:0≤p): Tin y (p*δ) (fun i=> p i • U i) w:= by
   obtain ⟨B,hB,H⟩:=h.serves; refine ⟨B,hB,fun i=> Ink.raise (Ink.scale (H i) (p i)) (by simp only [Pi.mul_apply,Real.norm_of_nonneg (he i),mul_left_comm (p i),le_refl])⟩ -- fix mul_left_comm
lemma tin_zero_t (h:Tin y 1 U w)(he:∀ i,0<p i): Tin y p (fun i=> p i • U i) w:= by simpa only [mul_one] using tin_sm h (show 0≤p from fun i=>(he i).le)
lemma leanT (h: Tin y p U w)(hp:∀ i,0<p i): Tin y 1 (fun i=> (p i)⁻¹ • U i) w := by
   obtain ⟨B,hB,H⟩:=h.serves; refine ⟨B,hB,fun i=> Ink.raise (Ink.scale (H i) _) ?_⟩ -- avoid canon
   rw [Pi.one_apply,mul_one,Real.norm_of_nonneg (inv_nonneg.mpr (hp _).le),mul_comm, mul_assoc, mul_inv_cancel₀ (hp i).ne',mul_one]
-- funded regardless of index repetition
lemma bucks_here {I:Type}{L:J→Side}{S V:∀ i,StripU G (L i)}{v v':J→ℝ}{p:I→ℝ}(h: Bucks τ e y δ w v v' S V)(K:I→J)(hx: Weighed p (y∘K))(hp:Audience p) : Bucks τ e p (δ∘K) (w∘K) (v∘K) (v'∘K) (fun i=>S (K i)) (fun i=>V (K i)):=by
   have hh {α β : J→Type}{A B:∀ j, Row (α j) (β j)}(h : RowBoth y δ A B v): RowBoth p (δ∘K) (fun i=>A (K i)) (fun i=>B (K i)) (v∘K) := by
      have H' {q:J→ℝ}{A:∀ j,Row (α j) (β j)}(h:SafeRow y q A v):SafeRow p (q∘K) (fun i=>A (K i)) (v∘K):= ⟨_,hx.sway hp (h.choose_spec.1.transfer K),fun _=> h.choose_spec.2 _⟩
      exact ⟨H' h.fresh,H' h.again,H' h.moves⟩
   refine ⟨fun i=>h.faith _,fun i=>h.bond _,hp,hx.sway hp (h.crop.transfer K),fun i=>h.hv _,fun i=> h.hs _,fun i=> h.ht _,fun i=> h.hh _,fun i=>h.hn _,fun i=> h.money _,hh h.hessian,hh h.meansT,fun i hi k hk b=>?_,fun i hi=> leaseT (Summit.Lease.whirls (h.castG i hi) K) hp hx le_rfl⟩
   let S:= RG08.Both.mold (h.ribs i hi k hk b) K; exact ⟨S.fresh.age hx hp,S.again.age hx hp,S.moves.age hx hp⟩
end voucher
section instructions
variable {I:Type}{V U: I→BoardU D w' G}
private lemma boarding {L:Side}{U:BoardU D w' G}{Q:StripU G L}(hp:Fair Q)(hx:1/2≤w')(hU:Marvel t U)(p:ℝ)(k:ℕ): aboard d Q.tree ((p•U) i r)=p • aboard d Q.tree (U i r):= by
   have h:= choir_weight hU p
   have H:= creamy d L hU.cap (fun i j=>(hU.hem i j|>.pens)) hx hp.odds -- L binder
   rw [← arise Q.tree hp.ct hp.odds hx _ _ h.cap h.hem,←arise Q.tree hp.ct hp.odds hx _ _ hU.cap hU.hem,cream_weight hU.hem hx hp.odds p]; exact spring_a (H.2 i r|>.pens) _ (scan_whole hp.ct)
lemma fetching_sm {L:Side}{U:BoardU D w' G}{Q:StripU G L}(hp:Fair Q)(hx:1/2≤w')(hU:Marvel t U)(p:ℝ): fetchU Q t d (p•U) i r=p • fetchU Q t d U i r:= by
   have he : Needle.push Q t d (p•U) i r=p • Needle.push Q t d U i r:= congr_fun (congr_fun (Arcade.rent_sm hp p hx hU d) _) _
   rw [formula_bucks hp (choir_weight hU p) hx,formula_bucks hp hU hx,smul_add, boarding hp hx hU _ 0] at he; exact add_left_cancel he
variable {y δ w v p σ : I→ℝ}{L : I→Side}{K M:∀ i,StripU G (L i)}
lemma fetching_p (hp:Bucks τ e y δ w v σ K M)(hx:1/2≤w')(hk:t≤τ)(h:i≤e)(he:∀ i,0<p i)(hU:∀ i,Marvel t (U i))(hh:∀ j k, awaits 1 i r j k→ Tin y p (fun v=> U v j k) σ) : Tin y p (fun j=>fetchU (K j) t d (U j) i r) w:= by
   let Q i:= (p i)⁻¹ • U i; have hQ i: Marvel t (Q i):= choir_weight (hU i) _
   have hV := tin_zero_t (forms_bucks (d:=d) hp hk h hQ hQ hx (fun j k h=> Twill.same (leanT (hh j k h) he))|>.one) he
   convert hV using 1; funext j; unfold Q; rw [fetching_sm (hp.faith _) hx (hU _),smul_inv_smul₀ (he j).ne']
lemma boarding_c (hp:Bucks τ e y δ w v σ K M)(hx:1/2≤w')(h:i≤e)(he:∀ i,0<p i)(hU:∀ i,Marvel t (U i))(hh: Tin y p (fun v=> U v i r) σ): Tin y p (fun j=> aboard d (K j).tree (U j i r)) w:= by
   let Q i:= (p i)⁻¹ • U i; have hQ i: Marvel t (Q i):= choir_weight (hU i) _
   have hV:= tin_zero_t (aboard_bucks (d:=d) hp hQ hQ hx (e:=i) (Twill.same (leanT hh he))|>.one) he
   convert hV using 1; funext j; unfold Q; rw [boarding (hp.faith _) hx (hU _) _ 0, smul_inv_smul₀ (he j).ne']
end instructions
end YM.RG08.Lyt
