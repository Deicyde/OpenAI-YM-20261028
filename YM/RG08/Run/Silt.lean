import YM.RG08.Run.Net
/-!
# Every other operation in the same basis. No strengthened demands. Uniform on input profiles drawn only after shells; η for transmission of evaluated packets.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Run
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door
open scoped BigOperators Topology Real ContDiff Classical
variable {X:Chain}{G:Gauge}{E e r d τ D j t i k m l n s :ℕ} {R σ θ η w A B C:ℝ} {v:ℝ}{L: Side}
variable {I J Y α β γ:Type}[NormedAddCommGroup Y][NormedSpace ℝ Y][CompleteSpace Y]
section lamp
abbrev utter (k:ℕ)(w:ℝ) := ((w⁻¹)^k *k.factorial*Real.exp w)
lemma utter_pos (h:0<w): 0≤ utter k w:= by unfold utter; positivity
variable {Q:Row α α}
lemma dith {f:Cover→ℝ} (h:Laurent.Width σ B f) (hp:0<σ): Charge (dime k) f (utter k σ*B):= by -- Width arg order
  apply budget_mono (budget_scale (utter_pos hp) h) (fun i=>mul_nonneg (Carrier.liftCost_pos ..) (norm_nonneg _))
  intro z; refine (mul_le_mul_of_nonneg_right (polynomial_price hp (show 0≤1+(size z:ℝ) by positivity) k) (norm_nonneg (f z))).trans_eq ?_; unfold utter; rw [mul_add,mul_one,Real.exp_add]; ring
set_option linter.unusedSectionVars false in
lemma sew_cis {V: Quire.Rooted Y α r}(h: cis k η V A)(hp:0≤η): cis k η (sew V) A:= sewn_income _ (fun i=>zero_le_one.trans (tailp hp i)) (fun i s=>by rw [tailP, tailP, show girth (i∘s)=girth i from Equiv.sum_comp s (fun j=> size (i j).1)]) h
lemma jib_cis {V:Quire.Rooted Y α (r+2)}(h: cis k η V A)(hp:0≤η)(hh:Q.strip σ B)(hg:0<σ)(hz:0≤B): cis k η (jib none Q V) (‖batting r‖*(B*A)):= by
  apply sew_cis _ hp; apply Ink.scale; apply Ink.pour _ _ (tailp hp); apply budget_mono (budget_scale hz h) (fun i=> mul_nonneg (zero_le_one.trans (tailp hp _)) (norm_nonneg _)); intro i
  change tailP k η (stems i) * ‖tuneS Q none i • V i‖ ≤ _
  rw [norm_smul]; refine (mul_le_mul (pow_le_pow_left₀ (by positivity) (add_le_add_right (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr ((stems_le (stem1 i)).trans (stems_le i))) hp) (1:ℝ)) k) (mul_le_mul_of_nonneg_right (stroke_known Q hh hg.le _ _ _) (norm_nonneg _)) (by positivity) (zero_le_one.trans (tailp hp _))).trans_eq (mul_left_comm ..)
lemma clasp_cis {U:Quire.Rooted Y α (r+1)}{V:Shale α (s+1)} (h:cis k η U A)(hh:Glow V σ C) (hp:Q.strip σ B)(hC:0≤B)(hz:0≤η)(hη:η≤1)(hB:0<σ) : cis k η (clasp Q U V) (‖syl r s‖*((((s+1:ℕ):ℝ)^k*(utter k σ*B))*(A*(utter k σ*C)))):= by
  have hV: Charge (tailP k 1) V (utter k σ*C):= by simpa only [tailP,one_mul, Charge] using glow_moment hh hB k
  let p := ((s+1:ℕ):ℝ)^k; have hP:0≤p:= by unfold p; positivity
  apply sew_cis _ hz; apply Ink.scale; apply Ink.pour _ _ (tailp hz); apply Ink.sires_cost (h.prods hV) _ _ (mul_nonneg hP (mul_nonneg (utter_pos hB) hC)) -- supplies
  intro i
  let W:= p*(tailP k η i.1*tailP k 1 i.2); have hW:0≤W:= mul_nonneg hP (mul_nonneg (zero_le_one.trans (tailp hz _)) (zero_le_one.trans (tailp zero_le_one _)))
  rw [mul_right_comm p]; apply budget_mono (budget_scale hW (dith (hp (i.1 0).2 (i.2 0).2) (k:=k) hB)); exact fun z=>mul_nonneg (zero_le_one.trans (tailp hz _)) (norm_nonneg _)
  intro z; have he : tailP k η (coral (i,z)) ≤ W*dime k z := by
    unfold W p tailP dime Carrier.liftCost; simp only [one_mul]; repeat rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    let a := (girth i.1:ℝ); let b:=(girth i.2:ℝ); let y:=(size z:ℝ); let t:= (girth (coral (i,z)):ℝ); let q : ℝ:=s
    have ha:0≤a:=Nat.cast_nonneg _; have hb:0≤b:=Nat.cast_nonneg _; have hy:0≤y:=Nat.cast_nonneg _; have hq:0≤q:=Nat.cast_nonneg _
    have hm: t≤(q+1)*a+b+q*y:= by unfold t q a b y; exact_mod_cast seized (i,z)
    push_cast; change 1+η*t ≤ (q+1)*((1+η*a)*(1+b))*(1+y)
    have hw: 1+η*a+b ≤ (1+η*a)*(1+b):=by nlinarith only [mul_nonneg (mul_nonneg hz ha) hb]
    grw [← hw]; nlinarith [mul_le_mul_of_nonneg_left hm hz, mul_le_mul_of_nonneg_right hη hb, mul_le_mul_of_nonneg_right hη (show 0≤q*y by positivity),show 0≤ η*a*y by positivity,show 0≤ η*a*y*q by positivity,show 0≤ b*y by positivity,show 0≤ b*y*q by positivity]
  refine (mul_le_mul_of_nonneg_right he (norm_nonneg _)).trans_eq (mul_assoc ..)
lemma spun_p {f:Quire.Rooted Y (Loc G 1) j}(h:cis k v f A)(hp:0≤v)(hu:v≤1): cis k v (crock f r) ((((r+1:ℕ):ℝ)^k*silkSale G j r)*A) := by
  let p:= ((r+1:ℕ):ℝ)^k; have hh:0≤p:= by unfold p; positivity
  apply sew_cis _ hp; apply Ink.pour _ _ (tailp hp); apply Ink.sires_cost h _ (fun i:Beads (Loc G 1) j × (Fin r→ Lacing G j)=> icing (Prod.snd∘i.1) i.2) (mul_nonneg hh (silkSale_pos ..))
  intro i; apply budget_finite (fun i=>mul_nonneg (zero_le_one.trans (tailp hp _)) (norm_nonneg _))
  have he (x: Fin r→ Lacing G j): tailP k v (sweets i x) ≤ p*tailP k v i := by
     rw [show p=_ from (rfl:p=((r+1:ℕ):ℝ)^k)]; unfold tailP; rw [← mul_pow]; apply pow_le_pow_left₀ (by positivity); let F:=(girth i:ℝ)
     have ht : (girth (sweets i x):ℝ)≤ r*(F+1):= by unfold F; exact_mod_cast (silk_thin (r:=r) i x)
     push_cast at *; nlinarith [mul_le_mul_of_nonneg_left ht hp, show 0≤ (r:ℝ) by positivity,mul_nonneg hp (show 0 ≤ F from Nat.cast_nonneg _)]
  let Q := fun x:Fin r→ Lacing G j=> ‖icing (Prod.snd∘i) x‖
  calc _ ≤ (p*tailP k v i) * ∑ x,Q x := by rw [mul_sum]; exact sum_le_sum fun x _=> mul_le_mul_of_nonneg_right (he x) (norm_nonneg _)
       _ ≤ _:= by rw [mul_right_comm p (silkSale _ _ _)]; exact mul_le_mul_of_nonneg_left (ice_fee ..) (mul_nonneg hh (zero_le_one.trans (tailp hp i)))
end lamp

section arose
variable [Fintype α] [Fintype β]{V:Quire.Rooted Y α r}{Q: Fin r→Row α β}
set_option linter.unusedSectionVars false in
lemma stage_l (h:cis k η V A)(hh:0≤η)(he:η≤1)(hv:0<σ) {C:Fin r→ℝ}(hC:∀ i,(Q i).strip σ (C i))(hp:0≤C): cis k η (rhyme V Q) (((Fintype.card β:ℝ)^r *(utter k σ)^r * ∏ j,C j)*A) := by
   apply Ink.pour _ _ (tailp hh); apply Ink.sires_cost h _ _ (mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (utter_pos hv) _)) (prod_nonneg fun i _=> hp i))
   intro i
   have hQ (j: Fin r): Charge (rug k) (fun x:Cover×β=> Q j (i j).2 x.2 x.1) (((Fintype.card β:ℝ)*utter k σ)* C j):= by
     let g (z:β×Cover):= dime k z.2*‖Q j (i j).2 z.1 z.2‖
     have hu := budget_rows g (fun _=> utter k σ*C j) (fun v=> dith (hC j _ v) hv) (budget_finite (fun _=> mul_nonneg (utter_pos hv) (hp j)) (by rw [sum_const,card_univ,nsmul_eq_mul]))
     rw [mul_assoc]; exact budget_pull (Equiv.prodComm ..) (Equiv.prodComm ..).injective hu
   have h' := budget_fin_prod _ (X:=fun j v=>rug k v*‖Q j (i j).2 v.2 v.1‖) hQ
   rw [prod_mul_distrib,prod_const,card_univ,Fintype.card_fin,mul_pow] at h'; rw [mul_comm _ (tailP k η i)]; apply budget_mono (budget_scale (show 0≤tailP k η i from zero_le_one.trans (tailp hh _)) h') (fun _=>mul_nonneg (zero_le_one.trans (tailp hh _)) (norm_nonneg _))
   intro j; have hz:= shift_priceM (k:=k) (fieldsAt (i,j)) i j (fun _=>rfl) hh he
   refine (mul_le_mul_of_nonneg_right hz (norm_nonneg _)).trans_eq ?_
   change tailP k η i*mint k j * ‖flicker Q (i,j)‖= tailP k η i * _; rw [mul_assoc,prod_mul_distrib]; unfold flicker; rw [norm_prod]; rfl
set_option linter.unusedSectionVars false in
lemma plank_m (b:Site L) (h:cis k η V A)(hp:0≤ w)(hw:w≤1)(he:w/L.val≤η): cis k w (shiftP b V) ((1+4*(r:ℝ))^k*A) := by
   apply Ink.pour _ _ (tailp hp); apply budget_mono (budget_scale (show 0≤(1+4*(r:ℝ))^k by positivity) h) (fun i=>mul_nonneg (zero_le_one.trans (tailp hp _)) (norm_nonneg _)); intro i; exact (mul_le_mul_of_nonneg_right (heel i b hp hw he) (norm_nonneg _)).trans_eq (mul_assoc ..)
end arose
end YM.RG08.Run
