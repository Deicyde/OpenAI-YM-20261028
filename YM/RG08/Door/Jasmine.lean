import YM.RG08.Door.Birds
/-!
# synthesis tape markets for one adjacent marked normalized op.
Includes conversion g, exponent not logged a second time. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Door
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall PowerSeries
open scoped BigOperators Topology Real Classical
variable {I E : Type}{α β : I→Type}{r s D τ h t d n i j e : ℕ}{y σ w v δ b c : I→ℝ}{L : I→Side}{R:ℝ}{G:Gauge}
variable {X Y: I→PowerSeries ℝ}
lemma rehearseT (hf:Audience y)(h : ∀ j≤e, Lease y δ (fun i=> coeff j (X i)) (fun i=>coeff j (Y i))) (hx:∀ i,constantCoeff (X i)=1)(hy:∀ i,constantCoeff (Y i)=1) (r k:ℕ) : Lease y δ (fun i=> glaze (X i) r k e) (fun i=> glaze (Y i) r k e) := by
  let A i j:= coeff j (X i); let B i j:=coeff j (Y i); let C i j:= coeff j (X i)⁻¹; let F i j:= coeff j (Y i)⁻¹
  have hA(s:PowerSeries ℝ): PowerSeries.mk (fun j=>coeff j s)=s:=by ext i; rw [coeff_mk]
  have hc(j)(hj:j ≤ e): Lease y δ (fun i=> C i j) (fun i=> F i j) := by
    have H:= Lease.undo hf (f:=A) (g:=B) h (fun i=>by simp [A,hx i]) (fun i=>by simp [B,hy i]) _ hj; unfold A B at H; simp_rw [hA] at H; exact H
  have ha (j)(hp:j≤ e): Lease y δ (fun i=> coeff j ((X i)^k)) (fun i=> coeff j ((Y i)^k)) := by
    have H:= Lease.powerT hf (f:=A) (g:=B) h k _ hp; unfold A B powT at H; simp_rw [hA] at H; exact H
  have hg (j)(hp:j≤e): Lease y δ (fun i=> coeff j ((X i)⁻¹ ^r)) (fun i=> coeff j ((Y i)⁻¹ ^r)) := by
    have H := Lease.powerT hf (f:=C) (g:=F) hc r _ hp; unfold C F powT at H; simp_rw [hA] at H; exact H
  unfold glaze; simp_rw [coeff_mul]; apply Lease.lists; exact hf
  intro j hj; have hp:=mem_antidiagonal.mp hj; exact (ha _ (by omega)).times (hg _ (by omega)) hf
variable {P Q: ∀ i,StripU G (L i)}{U V:I→BoardU D R G}
-- `e` fixed max and τ; α dimensions inside L. Width w push, σ input.
structure Bucks (τ t : ℕ)(y δ w v σ : I→ℝ)(P Q:∀ i,StripU G (L i)) : Prop where
  faith i : Fair (P i)
  bond i : Fair (Q i)
  env : Audience y
  crop : Weighed y (fun i=> ((L i).val:ℝ))
  hv : v ≤ 1
  hs : 0 ≤ δ
  ht : ∀ i, 0<w i
  hh : 0 ≤ σ
  hn i : v i ≤ (L i).val *σ i
  money : snug τ t (windows τ t) • w ≤ v
  hessian : RowBoth y δ (fun i=>(P i).cv) (fun i=>(Q i).cv) v
  meansT : RowBoth y δ (fun i=>(P i).tree) (fun i=>(Q i).tree) v
  ribs j (he:j≤t) n (hp:n≤windows τ t) k : Both y δ (fun i=>Refrain (veiled (P i).cv) (P i).song none n j k) (fun i=>Refrain (veiled (Q i).cv) (Q i).song none n j k) v
  castG k : k ≤ t→ Lease y δ (fun i=> coeff k (P i).scale) (fun i=>coeff k (Q i).scale)

abbrev halfP {L:Side}(P:StripU G L) (τ d:ℕ)(V:BoardU D R G)(e r:ℕ) := spring (halfU d (veiled P.cv) P.song τ V e r) (scan P.tree) -- binder i issue below
lemma snug_every (h:i ≤ τ)(he:e ≤ t)(hp:j ≤ n) : snug i e j ≤ snug τ t n := by unfold snug; gcongr; omega
variable {s' : ℕ}
lemma bucks_v (he:Bucks τ t y δ w v σ P Q) : w ≤ v := le_trans (show _ ≤ snug τ t (windows τ t) • w from by simpa only [one_smul] using smul_le_smul_of_nonneg_right (show 1≤ snug τ t (windows τ t) from snug_p) (show 0≤w from fun i=> (he.ht i).le)) he.money
lemma half_bucks (he:Bucks τ t y δ w v σ P Q) (hq:h≤τ)(hk:e ≤ t)(hv:∀ i,Marvel h (U i))(hV:∀ i,Marvel h (V i))(hR:1/2≤R)
    (hp:∀ j k, awaits 1 e r j k → Twill y δ (fun i=> U i j k) (fun i=> V i j k) σ): Twill y δ (fun i=>halfP (P i) h d (U i) e r) (fun i=>halfP (Q i) h d (V i) e r) w:= by
  have hx i := (he.ht i).trans_le (bucks_v he i)
  have hu i:= creamy d (L i) (hv i).cap (fun j k=>(hv i).hem j k |>.pens) hR (he.faith i).odds
  have hg i:= creamy d (L i) (hV i).cap (fun j k=>(hV i).hem j k|>.pens) hR (he.bond i).odds
  have hw:0≤ w:= fun i=>(he.ht i).le
  have hd:0≤ v:=hw.trans (bucks_v he)
  apply tw_both he.env (scanned_contract he.meansT (bucks_v he) he.env he.hs) he.ht _ he.hs (Weighed.constant _ (Nat.cast_nonneg (Fintype.card (Loc G 1))))
  unfold halfU; refine Twill.sums _ he.env fun j hj=> ?_
  have hP : j+1≤windows τ t:=by have ht:=mem_range.mp hj; unfold windows at *; omega
  refine murmur_f he.env hx he.hs (veil_contract he.hessian he.hs) (fun i=>(he.faith i).lived) (fun i=>(he.bond i).lived) (fun i=>(hu i).2) (fun i=>(hg i).2) (fun i=>(he.faith i).tune) (fun i=>(he.bond i).tune) (fun i=>(hu i).1) (fun i=>(hg i).1) (fun n hn j hj=>he.ribs j (by omega) n (by omega)) hw ((smul_le_smul_of_nonneg_right (snug_every hq hk hP) hw).trans he.money) fun i k hb=> cake_pair (hp i k (by simpa only [awaits,Nat.add_one_ne_zero,one_ne_zero,↓reduceIte] using hb)) hR (fun i=>(he.faith i).odds) hd he.hv he.hh he.hn he.crop he.env
lemma aboard_bucks (he:Bucks τ t y δ w v σ P Q) (hv:∀ i,Marvel h (U i))(hV:∀ i,Marvel h (V i))(hR:1/2≤R) (hp:Twill y δ (fun i=>U i e r) (fun i=> V i e r) σ) : Twill y δ (fun i=> aboard d (P i).tree (U i e r)) (fun i=> aboard d (Q i).tree (V i e r)) w := by
  have ht := (cake_pair (d:=d) hp hR (fun i=>(he.faith i).odds) ((show 0≤w from fun i=>(he.ht i).le).trans (bucks_v he)) he.hv he.hh he.hn he.crop he.env).soften (bucks_v he)
  have H := tw_both he.env (scanned_contract he.meansT (bucks_v he) he.env he.hs) he.ht ht he.hs (Weighed.constant _ (Nat.cast_nonneg (Fintype.card (Loc G 1))))
  simp_rw [fun i=> arise (P i).tree (he.faith i).ct (he.faith i).odds hR (U i) h (hv i).cap (hv i).hem e r d, fun i=> arise (Q i).tree (he.bond i).ct (he.bond i).odds hR (V i) h (hV i).cap (hV i).hem e r d] at H; exact H
abbrev juice {L:Side}(P:StripU G L)(τ d:ℕ)(U:BoardU D R G) := Shade.filop P.cv P.tree P.song none τ d U
lemma filop_bucks (he:Bucks τ t y δ w v σ P Q) (hq:h≤τ)(hk:e≤t)(hv:∀ i,Marvel h (U i))(hV:∀ i, Marvel h (V i))(hR:1/2≤R)
    (hp:∀ j k, awaits 0 e r j k → Twill y δ (fun i=> U i j k) (fun i=> V i j k) σ): Twill y δ (fun i=>juice (P i) h d (U i) e r) (fun i=>juice (Q i) h d (V i) e r) w := by
  unfold juice; simp_rw [fun i=> opening (he.faith i).cm (he.faith i).ct (hv i).hem (hv i).cap hR (he.faith i).odds (he.faith i).tune (he.faith i).lived,fun i=>opening (he.bond i).cm (he.bond i).ct (hV i).hem (hV i).cap hR (he.bond i).odds (he.bond i).tune (he.bond i).lived]
  refine Twill.plus (F:=fun i=> _) (V:=fun i=> _) (H:=fun i=> _) (U:=fun i=> _) (aboard_bucks he hv hV hR (hp e r (by simp [awaits]))) (half_bucks he hq hk hv hV hR ?_) he.env
  intro i j hh; apply hp i j; unfold awaits at hh ⊢; split_ifs at * <;> omega

abbrev fetchU {L:Side}(P:StripU G L)(τ d:ℕ)(U: BoardU D R G)(e r:ℕ):= halfP P τ d U e r + ∑ j∈range e, glaze P.scale r j (e-j) • juice P τ d U j r
lemma forms_bucks (he:Bucks τ t y δ w v σ P Q) (hq:h≤τ)(hk:e ≤ t)(hv:∀ i,Marvel h (U i))(hV:∀ i,Marvel h (V i))(hR:1/2≤R) (hp:∀ j k, awaits 1 e r j k → Twill y δ (fun i=> U i j k) (fun i=> V i j k) σ): Twill y δ (fun i=>fetchU (P i) h d (U i) e r) (fun i=>fetchU (Q i) h d (V i) e r) w := by
  unfold fetchU; refine Twill.plus (F:=fun i=> _) (V:=fun i=> _) (H:=fun i=> _) (U:=fun i=> _) (half_bucks he hq hk hv hV hR hp) (Twill.sums (range e) (f:=fun i j=> glaze (P j).scale r i (e-i) • _) (g:=fun i j=> glaze (Q j).scale r i (e-i) • _) he.env fun j hj=>?_ ) he.env
  have hh : j<e := mem_range.mp hj
  exact (filop_bucks he hq (hh.le.trans hk) hv hV hR (r:=r) (d:=d) fun i k hu=> hp i k (Or.inl (by unfold awaits at hu; omega))).scales (rehearseT he.env (fun i hi => he.castG i (hi.trans (le_trans (Nat.sub_le ..) hk))) (fun i=>(he.faith i).once) (fun i=>(he.bond i).once) _ _) he.env
lemma formula_bucks {L : Side}{S:StripU G L}{U: BoardU D R G}(he:Fair S)(hV:Marvel τ U)(hp:1/2≤R)(t e r:ℕ): Needle.push S τ t U e r= aboard t S.tree (U e r) + fetchU S τ t U e r := by
  unfold Needle.push fetchU; rw [ridge _ he.once,opening he.cm he.ct hV.hem hV.cap hp he.odds he.tune he.lived]; exact add_assoc .. 
end YM.RG08.Door
