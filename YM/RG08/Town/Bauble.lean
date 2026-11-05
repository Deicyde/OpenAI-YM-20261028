import YM.RG08.Town.Alone
/-!
# Overlapping transmissions in native charts preserve freshness including the scalar.
Endpoint uniform in arbitrary stretches of steps paying stated tickets.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.RG08.Town
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect Work.F08 Push.AbsoluteSums Matrix
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Staffer PertExtension.Series.Radial PertExtension.Series.Tested Pill Wings
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {I J:Type}{u : I→Windows}{w:J→ShoreP u}{X:Chain}{G:Gauge}{E e n r d τ D j k t ε:ℕ}{ν:G.ColorIndex}{F:Labels.Frame G d}{Ω:SectionData F}{H:Hol G}{D':ChartRatio G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}{R:ℝ}{h:1/2≤R}{hD:d+1≤D}{T:Signals P Q E τ H Ω h hD}{A:Grotto G P k E τ}
variable {ρ : ∀ i:Wall w 1,Site (X.S.block i.i)} {p q:J→ℝ} {δ : Wall w 0→ℝ}{U V: Wall w 0→ Tale G}
local notation "Γ" => heights (u:=u) X ν D'
local notation "Ⓨ" => wallY X
local notation "Λ" => strideP X w
section positive
lemma visits (hp:Pines A u)(he:Tights T S ν D' u)(hv:ε≤τ)(hU:Tie U X ν D' ε wallL ρ)(hV:Tie V X ν D' ε wallR ρ)(hδ:Arbor X w δ)(hx:∀ i:Wall w 1, tiltP X i ≤ q i.a)(ht:0≤p)(hq:0≤q)(hk:e≤E)(hr:r≠0)
    (hM:∀ i≤E,∀ j,j≠0→ Drum k (fun i=>Ⓨ (Wall.tip w i)) q p (fun t=>U (Wall.tip w t) i j) (fun t=>V (Wall.tip w t) i j) (fun i=> δ (Wall.tip w i))) : Drum k Ⓨ (badge q) (Λ p) (fun i=>U i e r) (fun i=>V i e r) δ := by
   have hA (e)(h:e≤E)(r)(hk:r≠0):= tapping hp he hv hU hδ h ht hk (fun i hi r h=> (hM i hi r h).first)
   have hB (e)(h:e≤E)(r)(hk:r≠0):= tapping hp he hv hV hδ h ht hk (fun i hi r h=> (hM i hi r h).second)
   refine ⟨hA e hk r hr,hB e hk r hr,?_⟩
   have hS (n): badge (n:=n) (w:=w) q * Λ p=Λ (q*p):= funext fun i=> by simp only [badge,strideP,Pi.mul_apply,mul_assoc]
   rw [hS]
   let F:= U-V; let y(t:Wall w 1):=δ t.low; let v(t:Wall w 1):=δ t.roof
   have hh:0≤y:= fun i=>hδ.pos _; have hv':y≤1:=fun i=>hδ.one _; have hp':0 ≤ (q*p):= fun i=>mul_nonneg (hq _) (ht _)
   let M:= billsT he w (δ:=badge q) (fun i=> (Wall.loan X i).trans (hx i)) k
   let Z:=wallY X (b:=w) (n:=0)
   have hP i: Stone ε (F i):= (hU.stone i).less (hV.stone i)
   have hn i r (h:r>ε+i): Card k Ⓨ (Λ (q*p)) (fun t=> F t i r) δ:= by simp_rw [show ∀ j,F j i r=0 from fun j=>not_ne_iff.mp (mt ((hP j).cap i r) (by omega))]; exact Card.zero
   change Card k Ⓨ _ (fun t=> F t e r) δ
   revert hr; refine tribes_ind (k:=ε) hk (fun i r=> r≠0→ Card k Ⓨ (Λ (q*p)) (fun t=>F t i r) δ) ?_ (fun i _ r hp h=> hn i r hp)
   intro e hl r hN hr; by_cases h':r≤ε+e; swap; · exact hn e r (by omega)
   refine sapling hp he hU.here hδ hP hl hv h' hr hp' (hM e hl r hr|>.funds) (fun i hi j hz=> hN i j (Or.inl hi) hz) (ρ:=ρ) ?_
   let G i (a: Tale G):= holdP (ρ i) (Γ (wallL i)).tree (a e r); let H' i (a:Tale _):= holdP (ρ i) (Γ (wallR i)).tree (a e r)
   let W i:= polishS (U i); let P' i:= polishS (V i)
   let J i:= coreT ε (Γ (wallL i)) (ρ i) (W i.roof) e r; let K i:= coreT ε (Γ (wallR i)) (ρ i) (P' i.roof) e r
   rw [show (fun t=> F (Wall.low (b:=w) t) e r-_)= J-K+(fun i:Wall w 1=> G i (V i.roof)-H' i (V i.roof)) from funext fun i=>?_,← hS]; swap
   · change U i.low e r-V i.low e r-holdP (ρ i) (Γ (wallL i)).tree (U i.roof e r-V i.roof e r)=_
     have hh i: inscribed ε (Γ (wallL i)) (ρ i) (U i.roof) e r=J i+G i (U i.roof):= by unfold J W; rw [coreT,puzzleS _ (hU.stone _) (M.one i) hr,polS_pos hr]; exact (sub_add_cancel ..).symm
     have hb i: inscribed ε (Γ (wallR i)) (ρ i) (V i.roof) e r= K i+H' i (V i.roof):= by unfold K P'; rw [coreT,puzzleS _ (hV.stone _) (he.fair (wallR i)) hr,polS_pos hr]; exact (sub_add_cancel ..).symm
     rw [hU.sewn,hV.sewn,hh,hb,stone_off (ρ i) ((hU.stone i.roof).tidy e r) ((hV.stone i.roof).tidy e r) (Γ (wallL i)).tree (he.fair (wallL i)|>.ct)]
     change (J i+G i (U _))-(K i+ H' i (V _))-(G i (U i.roof)-G i (V i.roof))=(J i-K i)+(G i (V i.roof)-H' i (V i.roof)); abel
   have hx i : y i/(X.S.block i.i).val≤v i:= hδ.tell i
   apply Card.more (U:=J-K) (V:=fun i=> G i (V i.roof)-H' i (V i.roof)) _ _ hh M.age; rotate_left
   · exact (hold_taps (K:=fun t=>Γ (wallL t)) (M:=fun i=>Γ (wallR i)) (z:=ρ) M (Drum.home ( (hB e hl _ hr).up M.pay ht)) hh hv' hx).funds -- binders mismatch? Drum F family.
   refine (core_b (K:=fun t=>Γ (wallL t)) (M:=fun t=>Γ (wallR t)) (z:=ρ) (U:=fun i=>W i.roof) (A:=fun i=>P' i.roof) M hl hv hh hv' hx (ρ:=Λ p) (fun i=>mul_nonneg (ht _) (gain_pos ..).le) (fun _=>jewel_stone (hU.stone _)) (fun _=>jewel_stone (hV.stone _)) (r:=r) ?_).funds
   intro i j hz; have h':i≤ E:=by unfold awaits at *; omega
   by_cases he:j=0
   · subst j; simp only [W,P',polish_dark]; exact Drum.zero
   simp only [P',W,polishS,pebble,Pi.sub_apply,he,↓reduceIte,sub_zero]; refine ⟨(hA _ h' _ he).up M.pay ht,(hB _ h' _ he).up M.pay ht,?_⟩
   rw [hS]; exact (hN i j hz he).up M.pay hp'
end positive

-- includes e=0 all scalar data before any scale convergence
lemma wines (hp:Pines A u)(he:Tights T S ν D' u)(hv:ε ≤τ)(hU:Tie U X ν D' ε wallL ρ)(hV:Tie V X ν D' ε wallR ρ)(hδ:Arbor X w δ)(hx:∀ i:Wall w 1, tiltP X i≤q i.a)(ht:0≤p)(hq:0≤q)(hk:e≤E)
    (hM:∀ i≤E,∀ j, Drum k (fun i=> Ⓨ (Wall.tip w i)) q p (fun t=>U (Wall.tip w t) i j) (fun t=>V (Wall.tip w t) i j) (fun i=>δ (Wall.tip w i))): Drum k Ⓨ (badge q) (badge p) (fun i=>U i e r) (fun i=>V i e r) δ := by
   have ht'(e)(h:e≤E)(r):= mittens hp he hv hU hδ h ht (r:=r) fun i hi j=> (hM i hi j).first
   have hz(e)(h:e≤E)(r):=mittens hp he hv hV hδ h ht (r:=r) fun i hi j=>(hM i hi j).second
   let S:= billsT he w (δ:=badge q) (fun i=> (Wall.loan X i).trans (hx i)) k
   refine ⟨ht' e hk r,hz e hk r,?_⟩
   let F:= U-V; have hp':0≤q*p:= fun i=>mul_nonneg (hq _) (ht _)
   have hh(i)(h:i≤E)(j)(hp:j≠0):Card k Ⓨ (badge (q*p)) (fun i'=> F i' i j) δ:= by
       apply waist hp'
       let hp':= visits ‹Pines A u› he hv hU hV hδ hx ht hq h hp (fun i hi j _=> hM i hi j)
       rw [← show badge (w:=w) (n:=0) q*Λ p=Λ (q*p) from funext fun t=> by simp only [strideP,badge,Pi.mul_apply,mul_assoc]]; exact hp'.funds
   change Card k Ⓨ (badge (q*p)) (fun i=> F i e r) δ
   by_cases h0:r=0
   swap; · exact hh e hk r h0
   subst r; induction e using Nat.strong_induction_on with
   | h e ih=>
      apply signify (A:=fun i=> F i e 0) (hM e hk 0|>.funds) hp' hδ.pos
      let P i:= coreT ε (Γ (wallL i)) (ρ i) (U i.roof) e 0; let Q i:=coreT ε (Γ (wallR i)) (ρ i) (V i.roof) e 0
      rw [show (fun i:Wall w 1=> F i.low e 0-F i.roof e 0)=P-Q from funext fun i=>?_]; swap
      · unfold F; simp only [Pi.sub_apply,P,Q,coreT]; rw [hU.sewn,hV.sewn,holdP,slateS _ _ _ ((hU.stone _).tidy _ _) (S.one i).ct,holdP,slateS _ _ _ ((hV.stone _).tidy _ _) (he.fair (wallR i)).ct]; abel
      refine (core_b (U:=fun i=>U i.roof) (z:=ρ) (K:=fun i=>Γ (wallL i)) (M:=fun i=> Γ (wallR i)) (A:=fun i=> V i.roof) (v:=fun i=>δ i.low) (w:=fun i=>δ i.roof) S hk hv (fun i=>hδ.pos _) (fun i=>hδ.one _) hδ.tell (ρ:=badge p) (fun i=>ht _) (fun i=> hU.stone _) (fun i=>hV.stone _) (r:=0) ?_).funds
      intro i j hT; have h':i≤E:= by unfold awaits at hT; omega
      refine ⟨(ht' _ h' j).mold Wall.roof,(hz _ h' j).mold Wall.roof,?_⟩
      by_cases hz:j=0; swap; · exact (hh i h' j hz).mold Wall.roof
      subst j; exact (ih i (by unfold awaits at hT; split_ifs at * <;> omega) h').mold Wall.roof
end YM.RG08.Town
