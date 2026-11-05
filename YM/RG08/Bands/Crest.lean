import YM.RG08.Bands.Zephyr
/-!
# Native loads moved with exact endpoints. Payment telescope across paint changes.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.RG08.Bands
open Filter Analysis Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect Work.F08 Push.AbsoluteSums Matrix
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Staffer PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Town
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {I J:Type}{n k r t b τ E:ℕ} {L:J→Side}{α:J→Type}[∀ i,Fintype (α i)]{G:Gauge}{B U: I→ J→ Tale G}
section event
variable {K M:∀ i: J, Row (α i) (α i)}{D V:∀ i,Canticle (α i)}{F P:I→∀ i, Screed ℝ (α i)}{p:List I}{a:I→ℕ}{y w η q δ:J→ℝ}
def Vily {X:Type} (K:Row X X): Prop:= ∀ i:Side,(K.acts i)ᵀ=K.acts i -- alias patch
lemma burn_step (h:Audience y)(hp:RowBoth y δ K M w)(ht:∀ i,Vily (K i))(hx:∀ i,Vily (M i))(hu:∀ i,Gets (D i))(hv:∀ i,Gets (V i))(hh:∀ i,0<w i)(hπ:Weighed y (fun i=>Run.utter k (w i)))(hη:0≤ η)(hs:η≤1)(ho:0≤δ)(hF:∀ i∈p,∀ j, Sails (a i) (F i j))(hP:∀ i∈p,∀ j,Sails (a i) (P i j))
   (hJ:BillsP k n E y δ q (fun j=>pullG none (K j) (fun i=>murmur none (K j) (D j) (F i j)) p) (fun j=> pullG none (M j) (fun i=>murmur none (M j) (V j) (P i j)) p) η)
   (hM:∀ i≤n,∀ e≤E,∀ r, Both y δ (fun j=>Refrain (K j) (D j) none i e r) (fun j=> Refrain (M j) (V j) none i e r) w) : BillsP k n E y δ q (fun j=> birth none (K j) (D j) (fun i=> F i j) p) (fun j=> birth none (M j) (V j) (fun i=>P i j) p) η := by
   let X j:= birth none (K j) (D j) (fun i=> F i j) p; let Y j:= birth none (M j) (V j) (fun i=> P i j) p
   have hX j:= burnout (fun i h=>hF i h j) (hp.fresh.status hh j) (hu j) (ht j); have hY j:= burnout (fun i h=>hP i h j) (hp.again.status hh j) (hv j) (hx j)
   intro i hi e he r; change Drum k y δ q (fun j=>X j i e r) (fun j=>Y j i e r) η
   induction i using Nat.caseStrongRecOn generalizing e r with
   | zero=> simp_rw [X,Y,birth_zero]; exact Drum.zero
   | ind i ih=>
     let Z j:= peels none (K j) (X j) i e r; let A j:=peels none (M j) (Y j) i e r
     let L j:= choirR none (K j) (D j) (X j) i e r; let N j:=choirR none (M j) (V j) (Y j) i e r
     let U j:=pullG none (K j) (fun i=> murmur none (K j) (D j) (F i j)) p i e r; let V' j:=pullG none (M j) (fun i=>murmur none (M j) (V j) (P i j)) p i e r
     let α:= (↑(i+1:ℕ):ℝ); have hA:α≠0:= Nat.cast_ne_zero.mpr (by omega)
     have hz : α • (fun j=>X j (i+1) e r)= Z+L+U:= funext fun j=> congr_fun (congr_fun (congr_fun (hX j) i) e) r
     have ht : α • (fun j=>Y j (i+1) e r)= A+N+V':= funext fun j=>congr_fun (congr_fun (congr_fun (hY j) i) e) r
     have hk i' (hi':i'≤ i) j hj t:= ih _ hi' (by omega) j hj t -- inspect argument
     have hh': Drum k y δ q L N η := by
        unfold L N choirR; simp only [Finset.sum_apply]
        let t (a b:ℕ×ℕ)(j):= Quire.hymn (K j) (X j a.1 b.1) (Refrain (K j) (D j) none a.2 b.2) r
        let v (a b:ℕ×ℕ)(j):= Quire.hymn (M j) (Y j a.1 b.1) (Refrain (M j) (V j) none a.2 b.2) r
        refine Drum.group (wheel i) h hη (F:=fun a j=>∑ b ∈wheel e,t a b j) (H:=fun a j=>∑ b ∈wheel e,v a b j) fun a ha=> Drum.group (wheel e) h hη (F:=t a) (H:=v a) fun b hb=>?_ -- spaces
        have hB:=mem_antidiagonal.mp hb; have hV:= mem_antidiagonal.mp ha
        unfold t v Quire.hymn
        refine Drum.group (wheel r) h hη (F:=fun l j=> grant r (clasp (K j) (X j a.1 b.1 (l.1+1)) _)) (H:=fun l j=> grant r (clasp (M j) (Y j a.1 b.1 (l.1+1)) _)) fun l hl=>?_
        exact (summative h hp (hk a.1 (by omega) b.1 (by omega) (l.1+1)) hη hs hh hπ (hM a.2 (by omega) b.2 (by omega) (l.2+1)) ho).grantor r
     have hm : Drum k y δ q ((α:ℝ) • (fun j=>X j (i+1) e r)) ((α:ℝ) • (fun j=> Y j (i+1) e r)) η:= by rw [hz,ht]; exact ((((rainy h hη hh ho hp (hk _ le_rfl e he (r+2))).more hh' hη h).more (hJ i (by omega) e he r) hη h))
     simpa only [inv_smul_smul₀ hA] using hm.weight α⁻¹
end event

section skirts
variable {P K:∀ i: J, StripU G (L i)}{q p: ∀ i: J, Site (L i)}{X Y:J→ Tale G}
variable {u:List I}{y η δ v x w σ:J→ℝ}{z t':I→J→Cover}{q': I→J→ℝ}{f:I→∀ i,Site (L i)}{A:I→ℕ}
lemma native_roots (h:LensP (k+b) E τ y δ v P K)(hk:t≤ τ)(hu:∀ i,Stone t (X i))(hx:∀ i,Stone t (Y i)) (hp:∀ i≤E,∀ r,Drum (k+b) y δ w (fun z=>X z i r) (fun z=>Y z i r) 1):
    BillsP (k+b) (windows τ E) E y δ w (fun i=> murmur none (veiled (P i).cv) (P i).song (reachP (p i) (X i))) (fun i=> murmur none (veiled (K i).cv) (K i).song (reachP (p i) (Y i))) 1:= by
  intro i hi e he r
  refine aurora h.age h.pos h.rent (veil_contract h.art h.rent) (fun i=>(h.one i).lived) (fun i=>(h.two i).lived) (fun i=> (reaches (hu i).cap (hu i).tidy (p i)).2) (fun i=>(reaches (hx i).cap (hx i).tidy (p i)).2) (fun i=>(h.one i).tune) (fun i=>(h.two i).tune) (fun m hm j hj k=> h.chargesG _ (hj.trans he) _ (hm.trans hi) k) zero_le_one le_rfl h.owns (fun i j hv=> lots (hp i (by unfold awaits at hv; omega) j) zero_le_one le_rfl (z:=p) (fun i=>?_) h.pay h.age)
  simp only [Pi.one_apply]; apply (div_le_one (by positivity)).2; exact_mod_cast (L i).property
lemma pow_pr (hp:∀ i∈u,0≤ q' i): 0 ≤ accrues q' u := by
   induction u with
   | nil=> exact zero_le_one
   | cons i u ih=> have he:= ih fun j hj=>hp j (List.mem_cons_of_mem _ hj); exact fun x=> mul_nonneg (hp i List.mem_cons_self x) (he x)
lemma hairpins {β:Type}{U P:I→HeatS β} (hp:∀ i∈u,U i=P i): castM U u=castM P u:= by
   induction u with
   | nil=> rfl
   | cons i v ih=>
      have hx:= ih fun j hj=>hp j (List.mem_cons_of_mem _ hj)
      change borne (U i) (castM U v)=borne (P i) (castM P v); exact congr_arg₂ borne (hp _ List.mem_cons_self) hx
private lemma vibrant {β:Type}{K:Row β β}{p:Option Side}{F H:I→HeatS β} (hp:∀ i∈u,F i=H i)(V:HeatS β): junction p K F V u=junction p K H V u:= by
   induction u with
   | nil=> rw [junction,junction]
   | cons b u ih=>
     have hh i hi:= hp i (List.mem_cons_of_mem _ hi); have hb:= hp b List.mem_cons_self; rw [junction,junction]; exact congr_arg₂ (· + ·) (congr_arg₂ borne (congr_arg (thunder p K V) hb) (hairpins (u:=u) hh)) (congr_arg₂ borne hb (ih hh))
private lemma present_j {β:Type}[Fintype β]{K:Row β β}{p:Option Side}{F H:I→HeatS β}(hv:∀ i∈u,F i=H i): pullG p K F u=pullG p K H u:= by
    induction u with
    | nil=> rw [pullG,pullG]
    | cons b u ih=>
      have he i hi:=hv i (List.mem_cons_of_mem _ hi); rw [pullG,pullG,hv b List.mem_cons_self]; exact congr_arg₂ (·+·) (vibrant he _) (congr_arg₂ borne rfl (ih he))
private lemma murmuring (h:∀ i∈u,∀ j,Lattice.lift (p j) + t' i j=(L j).val • z i j+ Lattice.lift (f i j))(he:∀ i∈u,∀ j, Stone (A i) (U i j))(ht:∀ i,Fair (P i)) (v) (hv:v∈u)(j):
    murmur none (veiled (P j).cv) (P j).song (reachP (p j) (Town.season (t' v j) (U v j))) = shiftM (z v) (fun i=> murmur none (veiled (P i).cv) (P i).song (reachP (f v i) (U v i))) j := by
    have hh:= reaches (he _ hv j).cap (he _ hv j).tidy (f v j)
    rw [show reachP (p j) (Town.season (t' v j) (U v j))=Town.season (z v j) (reachP (f v j) (U v j)) from funext fun i=>funext fun r=>lot_history (he _ hv _|>.tidy i r|>.pens) (h _ hv _)]
    exact funext fun i=>funext fun n=>funext fun r=> Eq.symm (murmur_places (veiled_whole (ht j).cm) (ht j).tune hh.2)
lemma steps_l (hS:LensP (k+b) E τ y δ v P K)(hp:LensP k E τ y δ v P K)
    (hT:∀ i,Vily (veiled (P i).cv))(hK:∀ i,Vily (veiled (K i).cv))
    (hu:loadᵣ A u≤τ) (hC: ∀ i∈u,A i≤τ)
    (hU: ∀ i∈u,∀ j, Stone (A i) (U i j)) (hB : ∀ i∈u,∀ j, Stone (A i) (B i j))
    (hF:∀ i∈u,∀ k'≤E,∀ r,Drum (k+b) y δ (q' i) (fun j=> U i j k' r) (fun j=>B i j k' r) 1) (h:∀ i∈u,∀ j,Lattice.lift (p j)+ t' i j=(L j).val • z i j + Lattice.lift (f i j)) (he:Leaves b u z y η σ v δ x (fun i=>veiled (P i).cv) (fun i=>veiled (K i).cv)) (hQ:∀ i∈u,0≤ q' i)(hz:u.Nodup)(ha:n≤E):
    Drum k y δ (accrues q' u*σ^b) (fun j=>jamT (P j) (fun i=>season (t' i j) (U i j)) (p j) A u n r) (fun j=>jamT (K j) (fun i=>season (t' i j) (B i j)) (p j) A u n r) η := by
   let R (V:I→J→Tale G) i j:= season (t' i j) (V i j)
   have h1 i (hi:i∈u) j:= (hU i hi j).transport (t' i j); have h2 i (hi:i∈u) j:= (hB i hi j).transport (t' i j)
   let F j:= hammers (P j) (fun i=>R U i j) (p j) u; let C j:= hammers (K j) (fun i=>R B i j) (p j) u
   have hpU i hi:= native_roots hS (hC i hi) (hU i hi) (hB i hi) (p:=fun j=> f i j) (hF i hi)
   let V₁ i j:= murmur none (veiled (P j).cv) (P j).song (reachP (f i j) (U i j)); let V₂ i j:= murmur none (veiled (K j).cv) (K j).song (reachP (f i j) (B i j))
   let D i j:= reachP (p j) (R U i j); let H i j:= reachP (p j) (R B i j)
   have hq:0 ≤ accrues q' u*σ^b:= fun i=>mul_nonneg (pow_pr hQ i) (pow_nonneg (he.reserve _) b)
   have hγ (L':Side) Z (h : Fair (Z:StripU G L')): Gets Z.song:= ⟨h.lived,fun i j=>⟨h.tune i j,h.bought i j⟩⟩ -- binder L
   have hx: BillsP k (windows τ E) E y δ (accrues q' u*σ^b) F C η:= by
      refine burn_step (n:=windows τ E) hp.age he.wage hT hK (fun i=> hγ _ _ (hp.one i)) (fun i=> hγ _ _ (hp.two i)) hp.pos hp.owns he.pos he.small hp.rent (F:=D) (P:=H) (K:=fun i=>veiled (P i).cv) (M:=fun i=>veiled (K i).cv) (a:=A) (p:=u) (fun i hi j=>sails_k _ (sails_from (h1 _ hi j))) (fun i hi j=>sails_k _ (sails_from (h2 _ hi j))) ?_ (fun i hi e he r=>hp.chargesG _ he _ hi r)
      convert chapter he hpU hz using 1
      · exact funext fun j=>present_j (fun i hi=> murmuring h hU hp.one i hi j)
      exact funext fun j=> present_j (fun i hi=> murmuring h hB hp.two i hi j)
   simp_rw [fun i=>jam_period (p:=p i) (hp.one i) (hv:=fun j hj=>sails_from (h1 j hj i)), fun i=>jam_period (p:=p i) (hp.two i) (hv:=fun j hj=>sails_from (h2 j hj i))]
   let V:=loadᵣ A u
   have hh (e)(he': e≤ E) : Drum k y δ (accrues q' u*σ^b) (fun i=>endP V (F i) e r) (fun i=>endP V (C i) e r) η:= by
      unfold endP; simp only [Finset.sum_apply]
      exact Drum.group (range _) hp.age he.pos fun b hb=> hx b (by have he:=mem_range.mp hb; unfold V windows at *; omega) _ he' r
   have hh e he':= marks_pair (hh e he') he.pos he.small hp.pos (Weighed.constant _ (Nat.cast_nonneg (Fintype.card (Loc G 1)))) hp.owns hp.age (scanned_contract hp.meanT le_rfl hp.age hp.rent) hp.rent
   unfold Tall.hill; refine Drum.group (range (n+1)) hp.age he.pos (F:=fun e i=> glaze (P i).scale r e (n-e) • hears (scan (P i).tree) (endP V (F i)) e r) (H:=fun e i=> glaze (K i).scale r e (n-e) • hears (scan (K i).tree) (endP V (C i)) e r) ?_
   intro i hi; exact (hh i (le_trans (mem_range_succ_iff.mp hi) ha)).sc (rehearseT hp.age (e:=n-i) (fun i hi=> hp.scaleT i (hi.trans ((Nat.sub_le ..).trans ha))) (fun i=>(hp.one i).once) (fun i=>(hp.two i).once) r i) hq hp.age he.pos
end skirts
end YM.RG08.Bands
