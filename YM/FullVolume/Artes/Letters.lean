import YM.FullVolume.Artes.Lagoon
/-! Packed trajectories tagged. Cluster convergence & all horizons. -/
set_option autoImplicit false
noncomputable section
namespace YM.Stationary.Artes
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Supply
open Shade Beacon Flagship ConeRay Tralis WilsonStartup WilsonStartup.Change WilsonStartup.Change.Reading Next.Free Next.Free.Retort
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical InnerProductSpace
variable {G: Gauge}{a:Levels G} {s: Sheet G}{L: Rolls s}{Q:PostCost L}{O:ChartRatio G}
variable {J:Horizon a}{V:ℕ→Reel G}{X:MapPrices}
variable {U:Kin J O} (h:Counter a J (O:=O) Q V X) (A:Archive a J)(hp:Inspected U Q V)
open Alive Wish
abbrev Motto (a:Levels G):=∀ i,Tale a i
structure Roadie (r:ℕ→Motto a)(U:Kin J O)(Q:PostCost L)(V:ℕ→Reel G): Prop where
    pamphlets N i (h:i+1<N): let t:=r N i; t.input= U.path N (i+1)∧ t.receipts=U.path N i ∧ t.Ψ=U.stationary N i∧ t.α=U.alpha N i∧ Alive Q O J V t N
    links i N (h:i+2<N) :(r N i).stock=(r N (i+1)).sold
include hp h
lemma author: ∃ r,Roadie r U Q V:=by
    haveI :Nonempty (Flagship G):=⟨⟨0,0,0⟩⟩; choose! S hX hv using fun i N (h: i<N)=> Flagship.laying (hp.records _ _ h).2
    let r:ℕ→Motto a:=fun N i=> {input:= U.path N (i+1), stock:= S (i+1) N, receipts:= U.path N i,sold:=S i N,Ψ:=U.stationary N i,α:=U.alpha N i }
    refine ⟨r,?_,fun _ _ _=>rfl⟩; intro N i hi t
    have he: i<N:=by omega
    have ht:=hp.sight; have hb:=hp.records i N he|>.1
    exact ⟨rfl,rfl,rfl,rfl,he,Tale.fromE (T:=r N i) hb h.staple (h.oath _ _ he.le) he (hX _ _ hi) (hX _ _ he) (hv _ _ he) (h.daily.expandR _ (ht.linked.cap _ _ hi.le)),ht.row N _ hi.le, hb⟩
-- cluster world. Body books.Bin
structure Cypress (A:Archive a J)(Q:PostCost L)(O:ChartRatio G)(V:ℕ→Reel G)(F:Motto a) :Prop where
    line i:Bottle (F i) A V O Q
    rows i: (F i).input=(F (i+1)).receipts
    latch i: (F i).stock=(F (i+1)).sold
structure Slip (X: ℕ→ Motto a)(K:Motto a)(w:ℕ→ℕ):Prop where
    free i: Tendsto (fun k=> (X (w k) i).α) atTop (𝓝 (K i).α)
    gems i: Flagship.Beacon (fun k=> (X (w k) i).sold) (K i).sold (a.params i).paths (a.clock.loopCap i)
    next i: Flagship.Beacon (fun k=> (X (w k) i).stock) (K i).stock (a.params (i+1)).paths (a.clock.loopCap (i+1))
    toll i j B : View (fun k=>(X (w k) i).Ψ j B) ((K i).Ψ j B) 0 0
variable {T:ℕ→Motto a}(H:Roadie T U Q V) (S:Motto a) {u:ℕ→ℕ}
omit h hp
private lemma recent {ι:Type}{X:Lights ι}{b:ℝ}{f g:ℕ→ Lights ι}(he:f=ᶠ[atTop] g)(h:Gleam f X b): Gleam g X b:=⟨(h.budget.and he).mono (fun i hi=> hi.2 ▸ hi.1),fun x=> (h.hinge x).congr' (he.mono fun n hn=> congr_arg (fun v: Lights ι=> v x) hn)⟩ -- spurious dep
private lemma surprise {S:Flagship G}{f g:ℕ→Flagship G}{b B:ℝ}(he:f=ᶠ[atTop] g)(h:Flagship.Beacon f S b B): Flagship.Beacon g S b B:=⟨recent (he.fun_comp Flagship.a) h.a,recent (he.fun_comp Flagship.b) h.b,recent (he.fun_comp Flagship.c) h.c⟩
include H hp A h
lemma cruising (hS:Tendsto u atTop atTop) : ∃ F:Motto a,∃ w:ℕ→ℕ, StrictMono w ∧ Cypress A Q O V F∧ Slip T F (u ∘ w) :=by
   have he (i:ℕ) : ∀ᶠ k in atTop,Alive Q O J V (T (u k) i) (u k) := (hS.eventually (eventually_gt_atTop (i+1))).mono fun k hk=> (H.pamphlets _ _ hk).2.2.2.2
   obtain ⟨P,v,hv,hP⟩ := rockets (f:=fun k i=>(T (u k) i).α) fun i=> Alive.radiant (he i)
   obtain ⟨C,g,hg,hC⟩:= shoots (f:=fun k i=>(T (u (v k)) i).sold) fun i=> hv.tendsto_atTop.eventually (cards (he i))
   have hm:=hv.comp hg; let z :ℕ→ℕ:=u∘v∘g; have hz:Tendsto z atTop atTop:=hS.comp hm.tendsto_atTop; have hu i:= (hP i).comp hg.tendsto_atTop
   let R (i):=printZ (rowPath (A.roots i)) (V i) (C i); let f:Motto a:=fun i=>⟨R (i+1),C (i+1),R i,C i,(U.stationary 0 i),P i⟩
   have he' i:Flagship.Beacon (fun k=> (T (z k) i).stock) (C (i+1)) (a.params (i+1)).paths (a.clock.loopCap (i+1)):=surprise (f:=fun k=> (T (z k) (i+1)).sold) ((hz.eventually (eventually_gt_atTop (i+2))).mono fun k hk=> (H.links i (z k) hk).symm) (hC _)
   have Hm (i:ℕ): ∀ᶠ k in atTop,Alive Q O J V (T (z k) i) (z k):= hm.tendsto_atTop.eventually (he i)
   choose Ψ hΨ hΩ using fun i=> casting (F:=f i) h A hz (Hm i) rfl rfl _ _ (he' i) ⟨rfl,rfl,rfl⟩ (hC i) ⟨rfl,rfl,rfl⟩ (hu i)
   let Q0:Motto a:=fun i=> { f i with Ψ:=Ψ i }; exact ⟨Q0,v ∘ g,hm,⟨fun i=> ⟨rfl,rfl,(hΨ (i+1)).out,hΨ i⟩,fun _=>rfl,fun _=>rfl⟩, ⟨ hu,hC,he', hΩ⟩⟩
omit A -- unnecessary syntax H and A required elsewhere
variable {A}
include hp H
private lemma payments (he:Tendsto u atTop atTop) (i:ℕ):∀ᶠ k in atTop, Alive Q O J V (T (u k) i) (u k) ∧ feeB a (i+1) ((T (u k) i).input):= (he.eventually (eventually_gt_atTop _)).mono fun k hk=> ⟨(H.pamphlets _ _ hk).2.2.2.2,(H.pamphlets _ _ hk).1.symm ▸ hp.sight.linked.cap _ _ hk.le⟩
omit h H hp in
private lemma winds_down (f:ℕ→ℝ)(h:∀ i,0≤f i)(he:∀ i,f i≤2)(hp:∀ i,f i ≤1/4*f (i+1)):∀ i,f i=0:=by
     intro i; have ht n: f i≤(1/4:ℝ)^n*2:=by
          suffices hh: ∀ i, f i≤ (1/4:ℝ)^n*2 by exact hh i
          intro i; induction n generalizing i with
          | zero=> simpa using he i
          | succ n ih=> rw [pow_succ',mul_assoc]; exact (hp i).trans (mul_le_mul_of_nonneg_left (ih (i+1)) (by norm_num))
     exact le_antisymm (by refine le_of_tendsto_of_tendsto' (tendsto_const_nhds (f:=atTop)) ?_ ht; simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num:0 ≤ (1/4:ℝ)) (by norm_num)).mul_const 2) (h i)
variable {F B:Motto a}(hv:Cypress A Q O V F)(hm: Cypress A Q O V B)(hU: Tendsto u atTop atTop)(hs:Slip T F u)
include hv hm hU hs A
lemma bud (x:Wish)(Hc:∀ i,x.ord (F i).stock (B i).stock): ∀ i, x.reads (B i).sold= x.reads (F i).sold:=by
    let g(i:ℕ):= x.coins V a i (x.reads (B i).sold - x.reads (F i).sold)/x.tap a i
    have hx₀ i : 0< x.tap a i:=lawful h x i
    have he i:x.coins V a i (x.reads (B i).sold)≤ x.tap a i:= x.stellar (hm.line i|>.honored.goes) (hm.line i|>.honored.out)
    have he' i:x.coins V a i (x.reads (F i).sold)≤ x.tap a i:= x.stellar (hv.line i|>.honored.goes) (hv.line i|>.honored.out)
    have hh₁ i:=x.vista (h.daily.vista i)
    have hp₁ i:0 ≤ g i:=div_nonneg (cover_at (hh₁ i) _) (hx₀ i).le
    have hp₂ i:g i≤2:=(div_le_iff₀ (hx₀ i)).mpr ((grime (hh₁ i) ..).trans ((add_le_add (he _) (he' _)).trans (two_mul _ |>.ge)))
    have hp₃ i: g i ≤ 1/4*g (i+1):=by
         have hZ:Flagship.Rig (V (i+1)) (B i).stock (a.S.side (i+1)) (a.params (i+1)).paths (a.clock.loopCap (i+1)):=by rw [hm.latch]; exact (hm.line (i+1)|>.honored.shape)
         have he:= affinity h x (f:=fun k=>T (u k) i) hU (hv.line i) (hm.line i) _ _ (hs.next i) (hs.gems i) hZ.2.1 hZ.2.2.2.1 hZ.2.2.2.2.2 (payments h hp H hU i) (Hc _)
         rw [hm.latch,hv.latch] at he; exact he
    intro i; have he:= ((div_eq_zero_iff).mp (winds_down g hp₁ hp₂ hp₃ i)).resolve_right (hx₀ i).ne'; exact sub_eq_zero.mp (money (hh₁ i) he)
lemma daylight (i:ℕ): (B i).α=(F i).α ∧ (B i).sold=(F i).sold ∧ (B i).receipts=(F i).receipts ∧ ∀ j U k, iteratedFDeriv ℝ k ((B i).Ψ j U) 0= iteratedFDeriv ℝ k ((F i).Ψ j U) 0:=by
    have hb i : (B i).sold.b=(F i).sold.b:= bud h hp H hv hm hU hs C (fun _=>trivial) i
    have h₂ i:(F i).stock.b=(B i).stock.b:=by rw [hv.latch,hm.latch]; exact (hb _).symm
    have hc i :(B i).sold.c=(F i).sold.c:=bud h hp H hv hm hU hs D h₂ i
    have h₃ i:(F i).stock.c=(B i).stock.c:=by rw [hv.latch,hm.latch]; exact (hc _).symm
    have hX i:(B i).sold.a=(F i).sold.a:=bud h hp H hv hm hU hs Wish.K (fun i=>⟨h₂ i,h₃ i⟩) i
    have hE i:(B i).sold=(F i).sold:=by
         cases hd:(F i).sold with
         | mk a b c=> cases he:(B i).sold with
             | mk d e f=> have h1:=hX i; have h2:=hb i; have h3:=hc i; rw [hd,he] at h1 h2 h3; dsimp only at h1 h2 h3; rw [h1,h2,h3]
    have hG i:(B i).stock=(F i).stock:=(hm.latch i).trans ((hE _).trans (hv.latch i).symm)
    have hY i:(B i).receipts=(F i).receipts :=by
       have hh:∀ (R:PathData G)(T:Flagship G),Lash (V i) T R→R=printZ R.row (V i) T:=by rintro ⟨r,v,x,y⟩ T ⟨h1,h2,h3⟩; dsimp only at h1 h2 h3; rw [h1,h2,h3]; rfl
       refine ((hh _ _ (hm.line i|>.honored.goes)).trans (Eq.trans ?_ (hh _ _ (hv.line i|>.honored.goes)).symm))
       rw [(hm.line i).leaf,(hv.line i).leaf,hE i]
    have hP:= (hm.rows i).trans ((hY _).trans (hv.rows i).symm)
    refine ⟨?_,hE i,hY i,fun j U k=>?_⟩
    · obtain ⟨x⟩:=h.nonterm; have he:=Tale.replay (hv.line i|>.honored) (hv.line i|>.honored) (hm.line i|>.honored) x h.helps 0 rfl (by rw [hP]) rfl (by rw [hY]) rfl (h₂ _) rfl (h₃ _) (by rw [hG]; simp)
      simpa only [sub_self,mul_zero,add_zero] using he.1
    let «W»:= (F i).input; obtain ⟨A,B',H'⟩:= (hm.line i).honored.score j U; have ht:= (hv.line i).honored.score j U
    rw [hP] at A B'
    let t:=(keyQ a i j); obtain ⟨hy,-⟩:= Change.compare (matches_self (k+1) (B'.2.2 t).1) (station_of B' t) (station_of ht.2.1 t) (definite_of A (Q.price _) t (B'.2.2 t).1)
    exact (hy.refl_comp (u:=Prod.snd) contDiffAt_snd).jets _ le_rfl
end YM.Stationary.Artes
