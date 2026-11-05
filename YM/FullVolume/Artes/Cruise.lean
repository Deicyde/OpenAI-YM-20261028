import YM.FullVolume.Artes.Gears
/-! Fixed level allPeriods Arc.Passing. Row.Shape and actual toll. -/
set_option autoImplicit false
noncomputable section
namespace YM.Stationary.Artes
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Supply
open Shade Beacon Flagship ConeRay Tralis WilsonStartup WilsonStartup.Change WilsonStartup.Change.Reading Next.Free Next.Free.Retort
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical InnerProductSpace
variable {G: Gauge}{a:Levels G} {s: Sheet G} {L: Rolls s}{Q:PostCost L}{O:ChartRatio G}{i:ℕ}
variable {F H W: Tale a i}{J : Horizon a}{V:ℕ→ Reel G}{X:MapPrices}(h:Counter a J (O:=O) Q V X)
-- Fixed list references
structure Archive (a: Levels G)(J:Horizon a) where
    roots:ℕ→ Bed
    origins i:Tendsto (fun n=> (J.H n i).roots) atTop (𝓝 ((roots i).roots))
    gifts i:Tendsto (fun n=> (J.H n i).metric) atTop (𝓝 ((roots i).metric))
namespace Archive
lemma held (H:Amplify J): Nonempty (Archive a J):=by
    choose g hg using H.roots; choose v hv using H.metric; exact ⟨⟨fun i=>{J.H 0 0 with roots:= g i,metric:=v i},hg,hv⟩⟩
end Archive
local notation "μ"=> a.S.side i
local notation "B"=> a.params i
variable (Y: Archive a J) {N:ℕ→ℕ}(he:Tendsto N atTop atTop)
include Y he
lemma trams {P:ℕ→PathData G}(hP:∀ᶠ n in atTop,(P n).row=rowPath (J.H (N n) i)){R:PathData G}(hR: R.row=rowPath (Y.roots i)){w b:ℝ}(hw:0<w)(ht:∀ᶠ i in atTop,∀ x, SumBudget (fun j=>|(P i|>.row x j).1| * Real.exp (w*(P i|>.row x j).2.length)) b): Drive P R w b :=by
    refine ⟨hw,hP.mono fun j hp=>by rw [hp]; exact fun _ _=> rfl,by rw [hR]; exact fun _ _=> rfl,fun x n=>?_,ht⟩
    rw [hR]; exact (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp ((Y.origins i).comp he) _) _) _).congr' (hP.mono fun i hp=> by dsimp only; rw [hp]; rfl)
variable {f:ℕ→ Tale a i}(hv:∀ᶠ k in atTop,Alive Q O J V (f k) (N k))(hX: F.input.row=rowPath (Y.roots (i+1))) (hY:F.receipts.row=rowPath (Y.roots i))
  (s1 s2:ℝ) (hp:Flagship.Beacon (fun i=> (f i).stock) F.stock s1 s2)(hc:Lash (V (i+1)) F.stock F.input)
  (ht:Flagship.Beacon (fun k=> (f k).sold) F.sold (a.params i).paths (a.clock.loopCap i))(hd:Lash (V i) F.sold F.receipts)
include hv h
local notation "p"=> a.params (i+1)
include hp hX hc
lemma pays : Calm (V (i+1)) (fun k=> (f k).input) F.input (p).clip (p).width ((p).paths*64) (64* a.clock.loopCap (i+1)):=by
   have hg := hv.mono fun i hi=> hi.stories.bounds
   exact ⟨ hg,trams Y he (hv.mono fun i hi=> hi.inside) hX (p).width_pos (hv.mono fun i hi=> (show PathData.Bounds _ _ _ _ _ from hi.stories.bounds).rows),h.daily.vista _, fun i=> (f i).stock,_,_,_,hp,hc,hv.mono fun i hi=>hi.stories.arrives ⟩
omit hp hX hc
include ht hY hd
lemma picks : Calm (V i) (fun k=>(f k).receipts) F.receipts (B).clip (B).width (B).paths (a.clock.loopCap i):=by
   exact ⟨hv.mono fun i hi=> hi.stories.out,trams Y he (hv.mono fun i hi=> hi.paid.lives.row) hY (B).width_pos (hv.mono fun i hi=> hi.stories.out.rows),h.daily.vista _,fun k=>(f k).sold,_,_,_,ht,hd,hv.mono fun k hk=>hk.stories.goes⟩
omit ht hY hd
private lemma dossier {H:Tale a i}(hc:Calm (V i) (fun k=>(f k).receipts) H.receipts (B).clip (B).width (B).paths (a.clock.loopCap i)): Tender H.ancient (slots (Y.roots i).metric G) ∧ ∀ x,alphaPay x (slots (Y.roots i).metric G)=1 :=by
   let X':= Y.roots i|>.metric; have hp:=h.staple
   let p0:=X.α (a.clock.J i); have hT : Next.Free.Retort.Fleet (fun k=> (J.H (N k) i).metric) X' p0 (X.Ω (a.clock.J i)):=⟨(Y.gifts i).comp he,X.alpha_pos _,(he.eventually (eventually_ge_atTop i)).mono (fun k hk=> (hp.rows _ _ hk).2.1)⟩
   refine ⟨⟨fun j=>(stain_knit _ _ hc.guides).analytic,⟨_,_,hT.kept,slots_cost hT.kept hT.lives⟩,fun j=> according (Row.rights _ _ hT.lives hT.kept.le) ?_⟩,fun x=>?_⟩
   · intro x y
     let g(c:Matrix (Body 2 (μ j)) (Body 2 (μ j)) ℝ):ℝ:=∑ i,parts G 1 (arm G (μ j) 1 x) i ⬝ᵥ (Precision.K c *ᵥ parts G 1 (arm G _ 1 y) i); have hr:Continuous g:=by unfold g Precision.K; fun_prop -- fail
     have hp0 : View (fun n=> (f n).ancient j) (H.ancient j) 0 0:= Beacon.arena hc.hearth (Stationary.input G (μ j)) (fun i=> ((Work.F03.represent_smooth i).comp (arm G _ _).contDiff).contDiffAt) _
     have hx := (ContinuousMultilinearMap.apply ℝ _ ℝ ![x,y]).continuous.continuousAt.tendsto.comp (hp0.goals 2)
     apply tendsto_nhds_unique hx ((hr.continuousAt.tendsto.comp (hT.muster _)).congr' (hv.mono ?_))
     intro k hk; exact (low_columns hk.stories.out hk.paid.lives.ties (hp.all _ _ hk.step.le _) (h.oath (N k) i hk.step.le _) |>.2.2 x y).symm
   rw [alphaPay, tip_fuel x hT.lives hT.kept (show X'.read 0=1 from ?_)]
   · norm_num
   exact tendsto_nhds_unique_of_eventuallyEq (hT.reads («p»:=0) (by unfold Next.Free.physical; simp)) tendsto_const_nhds (hv.mono fun k hk=> (h.staple.all _ _ hk.step.le 1).starts)
-- rethread graph.Migrate.Archive fixed
include hX hY hc ht hd hp
set_option maxHeartbeats 600000 in
lemma casting (hm:Tendsto (fun n=>(f n).α) atTop (𝓝 F.α)):
     ∃ Ψ:GainWire a i, Tale.Earns Q O V (Y.roots i).metric { F with Ψ:= Ψ } ∧ ∀ j (B' :Forest (a.clock.op i j).ratio), View (fun k=>(f k|>.Ψ) j B') (Ψ j B') 0 0 :=by
    have hC:= pays h Y he hv hX _ _ hp hc; have hP:= picks h Y he hv hY ht hd
    have H j (B':Forest (a.clock.op i j).ratio): ∀ᶠ k in atTop,Critical B' (p).clip (f k|>.input) ((f k).Ψ j B')∧PriceGap B' (p).clip (f k|>.input) (Q.η (a.clock.J (i+1))):= hv.mono fun i hi=> let h:= hi.stories.score j B';⟨h.2.1,h.1⟩
    have hW:= Q.price (a.clock.J (i+1)); choose Ψ hΨ using fun j b=> Beacon.pollination hC (H j b) hW ((a.blocks i j).branches)
    let P:= { F with Ψ:= Ψ }
    have hr :Flagship.Rig (V i) F.sold (a.S.side i) (a.params i).paths (a.clock.loopCap i):=
       ⟨(V i|>.e2).recurrences _ (hv.mono fun i hi=>hi.stories.shape.1) ht.a, ht.a.weight,(V i|>.e3).recurrences _ (hv.mono fun i hi=> hi.stories.shape.2.2.1) ht.b,ht.b.weight,(V i|>.e4).recurrences _ (hv.mono fun i hi=> hi.stories.shape.2.2.2.2.1) ht.c,ht.c.weight⟩
    have hX j (b:Forest (a.clock.op i j).ratio):= Beacon.dreams hC (H j b) (hΨ j b) hW
    obtain ⟨ha,hs⟩:=dossier h Y he hv hP
    refine ⟨Ψ,⟨hc, hd,hr,hC.guides,hP.guides,ha,hs,fun j b=> ⟨ Beacon.hatch hC (H j b), hΨ j b,?_⟩,fun j x y R S he hi=>?_⟩, hX⟩
    · intro m hm t; let u := arm G (a.S.side i j) 1
      have hg :=hC.pullback (H j b) t; let g (i:ℕ):= WilsonStartup.Change.graph ((f i).Ψ j b)
      let W:=WilsonStartup.Change.graph (Ψ j b); have hz: W 0=0:= Prod.ext rfl (hΨ j b).1; have hy: View g W 0 0 := (View.checked (x:=fun _=>0) contDiffAt_id tendsto_const_nhds).twins (hX j b)
      have hc:=hy.comp (H:=onSlice b t (p).clip F.input) (h:=fun i=>onSlice b t (p).clip (f i).input) (hz.symm ▸ hg.points (show _ from hv.mono fun i hi=>Eq.symm (show g i 0=0 from Prod.ext rfl ((hi.stories.score j b).2.1.1)))) -- fix
      let U:= fun (S:PathData G)=> mainTerm (B).clip S ∘ (represent (n:= a.S.side i j))
      have hv' : View (fun n=> U (f n|>.receipts)) (U P.receipts) 0 0:=by
         have hV : View (fun _ :ℕ=>(fun i=>u.symm i)) (fun i=>u.symm i) (fun _=>0) (0:fieldDir G _ 1):= View.checked (F:=fun x=> u.symm x) (u.symm.contDiff.contDiffAt) tendsto_const_nhds -- coercion
         refine (hV.comp (H:=intended (B).clip P.receipts) (h:=fun n=> intended (B).clip (f n|>.receipts)) ?_).ferry ?_ ?_
         · simp_rw [u.symm.map_zero]; exact hP.harvest.1
         · exact Eventually.of_forall fun x=> by simp [U,intended,Stationary.input,Function.comp_def,u]
         exact Eventually.of_forall fun i=> Eventually.of_forall fun x=> by simp [U,intended,Stationary.input,Function.comp_def,u]
      exact ⟨hc.star,hv'.star,tendsto_nhds_unique ((hc.goals m).congr' (hv.mono fun i hi=>(hi.stories.score j b|>.2.2 m hm t).2.2)) (hv'.goals m)⟩
    let b:= treeQ a i j; let t:=keyQ a i j
    let L:=arm G (a.S.side i j) 1; have heq : View (fun n=> f n|>.steaming O j) (P.steaming O j) 0 0 :=by
       have hE:= Beacon.steam hC (H j b) (hΨ j b) h.helps hW t; refine (View.checked (F:=fun i=> L i) (x:=fun _=>0) L.contDiff.contDiffAt tendsto_const_nhds).comp ?_; simp_rw [L.map_zero]; exact hE
    have hs' : View (fun n=> f n|>.ancient j) (F.ancient j) 0 0:=Beacon.arena hP.hearth (Stationary.input G (μ j)) (fun i=> ((Work.F03.represent_smooth i).comp (arm G _ _).contDiff).contDiffAt) _
    have hB' : View (fun n=> f n|>.traceN j) (F.traceN j) 0 0:= hP.harvest.2
    have h' (T:Tale a i)(h:ContDiffAt ℝ ω (T.ancient j) 0)(ht:ContDiffAt ℝ ω (T.traceN j) 0): tick (μ) T.pence j=T.α • (tick _ T.ancient j)+tick _ T.traceN j:=by
       change iteratedFDeriv ℝ 2 (T.α • T.ancient j + T.traceN j) 0 = T.α • (iteratedFDeriv ℝ 2 (T.ancient j) 0)+iteratedFDeriv ℝ 2 (T.traceN j) 0; rw [iteratedFDeriv_add_apply (show ContDiffAt ℝ 2 (T.α • T.ancient j) 0 from (h.of_le le_top).const_smul T.α) (ht.of_le le_top),iteratedFDeriv_const_smul_apply (h.of_le le_top)]
    have hX : Tendsto (fun n=> (f n).prices O j) atTop (𝓝 (P.prices O j)):=by
       change Tendsto _ _ (𝓝 ((tick _ (P.steaming O)) j - tick (μ) P.pence j)); rw [h' P hs'.star hB'.star]; exact ((heq.goals 2).sub ((hm.smul (hs'.goals 2)).add (hB'.goals 2))).congr' ((hs'.against.and hB'.against).mono fun n hx=> congr_arg (fun z=> tick (μ) ((f n).steaming O) j-z) (h' (f n) hx.1 hx.2).symm)
    exact le_of_tendsto (((ContinuousMultilinearMap.apply ℝ _ ℝ ![pew x R,pew y S]).continuous.continuousAt.tendsto.comp hX).abs) (hv.mono fun k hk=> hk.stories.credit _ x y R S he hi)
end YM.Stationary.Artes
#print axioms YM.Stationary.Artes.casting
