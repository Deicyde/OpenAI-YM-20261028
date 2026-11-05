import YM.FullVolume.Artes.Palm
/-! Female sleeve.Second bootstrap.Credit. Compare l/f across periods.Stamped no need universal per # config.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Stationary.Artes
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Supply
open Shade Beacon Flagship ConeRay Tralis WilsonStartup WilsonStartup.Change WilsonStartup.Change.Reading Next.Free Next.Free.Retort
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical InnerProductSpace
variable {G: Gauge}{a:Levels G} {s: Sheet G}{L: Rolls s}{Q:PostCost L}{O:ChartRatio G}{i:ℕ}
variable {F H: Tale a i}{J : Horizon a}{V:ℕ→ Reel G}{X:MapPrices}
variable (h:Counter a J (O:=O) Q V X) (A: Archive a J) {f:ℕ→ Tale a i}{w:ℕ→ℕ}
open Alive Wish
-- compare one-seed with a limit.F at stamp.Journey includes F Price and Q Upper bounds to avoid copying off-calendar.
structure Bottle {i:ℕ} (T: Tale a i)(A:Archive a J) (V:ℕ→ Reel G) (O:ChartRatio G)(Q:PostCost L):Prop where
    stem:T.input.row=rowPath (A.roots (i+1))
    leaf:T.receipts.row=rowPath (A.roots i)
    input : feeB a (i+1) T.input
    honored:T.Earns Q O V (A.roots i).metric
variable {A}
-- get credit for any real-hybrid
include h
private lemma splice (x:Wish) {T:Tale a i}{N:ℕ}(hu:Alive Q O J V T N)(hg:feeB a (i+1) T.input)(hp:Bottle H A V O Q):
     ∃ P: Tale a i, P.stock=x.pour T.stock (x.reads H.stock)∧ Alive Q O J V P N ∧ feeB a (i+1) P.input:=by
   let S:=x.pour T.stock (x.reads H.stock); let R:= printZ T.input.row (V (i+1)) S
   have hs:Lash (V (i+1)) S R:=⟨rfl,rfl,rfl⟩; have ht:feeB a (i+1) R:= Artes.bond x T.stock H.stock hu.stories.arrives hg hp.honored.arrives hp.input hs rfl
   obtain ⟨P,hh,hV,hX⟩:= destiny h R hu.step (show R.row=rowPath _ from hu.inside) S hs (h.daily.expandR _ ht); exact ⟨P,hV,hX,hh.symm ▸ ht⟩
omit h in
private lemma gemstones (x:Wish){X Y:Flagship G}{v:ℕ→ Flagship G}{a b:ℝ}(he:Flagship.Beacon v Y a b)(h1: ‖X.a‖≤ b)(h2:‖X.b‖≤ a)(h3:‖X.c‖≤ a){g:ℕ→Flagship G}(hu: g=ᶠ[atTop] fun i=>x.pour (v i) (x.reads X)):
    Flagship.Beacon g (x.pour Y (x.reads X)) a b :=by
    suffices ∀ Q:Flagship G,Flagship.Beacon (fun i=> x.pour (v i) (x.reads X)) Q a b→Flagship.Beacon g Q a b by
         apply this; cases x
         · exact ⟨he.a, ⟨Eventually.of_forall fun _=> h2,fun _=>tendsto_const_nhds⟩,he.c⟩
         · exact ⟨he.a,he.b, ⟨Eventually.of_forall fun _=> h3,fun _=>tendsto_const_nhds⟩⟩
         exact ⟨⟨Eventually.of_forall fun _=> h1,fun _=>tendsto_const_nhds⟩,he.b,he.c⟩
    have hr (w:ℕ)(_i:NeZero w) {u v:ℕ→Cameo G w}{U: Cameo G w}{b:ℝ}(h:Gleam u U b)(hx:v=ᶠ[atTop] u): Gleam v U b:=⟨ (hx.and h.budget).mono fun i hi=> hi.1.symm ▸ hi.2, fun i=> (h.hinge i).congr' (hx.mono fun k he=> congr_arg (fun a: Cameo G w=>a i) he.symm)⟩
    intro Q H; exact ⟨hr _ (by infer_instance) H.a (hu.fun_comp Flagship.a),hr _ (by infer_instance) H.b (hu.fun_comp Flagship.b),hr _ (by infer_instance) H.c (hu.fun_comp Flagship.c)⟩
-- compare cluster F outputs following actual w versus H.
lemma affinity (x:Wish)(he:Tendsto w atTop atTop)(hp:Bottle F A V O Q)(hh:Bottle H A V O Q)
   (b B:ℝ)(ht:Flagship.Beacon (fun k=>(f k).stock) F.stock b B)(hw:Flagship.Beacon (fun k=>(f k).sold) F.sold (a.params i).paths (a.clock.loopCap i))
   (hb: ‖H.stock.a‖ ≤ B)(hB:‖H.stock.b‖≤ b)(hc:‖H.stock.c‖≤ b)
   (hf:∀ᶠ k in atTop, Alive Q O J V (f k) (w k) ∧ feeB a (i+1) (f k).input) (hy:x.ord F.stock H.stock):
   x.coins V a i (x.reads H.sold - x.reads F.sold)/x.tap a i ≤ (1/4:ℝ)*(x.coins V a (i+1) (x.reads H.stock-x.reads F.stock) / x.tap a (i+1)):=by
    obtain ⟨M,hM⟩:= eventually_atTop.mp hf; haveI :Nonempty (Tale a i):=⟨F⟩; choose! g hG hz hX using fun n (hn:M≤n)=>splice h x (hM n hn).1 (hM n hn).2 hh
    let Q':= x.pour F.stock (x.reads H.stock); have he₁ : ∀ᶠ n in atTop, Alive Q O J V (g n) (w n):= (eventually_ge_atTop M).mono fun i hh=> hz i hh
    obtain ⟨U,d,B',hD,hc',hU⟩:= Alive.talison he₁
    let v:=w ∘ d; have hpD:=hD.tendsto_atTop; have hE:= (show Tendsto w atTop atTop from ‹Tendsto w atTop atTop›).comp hpD
    let T: Tale a i :=⟨ printZ F.input.row (V (i+1)) Q', Q', printZ F.receipts.row (V i) U,U,(F.Ψ), B'⟩
    have ha' : ∀ᶠ k in atTop, Alive Q O J V (g (d k)) (v k):= hpD.eventually he₁
    have hv':∀ᶠ i in atTop, (g i).stock=x.pour (f i|>.stock) (x.reads H.stock):= (eventually_ge_atTop M).mono fun i hh=> hG _ hh
    have hv :Flagship.Beacon (fun k=> (g (d k)).stock) T.stock b B:= gemstones x (drivenF hpD ht) hb hB hc (hpD.eventually hv')
    obtain ⟨Ξ,H',h'⟩:= casting (F:=T) (f:=g ∘ d) h A hE ha' hp.stem hp.leaf b B hv (by exact ⟨rfl,rfl,rfl⟩) hU (by exact ⟨rfl,rfl,rfl⟩) hc'
    obtain ⟨j⟩:= h.nonterm; have hr : x.reads H.sold=x.reads T.sold:=by
         have He : x.reads H.stock=x.reads T.stock := (Wish.at_pour ..).symm
         let R:= { T with Ψ:=Ξ }
         have hR:Tale.Earns Q O V (A.roots i).metric R:=H'
         have Hx: x.ord R.stock H.stock := x.ord_trans (x.ord_symm (Wish.ord_pour ..)) hy --fix
         have ht:=x.traffic hR hR hh.honored j h.helps 0 rfl (hp.stem.trans hh.stem.symm) rfl (hp.leaf.trans hh.leaf.symm) (x.ordained _) Hx (by change x.reads H.stock=_; simp; exact He)
         simpa [R] using ht
    rw [hr,show x.reads H.stock=x.reads T.stock from (Wish.at_pour ..).symm]; refine le_of_tendsto_of_tendsto ((trinket (F:=x.reads T.sold) (x.brace hU) (x.brace (drivenF hpD hw)) (x.vista (h.daily.vista i))).div_const (x.tap a i)) (((trinket (x.brace hv) (x.brace (drivenF hpD ht)) (x.vista (h.daily.vista (i+1)))).div_const (x.tap a (i+1))).const_mul (1/4:ℝ)) ?_
    filter_upwards [hpD.eventually_ge_atTop M] with n hN; exact Alive.snips h x (hM (d n) hN).1 (hz _ hN) (hM _ hN).2 (hX _ hN) (by rw [hG _ hN]; exact Wish.ord_pour ..)
end YM.Stationary.Artes
