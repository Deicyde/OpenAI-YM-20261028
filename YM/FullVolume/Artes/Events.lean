import YM.FullVolume.Artes.Letters
/-! Solar limit Kernel K full topology.Performance Pilot.With canonical selected labels, not gauge quotient. -/
set_option autoImplicit false
noncomputable section
namespace YM.Stationary.Artes
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Supply
open Shade Beacon Flagship ConeRay Tralis WilsonStartup WilsonStartup.Change WilsonStartup.Change.Reading Next.Free Next.Free.Retort
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical InnerProductSpace
variable {G: Gauge}{a:Levels G} {s: Sheet G}{L: Rolls s}{Q:PostCost L}{O:ChartRatio G}
variable {J:Horizon a}{V:ℕ→Reel G}{X:MapPrices}{U:Kin J O}
lemma travels {ι:Type}[TopologicalSpace ι] {f:ℕ→ι}{x:ι} (h:∀ u:ℕ→ℕ,StrictMono u→ ∃ v:ℕ→ℕ, StrictMono v∧ Tendsto (fun i=> f (u (v i))) atTop (𝓝 x)): Tendsto f atTop (𝓝 x):=by
    apply tendsto_def.mpr; intro b hb
    by_contra hu; obtain ⟨g,hg,H⟩:= extraction_of_frequently_atTop (show ∃ᶠ i in atTop, f i∉b from fun k=>hu (k.mono fun i hi=>not_not.mp hi))
    obtain ⟨u,h,hX⟩:= h _ hg; obtain ⟨i,hi⟩:= (hX.eventually hb).exists; exact H _ hi
open Alive Wish
lemma supreme (h: Counter a J (O:=O) Q V X) (hp:Inspected U Q V)(A:Archive a J):
    ∃ (T:ℕ→Motto a)(F:Motto a),Roadie T U Q V∧ Cypress A Q O V F ∧ ∀ i:ℕ, Flagship.Beacon (fun n=> (T n i).sold) ((F i).sold) (a.params i).paths (a.clock.loopCap i) ∧ Tendsto (fun n=> (T n i).α) atTop (𝓝 ((F i).α)) ∧ ∀ j B k, Tendsto (fun n=> iteratedFDeriv ℝ k ((T n i).Ψ j B) 0) atTop (𝓝 (iteratedFDeriv ℝ k ((F i).Ψ j B) 0)):=by
    obtain ⟨T,H⟩:= author h hp; obtain ⟨P,W,hW,hP,hR⟩:=cruising h A hp H tendsto_id
    refine ⟨T,P,H,hP,fun i=>?_⟩
    have ht:∀ᶠ n in atTop, Alive Q O J V (T n i) n := (eventually_gt_atTop (i+1)).mono fun n hn=> (H.pamphlets n i hn).2.2.2.2
    have hz:=Alive.cards ht
    have hu u (hh:StrictMono (u:ℕ→ℕ)): ∃ K:Motto a,∃ w:ℕ→ℕ, StrictMono w∧ Slip T K (u∘w)∧ (K i).α=(P i).α ∧ (K i).sold= (P i).sold ∧ ∀ j B k, iteratedFDeriv ℝ k ((K i).Ψ j B) 0= iteratedFDeriv ℝ k ((P i).Ψ j B) 0:=by
       obtain ⟨K,w,hw,hK,H'⟩:=cruising h A hp H hh.tendsto_atTop
       obtain ⟨h1,h2,h3,h4⟩:=daylight h hp H hP hK (u:=W) hW.tendsto_atTop hR i -- v/u id
       exact ⟨K,w,hw,H',h1,h2,h4⟩
    refine ⟨?_,?_,fun j B k=> travels fun u hh=>?_⟩
    · refine ⟨⟨hz.mono fun n hn=> hn.1,fun x=> travels fun u hh=>?_⟩, ⟨hz.mono fun n hn=> hn.2.1,fun x=> travels fun u hh=>?_⟩,⟨hz.mono fun n hn=>hn.2.2,fun x=> travels fun u hh=>?_⟩⟩ <;> obtain ⟨K,w,hw,hk,h1,h2,h4⟩:= hu u hh
      · refine ⟨w,hw,?_⟩; have hx:=(hk.gems i).a.hinge x; rw [h2] at hx; exact hx
      · refine ⟨w,hw,?_⟩; have hx:=(hk.gems i).b.hinge x; rw [h2] at hx; exact hx
      refine ⟨w,hw,?_⟩; have hx:=(hk.gems i).c.hinge x; rw [h2] at hx; exact hx
    · refine travels fun u hh=>?_ ; obtain ⟨K,w,hw,hk,h1,h2,h4⟩:= hu u hh; exact ⟨w,hw,h1 ▸ hk.free i⟩
    obtain ⟨K,w,hw,hk,h1,h2,h4⟩:=hu u hh; have hz:=(hk.toll i j B).goals k; rw [h4] at hz; exact ⟨w,hw,hz⟩
-- ease publicity
structure Cadre(Q:PostCost L)(U:Kin (a:=a) J O) :Prop where
   evolution:∀ (i:ℕ),let b:=a.params i -- a suffers incompatible; adjust name explicit levels binder
         ∃ R:PathData G,∃ V:Reel G, V.Price b.width ∧ R.Bounds b.clip b.width b.paths (a.clock.loopCap i) ∧ Calm V (fun k=> U.path k i) R b.clip b.width b.paths (a.clock.loopCap i)
   accounts (i:ℕ):∃ v,Tendsto (fun n=> U.alpha n i) atTop (𝓝 v)
   station i j B k: ∃ W,Tendsto (fun n=> iteratedFDeriv ℝ k (U.stationary n i j B) 0) atTop (𝓝 W)
   jac (i:ℕ):∃ v b,(a.params i).width < v ∧ ∀ᶠ n in atTop,∀ f: PlaqAxes,SumBudget (fun k=> |((U.path n i).row f k).1| * Real.exp (v*((U.path n i).row f k).2.length)) b
lemma xerox {S T:ℕ→PathData G}{V:Reel G}{R:PathData G}{p:Clip}{w a b:ℝ}(h:Calm V S R p w a b)(he:S=ᶠ[atTop] T): Calm V T R p w a b:=by
   have hx:=h.hearth
   refine ⟨(h.retained.and he).mono (fun i hi=> hi.2 ▸ hi.1),⟨hx.wage,(he.and hx.flit).mono (fun i hi=> hi.1 ▸ hi.2),hx.here, fun i j=>(hx.ink i j).congr' (he.mono fun x hz=> by dsimp only; rw [hz]),(he.and hx.sails).mono fun i hi=> hi.1 ▸ hi.2⟩,h.wide,?_⟩
   obtain ⟨p,Q,h,H,I,T'⟩:= h.stars; exact ⟨p,Q,h,H,I,T'.1,(he.and T'.2).mono fun i hi=> hi.1 ▸ hi.2⟩
lemma yields (h: Counter a J (O:=O) Q V X) (hp:Inspected U Q V)(ht:Amplify J): Cadre Q U:=by
   obtain ⟨A⟩:=Archive.held ht; obtain ⟨T,F,hT,hF,H⟩:=supreme h hp A
   have hv i: ∀ᶠ n in atTop, i+1<n:= eventually_gt_atTop _
   constructor
   · intro i b; let Y(n:ℕ):=T n i
     have ha:∀ᶠ i in atTop, Alive Q O J V (Y i) i := (hv i).mono fun j hz=> (hT.pamphlets j i hz).2.2.2.2
     have hp:= picks (f:=Y) h A tendsto_id ha (hF.line i).leaf (H i).1 (hF.line i).honored.goes
     exact ⟨(F i).receipts,_,hp.wide,hp.guides,xerox hp ((hv i).mono fun n hn=> (hT.pamphlets n i hn).2.1)⟩
   · intro i; exact ⟨_,(H i).2.1.congr' ((hv i).mono fun n hn=>(hT.pamphlets n i hn).2.2.2.1)⟩
   · intro i j B k; refine ⟨_,((H i).2.2 j B k).congr' ((hv i).mono ?_)⟩; intro n hn; dsimp only; rw [(hT.pamphlets n i hn).2.2.1]
   intro i; obtain ⟨v,b,hv,hg⟩:= h.daily.glyph i; refine ⟨v, rowPrice v b,hv,?_⟩
   filter_upwards [hg,eventually_ge_atTop i] with n hn hx f; rw [hp.sight.row n i hx]; exact price_paths hn f
-- Permit numerical retarget & hidden layer price. explicit a? can't with Cadre.a.
lemma replayQ {W': Horizon a}{Z:Kin W' O}(h:Cadre Q U)(hp:∀ i,(fun n=> U.path n i)=ᶠ[atTop] fun n=>Z.path n i)(he:∀ i,(fun n=> U.alpha n i)=ᶠ[atTop] fun n=>Z.alpha n i)(ht:∀ i j F,(fun n=> U.stationary n i j F)=ᶠ[atTop] fun n=>Z.stationary n i j F): Cadre Q Z:=by
    refine ⟨fun i=>?_,fun i=>⟨_,(h.accounts i).choose_spec.congr' (he _)⟩, fun i j F k=>⟨_,(h.station i j F k).choose_spec.congr' ( (ht _ _ F).mono fun n hz=>congr_arg (fun v=>iteratedFDeriv ℝ k v 0) hz)⟩,fun i=>?_⟩
    · obtain ⟨R,S,A,C,H⟩:=h.evolution i; exact ⟨R,S,A,C,xerox H (hp i)⟩
    obtain ⟨v,b,H,C⟩:= h.jac i; refine ⟨v,b,H,C.mp ((hp i).mono ?_)⟩; intro x hx; dsimp only at hx; rw [hx]; exact id
lemma history_copy {W': Horizon a}(h:Amplify J)(he:∀ i,(fun n=>J.H n i)=ᶠ[atTop] fun n=>W'.H n i)(hp:∀ i,(fun n=>J.towers n i)=ᶠ[atTop] fun n=> W'.towers n i): Amplify W':=by
    exact ⟨⟨fun i=> (h.diagonal i).copies ((he i).fun_comp Bed.diagonal),fun i=> (h.dual i).copies ((he i).fun_comp Bed.dual_diag), fun i=>(h.roots i).copies ((he i).fun_comp Bed.roots),fun i=>(h.metric i).copies ((he i).fun_comp Bed.metric),fun i=>(h.inverse i).copies ((he i).fun_comp Bed.inverse)⟩,
       fun i=> (h.prediction i).copies ((hp i).fun_comp Towers.A0),fun i=> (h.T i).copies ((hp i).fun_comp Towers.T),fun i=>(h.mf i).copies ((hp i).fun_comp Towers.mf),fun i=>(h.mn i).copies ((hp i).fun_comp Towers.mn),fun i=>(h.o i).copies ((hp i).fun_comp Towers.o)⟩
end YM.Stationary.Artes
#print axioms YM.Stationary.Artes.yields
