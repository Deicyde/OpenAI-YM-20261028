import YM.TraceExtension.Margin.Vote
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Margin
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open Next.Rank East
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Graces PhysicalNext.Repeat.Roost
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open Push.PriceCompiler WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset Planned.GuardedAtom Guard
open Shepherd StressFlux Perfect Loft Zn Shunt Wicket Turret Weir Terrace
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
section
variable (C:Family G)
abbrev Tickets:= ∀ k N p:ℕ, Quilt (C.labels.level 5) (C.side k p)
def Grant (𝓛:Filter (ℕ×ℕ))(t:Tickets C):Prop:= ∀ᶠ k in atTop,let x:= C.path.levels.clock.hatBeta k; ∀ᶠ p in 𝓛,WorthB C.labels C.localSection C.params (C.path.levels.params k) x (C.path.levels.clock.loopCap k) (C.path.rep p.1 p.2 k) (t k p.1 p.2)
lemma nice {F:Labels.Frame G 5}{n:Side}: Nonempty (Quilt F n):= ⟨⟨⟨0,0,0,0,0⟩,∅,∅,∅,fun _=> ⟨0,fun _=>∅,0,0⟩⟩⟩
end
variable {M:Metals G}{D:Rolls M.p}{A:Alloy M D}{X:Factor A}{Y:ℕ→ℝ}{B:Bid.Worth}{T:Bolt A}
variable {t:ℕ→ℕ}{U:∀ d N p:ℕ,TransferData ((Labels.frames G).level d) (Issue.trail T) N p}
variable (b:Bandage X Y B)(h:Nest X T) (hp:Vigil A.B.a)(θ:Acclaim A.B.a)(hs:supportQ A.B.a)(hG:G.Simple)
include hp h b θ hG hs
lemma agenda (𝓛:Filter (ℕ×ℕ))(hx:Tendsto Prod.fst 𝓛 atTop)(hv:Tendsto Prod.snd 𝓛 atTop): let C:= Family.mk (Issue.trail T) (Next.Foundations.hol G) (Labels.frames G) (localSection G) t U
    ∃ X:Tickets C,Grant C 𝓛 X:=by
    intro P; let K:=A.B.a; let V(i:ℕ)(p:ℕ×ℕ)(t:Quilt (P.labels.level 5) (P.side i p.2)):= WorthB P.labels P.localSection P.params (K.params i) (K.clock.hatBeta i) (K.clock.loopCap i) (P.path.rep p.1 p.2 i) t
    let TF (i:ℕ)(p:ℕ×ℕ):= if h:∃ q,V i p q then h.choose else Classical.choice nice
    refine ⟨fun k N p=>TF k (N,p),?_⟩; filter_upwards [dewWt ‹Bolt A› hp hG (W:=ℕ×ℕ), θ,ancient h hs hG,K.fits.deep.eventually_ge_atTop 5] with i hi ht hV hY
    let x:= K.clock.hatBeta i; let S:= K.params i; have hX:0 < shock x:=by unfold shock; positivity [bell K i]
    have he:= hi (shock x) hX 𝓛 Prod.fst Prod.snd hx hv;
    filter_upwards [he,(deep_n K.S i|>.comp hv).eventually_gt_atTop (20*(high x+rim x+10)),hx.eventually_gt_atTop i] with p hk hl hh; change V i p (TF i p); unfold TF; have hf:∃ t,V i p t:=by
        obtain ⟨Q,hΩ,hq,hz⟩:=hk; let R:=P.path.rep p.1 p.2 i; let L:= K.clock.loopCap i; have hz₁(d:ℕ)(hx:d≤5):Push.Local.Readable P.params (P.localSection d) R.p (K.S.side i p.2) (coupon G S):=by
            have hu:R.p=K.budget i:=(‹Bolt A›.choice.represents _ _ _ hh.le).vac; rw[hu]; exact livelyCard (A:=A) (n:=p.2) b.clock (hx.trans hY)
        obtain ⟨k,h₁,h₂⟩:= ht.1.sure L _ R Q (hV _ _ hh) ⟨hΩ,hq⟩ hl hz (Guard.Keeper.sufficient (Nest.samples hG h _ _ _ hh.le)) hz₁
        exact ⟨k,h₂⟩
    rw[dif_pos hf]; exact Classical.choose_spec hf
end YM.Trace.Margin
