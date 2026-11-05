import YM.RG08.Spar.Station
import YM.RG08.Flat.Mesh

noncomputable section
namespace YM.RG08.Spar
open Forms Rudder Packets Finset Function Lattice Laurent Pert.Bulk Exterior Filter Bloch Anchor Symmetry Isles Stationary RG Rows LinearMap Precision Tree RG08.Line
open scoped Topology BigOperators Classical ENNReal Matrix
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {c f:Side}{P:Patch}{k:KernelChoices}{G:Gauge}{b b':Bed}

/-- License the generic TEMPLATE equality `voucher` on literal cover outputs from using
A_tr in the actual-bulk-formal subroutine, rather than the all-face Ψ line. `H.Suffices`
and Warm refer to the linear flat prescription at this level and finite cutoff/history;
K(Diagonal) agreement on the very same witness tori. Uses quantitative transport and
closing but not actual Hessian convergence/Load derivatives at the physical fields.
-/
theorem inherited {A:Levels G}{H:Horizon A}{R:MapPrices}(hp:H.Suffices R)(m N:ℕ)(hn:m<N)(n:ℕ)(i:Fin n)(τ v σ C D:ℝ)(hτ:0<τ)(hP:τ≤1)(hv:0<v)(hσ:0<σ)(hC:0≤C) (F:Raw G.ColorIndex n)(hF:Cohort F)(_hg:Forms.Sym F)(he:Held (carpet (Tone G.ColorIndex)) σ C F):
 let L:=A.S.block m
 let j:=A.clock.J (m+1)
 let j':=A.clock.J m
 let P:Patch:= (A.clock.op m 0).patch
 let K:=A.clock.kernel
 let b:=H.H N (m+1)
 let μ:=Cell.plotted P K G b
 let U:=fine_share H N m
 let w:=min 1 (min (R.α j) (R.α j'))
 v≤τ→v≤w→v≤L.val*(σ/2)→Cell.Warm G K P b τ D→
 braces μ (compress 1 (picture G.ColorIndex n F))=compress 1 (voucher U F):=by
 intro L j j' P k b μ U w Hv Hw Hl Hwarm
 let V:=prism G.ColorIndex U
 have HT:Atlas w L 2 V (allotment R j j'):=prism_prices U G.ColorIndex (atlas_here hp n hn)
 have hc : city L V:=prism_city U G.ColorIndex (pass_response _ _ _)
 have W:0≤allotment R j j':=HT.nonneg
 let l(t):=A.S.side m t
 let u(t):=A.S.side (m+1) t
 let S(t):StepData (l t) (u t):=A.clock.op m t
 let γ(t):Matrix (cap G.ColorIndex (u t) 1) (cap G.ColorIndex (l t) 1) ℝ:=Cell.RootField k G (S t) b
 let δ(t):Matrix (cap G.ColorIndex (u t) 2) (cap G.ColorIndex (l t) 2) ℝ:=shaded _ _ G.ColorIndex (carrier_share H N m t)
 have Hμ:Priced v (D*Cell.key G P k) (clover L μ):= ((cozy Hwarm hτ.le hP).toPriced.mono Hv le_rfl)
 have HK:Priced v _ (clover L V):=ticket_atlas (T:=U) (atlas_here hp n hn) (pass_response _ _ _) hv.le Hw _
 have ha(t):Matches μ (γ t):=(Cell.viewed Hwarm hτ.le hP (S t).sizes).2 -- size uses eval def?
 have hd(t): Matches V (δ t):=by
    have he:= prism_match (T:=U) G.ColorIndex (values hp hn t)
    intro ⟨x,i,u⟩ ⟨y,j,v⟩; rcases eq_or_ne u v with hz|hz <;> simpa [V,δ,shaded,hz] using he (x,i,u) (y,j,v)
 have hb(t): shaded (u t) (u t) G.ColorIndex ((cobound 1).acts _) * γ t=δ t * shaded (l t) (l t) G.ColorIndex ((cobound 1).acts _):=by
    -- floor clip and pricing from H.plan
    have he:=desk (hp.all N (m+1) hn) Hwarm hτ.le hP (S t).sizes (H.towers N m) (hp.crossings N m t hn) (hp.all N m hn.le)
    exact he
 -- an analytic bound on X exists at any sufficiently tiny aperture before this use (braces may include arity 1 as n above)
 obtain ⟨t,E,he',hE,Hu⟩:∃ t E:ℝ,0<t∧0≤E∧Held (carpet (Kind G.ColorIndex 2)) t E (braces V (compress 2 F)):=by
    let T:=farm L (compress 2 F)
    have hl:v≤L.val*σ:=Hl.trans (by gcongr;nlinarith)
    rw [←braces_farm (L:=L)]
    -- use postblock morph and covers; Tagged cardDeck
    have ht:= ((bureau (farm_path (L:=L) (compress_path 2 hF)) (farm_cost (τ:=v) hv.le hl (compress_cost 2 he) hC) hv (by positivity) i).morph (fun _ :Fin n=>Isles.tagged (cardDeck HK) hv))
    exact ⟨v,_,hv,ht.cost,ht.palm⟩
 exact finish S (A:=γ) (D:=δ) (RG08.Flat.mesh_sides A.S m) i (fun _=>rfl) he hF hC hσ hv Hl Hμ HK ha hd hb hc Hu he' hE
end YM.RG08.Spar
