import YM.TraceExtension.Terrace.Annual
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Terrace
open Function Filter Set Lattice RG Wilson Labels Source MergeProof MergeProof.Accent Extra.Histories Bid Zn
open Extraction Next.UVStress Next.Rank.Price Next.Rank.East MergeProof.East Further.CorrectedLift Climb Analysis Work
open Further.PhysicalPeriodLimitF933 Shunt Weir PhysicalNext.Repeat.Quince PhysicalNext.Repeat.Legato.Bandage Push.GridApprox Cells
open Relay Pull Asymptotics
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G} {W:Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ} {D:∀ N p i:ℕ,i<N→GaugeDoor (C.path.rep N p (i+1)) (C.path.rep N p i)}
variable (P:C.Makes) (h:G.Simple) (θ:PostT C.path.levels)(K:Stock.Tabs C.path.levels) (ht:Scrim C W u ψ φ δ (fly C.path.levels) r D)(hM:Sceptre C W)
variable {F:Extraction.Order}{𝓛:Ultrafilter (ℕ×ℕ)} (hb:(𝓛:Filter (ℕ×ℕ))≤F.fuse)
set_option quotPrecheck false
local notation "A"=> C.path.levels
local notation "V!"=> C.path
local notation "b!"=> (𝓛:Filter (ℕ×ℕ))
variable {d k N p l:ℕ}
abbrev Films (C:Family G):= ∀ k _N p:ℕ, Film G (C.side k p)
abbrev ProbesC (C:Family G)(d:ℕ):=ℕ→ℕ×ℕ→ C.label d
def inside (𝓛:Filter (ℕ×ℕ))(f: Films C)(k l:ℕ):Prop:=∀ᶠ i:ℕ×ℕ in 𝓛,Interior (Push.GridApprox.window 0 l) (f k i.1 i.2)
def beamC (C:Family G)(d:ℕ)(f: Films C) : Pull.CutNet C :=fun k N p=>if h:k≤N then backTo C.path N p h (alto C.path k d • f k N p) else 0
structure TravelsC (𝓛:Filter (ℕ×ℕ))(f:Films C)(w:ProbesC C d)(v:ProbesC C d)(x:ℕ→ C.label d):Prop where
    state : ∀ᶠ k in atTop,∀ᶠ i:ℕ×ℕ in 𝓛, Bill C i.1 i.2 d k (f k i.1 i.2) (w k i) (v k i)
    lands : ∀ᶠ k in atTop,Tendsto (v k) 𝓛 (𝓝 (x k))
    charge : Calms C.S d x
include P h θ K ht hM hb
lemma recordsC (T:ℝ)(ht':0< T)(hp:supportQ C.path.levels) (d:ℕ)(f:Films C)(w:ProbesC C d)
    (hf:∀ᶠ i:ℕ in atTop,∀ᶠ p:ℕ×ℕ in (𝓛:Filter (ℕ×ℕ)), ∃ X: Coefficient (C.labels.level d) (C.side i p.2), AtomD (C.localSection d) C.params (C.path.rep p.1 p.2 i) X (f i p.1 p.2) (C.path.levels.clock.forcedAllowance i) (T*Shunt.grantS (C.path.levels.clock.hatBeta i)) (C.path.levels.clock.hatBeta i)∧ X.x=w i p): ∃ v x, TravelsC b! f w v x:=by
    let M i (p:ℕ×ℕ)(v:C.label d):= Bill C p.1 p.2 d i (f i p.1 p.2) (w i p) v
    have hN:∀ᶠ i:ℕ in atTop,∀ᶠ p:ℕ×ℕ in b!,∃ u, M i p u:=by
        filter_upwards [purchasing P h θ K ht hM d T ht' hp,hf] with i hi hv
        filter_upwards [(link_period hb).eventually hi,hv,(link_mesh hb).eventually_gt_atTop i] with p hp hQ hz
        obtain ⟨u,hu,hξ⟩:=hQ; obtain ⟨x,hx⟩:=hp _ hz u _ hu; exact ⟨x,by unfold M; rw [← hξ]; exact hx⟩
    let v i p:= if h:∃ u,M i p u then Classical.choose h else 0
    have he:∀ᶠ i:ℕ in atTop,∀ᶠ p:ℕ×ℕ in b!, M i p (v i p):=hN.mono fun i hi=>hi.mono fun p ht=> by unfold v; rw[dif_pos ht];exact Classical.choose_spec ht
    let V(i):= 2*outward C d i
    let R (i:ℕ)(x:C.label d):Prop:= Tendsto (v i) b! (𝓝 x)∧ ‖x‖ ≤ V i
    have ht:∀ᶠ i:ℕ in atTop,∃ x,R i x:=by
        filter_upwards [he,eventually_ge_atTop (C.ref d)] with i hi hp
        have ht':∀ᶠ p in b!, ‖v i p‖≤V i:=by filter_upwards [hi,(link_mesh hb).eventually_ge_atTop i] with p hp' hI; exact annual C P (f i p.1 p.2) _ _ hp' hp hI
        obtain ⟨x,hX⟩:= crewing _ _ _ ht'; exact ⟨x,hX,le_of_tendsto hX.norm ht'⟩
    let x i:= if h:∃ u,R i u then Classical.choose h else 0
    have hP:∀ᶠ i in atTop, R i (x i):= ht.mono fun i h=> by unfold x; rw[dif_pos h];exact Classical.choose_spec h
    refine ⟨v,x,he,hP.mono (fun i hi=>hi.1),?_⟩
    have hz : Calms C.S d V:=by
         unfold V; simp_rw[waters]; have ht:= (show Calms C.S 0 (fun _=>(2:ℝ)) from fun m h=> factor_const _ _ _ h).mul ((curtain (A)).mul (factor_calms C.S d)); rw[zero_add,zero_add] at ht;exact ht
    refine hz.smaller (isBigO_iff.mpr ⟨1,hP.mono (fun i hi=> (hi.2.trans (Real.le_norm_self _)).trans_eq (one_mul _).symm)⟩)
omit θ ht hM
lemma recordsBook {f:Films C}{q: ℕ→ℕ}(hq:CutQ C.path.levels q)(hc: ∀ᶠ k:ℕ in atTop, inside b! f k (q k)) {v x:ProbesC C d}{y}(hy:TravelsC b! f v x y) (HS: CellHyp C F) {S:Table C.book} (hV:F.PointLimits C S)(hp:S.Hierarchy): Book b! (beamC C d f) (fun k=>S.project d (y k)):=by
    refine from_center P HS hV hp hb hy.lands ?_; intro i
    let m:= max (basin (A) K i) (C.ref d); have hm : C.ref d ≤ m:= le_max_right ..; have hz:=tracks (A) K i
    have hP :=Stock.Tabs.open_later (A) 1 K hz (show basin (A) K i ≤ m from le_max_left ..) zero_le_one
    refine ⟨nativeC C d i m,tranquil d i m h,?_⟩
    filter_upwards [eventually_gt_atTop m,hy.state,hc,passing (A) h q hq i] with k hk ht hx hp
    filter_upwards [ht,hx,(link_mesh hb).eventually_ge_atTop k, (link_mesh hb).eventually (Stock.clear_interior C P i d)] with p ht hx he ⟨hv,hV⟩
    let h':i ≤ k:= hP.1.trans hk.le; let ζ:= h'.trans he
    let T:= tilesAt C.S p.2 ζ
    let V:= f k p.1 p.2; let Y:= beamC C d f k p.1 p.2; have hm': Interior (T.chamber 0) Y:=by
       apply Interior.enlarges _ (room_fits p.2 (A) (q k) h' he hp 0); unfold Y beamC; rw[dif_pos he]; apply backTo_local; rw[show anchor _ _ h' 0=0 from (C.S.toDepth h' p.2).root.map_zero];exact hx.scale _
    refine ⟨ζ,Next.UVStress.minus hm' (hV p.2 0 _),?_⟩; dsimp only [beamC]; rw [dif_pos he]; exact ht.root i m (q k) hP hm hk hp h' he hx
end YM.Trace.Terrace
