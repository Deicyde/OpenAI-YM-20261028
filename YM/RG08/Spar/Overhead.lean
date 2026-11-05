import YM.RG08.Spar.Forces

noncomputable section
namespace YM.RG08.Spar
open Forms Rudder Packets Finset Function Lattice Laurent Pert.Bulk Exterior Filter Bloch Anchor Symmetry Loop
open scoped Topology BigOperators Classical ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {I:Type}{n:ℕ}{σ τ C Q:ℝ}{F:Raw I (n+1)}

lemma diff_cloak {V:Submodule ℝ (Urn I (n+1))}{a:ℕ}{F G:Raw I (n+1)}(h:Cloak V a F)(hf:Cloak V a G):Cloak V a (F-G):=by
 refine ⟨h.path.sub hf.path,h.field'.sub hf.field',?_,?_,fun x=>sub_mem (h.hair x) (hf.hair x)⟩
 · exact fun e=>congrArg₂ (·-·) (h.beam e) (hf.beam e)
 intro s;rw [map_sub,h.firm s,hf.firm s]

lemma darkfirst {V:Submodule ℝ (Urn I (n+1))}(h:Cloak V 1 F)(he:Closing F)(hs:0<σ)(hc:0≤C)(hp:Held (carpet (Tone I)) σ C F):FirstNull F:=by
 rcases n with _|(_|n) <;> first|trivial|exact paidPole h.firm h.path h.field' he hp hs hc

structure Ready (V: Submodule ℝ (Urn I (n+1)))(σ C : ℝ)(F:Raw I (n+1)):Prop where
 dress : Cloak V 1 F
 closing : Closing F
 pos : 0≤C
 held : Held (carpet (Tone I)) σ C F

lemma Ready.sub {V : Submodule ℝ (Urn I (n+1))}{B D:ℝ}{T:Raw I (n+1)}(hf:Ready V σ C F)(hg:Ready V σ B T)(hd:Held (carpet (Tone I)) σ D (F-T))(ht:0≤D):Ready V σ D (F-T):=⟨diff_cloak hf.dress hg.dress,hf.closing.sub hg.closing,ht,hd⟩

variable [Fintype I]
def relift (V:Submodule ℝ (Urn I (n+1)))(θ:ℝ)(A:Raw I (n+1)):=Lyapunov V (4*θ) A

def Rigged (U : Submodule ℝ (Urn I (n+1)))(v θ K:ℝ):Prop := 0<θ ∧ θ≤v ∧ 0≤K ∧
  ∀ (F:Raw I (n+1)) (p : ℝ), Ready U v p F→
    let Z:=relift U θ F
    Cloak U 2 Z ∧ Held (carpet (Tone I)) θ (K*p) Z ∧ F=picture I (n+1) Z ∧
    ∀ (G:Raw I (n+1))(B D:ℝ),Ready U v B G→ 0≤D → Held (carpet (Tone I)) v D (F-G) →
       Held (carpet (Tone I)) θ (K*D) (Z-relift U θ G)

/-- Repeated use license with same theta at each stage. Announce at arity and any desired input
width v before L, supplies the rest. -/
theorem warehouse (σ:ℝ)(hs:0<σ)(hn:1≤n)(V:Submodule ℝ (Urn I (n+1)))(he:adjGrade V):∃ θ K, Rigged V σ θ K:=by
 obtain ⟨θ,K,h,hk,hK,H⟩:= Symmetry.arc σ hs hn V he
 refine ⟨θ,K,h,hk,hK,?_⟩
 intro F b hF Z
 obtain ⟨hp,hQ,hU,hS⟩:= H F b hF.dress hF.pos hF.closing (darkfirst hF.dress hF.closing hs hF.pos hF.held) hF.held
 refine ⟨hQ,hU,hp.symm,?_⟩
 intro G B C hG hC hm
 have hd:=hF.sub hG hm hC
 have ht:= (H (F-G) C hd.dress hC hd.closing (darkfirst hd.dress hd.closing hs hC hm) hm).2.2.1
 rw [hS G B hG.dress hG.pos hG.closing (darkfirst hG.dress hG.closing hs hG.pos hG.held) hG.held] at ht
 exact ht

/- apply to changes, where F-G = voucher (input curvature change) + aggregate strict forcing
(preceding ranks, nonflat, Δ in predictor etc) AFTER alignment; consumer proves that identity
for evaluated literal kernels (no change in diam sensor due to translation histories). -/

/-- convenient normalization-only difference budget -/
theorem patch_variation {G:Gauge}(hΓ:G.Simple)(s:ℝ)(_hS:s≠0){F F' T T':Raw G.ColorIndex 2}(σ p₁ p₂ A B d d':ℝ)(hs:0<σ)(h₁:0≤p₁)(h₂:0≤p₂)(hb:0≤B)(hd:0≤d)(hd':0≤d')
 (hF: Held (carpet (Tone G.ColorIndex)) σ p₁ F)(hf:Held (carpet (Tone G.ColorIndex)) σ p₂ F')(_hT:Held (carpet (Tone G.ColorIndex)) σ A T)(ht: Held (carpet (Tone G.ColorIndex)) σ B T')
 (h:Held (carpet (Tone G.ColorIndex)) σ d (F-F'))(he:Held (carpet (Tone G.ColorIndex)) σ d' (T-T')):
 |Loop.reading F hΓ s-Loop.reading F' hΓ s|≤d/|s| ∧
 Held (carpet (Tone G.ColorIndex)) σ (d+d/|s| *B+p₁/|s| *d') (Loop.patch F T hΓ s-Loop.patch F' T' hΓ s):=by
 let a:=Loop.reading F hΓ s; let b:=Loop.reading F' hΓ s
 have hh : |a-b|≤d/|s|:=by unfold a b Loop.reading;rw [←sub_div,abs_div]; gcongr;rw [←Loop.var_meter hΓ h₁ h₂ hs.le hF hf];exact Loop.bill_meter hΓ hd hs.le h
 have hp: |a|≤p₁/|s|:=by unfold a Loop.reading;rw [abs_div]; gcongr;exact Loop.bill_meter _ h₁ hs.le hF
 refine ⟨hh,?_⟩
 unfold Loop.patch
 change Held _ _ _ (F-a • T-(F'-b • T'))
 rw [show F-a • T-(F'-b • T')=(F-F')-(a-b) • T'-a • (T-T') by module]
 apply ((h.sub (ht.smul (a-b)) hd (by positivity)).sub (he.smul a) (by positivity) (by positivity)).mono le_rfl ?_ (fun _=>le_rfl)
 gcongr
end YM.RG08.Spar
