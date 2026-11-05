import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Locations
import YM.RG08.Quarry.School

/-! # Signed prescription still on the SAME incumbent flat sector after step. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Quarry
open Filter Function Matrix MeasureTheory Finset Lattice Exterior Wilson RG Precision Stationary Work.F05 Tree Carrel Prism Tack Camera Slate Gallery
open AnalyticBridge.GaussianFieldAlignment
open scoped Classical Matrix ContDiff Topology BigOperators InnerProductSpace PowerSeries ENNReal Matrix.Norms.Frobenius
variable {c f:Side}{G:Gauge}(S:StepData c f)(F:Forest S.ratio) (s:Signed)

abbrev glower(spin:Signed)(B:Forest S.ratio):Forest S.ratio:= Locations.forest spin 0 B
abbrev ribbon : (glower S s F).Free≃F.Free:= Locations.free s 0 F

private def fade (s:Signed)(i:Axis)(z:G.El):G.El:=if s.flip i then z⁻¹ else z

def swipe (u:F.Slice G)(i:(glower S s F).Free):G.El:= fade s i.val.2 (u (ribbon S F s i))
lemma away:Injective (swipe S F (G:=G) s):=by
 intro a b h;funext i;obtain ⟨j,rfl⟩:=(ribbon S F s).surjective i
 have ht:=congrFun h j;unfold swipe fade at ht;cases he:s.flip j.val.2<;> simpa only [he,Bool.false_eq_true, ↓reduceIte,_root_.inv_inj] using ht
lemma swiped:MeasurePreserving (swipe S F (G:=G) s) (F.order G) ((glower S s F).order G):=by
 let E:=ribbon S F s;let A:= (glower S s F)
 have ht : MeasurePreserving (fun u:F.Slice G=>u ∘ ⇑E) (F.order G) (A.order G):=by
    have hi:= measurePreserving_piCongrLeft (fun _:A.Free=>G.probHaar) E.symm
    convert! hi using 1
    · funext u i; change u (E i)= (MeasurableEquiv.piCongrLeft (fun _:A.Free=>G.El) E.symm) u i; simp [MeasurableEquiv.piCongrLeft,Equiv.piCongrLeft_apply]
    -- Fintype dec eq subtype or order definitional
 have hv :MeasurePreserving (fun u:A.Slice G=> fun i:A.Free=> fade s i.val.2 (u i)) (A.order G) (A.order G):=by
    refine measurePreserving_pi _ _ (fun i=>?_)
    unfold fade;cases he:s.flip i.val.2
    · simpa only [he,Bool.false_eq_true,↓reduceIte] using! MeasurePreserving.id G.probHaar
    · simpa only [he,↓reduceIte] using! G.preserve_inv
 exact hv.comp ht

def muted (u:AxisChart G F)(i:(glower S s F).Free):G.Color:=if s.flip i.val.2 then - (u (ribbon S F s i)) else u (ribbon S F s i)
lemma mute0:muted S F (G:=G) s 0=0:=by funext i;cases he:s.flip i.val.2 <;>simp [muted,he]
lemma mute_pace:Pace (muted S F (G:=G) s):=by apply contDiffAt_pi.mpr;intro i; unfold muted; split <;> first | exact (contDiffAt_apply ℝ G.Color _ _).neg|exact (contDiffAt_apply ℝ G.Color _ _)
lemma mute_exposes (u: AxisChart G F):exposure (glower S s F) 0 (muted S F s u)=swipe S F s (exposure F 0 u):=by
 funext i; unfold Work.F05.exposure swipe muted fade; cases he:s.flip i.val.2 <;> simp [Precision.link_one,Precision.replica_one,Work.F03.exp_neg_color]

lemma revolving(q:Lattice.Edge (Site f)): q∈ (glower S s F).trunks ↔Wilson.sendEdge s 0 q ∈ F.trunks:=by
 have he:=Locations.trunk_map s 0 F q
 rw [← Ratio.root_embed,map_zero] at he;exact he
lemma ribbons (q:(glower S s F).Free): ((ribbon S F s) q).val=Wilson.sendEdge s 0 q.val:=by have he:= Locations.free_site s 0 F q; rw [← Ratio.root_embed,map_zero] at he;exact he
private lemma reads (V:Lattice.Links _ G.El)(i:Lattice.Edge (Site f)):Lattice.pull s 0 V i=fade s i.2 (V (Wilson.sendEdge s 0 i)):=by unfold pull fade sendEdge; simp only [posDir,Lattice.Step.rotate,Bool.false_xor,Step.read]
lemma raveled (v:F.Slice G):(glower S s F).drape (swipe S F s v)=Lattice.pull s 0 (F.drape v):=by
 funext e; rw [reads]; by_cases he :e∈ (glower S s F).trunks
 · rw [show (glower S s F).drape _ e=1 from (glower S s F).on_tree _ ⟨e,he⟩,show F.drape v _=1 from F.on_tree v ⟨_,(revolving S F s e).mp he⟩]; cases ht:s.flip e.2<;>simp [fade,ht]
 rw [show (glower S s F).drape _ e=_ from (glower S s F).off_tree (swipe S F s v) ⟨e,he⟩]
 rw [← ribbons S F s ⟨e,he⟩,F.off_tree]; rfl

abbrev Holder:=Cellar (Lines G c 1)
def parade (z:Holder (G:=G) (c:=c) × AxisChart G F):=((0:Bid.Dir G c),muted S F s z.2)
lemma paged:Pace (parade S F (G:=G) s):=by
 let x:Holder (G:=G) (c:=c) × AxisChart G F:=0
 apply contDiffAt_const.prodMk
 exact ContDiffAt.comp (𝕜:=ℝ) (n:=ω) (f:=@Prod.snd (Holder (G:=G) (c:=c)) (AxisChart G F)) (g:=muted S F (G:=G) s) x (mute_pace S F s) contDiffAt_snd
-- incoming coarse chart map uses Carrel.basis
private lemma harvested(x:Cellar (Lines G c 1)): Carrel.offers G x=represent (borne id x):=funext fun i=>by rw [Work.F03.represent_link];rfl

def blade (x:Cellar (Lines G c 1)):Cellar (Lines G c 1):= Carrel.treated s x
lemma bladed: Pace (blade (c:=c) (G:=G) s):=by
 refine contDiffAt_pi.mpr (fun i=>?_)
 change Pace (fun x:Cellar (Lines G c 1)=> supply s i.2 * x (Carrel.badge s i))
 exact contDiffAt_const.mul (contDiff_apply ℝ ℝ _).contDiffAt
lemma blade0: blade (c:=c) (G:=G) s 0=0:=by funext i;exact mul_zero _
lemma blade_close (x:Cellar (Lines G c 1)): represent (borne id (blade s x))=pull s 0 (represent (borne id x)):=by rw [←harvested,←harvested,blade,tread]

def warp : Solved S F (@id (Lines G c 1)) id (blade s) (fun _ u=> switch (glower S s F) F 0 (muted S F s u)) s 0 where
 rates _:=⟨(Profiles.reroute (glower S s F) F G) ∘ swipe S F s,(Profiles.reroute _ _ _).injective.comp (away S F s), (Profiles.spending _ _ _).comp (swiped S F s)⟩
 grip:=by
   let f(z:Cellar (Lines G c 1) × AxisChart G F):= ((0:Bid.Dir G c),muted S F s z.2)
   have he : f 0=0:=Prod.ext rfl (mute0 S F s)
   exact ContDiffAt.comp _ (g:=uncurry (switch (glower S s F) F)) (f:=f) (he.symm ▸ switch_jet _ _) (paged S F s) -- hb binder 0 defeq
 run0:=by rw [mute0,Work.F05.switch_zero]
 zoom:=bladed s
 fit0:=blade0 s
 paid':=by
    let f(z:Cellar (Lines G c 1) × AxisChart G F):=((0:Bid.Dir G c),muted S F s z.2)
    have ht:f 0=0:=Prod.ext rfl (mute0 ..)
    have H:Tendsto f (𝓝 0) (𝓝 0):=by rw [←ht]; exact (paged S F s).continuousAt.tendsto
    filter_upwards [H.eventually (exposure_switch (glower S s F) F)] with z hz
    rw [Function.comp_apply,←mute_exposes]; exact hz
 field:=by
    apply Filter.Eventually.of_forall; rintro ⟨x,y⟩
    let z:=Work.F05.exposure F (0:Bid.Dir G c) y
    let r:=F.foldAt (pull s 0 (F.drape z))
    have hh : r ∘ S.ratio.embed=1:=funext (fun i=>F.fold_root _ _)
    refine ⟨r,?_,?_⟩
    · change F.drape (Profiles.wick F ((glower S s F).drape (swipe S F s z)))=_
      rw [raveled,Profiles.wears,← Ratio.root_embed,map_zero];rfl
    dsimp only; rw [blade_close,hh]
    funext i; simp [Lattice.gauge]
end YM.RG08.Quarry
