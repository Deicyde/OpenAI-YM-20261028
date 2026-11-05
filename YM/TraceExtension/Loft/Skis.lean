import YM.TraceExtension.Loft.Cosmo
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Loft
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson Finset Push.Uniform Audience Metric
open scoped BigOperators Topology ContDiff ComplexConjugate
variable {ι κ:Type}{G:Gauge}{F:KindF G}{V:Jar G}{σ η A C D ε a r:ℝ}{μ T:ι→ℝ}
lemma team {X:Burst ι (Fslot G)}{S:Skuta ι G}(h:S.Live η D ε A V)(hp:V.grey)(he:V.fees η C)(ha:0 < η)(hv:ColdR X T μ r)(hw:0 < ε)(b:ι→G.ColorIndex)(hx:∀ i,X.mark i=(coord 1,b i))(hk:∀ i,X.boost i=step 0): Yeti X T μ (S.useJar V) r b:=
    ⟨⟨Floe.vector h ha hp he X _, ice_w X _ hv, alp_t (p:=S.top) (B:=S.terra) hv hw (fun i=> (h i).1), hv⟩, ⟨Floe.ghost _ _,ice_w X _ hv,cinderTall hv,hv⟩,hx,hk⟩
lemma globe {X:Burst ι κ} (h:∀ i,μ i∈Set.Ioc (0:ℝ) 1) (hp:∀ i,FrontBox (X.lens i))(he:∀ i, ‖X.boost i‖≤1): ColdR X ((flay ∘ X.lens)+μ) μ furthest:=by
    refine ⟨furthest_pos, fun i=> add_pos_of_nonneg_of_pos (orbit_nonneg _) ((h i).1),fun i=> (add_le_add (orbit_boundary _ (hp i)) (h i).2).trans_eq (add_comm ..),he,fun i=> le_add_of_nonneg_right (h i).1.le,fun i=>(h i).1,fun _=>le_rfl,fun i=>le_add_of_nonneg_left (orbit_nonneg _),fun i=>(h i).2,hp⟩
lemma effect (h:V.fees η C)(hv: V.grey)(he:0 < ε)(hp:0 < η)(ht:G.Simple)(D A:ℝ):∃ i j :ℝ, 0 ≤ i ∧ 0 ≤ j ∧ ∀ (p:Orion V η D ε A) (μ:ℝ), μ∈Set.Ioc (0:ℝ) 1→ let X:= quick μ G (p.l.combine V|>.cast); Waves1 i μ (keelRay X p.a) ∧ Waves2 j μ (keelRay X p.a) G:=by
    let W:=Hstar V η D ε A × Set.Ioc (0:ℝ) 1; let f:W→ Hstar V η D ε A:=Prod.fst; let N (i:W):=(show Set.Ioc (0:ℝ) 1 from (show Hstar V η D ε A × _ from i).2)
    let J:=Looming f; let Q:=BundleS f; let M (i:W):= (f i).p.a; let μ(i:W):= (N i).val
    have H: ColdR J (flay ∘ J.lens+μ) μ furthest:=globe (fun i=>(N i).property) (fun i=>(f i).path) (fun _=>singleStep _)
    obtain ⟨i,hi,h1⟩:=Yeti.register (X:=J) (F:=Q.useJar V) (team (Bundled f) hv h hp H he M (fun _=>rfl) (fun _=>rfl))
    let E:={i:W// μ i≤ flay (f i).x}; let z:E → W:=Subtype.val; let v:=f∘z; let m:=Looming v; let S:=BundleS v; let L:=μ∘z
    have hh : ColdR m (flay ∘ m.lens+ L) L furthest:=globe (fun i=>(N _).property) (fun i=>(v i).path) (fun _=>singleStep _)
    let R:=flay ∘ m.lens
    have hw: ColdR m R L furthest:=by
       have hL i: L i ≤ R i:= i.property
       exact ⟨furthest_pos,fun i=>(hh.pos i).trans_le (hL i), fun i=> le_trans (b:=R i+L i) (le_add_of_nonneg_right (hh.pos i).le) (hh.upper i),fun i=>singleStep _,fun _=>le_rfl,hh.pos,fun i=>le_add_of_nonneg_right (hh.pos i).le,hL,hh.slim,hh.stage⟩
    obtain ⟨x,hx,h2⟩:=Yeti.shell (F:=S.useJar V) (team (Bundled v) hv h hp hw he (M∘z) (fun _=>rfl) (fun _=>rfl)) ht rfl furthest_pos
    exact ⟨i,x,hi,hx,fun p n hn=>⟨fun k hk=> h1 ((⟨k,p,hk⟩:Hstar V η D ε A),⟨n,hn⟩),fun k hk hx=> h2 ⟨((⟨k,p,hk⟩:Hstar V η D ε A),⟨n,hn⟩),hx⟩⟩⟩
end YM.Trace.Loft
