import YM.RG08.Roost.Eras

/-! # Script/moment capacities for harvest (not assuming filtration on the paths).
 Omit scalar geometry: one position held, arity0 not relevant on cover. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Sedan
open Filter Function Matrix MeasureTheory Finset Lattice Exterior Wilson RG Precision Stationary Work.F05 Tree Carrel Prism Tack Camera Gallery
open Forms Rudder Anchor Isles Laurent Pert.Bulk Packets Mount Glyph Room Bloch Quarry Aggregate Steam Spar Symmetry Roost
open scoped Classical Matrix ContDiff Topology BigOperators InnerProductSpace PowerSeries ENNReal Matrix.Norms.Frobenius
variable {c:Side}{G:Gauge}{P:Patch}{K:KernelChoices}{I J:Type}{n:ℕ}

def Honor (G:Gauge)(r:ℕ)(F:Rudder.Raw G.ColorIndex r):Prop:= Cloak (dressed G r) 2 F∧ ∃ σ p:ℝ, 0<σ ∧ 0 ≤ p ∧ Held (carpet _) σ p F
namespace Honor
variable {F D:Rudder.Raw G.ColorIndex n}
lemma pays (h:Honor G n F):let σ:ℝ:= h.2.choose;let p:=h.2.choose_spec.choose;0<σ ∧ 0≤p ∧ Held (carpet _) σ p F:= h.2.choose_spec.choose_spec
-- representative support can intersect at any positive margin, prices narrowed.
lemma nil : Honor G n 0 := by
 refine ⟨⟨fun _ _=>rfl,?_,Forms.Sym.zero,fun s=>map_zero _,fun i=>(dressed G n).zero_mem⟩,1,0,zero_lt_one,le_rfl,zero_held⟩
 -- graded zero
 exact graded_iff.mpr fun _ _ _=> rfl
lemma smul (h:Honor G n F)(p:ℝ): Honor G n (p • F):=by
 obtain ⟨hh,s,z,hs,hz,hP⟩:=h
 exact ⟨⟨hh.path.smul p,graded_iff.mpr (fun i x H=>by rw [Pi.smul_apply,graded_iff.mp hh.field' _ _ H,smul_zero]),hh.beam.smul p,fun q=>by rw [_root_.map_smul,hh.firm],fun x=>(dressed G n).smul_mem p (hh.hair x)⟩, s,|p| *z,hs,mul_nonneg (abs_nonneg _) hz,hP.smul _⟩
lemma plus (h:Honor G n F)(ht:Honor G n D):Honor G n (F+D):=by
 -- addition via diff cloak? diff cloak n+1. prove generic graded & symmetry etc.
 obtain ⟨h,s,p,hs,hp,hU⟩:=h;obtain ⟨q,t,x,hy,hx,hF⟩:=ht
 refine ⟨⟨h.path.add q.path,?_,h.beam.add q.beam,fun r=>?_,fun i=> add_mem (h.hair i) (q.hair i)⟩,min s t,p+x,lt_min hs hy,add_nonneg hp hx,(hU.mono (min_le_left ..) le_rfl (fun _=>le_rfl)).add (hF.mono (min_le_right ..) le_rfl (fun _=>le_rfl)) hp hx⟩
 · apply graded_iff.mpr;intro i x hi; rw [Pi.add_apply,graded_iff.mp h.field' i _ hi,graded_iff.mp q.field' i _ hi,zero_add]
 rw [map_add,h.firm,q.firm]
lemma minus (h:Honor G n F)(ht:Honor G n D):Honor G n (F-D):=by simpa only [neg_one_smul,sub_eq_add_neg] using h.plus (ht.smul (-1))
end Honor
variable {C:Castle G}
structure Fair (C:Castle G):Prop where
 rests r e:¬Live r e → C r e=0
 honor r e : Honor G (Mount.rank r) (C r e)

def Fair.rails (h:Sedan.Fair C): Mount.Stable C where
 dark:=h.rests
 width r e:= (h.honor r e).2.choose
 toll r e := (h.honor r e).2.choose_spec.choose
 dial _ _ := (h.honor .. |>.pays).1
 weight _ _ := (h.honor ..|>.pays).2.1
 banner _ _ := (h.honor ..).1
 hold r e := (h.honor r e|>.pays).2.2
lemma fair {C:Castle G}(h:Mount.Stable C):Fair C:=⟨h.dark,fun r i=>⟨h.banner ..,_,_,h.dial r i,h.weight r i,h.hold r i⟩⟩

-- positive-rank script including rank0 terms in the same fiber but NO assertions on their agreement. Head/parity conditions also on rank0 (g0 regulator-dependent separate homogeneous). -/
structure Grimoire (F:Grain (Market I)) : Prop where
 ceiling : ∀ i k,F i k ≠0→ k ≤ i+2 ∧ Even (i+k)
 solvent:legal F
 billed:∀ i,slaw F i
namespace Grimoire
variable {F D:Grain (Market I)}
lemma smul (h:Grimoire F)(x:ℝ):Grimoire (x • F):=by
 refine ⟨fun i n he=>h.ceiling i n (fun hr=>he (show x • F i n=0 by rw [hr,smul_zero])),fun i n=>?_,fun i n=>?_⟩
 · exact ⟨(h.solvent i n).1.smul x,(h.solvent i n).2.smul x⟩
 obtain ⟨a,p,ha,hp,hK⟩:=h.billed i n;exact ⟨_,_,ha,mul_nonneg (abs_nonneg x) hp,hK.smul x⟩
lemma negative (h:Grimoire F): Grimoire (-F):= neg_one_smul ℝ F ▸ h.smul (-1)
lemma add (h:Grimoire F)(hk: Grimoire D):Grimoire (F+D):=by
 refine ⟨?_,fun i n=>⟨(h.solvent i n).1.add (hk.solvent i n).1,(h.solvent i n).2.add (hk.solvent i n).2⟩,fun i=> Mount.slaw.add (h.billed i) (hk.billed i)⟩
 intro i n H;by_cases he:F i n=0
 · exact hk.ceiling _ _ (fun h=> H (show F i n+D i n=0 from by rw [he,h,add_zero]))
 exact h.ceiling _ _ he
lemma sub (h:Grimoire F)(hk:Grimoire D):Grimoire (F-D):=sub_eq_add_neg F D ▸ h.add hk.negative
lemma demand (C:Castle G)(h:Mount.Stable C):Grimoire (Mount.demand C):=by
 refine ⟨fun i n H=> ⟨(demand_out h H).2.2,(demand_out h H).2.1⟩,demand_solid h,fun i n=>carpet_demand C h i n⟩
end Grimoire
end YM.RG08.Sedan
