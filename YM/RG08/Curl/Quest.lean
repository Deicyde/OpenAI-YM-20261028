import YM.RG08.Curl.Hulls
/-! # Simultaneous choice on cutoff windows, keep within priced packet.
 One may instead call `boat` on differences and/or absolute old generation
 without looking at limit. Kinetic convention: complete base from Wils top at
 q=0 PLUS normalized affine-null difference from any other base log kernel.
 That's a canonical path construction, though no such paths assumed carried by
 the *actual* construction. We assert rate on lift weights, not equality of
 stationary normalization pairs of other schemes. -/
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Virtue
open Filter MeasureTheory Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent FreeResolvent Profiles Finset Next.Free Conductor UVExt.Paths Push.AbsoluteSums Staffer
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
open Chain Wings Summit
variable {X : Chain}{G : Gauge}{K : KPrices X.kernel}{g:KGate K}{P : Lending G X.kernel}{E : ℕ}{S : Prism G X.kernel g P E}{ν:G.ColorIndex}{D:ChartRatio G}
variable {I : Type} {u : I→Windows} {r e d q : ℕ}

def reference (ν:G.ColorIndex) (q:ℕ) := sector (caramel ν 2) (wilsonTop ν) q
abbrev Words (X : Chain)(ν:G.ColorIndex)(D : ChartRatio G)(q:ℕ)(i N:ℕ):= sector (Chain.column G X N i) (X.album ν D N i) q-reference ν q
abbrev LimitWords (X : Chain)(ν:G.ColorIndex)(D:ChartRatio G)(q:ℕ)(i:ℕ) := sector (quartz X G i) (statue X ν D i) q-reference ν q
lemma baseCraft (t:Wings u 0)(hp:X.Wake G)(hv:LocalRatio D): Fleet G ν (Words X ν D q t.i t.N) d:= by
    have he:RunsInk ν (caramel ν 2) (wilsonTop ν):= by
      have hh : Chain.column G X t.N t.N=caramel ν 2:= by unfold Chain.column K₀; rw [X.metric_wilson, caramel_two]; rfl
      rw [← hh]; exact ralliedK hp hv
    obtain ⟨ht,hp⟩:=lyricsInk (i:=ν) (rallies hp hv t) he q -- i
    exact ⟨fun i hi=> ht.tunes i,fun m=> ht.words _ _,sub_self _,hp⟩
-- infer ν in routines by expected binder
lemma Coals (t: Launch u)(h:Circuit S ν D u)(hp:X.Wake G)(hv:LocalRatio D)(hs:G.Simple)(hd:d+2*q≤E) : Fleet G ν (LimitWords X ν D q t.i) d := by
    let W:=statue X ν D t.i; let V:=quartz X G t.i; let U:=sector V W q
    have hw:= haltLocal t h hp hv hs
    have hc:RunsInk ν (caramel ν 2) (wilsonTop ν):= by
      have hh : Chain.column G X t.i t.i=caramel ν 2:= by unfold Chain.column K₀; rw [X.metric_wilson, caramel_two]; rfl
      rw [← hh]; exact ralliedK hp hv
    have hf j (he:j ≤ d+2): sector V W q j=sector V (graving E W) q j:=by
      match j with
      | 0=> rfl
      | 1=> unfold sector graving; rw [if_pos (by omega)]
      | j+2=> simp only [sector,graving,if_pos (show j+2*q ≤ E by omega)]
    have hZ := lyric_rate t h
    have hm (j)(he:j ≤ d+2): Tunable (U j) ∧ Glows (U j):= by
       unfold U; rw [hf j he]; exact ⟨Reflect.Tune_sector _ _ (fun i j=>(hw.2 i j).1) (hZ.sing fun i=> (X.high_stocks ν ..).1) _ _,fiscal_sector _ _ hw hZ.1 _ _⟩
    let p:=reference ν q; have hh j: Tunable (p j) ∧ Glows (p j):=tonesInk hc q j
    refine ⟨fun i hi=> ((hm i hi).1).sub (hh i).1,fun m=> ?_, sub_self _,?_⟩
    · obtain ⟨f,H,hF⟩:= statutory t h hp hv hs m q (d+2) (by omega)
      obtain ⟨g,G',hg⟩:= (inks_song hc q).words (d+2) m
      refine ⟨f-g,H.sub G',fun j hj=>?_⟩
      rw [show Tensor.coeff (f-g) j 0=Tensor.coeff f j 0-Tensor.coeff g j 0 by unfold Tensor.coeff; rw [iteratedFDeriv_sub_apply H.analytic.contDiffAt G'.analytic.contDiffAt,smul_sub],hF j hj,hg j hj]; exact (recital_sub (hm j hj).1.1 (hh j).1.1 m).symm
    have hp' : probeK ν (U 2)= probeK ν (p 2):= by
      have hV : probeK ν (p 2)=_:= talent hc q; rw [hV]
      split; next hz=> subst q; rw [show U 2=V from Reflect.sector_t ..]; exact probe_kept t h
      next hz=> rw [show U 2=W (2*q) 2 from Reflect.sector_unique _ _ (by omega) (by decide) (by omega)]; exact square_glow t h hp hv hs (by omega)
    obtain ⟨w,A,H,h'⟩:= (hm 2 (by omega)).2; obtain ⟨z,B,hx,hu⟩:= (hh 2).2
    exact (probe_diff ν h' hu H hx).trans (sub_eq_zero.mpr hp')
lemma Fleet.cross {F H:Panel G}(h:Fleet G ν F d)(he:Fleet G ν H d){w u B A:ℝ}(hp:0<w)(hv:0<u)(hh:Glow (F 2) w A)(ht:Glow (H 2) u B): Fleet G ν (F-H) d:= by
    refine ⟨fun i hi=> (h.tune i hi).sub (he.tune i hi),fun m=>?_,by change F 0-H 0=0; rw [h.nullF,he.nullF,sub_zero],?_⟩
    · obtain ⟨f,hF,Hf⟩:= h.model m; obtain ⟨g,hg,hX⟩:= he.model m
      refine ⟨_,hF.sub hg, fun i hi=> ?_⟩
      rw [show Tensor.coeff (f-g) i 0=Tensor.coeff f i 0-Tensor.coeff g i 0 by unfold Tensor.coeff; rw [iteratedFDeriv_sub_apply hF.analytic.contDiffAt hg.analytic.contDiffAt,smul_sub], Hf i hi,hX i hi]; exact (recital_sub (h.tune i hi).1 (he.tune i hi).1 m).symm
    apply Eq.trans (probe_diff ν hh ht hp hv); rw [h.cur,he.cur,sub_zero]
lemma fleet_fund (h:Circuit S ν D u)(hp:X.Wake G)(hv:LocalRatio D)(hs:G.Simple)(hd:d+2*q≤E): Both (menu X) (chop X (1/4)) (fun i:Wings u 0=> Words X ν D q i.i i.N (d+2)) (fun i=>LimitWords X ν D q i.i (d+2)) (fun i=>Tier S i.i) := by
    unfold Words LimitWords; simp only [Pi.sub_apply]; apply Both.sub (V:=fun i=>sector (quartz X G i.i) (statue X ν D i.i) q (d+2)) _ (Both.self (U:=fun t=> reference ν q (d+2)) ?_) (sh X)
    swap
    · simp only [reference,sector]; by_cases he:d+2*q=0
      · rw [if_pos he,show d=0 by omega]; simp only [prolong_self]; obtain ⟨V,hV,H⟩:=sugar_paid ν (r:=2) zero_le_one; exact ⟨_,Weighed.constant (menu X) hV,fun i=> glow_less H (tiers S i.i) (by simp only [Pi.one_apply,mul_one,le_refl])⟩
      simp only [if_neg he]; exact launchCrop S ν _ _ _
    simp only [sector]; by_cases he:d+2*q=0
    · simp only [if_pos he]; rw [show d=0 by omega]; simp only [prolong_self]; exact patched h
    simp only [if_neg he]; exact statues h hp hv hs hd _
end YM.RG08.Virtue
