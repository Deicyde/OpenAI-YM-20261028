import YM.TraceExtension.Prom.Zoom.Pepper
set_option autoImplicit false
noncomputable section
namespace YM.Next.UVStress
open Set Function Filter MeasureTheory Analysis Table Ward Climb Extraction
open MergeProof.East
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{C:Family G}{S:Table C.book}{F:Extraction.Order} {d:ℕ}
variable (H:S.Hierarchy)(h:F.Ordered C S)(a:(Bel C.book).Hierarchy)(P:C.Makes)
variable (X : Zoom)(V: ∀ d,Vane C d)(hz:∀ i,(V i).checked F a i)(he:∀ i,(V i).wheel.r=X.r i)
variable (𝓛:Ultrafilter (ℕ×ℕ))(hℓ:(𝓛:Filter _) ≤ F.fuse)
include hz he hℓ P h
lemma breadSky : ∃ (U:ℕ→Panel S),
     Approaches X U ∧ (∀ k d,d ≤ k → StraightAt H.spin a.spin (U k) d ∧ U k d ((Bel C.book).unit d)=S.unit d) ∧
     ∀ k,∃ Y : Lifts C k, Tendsto (V k).wheel.atCut (𝓛:Filter _) (𝓝 Y) ∧ ∀ d:Fin (k+1),∀ x, U k d x=S.project d (Y d x):=by
   have hq(k)(d:Fin (k+1)): ∀ᶠ j:ℕ×ℕ in F.fuse, (V k).wheel.atCut j d ((Bel C.book).unit d)= C.book.scalar d:= by
      let R:=V k
      let K:=R.k
      filter_upwards [large_mesh F (K+1)] with j hj
      change Next.Rank.East.ladd C _ _ _ _ _ _ (Further.CorrectedLift.ladder C d ((Bel C.book).unit d))=_
      rw [Further.CorrectedLift.ladder_unit]; exact Next.Rank.East.pure_start P ((hz k).early d) (Nat.le_of_lt hj) _ _ (((hz k).rate _ _ hj).1 d).1
   choose U Y hY hQ hu hD hθ using fun k=> harvestedSky H h a.spin (V k).wheel.toStation (hz k|>.fares) 𝓛 hℓ (hq k)
   refine ⟨U,⟨fun n v=> ⟨fun k=> (smoothZoom H.smooth _ (X.positive k)).sub (smoothDisc a.smooth v),?_⟩⟩,(fun k d hd=> ⟨hu k d hd,hD k d hd⟩),fun k=> ⟨Y k,hY k,hQ k⟩⟩
   intro s hK hC M hp ε hv
   have hh : Tendsto (fun k => costHint k * Station.charge v * M) atTop (𝓝 0) := by
      simpa using (cost_clears.mul_const (Station.charge v)).mul_const M
   filter_upwards [eventually_ge_atTop n, eventually_all.mpr (fun i=> eventually_ge_atTop (v i).1),size_ascends.eventually (Work.A05.compact_fits hK hC), hh.eventually (ge_mem_nhds hv)] with k hk hL ht hx t hw hb
   rw [test_sub]
   · rw [← he]; exact (hθ k n hk v hL t (hw.trans ht) M hp hb).trans hx
   · exact (smoothZoom H.smooth (panels (U k) ∘ v) (X.positive k)).continuousOn
   exact (smoothDisc (T:=(Bel C.book)) a.smooth v).continuousOn
lemma dockedSky (hd : DimAbove S) : ∃ (Z:Scaling S),path Z=X ∧
    Approaches (path Z) (isoPanel Z) ∧
    (∀ d, ∀ᶠ k in atTop, Coherent a.spin H.spin d (Z.U k d) ∧ Z.U k d ((Bel C.book).unit d)=S.unit d) ∧
    ∀ d, ∀ᶠ k in atTop, ∀ i:Fin (k+1),i.val=d → ∃ Y:Lifts C k,Tendsto (V k).wheel.atCut (𝓛:Filter _) (𝓝 Y) ∧ ∀ z,Z.U k i z=S.project i (Y i z):=by
   obtain ⟨Q,hQ,hD,Hq⟩:= breadSky H h a P X V hz he 𝓛 hℓ
   have hu d : ∀ᶠ k in atTop, Bijective (Q k d):= by
      filter_upwards [MeterTest.injects H.smooth a hQ d] with k hk
      exact ⟨hk,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (le_antisymm (LinearMap.finrank_le_finrank_of_injective hk) (hd d))).1 hk⟩
   let M k d := if p : Bijective (Q k d) then LinearEquiv.ofBijective _ p else
      LinearEquiv.ofBijective _ (hu d).exists.choose_spec
   let Z : Scaling S:= ⟨M,fun _ => 1,X.r,fun _=>one_pos,X.positive,X.shrinking,X.limits⟩
   have hZ(d):∀ᶠ k in atTop, isoPanel Z k d=Q k d:= by
      filter_upwards [hu d] with k hk
      dsimp only [isoPanel,Z,M]; rw [dif_pos hk]; rfl
   refine ⟨Z,rfl,⟨fun n v=>?_⟩,?_,?_⟩
   · refine (hQ.values n v).congr (fun k=>(smoothZoom H.smooth _ (X.positive k)).sub (smoothDisc a.smooth v)) ?_
     filter_upwards [eventually_all.mpr (fun i:Fin n=> hZ (v i).1)] with k hk
     intro y _; change tested _ _ _ _-_ =tested _ _ _ _-_
     unfold tested; rw [show (panels (Q k) ∘ v)=panels (isoPanel Z k) ∘ v from funext (fun i=>by
       change Sigma.mk (v i).1 (Q k _ _)=Sigma.mk (v i).1 (isoPanel Z k (v i).1 (v i).2)
       rw [hk])];rfl
   · intro d; filter_upwards [eventually_ge_atTop d,hZ d] with k hk hz
     obtain ⟨hp,he⟩:= hD k d hk; have hF(w):Z.U k d w=Q k d w:=LinearMap.congr_fun hz w
     exact ⟨⟨fun w=>by rw[hF,hF];exact hp.bars w,fun s w=> by rw[hF,hF]; exact hp.reflects s w⟩, (hF _).trans he⟩
   intro d; filter_upwards [hZ d] with k hp i hx; subst d; obtain ⟨Y,hf,hh⟩:= Hq k
   exact ⟨Y,hf,fun z=> (LinearMap.congr_fun hp z).trans (hh i z)⟩
end YM.Next.UVStress
