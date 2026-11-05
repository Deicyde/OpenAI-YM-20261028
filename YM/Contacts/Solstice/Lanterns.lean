import YM.Contacts.Solstice.Suture
/-!
# The patch rule about any diagonal

Total stages (all positions varied in full normal coordinates, centroid optionally kept). We will
integrate with respect to all given coordinates including possible center or outside ones as
well. Attach patch strict demands including Taylor freedom of the disjoint variables and all inner
operations. A common subtraction length suffices for any point in the stage (it is not reduced in
a patch near another collision). This uses the fact that operations in the displaced coordinates
refer only to their centers in the projected branch, already paid for in the Loan estimates.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Solstice
open Function Filter Set Metric MeasureTheory Submodule Table Spec Normal MultipleContact OPE Layers Harvest Route TopologicalSpace
open scoped Topology Classical BigOperators ContDiff InnerProductSpace MeasureTheory
variable {E W I : Type}[NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E]
variable {G: Gauge}{C : Family G}{F : Extraction.Order}{S: Table C.book}{Z : Final C F S}
variable {k : ℕ}{g : Normal.Group k}{P:E→ₗᵢ[ℝ] Points k}
local notation "GN" => Normal.Group k
variable {o : Points k} {s B : ℝ} {U : Set E}
variable (h : plane g≤ LinearMap.range P.toLinearMap) (hp : Collapsed g o)
/-- Candidates for the finite patch assembly. Their recipe did not change any exact jets;
it is enough to find positive clearance here; they need not bound any estimates in a larger chart.
-/
structure Lights (P : E→ₗᵢ[ℝ] Points k) (g : GN) (o : Points k) (s B : ℝ) where
    region : Set E
    groups : Pieces g
    clear : EmptyBank P groups s o region B
    gap : ℝ
    positive : 0< gap
    lit : Sober clear.route gap

-- when using P throughout, offset equality inside root makes any subcentroid differences in `Sober` compute in P plane
include hp
omit [FiniteDimensional ℝ E] in
lemma offsets (i j : Nails g) (x : E): centroid i.val (P x+o)-centroid j.val (P x+o)=centroid i.val (P x)-centroid j.val (P x):= by
   have hh (i:Nails g):centroid i.val o=centroid g o:= centroid_same i.property.2 _ _ (fun k hk=> hp k (i.property.1 hk)) -- include hp
   rw [map_add, map_add,hh,hh]; abel

lemma sober_from_bright {Q : Pieces g}(H : EmptyBank P Q s o U B) (hm : U⊆ bright P Q) : ∃ δ>(0:ℝ), Sober H.route δ:= by
   let φ:= 𝓝[>] (0:ℝ); have hx(i j:Q.parts)(hh:i≠j) (u : Nails i.val)(v:Nails j.val) : ∀ᶠ δ in φ,∀ x∈U,δ ≤ ‖H.route.oculus () u.val x-H.route.oculus () v.val x‖:= by
     rcases U.eq_empty_or_nonempty with he|he
     · exact Eventually.of_forall fun δ x hx=> (he ▸ hx : x∈(∅:Set E)).elim -- Set.empty not false defeq?
     let f(x:E):= ‖centroid u.val (P x)-centroid v.val (P x)‖; have hf: Continuous f:= (( (centroid _).continuous.comp P.continuous).sub ((centroid _).continuous.comp P.continuous)).norm
     obtain ⟨t,ht,hU⟩:= H.compact.exists_isMinOn he hf.continuousOn; have hb:0< f t:= norm_pos_iff.mpr (sub_ne_zero.mpr (hm ht i j hh u v))
     filter_upwards [Eventually.filter_mono (nhdsWithin_le_nhds (s:=Ioi 0)) (show ∀ᶠ w:ℝ in 𝓝 0,w ≤ f t from ge_mem_nhds hb)] with d hd; intro x hx; exact le_trans (le_trans hd (show f t ≤ f x from hU hx)) ( (congr_arg norm (offsets (P:=P) hp ⟨u.val,Finset.Subset.trans u.property.1 (Q.le i.property),u.property.2⟩ ⟨v.val,Finset.Subset.trans v.property.1 (Q.le j.property),v.property.2⟩ x).symm).le)
   have heL : ∀ᶠ δ in φ, Sober H.route δ:= by
      apply eventually_all.mpr; intro i; apply eventually_all.mpr; intro j; by_cases h:i=j; · exact Eventually.of_forall fun x hh=> (hh h).elim
      filter_upwards [eventually_all.mpr (fun u=> eventually_all.mpr (hx i j h u))] with d hd; rintro _ ⟨⟩ x hX f ⟨u,rfl⟩ g ⟨v,rfl⟩; exact hd u v x hX
   exact Eventually.exists ((show ∀ᶠ δ:ℝ in φ, 0<δ from self_mem_nhdsWithin).and heL)
include h hp
lemma illuminate (hB : B∈ Ioc (0:ℝ) 1)(hs : 0<s ∧2*s ≤ B) (x:E) : ∃ L : Lights P g o s B, x∈ interior L.region:= by
   let Q := Finpartition.ofSetSetoid (Setoid.ker (fun i=> P x i)) g
   have ht : x∈ bright P Q:= fun i j he=> equality_opens _ rfl he
   have hv(i:Q.parts): ∀ᶠ t in 𝓝 x,t∈ strip (normalOn P i.val) B:= by
      apply ( ((normalOn P i.val).starProjection.continuous.norm).tendsto x).eventually (p:=fun x=> x≤B); apply ge_mem_nhds; rw [(local_collapse ((plane_le (Q.le i.property)).trans h) x).1 (grouping_inside Q (P x) rfl i),norm_zero]; exact hB.1
   obtain ⟨δ,hδ,H⟩ := nhds_basis_closedBall.mem_iff.mp (((eventually_all.mpr hv).and ((open_bright P Q).mem_nhds ht)) : {x|(∀ i:Q.parts,x∈strip (normalOn P i.val) B)∧x∈bright P Q}∈ 𝓝 x)
   let L:= closedBall x δ
   let hL : EmptyBank P Q s o L B:= ⟨hB,fun i hi=>hp.subgroups (Q.le hi),fun i hi=> (plane_le (Q.le hi)).trans h,fun i hi t h'=> (H h').1 ⟨i,hi⟩,hs,isCompact_closedBall ..⟩
   obtain ⟨c,hc,he⟩:=sober_from_bright hp hL (fun x hx=> (H hx).2)
   exact ⟨⟨L,Q,hL,c,hc,he⟩,mem_interior_iff_mem_nhds.mpr (closedBall_mem_nhds _ hδ)⟩

lemma patch_need (hB : B ∈ Ioc 0 1)(hs : 0< s∧2*s≤ B)(hc : IsCompact U) : ∃ V : Finset (Lights P g o s B), U ⊆ ⋃ v∈ V, interior v.region := hc.elim_finite_subcover _ (fun _=>isOpen_interior) (fun x _=> Set.mem_iUnion.mpr (illuminate h hp hB hs x))

end YM.Contacts.Solstice
