import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lotus.Luminesce
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Lotus
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
namespace Leaf
variable (M : Leaf R) (X : Coat T F) (k:Finset ℕ)
open Census Itinerary
variable (H:Cash W X.x μ L Q o C T R)(hk:X.width=o.K) (V: Finset (Molecule S))
variable (h:joints T R Q.halo X.B V) {i:Molecule S}
-- average of angles, mark remains anchored address. test on disjoint choices.
lemma sticksU {m : ℕ} {V : Finset (Molecule S)} (h : (V:Set (Molecule S)).PairwiseDisjoint id) (he:i∈V) (hp:M.turn.badge S∈i) (z:Air f G): M.premium X W a Ñ k m z (V.biUnion id) = M.premium X W a Ñ k m z i*∏ j∈V.erase i,X.term R Ñ W a k m z j:=by
  let A:=M.turn.badge S; have hA:A∈V.biUnion id:=mem_biUnion.mpr ⟨i,he,hp⟩
  have hT : (V.biUnion id).erase A=i.erase A∪ ((V.erase i).biUnion id):=by
    nth_rw 1 [← insert_erase he]; ext l; constructor
    · intro hh; obtain ⟨hl,hv⟩:= mem_erase.mp hh; obtain ⟨j,hj,hvv⟩:=mem_biUnion.mp hv; rcases mem_insert.mp hj with rfl|hx; exact mem_union_left _ (mem_erase.mpr ⟨hl,hvv⟩);       exact mem_union_right _ (mem_biUnion.mpr ⟨j,hx,hvv⟩)
    intro hh; rcases mem_union.mp hh with hv|hv
    · exact mem_erase.mpr ⟨ne_of_mem_erase hv,mem_biUnion.mpr ⟨i,mem_insert_self .., mem_of_mem_erase hv⟩⟩
    obtain ⟨j,hj,hv⟩:=mem_biUnion.mp hv; obtain ⟨hb,hc⟩:=mem_erase.mp hj
    rw [insert_erase he]; refine mem_erase.mpr ⟨fun hg=>?_,mem_biUnion.mpr ⟨j,hc,hv⟩⟩
    exact Finset.disjoint_left.mp (h hc he hb) hv (hg.symm ▸ hp)
  unfold premium; rw [if_pos hA, if_pos hp,hT]; unfold term; rw [prod_union ?_, prod_biUnion (h.subset (Finset.erase_subset ..))]; rw [← mul_assoc]; rfl
  exact Finset.disjoint_left.mpr (fun z hz ht=> let ⟨j,hj,hf⟩:= mem_biUnion.mp ht
                                             Finset.disjoint_left.mp (h (mem_of_mem_erase hj) he (ne_of_mem_erase hj)) hf (mem_of_mem_erase hz)) -- private let elimination?
section circling
variable (hp:M.turn.badge S∈i) (he:i∈V)
include H hk h he hp
lemma constell (ht:X.manifest) : M.tithe X k W o.a Q.table Q.halo (V.biUnion id)= M.tithe X k W o.a Q.table Q.halo i*∏ j∈V.erase i,X.attains R Q.table W o.a k Q.halo j:=by
  let u:= X.body R Q.table W o.a k Q.halo; let F' := M.into X W o.a Q.table k Q.halo; let g0 p := if p=i then F' p else u p
  let D:= (F.order G).prod X.dice
  have h2 (w:F.Slice G × Air f G): F' (V.biUnion id) w=∏ p∈V,g0 p w:=by -- rename
    rw [← mul_prod_erase _ _ he]; simp only [g0,if_true]; rw [show F' (V.biUnion id) w=F' i w * ∏ j∈V.erase i,u j w from M.sticksU (X.wrapY w.1) k (unweave h) he hp w.2]
    exact congr_arg (_*·) (prod_congr rfl fun j hj=>by rw [if_neg (ne_of_mem_erase hj)])
  have hh p: Integrable (g0 p) D:=by unfold g0; split; exact (M.tip X k H hk ht p).2.1; exact H.integrated X rfl hk ht k p
  have hg p: Measurable (g0 p):=by
    unfold g0; split
    · exact M.tip X k H hk ht p|>.1.meas
    exact X.body_b Q.table_exists H.laws.intake (hk.symm ▸ H.laws.data.access) ..
  let g p (a:F.Slice G):=∫ v, g0 p (a,v) ∂ X.dice
  let I(p):=podium S G (ground R T Q.halo X.B p) X.B; let p : (V:Set _).PairwiseDisjoint H.unionP := h.2
  have hX:= H.laws.data; have hy : X.relating.PosDef := (hX.localP F X rfl hk ht).sails.fullC
  have hx z (V : F.Slice G) (b : F.Slice G) (hm : ∀ i:F.Free,atEdge S i.val∈ H.unionP z → V i=b i) (s t) (hr:Pond.swim (I z) s=Pond.swim (I z) t) : g0 z (V,s)=g0 z (b,t):=by
    have hc : Borough (X.wrapY V) (X.wrapY b) (H.unionP z) s t k k R:= ⟨(Village.refl _ _).wrap _ _ hm, (observe _).1 hr, fun _ _=>Iff.rfl⟩
    unfold g0; split
    · exact M.concur _ _ _ hc H.laws.data.room Q.buys (Finset.Subset.refl _) H.laws.intake
    exact H.concord z _ _ hc rfl (Finset.Subset.refl _)
  have ho z: (∫ v, F' (V.biUnion id) (z,v) ∂X.dice)=∏ p∈V,g p z:=by
    simp_rw [h2]; exact Pond.island hy.posSemidef V I (fun i hi j hj hn x hx y ha=>by
      apply X.shutter.width X.plate; by_contra hh; have he := le_of_not_gt hh
      have hc : 100≤ X.B:= H.laws.data.room.sight.1
      exact Finset.disjoint_left.mp (p hi hj hn) ((mem_filter.mp hx).2 (along S y) (he.trans (by omega))) ((mem_filter.mp ha).2 (along S y) (by rw [separation_self]; omega)))
      (fun i v=>g0 i (z,v)) (fun i _=>(hg i).comp (measurable_const.prodMk measurable_id)) (fun i _ a b=>hx i z z (fun _ _=> rfl) a b)
  let L i:= univ.filter fun j:F.Free=>atEdge S j.val∈ H.unionP i
  have hH := Pond.marched (fun _ : F.Free=> G.probHaar) V L (fun i hi j hj hk=> show Disjoint _ _ from Finset.disjoint_left.mpr fun y ha hb=> Finset.disjoint_left.mp (p hi hj hk) ((mem_filter.mp ha).2) ((mem_filter.mp hb).2)) g
    (fun i _=> (hg i|>.stronglyMeasurable.integral_prod_right').measurable) (fun i _ v b hh=> integral_congr_ae (ae_of_all _ fun z=>hx i v b (fun j hj=> hh j (mem_filter.mpr ⟨mem_univ _,hj⟩)) z z rfl))
  have hh' i: (∫ z,g i z ∂F.order G)=∫ z, g0 i z ∂D:= (integral_prod (g0 i) (hh i)).symm
  unfold tithe; rw [integral_prod _ (M.tip X k H hk ht _|>.2.1)]
  change (∫ z,(∫ y,F' (V.biUnion id) (z,y) ∂_) ∂_)=_
  simp_rw [ho]; change (∫ u,∏ j∈V, g j u ∂ F.order G)=_
  rw [show (∫ u,∏ j∈V, g j u ∂ F.order G)=∏ j∈V,∫ u, g j u ∂F.order G from hH,← mul_prod_erase _ _ he]
  simp_rw [hh']; rw [show g0 i=F' i from if_pos rfl]; refine congr_arg ((∫ z,F' i z ∂D)*·) (prod_congr rfl fun j hj => by rw [show g0 j= u j from if_neg (ne_of_mem_erase hj)]; rfl)
end circling
end Leaf
end YM.PhysicalNext.Repeat.Lotus
