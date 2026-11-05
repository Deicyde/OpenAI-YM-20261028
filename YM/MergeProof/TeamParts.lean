import YM.MergeProof.TeamKernel
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
namespace Team
variable (M : Team R) (X : Coat T F) (k:Finset ℕ)
variable (X' : Coat T F) {p : Molecule S} {l' k' : Finset ℕ} {Z : Support c} {u v : Air f G}
lemma concur (A:Borough X X' Z u v k k' R)(he: Room P S T X.x) (hl:500≤m) (hp: ground R T m X.B p⊆ Z)
    (hT : Intake P T X.x R) : M.premium X W a Ñ k m u p=M.premium X' W a Ñ k' m v p:=by
  unfold premium; split
  next ha=>
    have hW (M' : Leaf R)(hk:M'∈M.own) : M'.paidU X a (X.liftA R.beta u) = M'.paidU X' a (X'.liftA R.beta v):= by
      have hA:= ha (show M'.turn.badge S ∈ M.signs S from mem_image_of_mem _ hk)
      have hv : areas R T m X.B (M'.turn.badge S)⊆ Z := (subset_biUnion_of_mem _ hA).trans hp
      have hZ : Footprint.enlargement S.ratio m X.B (RG.inspected M'.crest)⊆ Z:= by rw [M'.turn.badge_area] at hv; exact hv
      have hx : M'.ingredient (X.input _)=M'.ingredient (X'.input _) := M'.specific _ _ (A.inherits he (l:=m) (by omega) _ hZ)
      have hh : ∀ i∈ areas R T 0 X.B (M'.turn.badge S),Cleanroom Z (30*X.B) i:=by
        intro i hi j hj; rw [M'.turn.badge_area] at hi; obtain ⟨x,h,p⟩:= halo_spec.mp hi
        apply hZ; refine halo_spec.mpr ⟨x,h,(separation_triangle x i j).trans ?_⟩; rw [zero_mul] at p
        exact le_trans (add_le_add p hj) ((zero_add _).trans_le (Nat.mul_le_mul_right X.B (by omega)))
      unfold Leaf.paidU Leaf.fond; rw [← A.B, A.enforces he _ hh, hx]
    rw [show M.paidU X a (X.liftA R.beta u) = M.paidU X' a _ from prod_congr rfl hW]
    exact congr_arg (_ * ·) (Finset.prod_congr rfl (fun i hi=> A.complete he hl i ((show areas R T m X.B i⊆ _ from subset_biUnion_of_mem _ ((Finset.mem_sdiff.mp hi).1)).trans hp) hT _ _ _))
  rfl
variable (H:Cash W X.x μ L Q o C T R)(hk:X.width=o.K)(ht:X.manifest)
include H hk
lemma coni (ht:X.manifest) (hq:X'.manifest)(hv:Village X X' (H.unionP p)) (hg :∀ i: Site f,S.ratio.parent i∈ H.unionP p → (i∈Contract.covered R k ↔ i∈Contract.covered R k')):
    M.tithe X k W o.a Q.table Q.halo p=M.tithe X' k' W o.a Q.table Q.halo p:=by
  have hh:X'.x=X.x:=hv.weather.symm
  -- H tip via explicit compatibility
  unfold tithe; rw [integral_prod _ (M.tip X k H hk ht p|>.2.1),integral_prod _ (M.tip X' k' (show Cash W X'.x μ L Q o C T R from hh.symm ▸ H) (hv.width ▸ hk) hq p|>.2.1)]
  apply integral_congr_ae; filter_upwards with y; let I:=podium S G (H.unionP p) X.B
  have hpX: X.relating.PosDef := (H.laws.data.localP F X rfl hk ht).sails.fullC
  have hp: X'.relating.PosDef:= (H.laws.data.localP F X' hh (hv.width ▸ hk) hq).sails.fullC
  have hb:circuit I X.relating=circuit I X'.relating:=by ext i j; exact hv.same_cov H.laws.data.room j.val j.2 i.val
  have hM : MeasurePreserving (swim I) X'.dice (arch I X.relating) := by rw [arch,hb]; exact orbit hp.posSemidef I
  let f (u:Air f G) := M.into X W o.a Q.table k Q.halo p (y,u)
  let f' (u:Air _ G) := M.into X' W o.a Q.table k' Q.halo p (y,u)
  have ht':Measurable f:= (M.tip X k H hk ht p|>.1.meas).comp (measurable_const.prodMk measurable_id)
  have hg':Measurable f':= (M.tip X' k' (show Cash W X'.x μ L Q o C T R from hh.symm ▸ H) (hv.width ▸ hk) hq p|>.1.meas).comp (measurable_const.prodMk measurable_id)
  have hc(u v)(hx: swim I u=swim I v): f u=f' v:= M.concur (X.wrapY y) k (X'.wrapY y) ⟨hv.wrap y y (fun _ _=>rfl),(observe I).mp hx,hg⟩ H.laws.data.room Q.buys (Finset.Subset.refl _) H.laws.intake
  rw [Pond.gathered (spill I) (spill_m I) (show MeasurePreserving (swim I) X.dice (arch I X.relating) from orbit hpX.posSemidef I) (settled I) (f:=f) (fun u v h=> (hc u v h).trans (hc v v rfl).symm) ht', Pond.gathered (spill I) (spill_m I) hM (settled I) (f:=f') (fun u v h=> (hc u u rfl).symm.trans (hc u v h)) hg']
  exact integral_congr_ae (Eventually.of_forall fun z=>hc _ _ rfl)

omit H hk
def locate (i:Molecule S): Team R := ⟨M.own.filter (fun j=> j.turn.badge S∈i),M.alone.mono (Finset.filter_subset ..)⟩
lemma lsign (i:Molecule S) : (M.locate i).signs S= M.signs S ∩ i:= by
  ext a; constructor
  · intro h; obtain ⟨j,hQ,rfl⟩:= mem_image.mp h; obtain ⟨hU,hp⟩:=mem_filter.mp hQ;exact mem_inter.mpr ⟨mem_image_of_mem _ hU,hp⟩
  intro h; obtain ⟨hP,hp⟩:= mem_inter.mp h; obtain ⟨j,hQ,rfl⟩:= mem_image.mp hP; exact mem_image_of_mem _ (mem_filter.mpr ⟨hQ,hp⟩)
private lemma sliceOff {α : Type*} [DecidableEq α] (H : Finset α)(p:Finset (Finset α)): (p.biUnion id) \ H = p.biUnion (fun i=> i\(H∩i)):=by
  ext a; simp only [Finset.mem_sdiff,mem_biUnion,id_eq,mem_inter]; grind

lemma sticksU {m : ℕ} {V : Finset (Molecule S)} (h : (V:Set (Molecule S)).PairwiseDisjoint id) (hp:M.signs S ⊆ V.biUnion id) (z:Air f G): M.premium X W a Ñ k m z (V.biUnion id) = ∏ j∈V,(M.locate j).premium X W a Ñ k m z j:=by
  unfold premium; simp_rw [lsign, if_pos inter_subset_right]; rw [if_pos hp]; unfold term; simp_rw [← M.lsign] -- except
  have ht : V.biUnion (fun j=> (M.locate j).own)=M.own:= by
    ext i; constructor
    · intro hi; obtain ⟨j,hj,hv⟩:=mem_biUnion.mp hi;exact (mem_filter.mp hv).1
    intro hi; obtain ⟨j,hj,hv⟩:=mem_biUnion.mp (hp (show i.turn.badge S∈M.signs S from mem_image_of_mem _ hi)); exact mem_biUnion.mpr ⟨j,hj,mem_filter.mpr ⟨hi,hv⟩⟩
  have hx : (V.biUnion id) \ M.signs S=V.biUnion (fun j=> j\(M.locate j).signs S):=by simp_rw [lsign]; exact sliceOff ..
  unfold paidU
  nth_rw 1 [← ht]; rw [hx,prod_biUnion,prod_biUnion, prod_mul_distrib]
  · exact fun i hi j hj hn=> Finset.disjoint_left.mpr fun k hK hL=>Finset.disjoint_left.mp (h hi hj hn) ((Finset.mem_sdiff.mp hK).1) ((Finset.mem_sdiff.mp hL).1)
  exact fun i hi j hj hn=> Finset.disjoint_left.mpr fun k hK hL=>Finset.disjoint_left.mp (h hi hj hn) ((mem_filter.mp hK).2) ((mem_filter.mp hL).2)

open Census Itinerary
variable (V: Finset (Molecule S))(h:joints T R Q.halo X.B V)
include H hk h
lemma constell (ht:X.manifest)(hp:M.signs S ⊆ V.biUnion id): M.tithe X k W o.a Q.table Q.halo (V.biUnion id)= ∏ j∈V,(M.locate j).tithe X k W o.a Q.table Q.halo j:=by
  let D:= (F.order G).prod X.dice; let g0 j:= (M.locate j).into X W o.a Q.table k Q.halo j
  let F' := M.into X W o.a Q.table k Q.halo
  have h2 (w:F.Slice G × Air f G): F' (V.biUnion id) w=∏ p∈V,g0 p w:= M.sticksU (X.wrapY w.1) k (unweave h) hp w.2
  have hh p: Integrable (g0 p) D:= ((M.locate p).tip X k H hk ht p).2.1
  have hg p: Measurable (g0 p):=((M.locate p).tip X k H hk ht p).1.meas
  let g p (a:F.Slice G):=∫ v, g0 p (a,v) ∂ X.dice
  let I(p):=podium S G (ground R T Q.halo X.B p) X.B; let p : (V:Set _).PairwiseDisjoint H.unionP := h.2
  have hX:= H.laws.data; have hy : X.relating.PosDef := (hX.localP F X rfl hk ht).sails.fullC
  have hx z (V : F.Slice G) (b : F.Slice G) (hm : ∀ i:F.Free,atEdge S i.val∈ H.unionP z → V i=b i) (s t) (hr:Pond.swim (I z) s=Pond.swim (I z) t) : g0 z (V,s)=g0 z (b,t):=by
    have hc : Borough (X.wrapY V) (X.wrapY b) (H.unionP z) s t k k R:= ⟨(Village.refl _ _).wrap _ _ hm, (observe _).1 hr, fun _ _=>Iff.rfl⟩
    exact (M.locate z).concur (X.wrapY V) _ _ hc H.laws.data.room Q.buys (Finset.Subset.refl _) H.laws.intake
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
  rw [show (∫ u,∏ j∈V, g j u ∂ F.order G)=∏ j∈V,∫ u, g j u ∂F.order G from hH]
  exact prod_congr rfl fun j _=> hh' j
end Team
end YM.PhysicalNext.Repeat.Lotus
