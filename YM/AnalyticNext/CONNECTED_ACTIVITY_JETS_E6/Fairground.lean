import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.ParkL

/-!
# Factorization at full global measures with swept Gaussian

Volume normalized and Y frozen. k average uniformly included.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Cash
open Filter Function Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented  Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {a α W μ C : ℝ} {R : Rep G f} {Z Z' : Support c}
variable {k k' : Finset ℕ} {w v : Air f G} {L : Side}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable (H : Cash W α μ L Q o C T R) (X : Coat T F) (he : X.x=α) (ht : X.width=o.K) (hf : X.manifest)
variable (l : Finset ℕ) (V : Finset (Molecule S)) (h : (V:Set (Molecule S)).PairwiseDisjoint H.unionP)

omit h he hf ht in
private lemma parks (hV : (V:Set (Molecule S)).PairwiseDisjoint id) (z : F.Slice G × Air f G) :
    (∏ p∈V,X.body R Q.table W o.a l Q.halo p z)= X.body R Q.table W o.a l Q.halo (V.biUnion id) z := by
  unfold Coat.body Coat.term; rw [prod_biUnion hV]; rfl

include he ht hf h
lemma rides (hV : (V:Set (Molecule S)).PairwiseDisjoint id) :
    X.attains R Q.table W o.a l Q.halo (V.biUnion id)=∏ p∈ V,X.attains R Q.table W o.a l Q.halo p := by
  let f':= X.body R Q.table W o.a l Q.halo
  have hF i : Measurable (f' i) := X.body_b Q.table_exists (he.symm ▸ H.laws.intake) (by rw [he,ht]; exact H.laws.data.access) ..
  let g i (y : F.Slice G):=∫ z, f' i (y,z) ∂X.dice
  let p:= h
  have hh i : X.attains R Q.table W o.a l Q.halo i=∫ y,g i y ∂F.order G := integral_prod (f' i) (H.integrated X he ht hf l i)
  let I (v) := podium S G (H.unionP v) X.B
  have hk : X.relating.PosSemidef := (H.laws.data.localP F X he ht hf).sails.fullC.posSemidef
  have hc : 100≤X.B := (H.laws.data.localP F X he ht hf).sails.room.sight.1
  have hp y : g (V.biUnion id) y=∏ i∈V,g i y := by
    have hg i (u v : Air f G) (hx : Pond.swim (I i) u=Pond.swim (I i) v) : f' i (y,u) = f' i (y,v) :=
      H.concord i (X.wrapY y) (X.wrapY y) ⟨Village.refl _ _, (observe _).1 hx,fun _ _=> Iff.rfl⟩ he (Finset.Subset.refl _)
    unfold g at *
    change _=∏ i∈V,∫ z, f' i (y,z) ∂sweep X.relating
    rw [← Pond.island hk V I ?_ (fun i z=>f' i (y,z)) (fun i _=> (hF i).comp (measurable_const.prodMk measurable_id)) (fun i _=>hg i)]
    · exact integral_congr_ae (ae_of_all _ fun z=> (parks X l V hV ..).symm)
    intro i hi j hj hn x hx z hz
    apply X.shutter.width X.plate
    by_contra hy
    have he := le_of_not_gt hy
    exact Finset.disjoint_left.mp (p hi hj hn) ((mem_filter.mp hx).2 (along S z) (he.trans (by omega)))
      ((mem_filter.mp hz).2 (along S z) (by rw [separation_self]; omega))
  let L i:= univ.filter fun j : F.Free=> atEdge S j.val∈ H.unionP i
  simp_rw [hh,hp]
  refine marched (fun i : F.Free=> G.probHaar) V L ?_ g (fun i _ => (hF i).stronglyMeasurable.integral_prod_right'.measurable) ?_
  · exact fun i hi j hj hh=> Finset.disjoint_left.mpr fun y hy hg=> Finset.disjoint_left.mp
      (p hi hj hh) ((mem_filter.mp hy).2) ((mem_filter.mp hg).2)
  intro i hi u b hh
  apply integral_congr_ae; filter_upwards with z
  exact H.concord i (X.wrapY u) (X.wrapY b) ⟨(Village.refl X (H.unionP i)).wrap _ _
    (fun j hj=> hh j <| mem_filter.mpr ⟨mem_univ _,hj⟩), fun _ _=> rfl,fun _ _=> Iff.rfl⟩ he (Finset.Subset.refl _)

omit H h he ht hf in
private lemma weightedProd {α β : Type} [Fintype α] [Fintype β] (f : α×β →ℝ) : likely f =
    likely (fun v=> likely fun b=> f (v,b)) := by
  unfold likely; rw [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul, mul_inv]; rw [← Finset.mul_sum]; ring

omit H h he ht hf in
private lemma jurs {κ Ω ι : Type} [Fintype ι] [Fintype Ω] [Nonempty Ω] (g : Fintype (ι→Ω))
    (V : Finset κ) (X : κ→Finset ι) (h : (V:Set κ).PairwiseDisjoint X) (f : κ → (ι→Ω)→ℝ)
    (hp : ∀ i∈V,∀ v w,(∀ p∈ X i, v p=w p) → f i v=f i w) :
    @likely _ g (fun u=> ∏ i∈V,f i u) = ∏ i∈ V,@likely _ g (f i) := by
  convert! Pond.jurisdictions V X h f hp

lemma red_carpet (hv : (V:Set (Molecule S)).PairwiseDisjoint id) :
    X.levelMean R Q.table W o.a l Q.halo (V.biUnion id)=∏ p∈ V,X.levelMean R Q.table W o.a l Q.halo p := by
  let f i (k : S.Choices) := (X.taggedL k).attains R Q.table W o.a l Q.halo i
  have hp i (j k : S.Choices) (hs : ∀ p∈H.unionP i, Prod.fst j p=Prod.fst k p) (hf' :
      ∀ b : Bond c,b.1∈ H.unionP i → Prod.snd j b=Prod.snd k b) : f i j=f i k := H.vista i (X.taggedL j) (X.taggedL k) he ht hf hf
    ⟨rfl,rfl,rfl,fun _ _=>Iff.rfl,fun _ _=> rfl,hs,hf',fun _ _ _=> rfl⟩ (fun _ _=> Iff.rfl)
  have ht' k : f (V.biUnion id) k= ∏ i∈V,f i k := H.rides (X.taggedL k) he ht hf l V h hv
  unfold levelMean; change likely (fun p=> f _ p)=∏ i∈ V, likely (fun p=> f i p)
  let g (k : S.SitesChoice) (p : S.BondChoice) := ∏ i∈V,f i (k,p)
  have hh k : likely (fun p=> g k p)=∏ i∈V, likely (fun p=> f i (k,p)) := by
    let T i:= univ.filter fun j : Bond c => j.1∈H.unionP i
    have hm : (V:Set (Molecule S)).PairwiseDisjoint T := fun i hi j hj hz=> Finset.disjoint_left.mpr fun y ha hk=> Finset.disjoint_left.mp
      (h hi hj hz) ((mem_filter.mp ha).2) ((mem_filter.mp hk).2)
    let J i (p : S.BondChoice) := f i (k,p)
    have he i (_hi : i∈ V) (u v : S.BondChoice) (hs : ∀ j∈ T i, u j=v j) : J i u=J i v := hp i (k,u) (k,v) (fun _ _=> rfl) (fun j hj=> hs j (mem_filter.mpr ⟨mem_univ _,hj⟩))
    exact jurs _ V T hm J he
  simp_rw [weightedProd (α:= S.SitesChoice) (β:= S.BondChoice), ht']
  change likely (fun p=> likely fun i=> g p i)=_
  simp_rw [hh]; refine jurs _ (Ω:=S.patch.FrameTag) (X:=H.unionP) V h (fun i p=> likely fun q=> f i (p,q)) (fun i _ x y hh=> ?_)
  exact congr_arg likely (funext fun j => hp i (x,j) (y,j) hh (fun _ _ => rfl))
end YM.ConnectedActivityE6.Cash
