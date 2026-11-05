import YM.MergeProof.TeamParts
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
private lemma weightedProd {α β : Type} [Fintype α] [Fintype β] (f : α×β →ℝ) : likely f =
    likely (fun v=> likely fun b=> f (v,b)) := by
  unfold likely; rw [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul, mul_inv]; rw [← Finset.mul_sum]; ring

private lemma jurs {κ Ω ι : Type} [Fintype ι] [Fintype Ω] [Nonempty Ω] (g : Fintype (ι→Ω))
    (V : Finset κ) (X : κ→Finset ι) (h : (V:Set κ).PairwiseDisjoint X) (f : κ → (ι→Ω)→ℝ)
    (hp : ∀ i∈V,∀ v w,(∀ p∈ X i, v p=w p) → f i v=f i w) :
    @likely _ g (fun u=> ∏ i∈V,f i u) = ∏ i∈ V,@likely _ g (f i) := by
  convert! Pond.jurisdictions V X h f hp

open Census Itinerary
variable (H:Cash W X.x μ L Q o C T R)(hk:X.width=o.K) (V: Finset (Molecule S))
variable (h:joints T R Q.halo X.B V) {i:Molecule S}

def steep (l:Finset ℕ)(W a:ℝ)(Ñ:ChartRatio G)(m:ℕ)(p : Molecule S) := likely fun q=> M.tithe (X.taggedL q) l W a Ñ m p
def bloom (W a:ℝ)(Ñ:ChartRatio G)(m:ℕ)(p : Molecule S) := if standsIn X R m p then M.steep (planted X p) (Matter.own p) W a Ñ m p else 0
-- derivative of ejections, product-rule rate
-- same forced scope even for markings. implies EXACT assembly.
def froth (W a:ℝ)(Ñ:ChartRatio G) (m : ℕ) (V:Finset (Molecule S)):= if joints T R m X.B V ∧ Matter.covers X V ∧ M.signs S ⊆ V.biUnion id then
    ∏ i∈V,(M.locate i).bloom X W a Ñ m i else 0
lemma tithe_off (i : Molecule S) (hp : ¬ M.signs S⊆ i): M.tithe X k W a Ñ m i=0:=by unfold tithe into premium; simp_rw [if_neg hp,integral_zero]
lemma bloom_off (i : Molecule S) (h : ¬ M.signs S⊆i): M.bloom X W a Ñ m i=0:=by
  unfold bloom steep likely; split; next=> simp_rw [M.tithe_off _ _ i h]; simp
  next=> rfl

include H hk h
lemma spices (hp:M.signs S ⊆ V.biUnion id) (ha:X.manifest): M.steep X k W o.a Q.table Q.halo (V.biUnion id)=∏j∈V,(M.locate j).steep X k W o.a Q.table Q.halo j:=by
  let m j (p:S.Choices):= M.tithe (X.taggedL p) k W o.a Q.table Q.halo j
  let f p (i' : S.Choices):= (M.locate p).tithe (X.taggedL i') k W o.a Q.table Q.halo p
  let J p : Support c:= ground R T Q.halo X.B p
  have hb(z:S.Choices):m (V.biUnion id) z=∏p∈ V,f p z:= M.constell (X.taggedL z) k H hk V h ha hp
  have hz i' (j k' : S.Choices) (hs : ∀ p∈J i', Prod.fst j p=Prod.fst k' p)
      (hf : ∀ b : Bond c,b.1∈ J i' → Prod.snd j b=Prod.snd k' b) : f i' j=f i' k':=by
    have hv : Village (X.taggedL j) (X.taggedL k') (H.unionP i'):=⟨rfl,rfl,rfl,fun _ _=>Iff.rfl,fun _ _=>rfl,hs,hf,fun _ _ _=> rfl⟩
    exact (M.locate i').coni (X.taggedL j) _ _ H hk ha ha hv (fun _ _=>Iff.rfl)
  have hv : M.steep X k W o.a Q.table Q.halo (V.biUnion id)=∏p∈V,likely (f p):=by
    let g (k : S.SitesChoice) (p : S.BondChoice) := ∏ i∈V,f i (k,p)
    have hh k : likely (fun p=> g k p)=∏ i∈V, likely (fun p=> f i (k,p)) := by
      let T0 i:= univ.filter fun j : Bond c => j.1∈J i
      have hm : (V:Set _).PairwiseDisjoint T0 := fun i hi j hj hu=> Finset.disjoint_left.mpr fun y ha hk=> Finset.disjoint_left.mp (h.2 hi hj hu) ((mem_filter.mp ha).2) ((mem_filter.mp hk).2)
      exact jurs _ V T0 hm (fun i p=>f i (k,p)) (fun i _ v b hh=> hz _ _ _ (fun _ _=>rfl) (fun j hj=>hh j (mem_filter.mpr ⟨mem_univ _,hj⟩)))
    change likely (m (V.biUnion id))=_
    simp_rw [weightedProd (α:=S.SitesChoice) (β:=S.BondChoice),hb]
    change likely (fun k=>likely fun p=>g k p)=_
    simp_rw [hh]
    exact jurs _ (Ω:=S.patch.FrameTag) _ J h.2 _ (fun i _ x y hv=> congr_arg likely (funext fun j=> hz i _ _ hv (fun _ _ =>rfl)))
  exact hv
-- ferry from Manifesto evidence on same packet.
omit H hk h in
private lemma plant_area {l : ℕ} (h : claimed X R l p) (o : Site c) (hp : o∈ ground R T l X.B p) :
    o∈ (planted X p).seeds.place ↔ o∈(roster p).place := by
  have he := h.2; unfold place; simp only [preps,planted,mem_union]; rw [← he,mem_inter]; simp [hp]

lemma scents (he : Matter.covers X V) (hi : p∈V) (hy : standsIn X R Q.halo p)
     : M.bloom X W o.a Q.table Q.halo p=M.steep (preps X (roster (V.biUnion id))) (Matter.own (V.biUnion id)) W o.a Q.table Q.halo p := by
  let Y:= planted X p; let A:= V.biUnion id; let Y':=preps X (roster A); let s:= H.unionP
  have hm : Y'.manifest := by unfold manifest Y' preps A; rw [totals]; exact he
  rw [bloom, if_pos hy];
  unfold steep; apply congr_arg likely; funext k
  have hl : (V:Set _).PairwiseDisjoint s := h.2
  have hv i (hc : i∈ V) (o) (hx : o∈s p) (hy : o∈ s i) : p=i := by
    by_contra hn; exact Finset.disjoint_left.mp (hl hi hc hn) hx hy
  have hp (x) (hx : x∈ s p) : x∈ (roster p).place ↔ x∈(roster A).place := by
    rw [← Packets.place_reads,← Packets.place_reads]; constructor
    · intro h; obtain ⟨v,hv,h⟩ := mem_biUnion.mp h
      exact mem_biUnion.mpr ⟨v,(star_sizes V _).2 ⟨p,hi,hv⟩,h⟩
    intro h; obtain ⟨j,hj,h⟩ := mem_biUnion.mp h; obtain ⟨i,hi,hb⟩ := (star_sizes V _).1 hj
    refine mem_biUnion.mpr ⟨j,(hv i hi _ hx (claim_zoneA R T _ _ i _ hb h)).symm ▸ hb,h⟩
  refine M.coni (Y.taggedL k) _ (Y'.taggedL k) H hk (planted_valid X p) hm
    ⟨rfl,rfl,rfl,fun i hi=> (plant_area X hy.2 i hi).trans (hp i hi), fun _ _=>rfl,
      fun _ _=> rfl, fun _ _=>rfl,fun _ _ _=> rfl⟩ ?_
  intro i hj; constructor
  · intro hh; obtain ⟨j,hv,hh⟩ := mem_biUnion.mp hh; exact mem_biUnion.mpr ⟨j,(gloss V _).2 ⟨p,hi,hv⟩,hh⟩
  intro hq; obtain ⟨b,hb,hx⟩ := mem_biUnion.mp hq; obtain ⟨v,hb,hk⟩ := (gloss V _).1 hb
  exact mem_biUnion.mpr ⟨b,(hv v hb _ hj (claim_zoneK R T _ _ v _ hk hx)).symm ▸ hk,hx⟩

-- pointwise product per Character, covers even if only one flag on mark.
lemma harvest : M.froth X W o.a Q.table Q.halo V=M.bourbon X W o.a Q.table Q.halo (V.biUnion id) :=by
  have ht:=cap_iff X h; unfold froth bourbon; dsimp only at *; simp_rw [ht]
  by_cases hp : Matter.covers X V ∧ ∀ i∈V,standsIn X R Q.halo i
  · rw [if_pos hp]; let p := V.biUnion id; let Y:= preps X (roster p); change _=M.steep Y (Matter.own p) W o.a Q.table Q.halo p
    by_cases ha:M.signs S ⊆ p
    · rw [M.spices Y (Matter.own p) H hk V h ha ((ht.2 hp).1.1), if_pos ⟨h,hp.1,ha⟩]; exact prod_congr rfl fun i hi=> (M.locate i).scents X H hk V h hp.1 hi (hp.2 i hi)
    rw [if_neg (fun h=>ha h.2.2)]; unfold steep likely; simp_rw [M.tithe_off _ _ p ha]; simp
  rw [if_neg hp]; split
  next hx =>
    obtain ⟨v,hv,ha⟩:∃ v∈V,¬standsIn X R Q.halo v:=by by_contra! hh; exact hp ⟨hx.2.1,hh⟩
    exact prod_eq_zero hv (if_neg ha)
  rfl
omit h
lemma streetP : HasSum (fun V:Finset (Molecule S)=> overhead X R Q.table * M.froth X W o.a Q.table Q.halo V) (S.push R.beta M.cicada X.V):=by
  let f V:= overhead X R Q.table * M.froth X W o.a Q.table Q.halo V; let g:= Ac.Parts H.supportP
  have he : Injective g:= LeftInverse.injective (show LeftInverse (fun t=> t.biUnion id) g from fun i=>Ac.reconstruct ..); apply (he.hasSum_iff (f:=f) ?_).1
  · refine (M.success X H hk).congr_fun (fun p=>?_)
    have hp : joints T R Q.halo X.B (g p):= ⟨fun i hi=> (Ac.lives H.supportP p hi).2, Ac.separate ..⟩
    unfold f Function.comp; dsimp only; rw [M.harvest X H hk _ hp,show (g p).biUnion id=p from Ac.reconstruct ..]
  intro i hi; unfold f froth; rw [if_neg (fun h=>hi ⟨_,separates h.1⟩),mul_zero]
end Team
end YM.PhysicalNext.Repeat.Lotus
