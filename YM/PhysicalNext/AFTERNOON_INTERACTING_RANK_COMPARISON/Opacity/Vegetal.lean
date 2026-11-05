import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE.Covers
import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Rebased
import YM.Extra.MULTISOURCE_BOUNDS.Merger
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Plotter
/-!
# Finite unmarked Body roster carrier

Print on ancestral R∅ rather than a selector, orientation proof after Rosters.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Pump
open Function Lattice RG Pressure Tree Wilson AnalyticBridge.GaussianFieldAlignment Locations Channels
open Matrix Finset PhysicalGuard7f546.Curved Next.SectorChange Precision AnalyticBridge.LocalGaussianLaws Filter
    SectorTools.PhysicalGaussianSwitch AnalyticBridge.RelativeLogdet MeasureTheory Push.Local
    Push.SectorMeasure Push.SectorMeasure.Oriented Push.AbsoluteSums Pressure.Stores
    AnalyticNext.ConnectedActivity GaugeRoute Packets Display Display.Sew Pot Marker
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {c f : Side} {G : Gauge} {S : StepData c f} {x W : ℝ} {A B : Stores S} {p q : Pilot G S x} {v : Dyed G S} {P : Teller G}
namespace Vale
abbrev Herbs (S:StepData c f) (x:ℝ):= Rung S x ⊕ Fleck S ⊕ Glade c
variable (v : Dyed G S) (W) (M : Plate v x W)

def atomP (i : Herbs S x) (p : Pilot G S x): ℝ:= i.elim (fun i=> checkIn v i p * autumn v W M (rips i) p) (Sum.elim (fun i=>v.sock W i p) (fun j=>Real.exp (M.aux j p)-1))

def scarf (i : Herbs S x) := i.elim (fun i=>acre (rips i)) (Sum.elim (spanFoot S x) Subtype.val)
def bread (i : Herbs S x) := i.elim (fun i=>(rips i).val) (fun _=> store S ∅)
def loves (i : Herbs S x) : Support f:=i.elim markT fun _=>∅
def dues (i : Herbs S x) : Support c:= i.elim (fun i=>acre (rips i)) fun _=>∅
@[simp] lemma blankFlags : (Packets.store S ∅).flags=∅:= by ext; simp [Packets.store]

lemma plate_tag (H : Boosted v.things P x) (hm : Coverage.shutters S.patch+1≤radiusB x) (hd : 0<v.arc) (hr :2*v.arc<firstRadius G) (i : Herbs S x) : Pulled (atomP W v M i) (scarf i) ∧ Tinted (atomP W v M i) ∧
    ∀ p e, atomP W v M (Equiv.sumCongr (traveling S x e) (Equiv.sumCongr (pursuit S e) (garden (orient e))) i) p = atomP W v M i (spires e p):= by
  rcases i with i|i|i
  · obtain ⟨hc,he⟩:= guard_paid v H hd hr H.produced.scale i
    obtain ⟨hp,h,H₁⟩:= booth_cape v W M H hm hd hr (rips i)
    refine ⟨hc.times hp,fun p hp f=> congr_arg₂ HMul.hMul (he p hp f) (h p hp f),fun p e=>?_⟩
    exact congr_arg₂ HMul.hMul (planted_turn v H.funded i p e).symm (H₁ p e).symm
  · obtain ⟨hv,hP⟩:= v.sock_budget W H i hm hd hr; exact ⟨hv,hP,fun p e=> v.sock_ship W H.funded i e p⟩
  let f (x:ℝ):=Real.exp x-1
  exact ⟨(M.tip i).twine (show Measurable f from Real.continuous_exp.measurable.sub measurable_const),fun p hp e=>congr_arg f (M.mine i p hp e),fun p e=> congr_arg f (M.toll e p i)⟩

-- for direct Body.
structure Draft (v : Dyed G S) (P : Teller G) (x W : ℝ) : Prop where
  enrolled : Boosted v.things P x
  width : Coverage.shutters S.patch+1≤radiusB x
  pos : 0<v.arc
  radius : 2*v.arc<firstRadius G

variable {v W M} (H : Draft v P x W)
abbrev bare (n : Side) : Empty→ Site n:= Empty.elim

def amount (M : Plate v x W) (O : Orchard S) (i : Herbs S x): PaintCan S G x O (bare c) v.bp.threshold where
  X:=scarf i
  goal:=(bread i).flags
  supplies:=loves i
  wants:=loves i
  barricade:=dues i
  encumbrance:=∅
  permit:=((bread i).costs,(bread i).aisles)
  hues:= Next.Rank.Glyph.quiet _
  lamp:=fun A k V y=> (↑(atomP W v M i ⟨A,k.wood,k.tag,V,y⟩):ℂ)
  exists_site := by
    rcases i with i|i|i; exact acres_lit _; exact ⟨_,halo_subset _ _ (footfall S i)⟩; exact i.property
  go:= by
    rcases i with i|i; exact fun j hj=> halo_subset _ _ (mem_union_right _ hj); change (Packets.store S ∅).flags⊆_; simp
  store := by
    rcases i with i|i
    · exact fun k h=> transmit (rips i) (mem_image_of_mem _ (i.property h))
    exact fun k h=> False.elim (notMem_empty k h)
  feeds := by
    rcases i with i|i
    · exact fun k h=> transmit (rips i) (mem_image_of_mem _ (i.property h))
    exact fun k h=> False.elim (notMem_empty k h)
  coverage := by rcases i with i|i; exact Subset.refl _; exact empty_subset _
  embeds := by simp
  lends := by
    rcases i with i|i
    · exact fun k hk=> halo_subset _ _ (mem_union_left _ hk)
    intro i; simp [bread,store,wards]
  remembers := fun t=> t.elim
  sees:= (Pulled.versed (plate_tag _ _ _ H.enrolled H.width H.pos H.radius i|>.1) (plate_tag _ _ _ H.enrolled H.width H.pos H.radius i|>.2.1) O _ v.bp.threshold).comp Complex.ofReal Complex.continuous_ofReal.measurable

abbrev Sprigs (M : Plate v x W) (O : Orchard S) := Club (amount H M O)

def sprouting (M : Plate v x W) (O : Orchard S) (i : Sprigs H M O): Zest G S x O v.bp.threshold where
  zone:=zone (amount H M O) i
  up:= i.val.biUnion loves
  down:=cardGoal (amount H M O) i.val
  data:= glow (amount H M O) i.val
  weight:=stage (amount H M O) i.val
  key:= by
    intro _ hz; obtain ⟨j,hj,rfl⟩:= mem_image.mp hz; obtain ⟨u,hu,ht⟩:= mem_biUnion.mp hj
    exact mem_biUnion.mpr ⟨u,hu,(amount H M O u).store j ht⟩
  sent := goalZone ..
  contains := by
    rw [cost_bundled]; intro j hj; obtain ⟨k,hk,h⟩:=mem_biUnion.mp hj
    exact mem_biUnion.mpr ⟨k,hk,(amount H M O k).lends h⟩
  selects := has ..
  follows := observer ..

lemma contracts {M : Plate v x W} {O : Orchard S} {i : Sprigs H M O} (A k U y) : (sprouting H M O i).weight A k U y = (↑(∏ j∈i.val,atomP W v M j ⟨A,Streak.wood k,Streak.tag k,U,y⟩) : ℂ):= by push_cast; rfl

lemma at_view (M : Plate v x W) (O : Orchard S) (s : Finset (Rung S x)) (r : Finset (Fleck S⊕Glade c)) :
    enlist (amount H M O) (s.disjSum r) ↔ (s:Set (Rung S x)).PairwiseDisjoint fun i=> acre (rips i) := by
  constructor
  · intro h
    exact fun i hi j hj hij => h.1.1 (inl_mem_disjSum.mpr hi) (inl_mem_disjSum.mpr hj) (mt Sum.inl.inj hij)
  refine fun h=>⟨⟨?_,fun i _ j _ _=> disjoint_empty_left _,rfl⟩,fun i _ j _ _=> disjoint_empty_left _⟩
  rintro (i|i) hi (j|j) hj hij <;> first | exact disjoint_empty_left _| exact disjoint_empty_right _ | exact h (inl_mem_disjSum.mp hi) (inl_mem_disjSum.mp hj) (fun h=>hij (h ▸ rfl))
lemma membership (M : Plate v x W) (O : Orchard S) (hp : v.bp.threshold=temp x)
    (u : Support f) (p : Pilot G S x) (hz : Matched p) (s : Finset (Rung S x)) (r : Finset (Fleck S⊕Glade c)) :
    let V:=amount H M O; let a:=s.disjSum r
    (enlist V a ∧ cardGoal V a=flags v.bp.threshold p.view ∧ p.key=stapled x (glow V a) p.view ∧ a.biUnion loves=u) ↔
       ((s:Set (Rung S x)).PairwiseDisjoint (fun i=> acre (rips i)) ∧ s.image rips=owners p.key x ∧ s.biUnion markT=u):= by
  intro V a
  have hv : cardGoal V a=s.biUnion fun i=>(rips i).val.flags:=by ext; simp [V,a,cardGoal,amount,bread,rips, Sum.exists]
  have hh : glow V a=(s.biUnion (fun i=> (rips i).val.costs),s.biUnion (fun i=>(rips i).val.aisles)):= by
    unfold glow a; rw [sup_disjSum]; dsimp only [V,amount,bread,Sum.elim_inl,Sum.elim_inr]
    have ht : ((store S ∅).costs,(store S ∅).aisles)= (⊥ : vouchers S):=by ext i <;> simp [store]
    rw [ht]; rw [show (r.sup fun _=> (⊥ : vouchers S))=⊥ from by simp,sup_bot_eq]; clear hv a
    induction s using Finset.induction_on with
    | empty => simp; rfl
    | insert i s hi ih => simp_rw [biUnion_insert,sup_insert, ih]; rfl
  have hl : a.biUnion loves=s.biUnion markT:= by ext; simp [loves,a, Sum.exists]
  rw [at_view,hv,hh,hl,hp]; let f:= s.image rips
  apply and_congr_right_iff.mpr; intro h
  have he : (f:Set (Core S x)).PairwiseDisjoint acre := by intro i hi j hj hij; obtain ⟨i,h1,rfl⟩:=mem_image.mp hi; obtain ⟨j,h2,rfl⟩:=mem_image.mp hj; exact h h1 h2 (fun h=>hij (congr_arg rips h))
  rw [owner_eq, and_iff_right he]; let Q:=p.key
  rw [← and_assoc]; apply and_congr _ Iff.rfl
  have hF : RG.flags (temp x) p.view=Q.flags:= (show p.key.flags=RG.flags _ _ from hz).symm
  have hs : (f.biUnion fun o=> seeds S o.val)=(s.biUnion (fun i=> (rips i).val.costs)).disjSum ((s.biUnion (fun i=> (rips i).val.aisles)).disjSum (s.biUnion (fun i=> (rips i).val.flags))) := by
    ext i; rcases i with i|i|i <;> simp only [f,Finset.mem_biUnion, Finset.exists_mem_image,seeds, inl_mem_disjSum,inr_mem_disjSum]
  refine ⟨?_,?_⟩
  · rintro ⟨hg,hh⟩
    rw [hs, hg,hF,show (s.biUnion _) = p.key.costs from (congr_arg Stores.costs hh).symm,show (s.biUnion _) = p.key.aisles from (congr_arg Stores.aisles hh).symm]
    rfl
  rw [hs]; intro ht
  have hk := congr_arg (Packets.store S) ht
  rw [stapled]
  rw [Packets.store_seeds S] at hk
  simp only [Packets.store,Finset.toRight_disjSum,Finset.toLeft_disjSum] at hk
  rw [hF]; exact ⟨congr_arg Stores.flags hk,hk.symm.trans (by rw [show p.key.flags=_ from (congr_arg Stores.flags hk).symm])⟩
end Vale
end YM.PhysicalNext.InteractingRank.Pump
