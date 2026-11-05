import YM.Extra.MULTISOURCE_TRAJECTORIES.Algebra
import YM.Extra.MULTISOURCE_TRAJECTORIES.Packets
import YM.PREC.Derivative
import YM.Work.F05.Measure

/-!
# Merging marked attaching factors into *this very vacuum*'s addresses

Finite marked alphabet, arbitrary countable Wilson vacuum alphabet. Keep
all overlaps including marked-marked, exact inventories, old K predicates
(already enforced by the K functions), and never count a collision of
markers as a power of a source. This is an absolute reindexing, not a
small-norm argument. Unit singleton
factors needn't enter the merger. A catalog of host addresses must actually
have been included in the retained vacuum labels (may be shared; one for
an entire support/inventory pair is enough).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Trajectories
open Lattice Wilson RG Overlay Marker Function Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V] {R : Census V} {P : Rep G n}

structure Room (n : Side) where
  wall : Support n
  bill : Support n
  needs : bill.Nonempty
  inside : bill ⊆ wall

def Aperture (P : Rep G n) := ∀ a : Room n, ∃ i, (P.activities.forced i).support = a.wall ∧
  (P.activities.forced i).inventory = a.bill ∧ ∀ U, (P.activities.forced i).extraTest U

/-- An unmasked decomposition of the source part of the dimensionless
logarithm (no log-vacuum term); `H` also used on the complement, NOT only
its germ. Ambient unmasked estimates will be a distinct producer need. -/
structure Layers (P : Rep G n) (R : Census V) (α : Type*) where
  origins : V → Site n
  units : V → ℂ
  region : α → Support n
  tag : α → R.Mode
  H : α → Config G n → ℂ

private local instance : IsTopologicalSemiring (Poly R) where

namespace Layers
variable {α : Type*} [DecidableEq α] (X : Layers P R α)

structure Anchored : Prop where
  proper i : (X.tag i).val.Nonempty
  home i j : j∈(X.tag i).val → X.origins j∈X.region i

structure Ready : Prop extends Anchored X where
  regular i : P.p.Regular (X.region i) (X.H i)

def residual (i : α) (U : Config G n) := if Healthy P.p.threshold (X.region i) U then 0 else X.H i U

abbrev Letter (α : Type*) := ℕ ⊕ α

def area (l : Letter α) : Support n := l.elim (fun i => (P.activities.forced i).support) X.region

def skin (s : Finset (Letter α)) : Support n := s.biUnion X.area

def plot (s : Finset (Letter α)) : Support n := s.toLeft.biUnion fun i => (P.activities.forced i).inventory


def weight (U : Config G n) (l : Letter α) : ℂ := l.elim (fun i => (P.activities.K i U:ℂ)) (fun i => X.residual i U)

def reach (U : Config G n) (l : Letter α) : Poly R := Poly.send (l.elim (fun _ => R.quiet) X.tag) (X.weight U l)

def start (U : Config G n) (s : Finset (Letter α)) : Poly R :=
  if P.activities.admissible P.p U s.toLeft then ∏ l∈s, X.reach U l else 0

/-- A marked component (non-activated ones may of course have zero coefficient).
Internal disjointness refers to the old forced supports. Eligibility on the union
is reimposed on assembly. Distinct family members with same tags cannot merge.
-/
structure Solid (s : Finset (Letter α)) : Prop where
  old : s.toLeft.Nonempty
  mark : s.toRight.Nonempty
  join : Ac.Spark X.area s
  sep : (s.toLeft : Set ℕ).PairwiseDisjoint fun i => (P.activities.forced i).support
  fits : Fits X.tag s.toRight

abbrev Component := {s : Finset (Letter α) // X.Solid s}
abbrev Choice := ℕ ⊕ X.Component

def pieces (a : X.Choice) : Finset (Letter α) := a.elim (fun i => {Sum.inl i}) (fun c => c.val)

omit [DecidableEq α] in
lemma plot_le (s : Finset (Letter α)) : plot (P:=P) s ⊆ X.skin s := by
  intro x hx
  obtain ⟨i,hi,hx⟩ := mem_biUnion.mp hx
  exact mem_biUnion.mpr ⟨.inl i,mem_toLeft.mp hi,(P.activities.forced i).inventory_sup hx⟩

omit [DecidableEq α] in
lemma area_nonempty (h : X.Anchored) (l : Letter α) : (X.area l).Nonempty := by
  cases l with
  | inl i => exact (P.activities.forced i).inventory_ne.mono (P.activities.forced i).inventory_sup
  | inr i => obtain ⟨s,hs⟩ := h.proper i; exact ⟨_,h.home i s hs⟩

def room (c : X.Component) : Room n where
  wall := X.skin c.val
  bill := plot (P:=P) c.val
  inside := X.plot_le c.val
  needs := by
    obtain ⟨i,hi⟩ := c.property.old
    obtain ⟨x,hx⟩ := (P.activities.forced i).inventory_ne
    exact ⟨x,mem_biUnion.mpr ⟨i,hi,hx⟩⟩

def slot (a : X.Choice) : ℕ := a.elim id (fun c => if h : Aperture P then (h (X.room c)).choose else 0)

omit [DecidableEq α] in
@[simp] lemma slot_old (i : ℕ) : X.slot (.inl i) = i := rfl

omit [DecidableEq α] in
@[simp] lemma skin_slot (a : X.Choice) (h : Aperture P) :
    X.skin (X.pieces a) = (P.activities.forced (X.slot a)).support := by
  cases a with
  | inl i => simp [skin,pieces,area]
  | inr c => exact (h (X.room c)).choose_spec.1.symm.trans (by rw [slot, Sum.elim_inr,dif_pos h])

omit [DecidableEq α] in
private lemma toLeft_single (i : ℕ) : toLeft ({Sum.inl i} : Finset (Letter α)) = {i} := by ext; simp

omit [DecidableEq α] in
@[simp] lemma plot_slot (a : X.Choice) (h : Aperture P) :
    plot (P:=P) (X.pieces a) = (P.activities.forced (X.slot a)).inventory := by
  cases a with
  | inl i => simp [plot,pieces,toLeft_single]
  | inr c => exact (h (X.room c)).choose_spec.2.1.symm.trans (by rw [slot, Sum.elim_inr,dif_pos h])

omit [DecidableEq α] in
lemma slot_unrestricted (c : X.Component) (h : Aperture P) :
    ∀ U,(P.activities.forced (X.slot (.inr c))).extraTest U := by
  rw [slot,Sum.elim_inr,dif_pos h]; exact (h (X.room c)).choose_spec.2.2

omit [DecidableEq α] in
lemma pieces_injective : Injective X.pieces := by
  intro a b hab
  have hm (c : X.Component) (i : ℕ) : c.val ≠ {Sum.inl i} := by
    intro he; obtain ⟨j,hj⟩ := c.property.mark
    rw [mem_toRight, he] at hj
    simp at hj
  cases a with
  | inl i => cases b with
    | inl j => congr 1; exact Sum.inl.inj (singleton_inj.mp hab)
    | inr c => exact (hm c i hab.symm).elim
  | inr c => cases b with
    | inl j => exact (hm c j hab).elim
    | inr d => congr 1; exact Subtype.ext hab

omit [DecidableEq α] in
lemma spark (a : X.Choice) : Ac.Spark X.area (X.pieces a) := by
  cases a with
  | inr c => exact c.property.join
  | inl i =>
    refine ⟨singleton_nonempty _,?_⟩
    intro a ha b hb
    rw [mem_singleton.mp ha,mem_singleton.mp hb]; exact .refl

omit [DecidableEq α] in
lemma pieces_sep (a : X.Choice) : ((X.pieces a).toLeft : Set ℕ).PairwiseDisjoint fun i => (P.activities.forced i).support := by
  cases a with
  | inr c => exact c.property.sep
  | inl i => simp [pieces,toLeft_single]

def stamp (c : X.Component) := unionTag X.tag c.val.toRight c.property.fits

def entry (c : X.Component) (U : Config G n) : ℂ :=
  if (P.activities.forced (X.slot (.inr c))).eligible P.p.threshold U then ∏ l∈c.val,X.weight U l else 0

def cargo (U : Config G n) : X.Choice → Poly R :=
  Sum.elim (fun i => Poly.send R.quiet (P.activities.K i U : ℂ)) (fun c => Poly.send (X.stamp c) (X.entry c U))

def selection (U : Config G n) := Packets.selected X.slot (P.activities.admissible P.p U)

def gathered (U : Config G n) := Packets.value X.slot (P.activities.admissible P.p U) (X.cargo U)

private def flatten (s : Finset X.Choice) := s.biUnion X.pieces

private lemma plot_flatten (h : Aperture P) (s : Finset X.Choice) :
    plot (P:=P) (X.flatten s) = (s.image X.slot).biUnion (fun i => (P.activities.forced i).inventory) := by
  rw [image_biUnion]
  simp_rw [← X.plot_slot _ h]
  unfold plot flatten
  ext i; simp only [mem_biUnion,mem_toLeft]; tauto

omit [DecidableEq α] in
private lemma shells_sep (h : Aperture P) {s : Finset X.Choice} {U : Config G n} (hs : X.selection U s) :
    (s : Set X.Choice).PairwiseDisjoint (fun a => X.skin (X.pieces a)) := by
  intro i hi j hj hn
  simp only [onFun] at *
  rw [X.skin_slot _ h, X.skin_slot _ h]
  exact hs.1.1 (mem_image_of_mem _ hi) (mem_image_of_mem _ hj) (fun e => hn (hs.2 hi hj e))

private lemma flatten_admissible (h : Aperture P) {s : Finset X.Choice} {U : Config G n}
    (hs : X.selection U s) : P.activities.admissible P.p U (X.flatten s).toLeft := by
  constructor
  · intro i hi j hj hn
    obtain ⟨a,ha,hi⟩ := mem_biUnion.mp (mem_toLeft.mp hi)
    obtain ⟨b,hb,hj⟩ := mem_biUnion.mp (mem_toLeft.mp hj)
    by_cases he : a=b
    · subst b; exact X.pieces_sep a (mem_toLeft.mpr hi) (mem_toLeft.mpr hj) hn
    apply disjoint_left.mpr
    intro x hx hy
    exact disjoint_left.mp (X.shells_sep h hs ha hb he) (mem_biUnion.mpr ⟨Sum.inl i,hi,hx⟩) (mem_biUnion.mpr ⟨Sum.inl j,hj,hy⟩)
  exact (X.plot_flatten h s).trans hs.1.2

private lemma parts_flatten (h : Aperture P) {s : Finset X.Choice} {U : Config G n}
    (hs : X.selection U s) : Ac.Parts X.area (X.flatten s) = s.image X.pieces := by
  rw [show X.flatten s = (s.image X.pieces).biUnion id by rw [image_biUnion]; rfl]
  apply Ac.separates
  · intro a ha; obtain ⟨i,hi,rfl⟩ := mem_image.mp ha; exact X.spark i
  intro a ha b hb hn
  obtain ⟨i,hi,rfl⟩ := mem_image.mp ha; obtain ⟨j,hj,rfl⟩ := mem_image.mp hb
  exact X.shells_sep h hs hi hj (fun e => hn (congrArg X.pieces e))

omit [DecidableEq α] in
lemma reach_split (s : Finset (Letter α)) (U : Config G n) :
    ∏ i∈s,X.reach U i = Poly.send R.quiet (∏ i∈s.toLeft, (P.activities.K i U:ℂ)) *
      ∏ i∈s.toRight,Poly.send (X.tag i) (X.residual i U) := by
  rw [prod_sum_eq_prod_toLeft_mul_prod_toRight]
  congr 1
  exact (map_prod (Poly.bead R) _ _).symm

private lemma intersection {s : Finset ℕ} {U : Config G n} (h : P.activities.admissible P.p U s) {i : ℕ} (hi : i∈s) :
    (P.activities.forced i).support ∩ flags P.p.threshold U = (P.activities.forced i).inventory := by
  rw [← h.2]
  ext x; rw [mem_inter]; constructor
  · rintro ⟨hx,hx'⟩
    obtain ⟨j,hj,hx'⟩ := mem_biUnion.mp hx'
    by_contra he
    have hn : i≠j := fun e => he (e.symm ▸ hx')
    exact disjoint_left.mp (h.1 hi hj hn) hx ((P.activities.forced j).inventory_sup hx')
  intro hx; exact ⟨(P.activities.forced i).inventory_sup hx,mem_biUnion.mpr ⟨i,hi,hx⟩⟩

omit [DecidableEq α] in
private lemma prod_pieces (h : Aperture P) {s : Finset X.Choice} {U : Config G n}
    (hs : X.selection U s) {a : X.Choice} (ha : a∈s) : ∏ i∈X.pieces a,X.reach U i = X.cargo U a := by
  cases a with
  | inl i => rw [show X.pieces (.inl i) = {Sum.inl i} from rfl,prod_singleton]; rfl
  | inr c =>
    change ∏ i∈c.val,_ = Poly.send (X.stamp c) (X.entry c U)
    rw [reach_split, tagged_prod X.tag c.val.toRight c.property.fits,
      tagged_mul (z:=unionTag X.tag c.val.toRight c.property.fits) _ _ (Poly.vacuum .. |>.mpr rfl),entry,
      if_pos ⟨intersection hs.1 (mem_image_of_mem _ ha), X.slot_unrestricted c h U⟩,
      prod_sum_eq_prod_toLeft_mul_prod_toRight]
    rfl

private lemma flat_match (h : Aperture P) (hx : X.Anchored) {s : Finset X.Choice} {U : Config G n}
    (hs : X.selection U s) : X.start U (X.flatten s) = X.gathered U s := by
  have hf := X.flatten_admissible h hs
  unfold selection at hs
  rw [start, if_pos hf, gathered,Packets.value,if_pos hs,flatten,prod_biUnion ?_]
  · exact prod_congr rfl fun i hi => X.prod_pieces h hs hi
  intro a ha b hb hn
  apply disjoint_left.mpr
  intro i hi hj
  obtain ⟨x,hx⟩ := X.area_nonempty hx i
  exact disjoint_left.mp (X.shells_sep h hs ha hb hn) (mem_biUnion.mpr ⟨i,hi,hx⟩) (mem_biUnion.mpr ⟨i,hj,hx⟩)

/-- Every part of a surviving input monomial is one whole old isolated K or
contains both attaching terms and at least one old K. Uses exact global coverage. -/
private lemma recognize {s : Finset (Letter α)} {U : Config G n} (hs : X.start U s ≠ 0)
    {p : Finset (Letter α)} (hp : p∈Ac.Parts X.area s) : ∃ a : X.Choice, X.pieces a=p := by
  unfold start at hs
  split at hs
  swap; contradiction
  rename_i had
  obtain ⟨hle,hj⟩ := Ac.lives X.area s hp
  have hold : p.toLeft.Nonempty := by
    obtain ⟨l,hl⟩ := hj.1
    cases l with
    | inl i => exact ⟨i,mem_toLeft.mpr hl⟩
    | inr i =>
      have hr : ¬ Healthy P.p.threshold (X.region i) U := by
        intro he; exact hs (prod_eq_zero (hle hl) (by simp [reach,weight,residual,he]))
      obtain ⟨x,hx,hx'⟩ := not_disjoint_iff.mp hr
      rw [← had.2] at hx'; obtain ⟨k,hk,hx'⟩ := mem_biUnion.mp hx'
      have hc : Ac.chain X.area s (Sum.inr i) (.inl k) := .single
        ⟨hle hl,mem_toLeft.mp hk,x,hx,(P.activities.forced k).inventory_sup hx'⟩
      refine ⟨k,mem_toLeft.mpr ?_⟩
      rw [← Ac.contains X.area hp _ hl]; exact (Ac.bright ..).mpr ⟨mem_toLeft.mp hk,hc⟩
  by_cases hm : p.toRight.Nonempty
  · rw [X.reach_split] at hs
    have he := fits_of_tagged_prod X.tag (right_ne_zero_of_mul hs)
    exact ⟨.inr ⟨p,hold,hm,hj,(fun i hi j hj => had.1 (toLeft_subset_toLeft hle hi) (toLeft_subset_toLeft hle hj)),
      he.subset X.tag (toRight_subset_toRight hle)⟩,rfl⟩
  obtain ⟨i,hi⟩ := hold
  have hl : ∀ l∈p,∃ k∈s.toLeft,l=Sum.inl k := by
    intro l he; cases l with
    | inl k => exact ⟨k,mem_toLeft.mpr (hle he),rfl⟩
    | inr k => exact (hm ⟨k,mem_toRight.mpr he⟩).elim
  refine ⟨.inl i,eq_comm.mp (eq_singleton_iff_unique_mem.mpr ⟨mem_toLeft.mp hi,fun l hmem => ?_⟩)⟩
  have hc := hj.2 _ (mem_toLeft.mp hi) _ hmem
  clear hmem
  induction hc with
  | refl => rfl
  | tail _ hh IH =>
    obtain ⟨k,hk,rfl⟩ := hl _ hh.2.1
    congr 1
    by_contra hn
    obtain ⟨-, -, x,hx,hx'⟩ := hh
    exact disjoint_left.mp (had.1 hk (toLeft_subset_toLeft hle hi) hn) hx' (show x∈X.area (Sum.inl i) from IH ▸ hx)

private lemma unflatten (h : Aperture P) {s : Finset (Letter α)} {U : Config G n} (hs : X.start U s ≠ 0) :
    ∃ b, X.selection U b ∧ X.flatten b = s := by
  let parts := Ac.Parts X.area s
  let f := fun p : parts => (X.recognize hs p.property).choose
  let b := parts.attach.image f
  have he : b.image X.pieces = parts := by
    ext i
    constructor
    · intro hi; obtain ⟨a,ha,rfl⟩ := mem_image.mp hi; obtain ⟨p,-,rfl⟩ := mem_image.mp ha
      rw [(X.recognize hs p.property).choose_spec]; exact p.property
    intro hi
    exact mem_image.mpr ⟨_,mem_image_of_mem f (mem_attach parts ⟨i,hi⟩),(X.recognize hs hi).choose_spec⟩
  have ht : X.flatten b = s := by
    rw [show X.flatten b = (b.image X.pieces).biUnion id by rw [image_biUnion]; rfl,he]; exact Ac.reconstruct X.area s
  have hsep : (b : Set X.Choice).PairwiseDisjoint (fun a => (P.activities.forced (X.slot a)).support) := by
    intro i hi j hj hn; dsimp only [onFun]; rw [← X.skin_slot i h, ← X.skin_slot j h]
    have hparts (a) (ha : a ∈ b) : X.pieces a ∈ parts := he ▸ mem_image_of_mem X.pieces ha
    exact Ac.separate X.area s (hparts i hi) (hparts j hj) (X.pieces_injective.ne hn)
  refine ⟨b,⟨⟨?_, ?_⟩, ?_⟩,ht⟩
  · intro i hi j hj hn
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hi; obtain ⟨k,hk,rfl⟩ := mem_image.mp hj
    exact hsep ha hk (fun e => hn (congrArg X.slot e))
  · rw [← X.plot_flatten h,ht]; unfold start at hs; split at hs
    next ha => exact ha.2
    contradiction
  intro i hi j hj hij
  by_contra hn
  have hh := hsep hi hj hn
  dsimp only [onFun] at hh; rw [hij] at hh
  obtain ⟨z,hz⟩ := (P.activities.forced (X.slot j)).inventory_ne.mono (P.activities.forced (X.slot j)).inventory_sup
  exact disjoint_left.mp hh hz hz

private lemma hasSum_gathered_iff (h : Aperture P) (hx : X.Anchored) {U : Config G n} {z : Poly R} :
    HasSum (X.gathered U) z ↔ HasSum (X.start U) z := by
  have active (s : support (X.gathered U)) : X.selection U s.val := by
    by_contra hn
    exact s.property (if_neg hn)
  have he (s : support (X.gathered U)) := X.flat_match h hx (active s)
  let f : support (X.gathered U) → support (X.start U) := fun s => ⟨X.flatten s.val,
    show X.start U (X.flatten s.val) ≠ 0 from by rw [he s]; exact s.property⟩
  have hi : Injective f := by
    intro s t hst
    apply Subtype.ext; apply image_injective X.pieces_injective
    rw [← X.parts_flatten h (active s),← X.parts_flatten h (active t), show X.flatten s.val=X.flatten t.val from congrArg Subtype.val hst]
  have ht : Surjective f := by
    intro s; obtain ⟨b,hb,e⟩ := X.unflatten h s.property
    exact ⟨⟨b,show X.gathered U b ≠ 0 from by rw [← X.flat_match h hx hb,e]; exact s.property⟩,Subtype.ext e⟩
  exact (Equiv.ofBijective f ⟨hi,ht⟩).hasSum_iff_of_support he

omit [DecidableEq α] in
lemma cargo_series {δ κ : ℝ} [Fintype α] (H : P.activities.Valid P.p δ κ) (U : Config G n) :
    Summable (fun i => Poly.price (fun _ => 1) (X.cargo U i)) := by
  let w := fun _ : V => (1:ℝ)
  obtain ⟨q,hq,hK⟩ := Activities.K_total H.boundK
  refine Summable.sum _ (hq.of_nonneg_of_le (fun _ => Poly.nonnegative (w:=w) (by simp [w]) _) (fun i => ?_)) ?_
  · simpa only [comp_apply,cargo,Sum.elim_inl,Poly.solo,Poly.quiet_toll,one_mul,Complex.norm_real] using (hK i).2 U
  let z (l : Letter α) := l.elim q (fun i => ‖X.residual i U‖)
  have hz : Summable z := Summable.sum z hq Summable.of_finite
  have he (l : Letter α) : ‖X.weight U l‖ ≤ z l := by
    cases l with
    | inl i => simpa only [weight,z,Sum.elim_inl,Complex.norm_real] using (hK i).2 U
    | inr i => exact le_rfl
  have hs := (summable_finsetProd_of_summable_nonneg (fun i => (norm_nonneg _).trans (he i)) hz).comp_injective
    (Subtype.val_injective (p:=X.Solid))
  refine hs.of_nonneg_of_le (fun _ => Poly.nonnegative (w:=w) (by simp [w]) _) (fun c => ?_)
  dsimp only [comp_apply,cargo,Sum.elim_inr,entry]
  split
  · simpa only [Poly.solo,Poly.toll,prod_const_one,one_mul,norm_prod] using
      (prod_le_prod (s:=c.val) (fun _ _ => norm_nonneg _) (fun i _ => he i))
  · simp only [Poly.send_zero,Poly.zero_price]; exact prod_nonneg fun i _ => (norm_nonneg _).trans (he i)

omit [DecidableEq α] in
private lemma split (U : Config G n) (s : Finset (Letter α)) : X.start U s =
    Poly.send R.quiet (P.activities.gasOccurrence P.p s.toLeft U) *
      ∏ i∈s.toRight,Poly.send (X.tag i) (X.residual i U) := by
  unfold start Activities.gasOccurrence
  split_ifs with hs
  · rw [reach_split,Complex.ofReal_prod]
  rw [Complex.ofReal_zero,Poly.send_zero,zero_mul]

omit [DecidableEq α] in
private lemma gas_series {δ κ : ℝ} (H : P.activities.Valid P.p δ κ) (U : Config G n) :
    HasSum (fun i => Poly.send R.quiet (P.activities.gasOccurrence P.p i U))
      (Poly.send R.quiet (P.activities.gas P.p U)) :=
    (Complex.hasSum_ofReal.mpr ((Activities.gasSeries H).summable U).hasSum).map (Poly.bead R) (Overlay.Bands.sends R.quiet)

private def attachments [Fintype α] (U : Config G n) := ∑ s : Finset α,∏ i∈s, Poly.send (X.tag i) (X.residual i U)

omit [DecidableEq α] in
private lemma extract [Fintype α] {U : Config G n} {v : Poly R} (hs : HasSum (X.start U) v) :
    HasSum (fun b => (Poly.send R.quiet (P.activities.gasOccurrence P.p b U)) * X.attachments U) v := by
  let e := (@Finset.sumEquiv ℕ α).toEquiv
  have hf := e.symm.hasSum_iff.mpr hs
  have he (b : Finset ℕ × Finset α) := X.split U (e.symm b)
  simp_rw [show ∀ b : Finset ℕ × Finset α, (e.symm b).toLeft = b.1 from fun b => congrArg Prod.fst (e.apply_symm_apply b),
      show ∀ b : Finset ℕ × Finset α, (e.symm b).toRight = b.2 from fun b => congrArg Prod.snd (e.apply_symm_apply b)] at he
  simp_rw [comp_def,he] at hf
  exact hf.prod_fiberwise (fun b => (hasSum_fintype (fun s : Finset α => ∏ i∈s, Poly.send (X.tag i) (X.residual i U))).mul_left
    (Poly.send R.quiet (P.activities.gasOccurrence P.p b U)))

theorem merged [Fintype α] (h : Aperture P) (hx : X.Anchored) {δ κ : ℝ} (H : P.activities.Valid P.p δ κ) (U : Config G n) :
    HasSum (X.gathered U) (Poly.send R.quiet (P.activities.gas P.p U) *
      ∏ i,(1+Poly.send (X.tag i) (X.residual i U))) := by
  have hw (_ : V) : (0:ℝ)<1 := zero_lt_one
  have hc := X.cargo_series H U
  have hh := Packets.summable_value X.slot (P.activities.admissible P.p U) _ hw hc
  change Summable (X.gathered U) at hh
  have hs := X.extract ((X.hasSum_gathered_iff h hx).1 hh.hasSum)
  have he := ((gas_series (R:=R) H U).mul_right (X.attachments U)).unique hs
  rw [prod_one_add,powerset_univ, ← attachments, he]; exact hh.hasSum
end Layers
end YM.Extra.Trajectories
