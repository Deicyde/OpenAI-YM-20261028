import YM.Next.SCHEDULE.Dues
import YM.Progress.DIRECTED_RECIPE.Pellets
import YM.Work.H03

/-!
# Maps when remembering species covariance

It is not enough, when implementing a step, to check that counts of
readdressed terms match. Use a known movement of input E/K/log tensors.
Here we show how to pay the SAME permutation throughout a curve if the raw
geometry has that property. Our `Packed` will already give **pointwise**
use, which needs no such additional hypothesis. Recovery respects even the
named unused slots. Lifts the primitives (as in Work.H03) to a uniform and
*commuting with the receipt embeddings* Moves. No assertion every pair of
permutations transport correctly when attached in different views.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Progress.DirectedRecipe
open Function Set RG Wilson Lattice RG.Shoot Ovens Ovens.Pipes MeasureTheory
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G : Gauge} {n : Side}

structure Layout (X : Pipes G n) (s : Signed) (b : Site n) where
  reg : Equiv.Perm ℕ
  hard : Equiv.Perm ℕ
  soft : Equiv.Perm ℕ
  aligns i : regMap (destination s b) (X.reg i)=X.reg (reg i)
  kernels i : hardMap (destination s b) (readFoot (X.kernel i))=readFoot (X.kernel (hard i))
  extra i U : (X.kernel (hard i)).extraTest U ↔ (X.kernel i).extraTest (pull s b U)
  others i : (X.softer i).image (affine s b) = X.softer (soft i)

namespace Layout
open Rack
variable {X : Pipes G n} {s : Signed} {b : Site n}

structure Follows (L : Layout X s b) (d : Tap G n) : Prop where
  E i U : d.regular (L.reg i) U=d.regular i (pull s b U)
  K i U : d.forced (L.hard i) U=d.forced i (pull s b U)
  logs i U : d.logarithm (L.soft i) U=d.logarithm i (pull s b U)

lemma from_raw {d : Tap G n} (M : (X.pours d).Moves s b) {p : Equiv.Perm ℕ}
    (h : ∀ i, X.softer (p i) = (X.softer i).image (affine s b)) (ht : ∀ U i,d.logarithm (p i) U=
      d.logarithm i (pull s b U)) :
    ∃ L : Layout X s b, L.reg=M.ep ∧ L.hard=M.kp ∧ L.soft=p ∧ L.Follows d :=
  ⟨⟨M.ep,M.kp,p,fun _ => reg_ext (M.reg_site _).symm (M.reg_support _).symm,
    fun _ => foot_ext (M.forced_support _).symm (M.forced_inventory _).symm, M.forced_tests,
    fun i => (h i).symm⟩,rfl,rfl,rfl,⟨M.valuesE,M.valuesK,fun i U => ht U i⟩⟩

variable (L : Layout X s b)

def inflate : Layout (drawer G n) s b where
  reg := rearrange (regularKeys n) (regMap (destination s b)) L.reg
  hard := rearrange (hardKeys n) (hardMap (destination s b)) L.hard
  soft := rearrange (softKeys n) (softMap (destination s b)) L.soft
  aligns _ := (congr_arg Prod.fst (stocked ..)).symm
  kernels i := (congr_arg Prod.fst (stocked (hardKeys n) (hardMap (destination s b)) L.hard i)).symm
  extra _ _ := Iff.rfl
  others i := (congr_arg Subtype.val (congr_arg Prod.fst (stocked (softKeys n) (softMap (destination s b)) L.soft i))).symm

lemma usesReg i : L.inflate.reg (upE X i) = upE X (L.reg i) := move_stock _ _ _ _ L.aligns _
lemma usesHard i : L.inflate.hard (upK X i) = upK X (L.hard i) :=
  move_stock _ _ _ (fun i => readFoot (X.kernel i)) L.kernels _
lemma usesSoft i : L.inflate.soft (upS X i) = upS X (L.soft i) :=
  move_stock (softKeys n) (softMap (destination s b)) L.soft (fun i => ⟨X.softer i, X.sites i⟩)
    (fun i => Subtype.ext (show (X.softer i).image _ = X.softer (L.soft i) from L.others i)) _

lemma inflates (d : Tap G n) (h : L.Follows d) : L.inflate.Follows (widen X d) := by
  constructor
  · intro i U; by_cases hi : i∈range (upE X)
    · obtain ⟨i,rfl⟩ := hi; simp only [usesReg,widen,stuffed,h.E]
    simp [widen,blank _ _ hi,blank _ _ (unused L.usesReg hi)]
  · intro i U; by_cases hi : i∈range (upK X)
    · obtain ⟨i,rfl⟩ := hi; simp only [usesHard,widen,stuffed,h.K]
    simp [widen,blank _ _ hi,blank _ _ (unused L.usesHard hi)]
  intro i U; by_cases hi : i∈range (upS X)
  · obtain ⟨i,rfl⟩ := hi; simp only [usesSoft,widen,stuffed,h.logs]
  simp [widen,blank _ _ hi,blank _ _ (unused L.usesSoft hi)]

def atoms : Equiv.Perm Label := Equiv.sumCongr L.hard L.soft

lemma footprint (i : Label) : X.patch (L.atoms i) = (X.patch i).image (affine s b) := by
  cases i with
  | inl i => exact (congr_arg Foot.support (L.kernels i)).symm
  | inr i => exact (L.others i).symm

lemma old_hard (i : ℕ) : (X.kernel (L.hard i)).support = (X.kernel i).support.image (affine s b) := L.footprint (.inl i)
lemma old_inv (i : ℕ) : (X.kernel (L.hard i)).inventory = (X.kernel i).inventory.image (affine s b) :=
  (congr_arg Foot.inventory (L.kernels i)).symm
lemma located (A : Finset Label) : lefts (A.map L.atoms.toEmbedding) = (lefts A).map L.hard.toEmbedding := by
  ext x; simp [lefts, Layout.atoms]

lemma preserves (A : Finset Label) : X.contains A ↔ X.contains (A.map L.atoms.toEmbedding) := by
  let e := destination s b
  let p := L.atoms
  let A' := A.map p.toEmbedding
  have hb : ∀ i j, Ac.bonds X.patch A' (p i) (p j) ↔ Ac.bonds X.patch A i j := by
    intro i j
    simp only [Ac.bonds,A', Finset.mem_map_equiv,Equiv.symm_apply_apply,p, Ac.meets, L.footprint]
    constructor
    · rintro ⟨hi,hj,x,hx,hy⟩
      obtain ⟨y,hU,heu⟩ := Finset.mem_image.mp hx; obtain ⟨z,hV,hev⟩ := Finset.mem_image.mp hy
      have HH : y=z := e.injective (heu.trans hev.symm)
      exact ⟨hi,hj,y,hU,HH.symm ▸ hV⟩
    rintro ⟨hi,hj,x,hx,hy⟩
    exact ⟨hi,hj,affine s b x, Finset.mem_image_of_mem _ hx, Finset.mem_image_of_mem _ hy⟩
  have hx : ∀ i j,Ac.chain X.patch A i j ↔ Ac.chain X.patch A' (p i) (p j) := by
    intro i j
    constructor <;> intro h
    · exact Relation.ReflTransGen.lift p (fun a b H => (hb a b).2 H) i j h
    have he : Ac.bonds X.patch A' ≤ onFun (Ac.bonds X.patch A) p.symm := by
      intro a b ha; obtain ⟨a,rfl⟩ := p.surjective a; obtain ⟨b,rfl⟩ := p.surjective b
      simp only [onFun,Equiv.symm_apply_apply]; exact (hb ..).1 ha
    have ht := Relation.ReflTransGen.lift p.symm he _ _ h
    simpa [onFun,Ac.chain] using ht
  have hQ : Ac.Spark X.patch A ↔ Ac.Spark X.patch A' := by
    constructor <;> rintro ⟨hv,h⟩
    · refine ⟨hv.map,fun i hi j hj => ?_⟩
      obtain ⟨i,hia,rfl⟩ := Finset.mem_map.mp hi
      obtain ⟨j,hja,rfl⟩ := Finset.mem_map.mp hj
      exact (hx ..).mp (h i hia j hja)
    exact ⟨Finset.map_nonempty.mp hv,fun i hi j hj => (hx ..).mpr
      (h (p i) (Finset.mem_map.mpr ⟨i,hi,rfl⟩) (p j) (Finset.mem_map.mpr ⟨j,hj,rfl⟩))⟩
  have ht i j : Disjoint (X.kernel (L.hard i)).support (X.kernel (L.hard j)).support ↔
      Disjoint (X.kernel i).support (X.kernel j).support := by
    rw [L.old_hard,L.old_hard]; exact Finset.disjoint_image e.injective
  unfold Pipes.contains
  rw [L.located,Finset.map_nonempty,hQ,paired L.hard.toEmbedding ht]

lemma biImage {ι : Type*} (f : ι → Support n) (g : Equiv.Perm ι) (p : Equiv.Perm (Site n))
    (hf : ∀ i, f (g i) = (f i).image p) (A : Finset ι) :
    (A.map g.toEmbedding).biUnion f = (A.biUnion f).image p := by
  rw [mapped_biUnion _ hf]; ext i; simp
  constructor
  · rintro ⟨a,H,b,h,rfl⟩; exact ⟨b,⟨a,H,h⟩,rfl⟩
  rintro ⟨b,⟨a,h,H⟩,rfl⟩; exact ⟨a,h,b,H,rfl⟩

def slide : Equiv.Perm X.Pellet := Equiv.subtypeEquiv L.atoms.finsetCongr (L.preserves)

def walk (F : ℕ≃ X.Pellet) : Equiv.Perm ℕ := (F.trans L.slide).trans F.symm

lemma ready (F : ℕ≃ X.Pellet) (i) : (F (L.walk F i)).val = (F i).val.map L.atoms.toEmbedding := by
  unfold walk; rw [Equiv.trans_apply,Equiv.trans_apply, Equiv.apply_symm_apply]; rfl

/-- For each payable Layout the *same* walk works for any d with that
layout. Strengthens the "some permutation" in use at startup. -/
def motion (F : ℕ≃ X.Pellet) (P : BudgetPoint) {d : Tap G n} (h : L.Follows d) :
    (fused F P d).Moves s b := by
  have hs i : (addr F P (L.walk F i)).support = (addr F P i).support.image (affine s b) := by
    dsimp only [addr,skin]; rw [L.ready]
    exact biImage _ _ (destination s b) L.footprint _
  have hi i : (addr F P (L.walk F i)).inventory = (addr F P i).inventory.image (affine s b) := by
    dsimp only [addr,plot]; rw [L.ready,L.located]
    exact biImage _ _ (destination s b) L.old_inv _
  have hT i U : (addr F P (L.walk F i)).extraTest U ↔ (addr F P i).extraTest (pull s b U) := by
    simp only [addr,condition,L.ready,L.located,Finset.forall_mem_map, Equiv.coe_toEmbedding]
    exact forall₂_congr fun j _ => Work.H03.eligible_send s b P.threshold U _ _ (L.old_hard j) (L.old_inv j) (L.extra j U)
  have hv i U : reach d (L.atoms i) U = reach d i (pull s b U) := by
    cases i
    · exact h.K ..
    · simp only [reach,atoms,Equiv.sumCongr_apply, Sum.map_inr,Sum.elim_inr,h.logs]
  refine ⟨L.reg,L.walk F,fun i => (congr_arg RegularAddress.site (L.aligns i)).symm,
    fun i => (congr_arg RegularAddress.support (L.aligns i)).symm,hs,hi,hT,h.E,?_⟩
  intro i U
  have he := Work.H03.eligible_send s b P.threshold U _ _ (hs i) (hi i) (hT i U)
  simp only [fused,solid,he,L.ready,Finset.prod_map, Equiv.coe_toEmbedding, hv]




end Layout


end YM.Progress.DirectedRecipe
