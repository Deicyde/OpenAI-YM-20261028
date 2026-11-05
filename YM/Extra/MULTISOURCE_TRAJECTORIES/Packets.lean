import Mathlib.RingTheory.Nilpotent.Exp
import YM.Next.EXTRACTION.Tails
import YM.Work.B04
import YM.Work.B18
/-!
# Exact compaction of countably many alternative packet entries

If two history packets are assigned the same (nonempty support) address they
cannot occur together. After proving absolute convergence one can either test
whole selections of histories, or sum the histories assigned to each address
first and then take the usual gas over addresses.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Trajectories
open Finset Marker Filter Function RG
open scoped BigOperators Topology Classical

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
variable {V : Type*} [DecidableEq V] {R : Census V}

namespace Packets

variable (slot : ι → κ) (adm : Finset κ → Prop) (F : ι → Poly R)

def selected (s : Finset ι) := adm (s.image slot) ∧ (s : Set ι).InjOn slot

def value (s : Finset ι) : Poly R := if selected slot adm s then ∏ i∈s,F i else 0

omit [DecidableEq ι] in
lemma summable_value {w : V → ℝ} (hw : ∀ i, 0 < w i) (hf : Summable (fun i => Poly.price w (F i))) :
    Summable (value slot adm F) := by
  let b (s : Finset ι) := ∏ i∈s,Poly.price w (F i)
  have hs : Summable b := summable_finsetProd_of_summable_nonneg (fun i => Poly.nonnegative hw _) hf
  refine (Poly.budgeted hw hs fun s => ?_).1
  dsimp only [value]; split
  · exact Poly.multiple hw _ _
  · simp only [Poly.zero_price]; exact prod_nonneg fun i _ => Poly.nonnegative hw _

private abbrev Fiber (b : κ) := {x // slot x = b}
private abbrev Row (s : Finset κ) := (b : s) → Fiber slot b.val
private abbrev Target (s : Finset κ) := {t : Finset ι // t.image slot = s}

private def flatten {s : Finset κ} (p : Row slot s) : Target slot s :=
  ⟨univ.image (fun i : s => (p i).val), by ext i; simp [(p _).property]⟩

private lemma inj {s : Finset κ} : Injective (@flatten ι κ _ _ slot s) := by
  intro p q he
  funext i
  have hm : (p i).val ∈ (flatten slot p).val := mem_image_of_mem _ (mem_univ i)
  rw [he] at hm
  obtain ⟨j,-,hj⟩ := mem_image.mp hm
  have hh : j = i := Subtype.ext ((q j).property.symm.trans ((congrArg slot hj).trans (p i).property))
  exact Subtype.ext (hh ▸ hj.symm)

omit [DecidableEq ι] [DecidableEq κ] in
private lemma row_inj {s : Finset κ} (p : Row slot s) : Injective (fun i : s => (p i).val) := by
  intro i j he; exact Subtype.ext ((p i).property.symm.trans ((congrArg slot he).trans (p j).property))

private lemma matching {s : Finset κ} (hs : adm s) (p : Row slot s) :
    value slot adm F (flatten slot p).val = ∏ i,(F (p i).val) := by
  rw [value,if_pos (show selected slot adm (flatten slot p).val from ?_)]
  · exact prod_image (row_inj slot p).injOn
  refine ⟨(flatten slot p).property.symm ▸ hs,?_⟩
  intro x hx y hy he
  obtain ⟨i,-,rfl⟩ := mem_image.mp hx
  obtain ⟨j,-,rfl⟩ := mem_image.mp hy
  have hh : i = j := Subtype.ext ((p i).property.symm.trans (he.trans (p j).property))
  subst j; rfl

private lemma in_range {s : Finset κ} (z : Target slot s)
    (hz : value slot adm F z.val ≠ 0) : z ∈ Set.range (flatten slot) := by
  have hs : (z.val : Set ι).InjOn slot := by
    unfold value at hz; split at hz
    next he => exact he.2
    contradiction
  have pick (i : s) : ∃ x∈z.val,slot x=i.val := mem_image.mp (z.property.symm ▸ i.property)
  choose x hx h using pick
  let p (i : s) : Fiber slot i.val := ⟨x i,h i⟩
  refine ⟨p,Subtype.ext (Finset.ext fun b => ?_)⟩
  constructor
  · intro he; obtain ⟨i,-,rfl⟩ := mem_image.mp he; exact hx i
  intro he
  let i : s := ⟨slot b,z.property ▸ mem_image_of_mem slot he⟩
  exact mem_image.mpr ⟨i,mem_univ i,hs (hx i) he (h i)⟩

private lemma product {s : Finset κ} (ha : adm s) (hs : Summable (value slot adm F)) (hf : Summable F) :
    ∑' p : Row slot s, value slot adm F (flatten slot p).val =
      ∏ i∈s,∑' x : Fiber slot i,F x.val := by
  let f (i : κ) := ∑' x : Fiber slot i,F x.val
  let q := fun p : Row slot s => value slot adm F (flatten slot p).val
  have hq : Summable q := hs.comp_injective (Subtype.val_injective.comp (inj slot))
  let X (D : Finset ι) (i : s) : Finset (Fiber slot i.val) := D.subtype (fun x => slot x=i.val)
  have he (i : s) : Tendsto (fun D => X D i) atTop atTop := by
    refine tendsto_atTop_finset_of_monotone (fun A B h z hz => mem_subtype.mpr (h (mem_subtype.mp hz))) ?_
    exact fun z => ⟨{z.val},mem_subtype.mpr (mem_singleton_self _)⟩
  have ht (i : s) : Tendsto (fun D => ∑ x∈X D i,F x.val) atTop (𝓝 (f i.val)) :=
    (hf.comp_injective (i:=fun x : Fiber slot i.val => x.val) Subtype.val_injective).hasSum.comp (he i)
  have hh : Tendsto (fun D => ∏ i : s,∑ x∈X D i,F x.val) atTop (𝓝 (∏ i : s, f i.val)) :=
    tendsto_finsetProd _ (fun i _ => ht i)
  have hp : Tendsto (fun D => Fintype.piFinset (X D)) atTop atTop := by
    refine tendsto_atTop_finset_of_monotone (fun A B h z hz => Fintype.mem_piFinset.mpr fun i => ?_) ?_
    · exact mem_subtype.mpr (h (mem_subtype.mp (Fintype.mem_piFinset.mp hz i)))
    intro p; exact ⟨(flatten slot p).val, Fintype.mem_piFinset.mpr fun i => mem_subtype.mpr (mem_image_of_mem _ (mem_univ i))⟩
  have hv : Tendsto (fun D => ∑ p∈Fintype.piFinset (X D), q p) atTop (𝓝 (∑' p,q p)) :=
    hq.hasSum.comp hp
  simp_rw [prod_univ_sum] at hh
  dsimp only [q] at hv
  simp_rw [matching slot adm F ha] at hv
  change ∑' p,q p=∏ i∈s,f i
  simp_rw [q, matching slot adm F ha]
  exact (tendsto_nhds_unique hv hh).trans (prod_subtype s (fun _ => Iff.rfl) f).symm

theorem repack (hs : Summable (value slot adm F)) (hf : Summable F) :
    HasSum (fun s => if adm s then ∏ i∈s,∑' x : {x // slot x=i}, F x.val else 0)
      (∑' z,value slot adm F z) := by
  convert hs.hasSum.tsum_fiberwise (fun z => z.image slot) using 1
  · rfl
  ext1 s
  change (if adm s then _ else _) = ∑' x : Target slot s,value slot adm F x.val
  split
  next h =>
    exact (product slot adm F h hs hf).symm.trans ((inj slot).tsum_eq (fun z hz => in_range slot adm F z hz))
  next h => simp [value, selected, fun (x : Target slot s) => x.property, h]
end Packets
end YM.Extra.Trajectories
