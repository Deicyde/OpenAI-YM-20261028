import YM.AnalyticNext.GRID_STOP_ATTENUATION.Alphabet.Supports
import YM.Bid.Drops

set_option warningAsError false

/-! # Exact tangent kernel elements

Tested here on `Multi.tangent`, the actual covered gas convention under
use. Even when using just this convention it is invalid to deduce actual
entries from a signed singleton density equality.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.GridStop.Alphabet
open Function Filter MeasureTheory RG Wilson Lattice Marker Overlay Source Bid Labels Multi Multi.Pack
open Finset
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {n : Side} {G : Gauge}

section many
variable {α : Type*} [CommSemiring α]
variable (D : Support n) (F W : Pack n → α)

lemma guests : (∑ b∈Pack.clears D,∑ i∈b,W i * ∏ v∈b.erase i,F v) = ∑ i,W i * diamond D F i := by
  let L := Pack.clears D
  let f (b : Finset (Pack n)) i := if i∈b then W i*shells F (b.erase i) else 0
  have he b : (∑ i∈b,W i*∏ v∈b.erase i,F v)=∑ i,f b i := by
    let S : Finset (Pack n) := univ.filter (fun i => i∈b)
    have hS : S=b := by simp [S]
    conv_lhs => arg 1; rw [← hS]
    unfold S; rw [Finset.sum_filter]; exact Finset.sum_congr rfl fun i _ => by unfold f shells; split <;> rfl
  simp_rw [he]; rw [sum_comm]; apply sum_congr rfl; intro i _
  unfold diamond f; rw [mul_sum]
  rw [show (∑ x∈clears D,if i∈x then W i*shells F (x.erase i) else 0)=∑ x ∈ (clears D).filter (fun x => i∈x),W i*shells F (x.erase i) by
    rw [Finset.sum_filter]; exact Finset.sum_congr rfl fun j _ => by split <;> rfl]
  have hh (b : Finset (Pack n)) : W i * (if listed D i b then shells F b else 0) = if listed D i b then W i * shells F b else 0 := mul_ite .. |>.trans (by rw [mul_zero])
  simp_rw [hh]; rw [← Finset.sum_filter]
  symm; refine Finset.sum_bij (fun j _ => insert i j) ?_ ?_ ?_ ?_
  · intro j he; exact mem_filter.mpr ⟨((lit D i j).mp (mem_filter.mp he).2).1,mem_insert_self ..⟩
  · intro a ha b hb H; obtain ⟨_,ha⟩ := (lit D i a).mp (mem_filter.mp ha).2
    obtain ⟨_,hb⟩ := (lit D i b).mp (mem_filter.mp hb).2
    simpa [ha,hb] using congr_arg (Finset.erase · i) H
  · intro b hb; obtain ⟨hx,H⟩ := mem_filter.mp hb
    refine ⟨b.erase i,mem_filter.mpr ⟨mem_univ _,(lit D i _).mpr ?_⟩,Finset.insert_erase H⟩
    simpa [Finset.insert_erase H] using hx
  intro a he; obtain ⟨_,ha⟩ := (lit D i a).mp (mem_filter.mp he).2
  rw [erase_insert ha]
end many

variable (P : Rep G n)

def soloPay (p : Pack n) (F : Config G n → ℂ) : Pulse G n := (0,fun j => if j=p then F else 0)

def shielded (p : Pack n) (F : Config G n → ℂ) (U : Config G n) :=
    if p.zone ∩ flags P.p.threshold U = p.flagsAt then F U else 0

/-- Move one forced insertion to include z, recomposing the unique Pack
if another was using z. Includes *old* inventory even in `braid`,
discard no far partners. -/
def enlarged (p : Pack n) (z : Site n) (F : Config G n → ℂ) : Pulse G n :=
    soloPay (spread p z) (shielded P (spread p z) F) + ∑ j∈attaches p z, soloPay (braid p j) (shielded P (braid p j)
      (fun U => F U * incumbent P U j))

def nullPay (p : Pack n) (z : Site n) (F : Config G n → ℂ) := soloPay p F - enlarged P p z F



lemma tangent_add (D F : Pulse G n) : tangent P (D+F)=tangent P D+tangent P F := by
  funext U; unfold tangent; simp only [Prod.fst_add,Prod.snd_add, Pi.add_apply, add_mul,Finset.sum_add_distrib,mul_add]; ring










end YM.AnalyticNext.GridStop.Alphabet
