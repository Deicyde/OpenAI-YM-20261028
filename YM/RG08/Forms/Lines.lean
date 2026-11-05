import YM.RG08.Forms.Shuffle
import YM.RG08.Rows.Algebra

/-!
# Line budget for heat-equation contractions
-/
noncomputable section
namespace YM.RG08.Forms
open Pert.Bulk Packets Finset Function Lattice
open scoped BigOperators Topology ENNReal Classical
set_option autoImplicit false
variable {I M : Type}

abbrev Line (I : Type) := I → I→ℝ

def link (d : Ground I) (σ : ℝ) (Γ : Line I) := fun i j=> bill (Γ i j) (σ*d.span i j)

structure Wire (d : Ground I) (σ B : ℝ) (Γ : Line I) : Prop where
 width : 0≤σ
 gain : 0≤B
 forth : ∀ i,∑' j, link d σ Γ i j ≤ ENNReal.ofReal B
 back : ∀ j,∑' i, link d σ Γ i j ≤ ENNReal.ofReal B

variable {d : Ground I}{Γ : Line I}{σ τ p q : ℝ}

lemma Wire.mono (h : Wire d σ p Γ) (hτ : 0 ≤ τ) (hs : τ≤σ) (hp : p≤q) : Wire d τ q Γ := by
 have hU (i j:I) : link d τ Γ i j ≤ link d σ Γ i j:=bill_mono le_rfl (mul_le_mul_of_nonneg_right hs (d.nn ..))
 exact ⟨hτ,h.gain.trans hp,fun i=> (ENNReal.tsum_le_tsum fun j=>hU i j).trans ((h.forth i).trans (by gcongr)),fun j=> (ENNReal.tsum_le_tsum fun i=>hU i j).trans ((h.back j).trans (by gcongr))⟩
lemma Wire.toll (h : Wire d σ p Γ) (i j:I) : link d σ Γ i j ≤ ENNReal.ofReal p := (ENNReal.le_tsum j).trans (h.forth i)
lemma Wire.plain (h : Wire d σ p Γ) (i j:I) : |Γ i j| ≤ p := (le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (mul_nonneg h.width (d.nn ..)))).trans ((ENNReal.ofReal_le_ofReal_iff h.gain).mp (h.toll i j))
lemma Wire.turn (h : Wire d σ p Γ) : Wire d σ p (Function.swap Γ):= by
 have he (j k : I) : link d σ (Function.swap Γ) j k=link d σ Γ k j:= by simp only [link,swap];rw [d.left]
 exact ⟨h.width,h.gain,fun i=>by simp_rw [he];exact h.back i,fun j=>by simp_rw [he]; exact h.forth j⟩

lemma wire_carpet [Fintype I] {K : Kernel I I} (σ p:ℝ)(hs:0≤σ)(hp:0≤p)(hK:RowCost σ 1 K p)(hK':ColCost σ 1 K p) : Wire (carpet I) σ (Fintype.card I * p) K:=by
 have h (i j:Market I):link (carpet I) σ K i j=bill (K i j) (σ*delta 1 i.1 j.1):=by
  simp [link,carpet,delta] -- one.val simplification?
 refine ⟨hs,by positivity,fun j=>?_,fun j=>?_⟩ <;>
 rw [ENNReal.tsum_prod'] <;> simp_rw [h,tsum_fintype]
 · exact full_sum _ p hp (hK j)
 exact full_sum _ p hp (fun a=> hK' a j)

end YM.RG08.Forms
