import YM.Further.CURVED_GAUSSIAN_JETS.Tracks
import YM.Further.CURVED_GAUSSIAN_JETS.Weights
import YM.Next.MULTISOURCE.Collateral
import YM.Next.ROTATIONS.Band
import YM.Next.WARD_BIN.Stencils
import YM.Push.CUTOFF_PROJECTORS.Along
import YM.Push.CUTOFF_PROJECTORS.Spectral
import YM.SectorNext.VACUUM_NORMALIZATION.Deletion

/-!
# Connected full-halo accounts for position chains

Projection for charged output sites (`b`) can differ from the index
in matrix estimates (`a` in the next files). Scaled torus convention
coverNumber, arbitrary winding, no sparsity on allowed holes or paths.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CurvedGaussianJets.Tracks
open Matrix Function Filter Jets Lattice Wilson RG Precision Set MeasureTheory Push.Uniform SectorNext.Vacuum
open scoped Matrix.Norms.Frobenius BigOperators Classical Topology ContDiff
variable {I : Type*} {c f : Side} {b : I → Site c} {d m N D K : ℕ} {p : Run I d}

def spots (b : I → Site c) (p : Run I d) := Finset.univ.image (b ∘ p)
def dots (b : I → Site c) (D : ℕ) (p : Run I d) := halo D (spots b p)
def Hops (b : I → Site c) (D : ℕ) (p : Run I d) := ∀ i : Fin d,separation (b (p i.castSucc)) (b (p i.succ)) ≤ D
lemma dots_mem {x : Site c} : x∈dots b D p ↔ ∃ i : Fin (d+1), separation (b (p i)) x ≤ D := by unfold dots spots; simp [halo_spec]
lemma dots_here (i : Fin (d+1)) : b (p i) ∈ dots b D p := dots_mem.mpr ⟨i,by rw [separation_self]; omega⟩
lemma dots_zero {p : Run I 0} : dots b D p=halo D {b (p 0)} := by
  ext; simp only [dots_mem,halo_spec,Finset.mem_singleton]; constructor
  · rintro ⟨i,hi⟩; exact ⟨_,rfl,(show i=0 by haveI : Subsingleton (Fin (0+1)) := inferInstanceAs (Subsingleton (Fin 1)); exact Subsingleton.elim _ _) ▸ hi⟩
  rintro ⟨i,rfl,hi⟩; exact ⟨0,hi⟩
lemma dots_next {p : Run I (d+1)} : dots b D p = halo D {b (p 0)} ∪ dots b D (Fin.tail p) := by
  ext; simp only [dots_mem,Finset.mem_union,halo_spec,Finset.mem_singleton,exists_eq_left]; constructor
  · rintro ⟨i,hi⟩; exact Fin.cases Or.inl (fun j hj=> Or.inr ⟨j,hj⟩) i hi
  rintro (h|⟨j,hj⟩); exact ⟨0,h⟩; exact ⟨j.succ,hj⟩
namespace Hops
lemma tail {p : Run I (d+1)} (h : Hops b D p) : Hops b D (Fin.tail p) := fun i=> h i.succ
lemma close (h : Hops b D p) (i : Fin (d+1)) : separation (b (p 0)) (b (p i)) ≤ d*D := by
  induction d with
  | zero => rw [(show 0=i by haveI : Subsingleton (Fin (0+1)) := inferInstanceAs (Subsingleton (Fin 1)); exact Subsingleton.elim _ _),separation_self,zero_mul]
  | succ d ih => induction i using Fin.cases with
                 | zero => simp
                 | succ i => exact (separation_triangle _ (b (Fin.tail p 0)) _).trans ((Nat.add_le_add (show separation (b (p 0)) (b (Fin.tail p 0)) ≤ D from h 0) (ih h.tail i)).trans_eq (by ring))
lemma reaches (h : Hops b D p) {x : Site c} (hx : x∈dots b D p) : separation (b (p 0)) x ≤ (d+1)*D := by obtain ⟨i,hi⟩ := dots_mem.mp hx; exact (separation_triangle _ (b (p i)) x).trans ((Nat.add_le_add (h.close i) hi).trans_eq (Nat.succ_mul ..).symm)
lemma sum_tiles (h : Hops b (m*N) p) (hN : 0 < N) : coverNumber N (dots b (m*N) p) ≤ (d+1)*(m+m+1)^4 := by
  induction d with
  | zero => rw [dots_zero]; exact (Corona.tile _ _ _ hN).trans (by simp)
  | succ d ih => rw [dots_next]; apply (Corona.meets_sum (halo_spec.mpr ⟨_,Finset.mem_singleton_self _,show separation (b (p 0)) (b (Fin.tail p 0)) ≤ _ from h 0⟩) (dots_here 0) N).trans
                 exact (Nat.add_le_add (Corona.tile _ _ _ hN) (ih h.tail)).trans_eq (by ring)
end Hops

variable [Fintype I]
variable (b) in
def disk (x : Site c) (R : ℕ) := Finset.univ.filter fun i : I=> separation (b i) x ≤ R
lemma size_disk (x : Site c) (R : ℕ) (hb : Multiplicity b K) : (disk b x R).card ≤ (R+R+1)^4*K := by
  have hc : disk b x R ⊆ (halo R {x}).biUnion (fun y=>Finset.univ.filter fun i : I=> b i=y) := by
    intro i hi; exact Finset.mem_biUnion.mpr ⟨b i,halo_spec.mpr ⟨x,Finset.mem_singleton_self _,separation_comm .. ▸ (Finset.mem_filter.mp hi).2⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩
  refine ((Finset.card_le_card hc).trans Finset.card_biUnion_le).trans ((Finset.sum_le_sum fun i _=>hb i).trans ?_)
  simp only [Finset.sum_const,nsmul_eq_mul]; have h := Corona.halo_size {x} R; rw [Finset.card_singleton,one_mul] at h; exact Nat.mul_le_mul_right _ h
lemma projection_count {a : I → Site f} (r : Ratio c f) (h : Multiplicity a K) : Multiplicity (r.parent ∘ a) (((r.count.val+r.count.val+1)^4 * K)) := by
  intro x; apply le_trans _ (size_disk (r.embed x) _ h); apply Finset.card_le_card; intro i hi
  have he : r.parent (a i)=x := (Finset.mem_filter.mp hi).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, he ▸ (by have := Corona.near r (a i); omega : separation (a i) (r.embed (r.parent (a i))) ≤ _)⟩
end YM.Further.CurvedGaussianJets.Tracks
