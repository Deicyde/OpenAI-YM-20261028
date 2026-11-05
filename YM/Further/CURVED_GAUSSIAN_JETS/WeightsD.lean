import YM.Further.CURVED_GAUSSIAN_JETS.Shape

set_option autoImplicit false
noncomputable section
namespace YM.Further.CurvedGaussianJets.Shape
open Function Filter Matrix Lattice Wilson Tree RG Precision Pressure Exterior Bid SectorNext.Vacuum FlatTree Progress.StationaryScenes Push.Uniform
open Green (wt wt_pos Rows Both)
open scoped Matrix.Norms.Frobenius BigOperators Classical Topology
variable {G : Gauge} {c f n : Side} {S : StepData c f} {F : Forest S.ratio} (H : Finset F.Free)

abbrev keySite (j : Bits H G) := (free S H j.1).1
abbrev fineSite (s : Signed) (p : Shape.Page G f 2) := s.act (R:=Per f) p.1.1
abbrev coarseSite (S : StepData c f) (p : Shape.Page G c 1) := S.ratio.embed p.1.1

def capacity (G : Gauge) (k : ℕ) := Fintype.card (TypeFace k × G.ColorIndex)
def crowd (G : Gauge) := capacity G 2 + capacity G 1
lemma counts {k : ℕ} (g : Site c → Site n) (h : Injective g) : Multiplicity (fun p : Shape.Page G c k=>g p.1.1) (capacity G k) := fun x=> by
  unfold capacity; rw [←Finset.card_univ]
  refine Finset.card_le_card_of_injOn (fun j=> (j.1.2,j.2)) (fun i hi=> Finset.mem_univ _) fun i hi j hj hh => ?_
  exact Prod.ext (Prod.ext (h ((Finset.mem_filter.mp hi).2.trans ((Finset.mem_filter.mp hj).2.symm))) (congr_arg Prod.fst hh)) (Prod.mk.inj hh).2
lemma key_count : Multiplicity (keySite (G:=G) H) (crowd G) := by
  let b (j : Bits H G) : Shape.Page G f 1 := (free S H j.1,j.2)
  have he := (counts (G:=G) id Function.injective_id (k:=1)).comp (f:=b) (fun i j hh=> Prod.ext ((free S H).injective (congr_arg Prod.fst hh)) (Prod.mk.inj hh).2)
  exact fun i=>(he i).trans (by unfold crowd; omega)
lemma fine_count (s : Signed) : Multiplicity (fineSite (G:=G) (f:=f) s) (crowd G) := fun x => (counts s.act s.act_injective x).trans (by unfold crowd; omega)
lemma coarse_count (S : StepData c f) : Multiplicity (coarseSite (G:=G) S) (crowd G) := fun x=> (counts S.ratio.embed S.ratio.embed_injective x).trans (by unfold crowd; omega)
variable {I J : Type*} [Fintype I] [Fintype J] {a : I → Site n} {b : J → Site n} {M : Matrix I J ℝ} {w C D : ℝ}
omit [Fintype I] in
lemma row_pay {k : ℕ} (hb : Multiplicity b k) (hw : 0<w) (hc : 0≤C)
    (h : ∀ i j, wt (2*w) (a i) (b j) * |M i j| ≤ C) : Green.Rows a b M w (C*(k * Push.Uniform.countCost w)) := by
  intro i
  have ht (j : J) : wt w (a i) (b j)*|M i j| ≤ C*Decay w (a i) (b j) := by
    apply le_trans _ (mul_le_mul_of_nonneg_right (h i j) (decay_pos ..).le)
    rw [mul_right_comm,Decay,wt,wt,←Real.exp_add]; exact le_of_eq (by ring_nf)
  apply (Finset.sum_le_sum (fun j _ => ht j)).trans
  rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (hb.count b hw _) hc
lemma both_pay {k : ℕ} (ha : Multiplicity a k) (hb : Multiplicity b k) (hw : 0<w) (hc : 0≤C)
    (h : ∀ i j, wt (2*w) (a i) (b j) * |M i j| ≤ C) : Green.Both a b M w (C*(k * Push.Uniform.countCost w)) (C*(k * Push.Uniform.countCost w)) :=
  ⟨row_pay hb hw hc h, row_pay ha hw hc fun i j=>by rw [Green.wt_symm]; exact h j i⟩
end YM.Further.CurvedGaussianJets.Shape
