import YM.Next.EXTRACTION.Tails
import YM.Next.FOUNDATIONS.SU2
import YM.Push.FREE_RESOLVENT.PathsAffine

/-!
# Apply row kernels to literal Pressure read

Show weighted path column entries on arbitrary color inputs are the
physical replacements (even for shortened numerical kernel used in Base).
Not interchanging inverse or chart derivatives here; this is a useful witness check
of the definition in `Affine` against  notation and existing `shorten`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FreeResolvent.Affine
open Lattice Wilson RG Matrix Laurent Bloch Exterior Precision Tree Bid TestD Filter Function Set
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
variable {G : Gauge} {c f : Side}

lemma color_tile (C : G.Color) (u : G.El) (i : G.ColorIndex) :
    (∑ j : G.ColorIndex, (G.adjoint u (EuclideanSpace.basisFun G.ColorIndex ℝ j)) i * C j)=G.adjoint u C i := by
  let B := EuclideanSpace.basisFun G.ColorIndex ℝ
  let L : G.Color →L[ℝ] ℝ := PiLp.proj (𝕜:=ℝ) 2 (fun _ : G.ColorIndex => ℝ) i
  have hp : C=∑ i, C i • B i := (B.sum_repr C).symm
  calc
    _ = L (G.adjoint u (∑ i, C i • B i)) := by
      rw [map_sum,map_sum]; simp only [map_smul,smul_eq_mul]; apply Finset.sum_congr rfl; intro j _; exact mul_comm ..
    _ = _ := by rw [← hp]; rfl

lemma reads_row (S : StepData c f) (s : Signed) (W : PathData G) (r : Admit) {σ M : ℝ} (hs : 0 ≤ σ) (h : Sheet W σ M)
    (B : Vec G c 1) (C : fieldDir G f 2) (p : Face (Per f)) :
    HasSum (fun k : ℕ => let z := W.row p.2 k; if r z.2 then z.1 • (G.adjoint (travel (shone S s B) p.1 z.2.walk)
      (C (wrap f z.2.offset+p.1,plaquette z.2.plaq))) else 0)
      (decode (tracks S s W r B *ᵥ flatten C) (p.1,plaquette p.2)) := by
  rcases p with ⟨x,p⟩
  let A (i) := W.row p i
  let F (i) := if r (A i).2 then (A i).1 • (G.adjoint (travel (shone S s B) x (A i).2.walk)
    (C (wrap f (A i).2.offset+x,plaquette (A i).2.plaq))) else 0
  have ht : Summable fun i => |(A i).1| := Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun i =>
    le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (mul_nonneg hs (show 0 ≤ ((A i).2.length:ℝ) by positivity)))) (h p).2.1
  have he k : ‖F k‖ ≤ |(A k).1| * ‖C‖ := by
    unfold F; split <;> rename_i H; swap; · rw [norm_zero]; positivity
    rw [norm_smul, Real.norm_eq_abs,G.norm_adjoint]; exact mul_le_mul_of_nonneg_left (norm_le_pi_norm C _) (abs_nonneg _)
  have hp := Summable.of_norm_bounded (ht.mul_right _) he
  change HasSum F _; rw [hp.hasSum_iff]
  symm; ext i
  let a : tile G f := (x,plaquette p,i)
  let L : G.Color →L[ℝ] ℝ := PiLp.proj (𝕜:=ℝ) 2 (fun _ : G.ColorIndex => ℝ) i
  have hh (j : tile G f) : Summable fun k => edgework S s W r a j k B := by
    refine Summable.of_norm_bounded ht fun k => ?_
    unfold edgework
    dsimp only [a]; rw [show plaqEquiv.symm (plaquette p)=p from plaqEquiv.symm_apply_apply _]
    split
    · rw [norm_mul,Real.norm_eq_abs]; apply mul_le_of_le_one_right (abs_nonneg _)
      unfold element; split
      · have h : ‖(G.adjoint (travel (shone S s B) x (A k).2.walk) (EuclideanSpace.basisFun G.ColorIndex ℝ j.2.2))‖=1 := by simp
        change |((G.adjoint _) _ : G.Color) _| ≤ _
        rw [← h]; simpa only [EuclideanSpace.basisFun_inner, OrthonormalBasis.norm_eq_one, one_mul] using
          abs_real_inner_le_norm (EuclideanSpace.basisFun G.ColorIndex ℝ i) (G.adjoint (travel (shone S s B) x (A k).2.walk) (EuclideanSpace.basisFun G.ColorIndex ℝ j.2.2))
      simp
    rw [norm_zero]; exact abs_nonneg _
  change (∑ j, (∑' k, edgework S s W r a j k B)*flatten C j)=L (∑' b, F b)
  simp_rw [L.map_tsum hp, ← tsum_mul_right]
  rw [← Summable.tsum_finsetSum (fun j _ => (hh j).mul_right (flatten C j))]; refine tsum_congr fun k => ?_
  let u := travel (shone S s B) x (A k).2.walk
  unfold edgework F
  dsimp only [a]
  rw [show plaqEquiv.symm (plaquette p)=p from plaqEquiv.symm_apply_apply _]
  by_cases h : r (A k).2=true
  · simp only [show r _=true from h,if_true,show W.row p k=A k from rfl]
    rw [map_smul,Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type,element, Prod.mk.injEq,ite_mul,mul_ite,mul_zero,smul_eq_mul,ite_and]
    -- move sums with conditions through sums
    rw [Finset.sum_eq_single (wrap _ (A k).2.offset+x)]
    · simp only [if_true, zero_mul]
      rw [Finset.sum_eq_single (plaquette (A k).2.plaq)]
      · simp_rw [if_true,mul_assoc,← Finset.mul_sum]
        let v := C (wrap f (A k).2.offset+x,plaquette (A k).2.plaq); congr 1; exact color_tile v u i
      · intro b _ hb; simp [hb]
      simp
    · intro y _ hy; simp [hy]
    simp
  · simp [A] at h; simp [A,h]


end YM.FreeResolvent.Affine
