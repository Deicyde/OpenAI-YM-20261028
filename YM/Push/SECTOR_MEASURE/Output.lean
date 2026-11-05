import YM.Push.SECTOR_MEASURE.Decompose
import YM.Work.B02.Slab

/-!
# On the actual pushforward 

Recover `StepData.push` on the true tree slice as a sum of the intact
sector columns, and normalize with the common denominator. Tags summed
once with probability (`likelihood` relative to COUNTING), the noise
normalized *for that choice* against probability Haar. No inference
that after a guard is imposed subgroups of these tags/slices can be
multiplied as independent costs.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.SectorMeasure

open Filter Function Lattice RG Wilson Pressure Pressure.Stores Tree MeasureTheory
open Next.Fluctuations.Sector
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {G : Gauge} {c f n : Side} {S : StepData c f} {P : Teller G} {T : Tube G S} {x W : ℝ}

section slicing

-- Integrable on the forest slice itself. Not claiming this from taking
-- a restriction to SliceSet (in fact this needs gauge invariance).
-- Follow the isomorphisms in `Forest.pack`.
variable {X : Type*} [NormedAddCommGroup X]

private def transport (F : Forest S.ratio) (k : Site f → G.El) :
    MeasurableEquiv (F.Slice G) (F.Slice G) where
  toFun := fun s i => k i.val.1*s i*(k (i.val.1+step i.val.2))⁻¹
  invFun := fun s i => (k i.val.1)⁻¹*s i*k (i.val.1+step i.val.2)
  left_inv := by intro s; funext; group
  right_inv := by intro s; funext; group
  measurable_toFun := by simp only [Equiv.coe_fn_mk]; fun_prop
  measurable_invFun := by simp only [Equiv.coe_fn_symm_mk]; fun_prop

theorem drape_integrable (F : Forest S.ratio) (g : Config G f → X) (h : Integrable g (prior G f))
    (he : GaugeInvariant g) : Integrable (fun a => g (F.drape a)) (F.order G) := by
  let M : Measure (↥F.trunks → G.El) := Measure.pi (fun _ => G.probHaar)
  letI : IsProbabilityMeasure M := by unfold M; infer_instance
  have hm : MeasurePreserving F.seam (prior G f) (M.prod (F.order G)) := by
    unfold prior M Forest.order
    convert! measurePreserving_piEquivPiSubtypeProd (fun _ : Edge (Site f) => G.probHaar) (fun i => i∈F.trunks)
  have hM : Integrable (fun x => g (F.seam.symm x)) (M.prod (F.order G)) :=
    (hm.symm.integrable_comp_emb F.seam.symm.measurableEmbedding).mpr h
  obtain ⟨w, hw⟩ : ∃ w : ↥F.trunks → G.El, Integrable (fun a => g (F.seam.symm (w,a))) (F.order G) :=
    hM.prod_right_ae.exists
  -- Fix just one tree-link value w. All free-link uses, transformed
  -- once, read this same value.
  let k := F.foldAt (F.seam.symm (w,(1:F.Slice G)))
  have HK : MeasurePreserving (transport F k) (F.order G) (F.order G) :=
    measurePreserving_pi _ _ fun i : F.Free => G.preserve_two_sided (k i.val.1) ((k (i.val.1+step i.val.2))⁻¹)
  apply (HK.integrable_comp_emb (transport F k).measurableEmbedding).mp
  have hg (y : F.Slice G) : g (F.seam.symm (w,y)) = g (F.drape (transport F k y)) := by
    rw [← he k (F.seam.symm (w,y))]
    congr 1
    funext i; by_cases e : i∈F.trunks
    · have H : k=F.foldAt (F.seam.symm (w,y)) := F.names _ _ (fun z hz ↦ by
        let t : ↥F.trunks := ⟨z,hz⟩
        exact (congr_fun (congr_arg Prod.fst (F.seam.apply_symm_apply (w,(1:F.Slice G)))) t).trans
          (congr_fun (congr_arg Prod.fst (F.seam.apply_symm_apply (w,y))) t).symm)
      exact Eq.trans (by rw [H]; exact F.compress _ _ e) (F.on_tree _ ⟨i,e⟩).symm
    let t : F.Free := ⟨i,e⟩
    rw [show F.drape _ i = _ from F.off_tree (transport F k y) t]
    change k i.1*F.seam.symm (w,y) i*(k _)⁻¹=k i.1*y t*(k _)⁻¹
    rw [show F.seam.symm (w,y) i = y t from congr_fun (congr_arg Prod.snd (F.seam.apply_symm_apply (w,y))) t]
  simp_rw [hg] at hw
  exact hw

end slicing

section push

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Output columns for a specified input function (including any
normalization). Relative to probability Haar prior on `V`. -/
def output (D : Allocation G S x W) (F : Forest S.ratio) (β : ℝ) (g : Config G f → X) (A : Stores S)
    (V : Config G c) : X :=
  D.column A F V (through S F β V (fun _ a => g (F.drape a)))

variable (D : Allocation G S x W) (F : Forest S.ratio) (β : ℝ) (g : Config G f → X)





lemma output_env [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (hm : S.patch.Branches S.kernel G) (h : Envelope g) (A : Stores S) : Envelope (output D F β g A) := by
  apply D.column_env hm A F (fun k p => through S F β p.2 (fun _ a => g (F.drape a)) k p.1)
  intro k
  have h1 : Measurable (fun a : F.Slice G × Config G c => F.drape a.1) :=
    F.continuous_drape.measurable.comp measurable_fst
  have h2 : Measurable (fun a : F.Slice G × Config G c => a.2) := measurable_snd
  exact Env.scale (env_tagged β k hm h1 h2) (Env.along h h1)

/-- The already normalized block kernel. True for *every* V, not just a.e. -/
theorem push_columns [CompleteSpace X] (hm : S.patch.Branches S.kernel G)
    (h : Integrable g (prior G f)) (he : GaugeInvariant g) (V : Config G c) :
    (∑ A, output D F β g A V) = S.push β g V := by
  let L : S.Choices → F.Slice G → X := fun _ a => g (F.drape a)
  have hg k : Integrable (through S F β V L k) (F.order G) :=
    through_integrable F β V L hm k (drape_integrable F g h he)
  rw [F.pushing (S.isKernel hm β) g V he h (fun k U => S.covary hm k β U V)]
  change (∑ A, D.column A F V (through S F β V L)) = _
  rw [D.partitions hm F V _ hg]
  unfold tagTotal; rw [← integral_finsetSum _ fun i _ => hg i]
  apply integral_congr_ae
  filter_upwards with a
  unfold StepData.density through taggedKernel L; rw [Finset.sum_smul]







end push

section wilson
open scoped ENNReal



variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (β : ℝ)







section columns
variable (hm : S.patch.Branches S.kernel G) (D : Allocation G S x W) (F : Forest S.ratio)
include hm





end columns


end wilson
end YM.Push.SectorMeasure
