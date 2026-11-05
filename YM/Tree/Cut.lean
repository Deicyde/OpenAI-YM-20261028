import YM.Tree.Pines

/-!
# Actual tree-gauge slice

For any forest, without changing a single coarse argument. No Gaussian slicing
or making edge variables independent on a conditioned event. Pins are physical
sites/positive edges. Use `drape` to get the physical links. All identities
before exponential-chart coordinates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Tree.Forest
open Lattice Wilson RG MeasureTheory Function Filter
open scoped Topology Matrix.Norms.Frobenius BigOperators ENNReal
variable {c f : Side} {g : Ratio c f} (A : Forest g) {G : Gauge}

abbrev Free := {i : Edge (Site f) // i∉ A.trunks}
abbrev Slice (G : Gauge) := A.Free → G.El

def foldAt (U : Config G f) (i : Site f) := (travel U i (A.hike i))⁻¹

lemma fold_root (U : Config G f) (x : Site c) : A.foldAt U (g.embed x)=1 := by
  unfold foldAt
  rw [hike, dif_neg ?_,travel, inv_one]
  rintro h; exact h (by rw [Ratio.embed_parent])

lemma fold_step (U : Config G f) {x : Site f} (hx : leaf g x) :
    A.foldAt U x * (A.up x).read U x=A.foldAt U (x+(A.up x).vec) := by
  rw [foldAt, hike, dif_pos hx, travel, mul_inv_rev, inv_mul_cancel_right,foldAt]

lemma compress (U : Config G f) (i : Edge (Site f)) (h : i ∈ A.trunks) :
    Lattice.gauge (A.foldAt U) U i=1 := by
  obtain ⟨x,hx,rfl⟩ := (trunk_mem_iff A _).mp h
  have hh : (A.up x).read (Lattice.gauge (A.foldAt U) U) x=1 := by rw [Step.gauge_read,A.fold_step U hx,mul_inv_cancel]
  unfold Step.read at hh
  cases he : (A.up x).neg <;> simpa [he] using hh

lemma names (U V : Config G f) (h : ∀ z∈ A.trunks, U z=V z) : A.foldAt U=A.foldAt V := by
  funext x; induction x using hike.induct A with
  | case1 x hx ih =>
    have he : (A.up x).read U x=(A.up x).read V x := by unfold Step.read; rw [h _ ((A.trunk_mem_iff _).mpr ⟨x,hx,rfl⟩)]
    have hh' := A.fold_step U hx; rw [he,ih,← A.fold_step V hx] at hh'
    exact mul_right_cancel hh'
  | case2 x hx => rw [show x=g.embed (g.parent x) from Classical.not_not.mp hx,fold_root,fold_root]

@[fun_prop] lemma folds (i : Site f) : Continuous fun U : Config G f => A.foldAt U i := by unfold foldAt; fun_prop

def seam : Config G f ≃ᵐ ((↥A.trunks → G.El) × A.Slice G) := MeasurableEquiv.piEquivPiSubtypeProd _ _

def drape (S : A.Slice G) : Config G f := A.seam.symm (1,S)

theorem on_tree (S : A.Slice G) (i : ↥A.trunks) : A.drape S i=1 :=
    congr_fun (congr_arg Prod.fst (A.seam.apply_symm_apply (1,S))) i

@[simp] theorem off_tree (S : A.Slice G) (i : A.Free) : A.drape S i=S i :=
    congr_fun (congr_arg Prod.snd (A.seam.apply_symm_apply (1,S))) i

@[fun_prop] theorem continuous_drape : Continuous (A.drape (G := G)) := by
  apply continuous_pi
  intro i
  by_cases h : i ∈ A.trunks
  · have he (x : A.Slice G) : A.drape x i=1 := A.on_tree x ⟨i,h⟩
    simp_rw [he]; fun_prop
  have he (x : A.Slice G) : A.drape x i = x ⟨i,h⟩ := A.off_tree x ⟨i,h⟩
  simp_rw [he]; fun_prop

def order (G : Gauge) : Measure (A.Slice G) := Measure.pi fun _ => G.probHaar
instance (G : Gauge) : IsProbabilityMeasure (A.order G) := by unfold order; infer_instance

private def rearrange (k : Site f → G.El) : MeasurableEquiv (A.Slice G) (A.Slice G) where
  toFun := fun s i => k i.val.1*s i*(k (i.val.1+step i.val.2))⁻¹
  invFun := fun s i => (k i.val.1)⁻¹*s i*k (i.val.1+step i.val.2)
  left_inv := by intro s; funext; group
  right_inv := by intro s; funext; group
  measurable_toFun := by simp only [Equiv.coe_fn_mk]; fun_prop
  measurable_invFun := by simp only [Equiv.coe_fn_symm_mk]; fun_prop

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

theorem pack (F : Config G f → X) (h : Integrable F (prior G f))
    (he : ∀ k : Site f → G.El, (∀ i, k (g.embed i)=1) → ∀ U,F (Lattice.gauge k U)=F U) :
    (∫ U : Config G f, F U ∂prior G f) = ∫ x : A.Slice G,F (A.drape x) ∂A.order G := by
  let M : Measure (↥A.trunks → G.El) := Measure.pi (fun _ => G.probHaar)
  letI : IsProbabilityMeasure M := by unfold M; infer_instance
  have hS : MeasurePreserving A.seam (prior G f) (M.prod (A.order G)) := by
    unfold prior M order
    convert! measurePreserving_piEquivPiSubtypeProd  (fun _ : Edge (Site f) => G.probHaar) (fun i => i∈A.trunks)
  rw [← hS.symm.integral_comp' F]
  have H : Integrable (fun x => F (A.seam.symm x)) (M.prod (A.order G)) :=
    (hS.symm.integrable_comp_emb A.seam.symm.measurableEmbedding).mpr h
  rw [integral_prod _ H]; clear H
  have hh (x : ↥A.trunks → G.El) : (∫ y,F (A.seam.symm (x,y))∂A.order G) = ∫ y,F (A.drape y) ∂A.order G := by
    let k := A.foldAt (A.seam.symm (x,(1:A.Slice G)))
    have HS : MeasurePreserving (A.rearrange k) (A.order G) (A.order G) :=
      measurePreserving_pi _ _ fun i : A.Free => G.preserve_two_sided (k i.val.1) ((k (i.val.1+step i.val.2))⁻¹)
    have hg (y : A.Slice G) : F (A.seam.symm (x,y))=F (A.drape (A.rearrange k y)) := by
      rw [← he k (fun x => A.fold_root _ x)]
      congr 1
      funext i; by_cases e : i∈A.trunks
      · have H : k=A.foldAt (A.seam.symm (x,y)) := A.names _ _ (fun z h ↦ by
          let t : ↥A.trunks := ⟨z,h⟩
          exact (congr_fun (congr_arg Prod.fst (A.seam.apply_symm_apply (x,(1:A.Slice G)))) t).trans (congr_fun (congr_arg Prod.fst (A.seam.apply_symm_apply (x,y))) t).symm)
        exact Eq.trans (by rw [H]; exact A.compress _ _ e) (A.on_tree _ ⟨i,e⟩).symm
      let t : A.Free := ⟨i,e⟩
      rw [show A.drape _ i = _ from A.off_tree (A.rearrange k y) t]
      change k i.1*A.seam.symm (x,y) i*(k _)⁻¹=k i.1*y t*(k _)⁻¹
      rw [show A.seam.symm (x,y) i = y t from congr_fun (congr_arg Prod.snd (A.seam.apply_symm_apply (x,y))) t]
    simp_rw [hg]
    exact HS.integral_comp' (fun x ↦ F (A.drape x))
  simp_rw [hh]; simp

/-- Actual block use. h includes both Covariant proof and numeric branch API. -/
theorem pushing {S : StepData c f} (A : Forest S.ratio) {β : ℝ}
    (hk : S.IsKernel β G) (F : Config G f → X) (V : Config G c) (hf : GaugeInvariant F) (h : Integrable F (prior G f))
    (H : ∀ k : Site f → G.El,∀ U : Config G f, S.density β (Lattice.gauge k U) (Lattice.gauge (k ∘ S.ratio.embed) V) = S.density β U V) :
    S.push β F V = ∫ x : A.Slice G, S.density β (A.drape x) V • F (A.drape x) ∂A.order G := by
  refine A.pack _ (StepData.push_slice hk V F h) (fun k hv U => ?_)
  have he : Lattice.gauge (k ∘ S.ratio.embed) V=V := by funext; simp [Lattice.gauge,hv]
  rw [hf,← H k U,he]
end YM.Tree.Forest
