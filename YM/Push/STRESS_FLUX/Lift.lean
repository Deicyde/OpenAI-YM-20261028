import YM.Push.STRESS_FLUX.Counts

/-!
Equivariant lifts/counts through the actual exterior quotients. No commutation of ordinary continuous rotations with the quotient is assumed or used.
-/
set_option autoImplicit false
noncomputable section
namespace YM.StressFlux
open Labels Function Gauge Table
open scoped Topology BigOperators Matrix.Norms.Frobenius InnerProductSpace

variable {G : Gauge} {L : Register G} {S : Table L} {d : ℕ}

def spinQ (H : S.RealSpin) (s : Signed) : Module.End ℝ (S.Field d) := (S.mirror H d s).restrictScalars ℝ
def conjQ (H : S.RealSpin) : Module.End ℝ (S.Field d) where
  toFun := S.conj H d
  map_add' := map_add _
  map_smul' r x := by
    rw [← IsScalarTower.algebraMap_smul ℂ r, map_smulₛₗ, RingHom.id_apply, ← IsScalarTower.algebraMap_smul ℂ r]; simp

abbrev TableTwo (H : S.RealSpin) := tensors (V:=S.Field 4) (spinQ H) (conjQ H)
abbrev TableOne (H : S.RealSpin) := vectors (V:=S.Field 5) (spinQ H) (conjQ H)

def fromPol (S : Table L) : Label G d →ₗ[ℝ] S.Field d :=
    (S.project d ∘ₗ (L.coord d).coords.toLinearMap).restrictScalars ℝ
@[simp] lemma fromPol_formula (v : Label G d) : fromPol S v = S.project d ((L.coord d).coords v) := rfl
@[simp] lemma spinQ_fromPol (v : Label G d) (H : S.RealSpin) (s : Signed) :
    spinQ H s (fromPol S v) = fromPol S (spinR s v) := by
  change S.mirror H d s (fromPol S v) = fromPol S _; rw [fromPol_formula, mirror_project, Register.mirrorGroup,Labels.Frame.act_coords]; rfl
@[simp] lemma conjQ_fromPol (v : Label G d) (H : S.RealSpin) :
    conjQ H (fromPol S v) = fromPol S (conjR v) := by
  change S.conj H d (fromPol S v) = fromPol S _; rw [fromPol_formula,conj_project, fromPol_formula]
  exact congr_arg _ ( (L.coord d).coords.symm.injective (by rw [← L.geom_conj]; simp [conjR]))
lemma spinR_mul (s t : Signed) (v : Label G d) : spinR (s*t) v = spinR s (spinR t v) := by
  change tensor (s*t).ortho v = _; rw [show (s*t).ortho=s.ortho*t.ortho from map_mul Signed.inclusionO .., tensor_mul]; rfl
lemma spinQ_mul (s t : Signed) (v : S.Field d) (H : S.RealSpin) : spinQ H (s*t) v = spinQ H s (spinQ H t v) := S.mirror_mul H d s t v

private def inverse (S : Table L) : S.Field d →ₗ[ℝ] Label G d :=
    ((L.coord d).coords.symm.toLinearMap ∘ₗ S.representative d).restrictScalars ℝ
@[simp] private lemma inverse_eq (x : S.Field d) : fromPol S (inverse S x) = x := by simp only [fromPol_formula,inverse, LinearMap.restrictScalars_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,S.rep]
private def realSection (H : S.RealSpin) := (2:ℝ)⁻¹ • ((inverse S : S.Field d →ₗ[ℝ] Label G d) + conjR ∘ₗ inverse S ∘ₗ conjQ H)
private lemma section_real (H : S.RealSpin) (x : S.Field d) : realSection H (conjQ H x) = conjR (realSection H x) := by
  simp only [realSection,LinearMap.smul_apply, LinearMap.add_apply, map_smul, map_add, LinearMap.comp_apply, show conjQ H (conjQ H x)=x from S.reflect_star H ..,show ∀ v : Label G d, conjR (conjR v)=v from fun v => twice v]; congr 1; apply add_comm
private lemma section_eq (H : S.RealSpin) (x : S.Field d) : fromPol S (realSection H x) = x := by
  simp only [realSection, LinearMap.smul_apply, LinearMap.add_apply, map_smul, map_add,
    LinearMap.comp_apply, ← conjQ_fromPol _ H, inverse_eq]
  rw [show conjQ H (conjQ H x)=x from S.reflect_star H ..]
  rw [← two_smul ℝ, smul_smul]; norm_num

def equivariantSection (H : S.RealSpin) := ((Fintype.card Signed : ℝ)⁻¹) •
    ∑ s : Signed, spinR s ∘ₗ (realSection H : S.Field d →ₗ[ℝ] Label G d) ∘ₗ spinQ H s⁻¹

lemma section_right (x : S.Field d) (H : S.RealSpin) : fromPol S (equivariantSection H x) = x := by
  have he (s : Signed) : spinQ H s (spinQ H s⁻¹ x)=x := by rw [← spinQ_mul,mul_inv_cancel]; exact S.mirror_one H ..
  simp only [equivariantSection,LinearMap.sum_apply,LinearMap.smul_apply,map_smul,map_sum,LinearMap.comp_apply,
    ← spinQ_fromPol _ H,section_eq,he, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  haveI : Nonempty Signed := ⟨1⟩
  rw [inv_mul_cancel₀ (by exact_mod_cast (show Fintype.card Signed ≠ 0 from Fintype.card_pos.ne')),one_smul]

lemma section_color (x : S.Field d) (H : S.RealSpin) : equivariantSection H (conjQ H x) = conjR (equivariantSection H x) := by
  have he (s : Signed) : spinQ H s (conjQ H x) = conjQ H (spinQ H s x) := (S.mirror_star H ..).symm
  simp only [equivariantSection, LinearMap.sum_apply,LinearMap.smul_apply,map_smul,map_sum,LinearMap.comp_apply,he,section_real,
    show ∀ s : Signed, ∀ v : Label G d, spinR s (conjR v) = conjR (spinR s v) from fun s v => (real_turn s.ortho v).symm]

lemma section_turn (s : Signed) (x : S.Field d) (H : S.RealSpin) : spinR s (equivariantSection H x) = equivariantSection H (spinQ H s x) := by
  simp only [equivariantSection, LinearMap.sum_apply,LinearMap.smul_apply,map_smul,map_sum,LinearMap.comp_apply]; apply congr_arg (_ • ·)
  refine Fintype.sum_equiv (Equiv.mulLeft s) _ _ fun t => ?_
  simp only [show Equiv.mulLeft s t = s*t from rfl, ← spinQ_mul, mul_inv_rev, mul_assoc,inv_mul_cancel,mul_one,spinR_mul]

section Transfer
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    {K : Signed → Module.End ℝ V} {R : Module.End ℝ V} {D : Signed → Module.End ℝ W} {T : Module.End ℝ W}
    (A : V →ₗ[ℝ] W) (h : ∀ s x, A (K s x) = D s (A x)) (H : ∀ x, A (R x) = T (A x))

def vectorMap : vectors K R →ₗ[ℝ] vectors D T where
  toFun v := ⟨fun a => A (v.val a), fun a => (H _).symm.trans (congr_arg A (v.property.1 a)), fun s a => by
    dsimp; rw [← h,v.property.2,map_smul]⟩
  map_add' v w := Subtype.ext (funext fun a => map_add A (v.val a) (w.val a))
  map_smul' c v := Subtype.ext (funext fun a => map_smul A c (v.val a))

def tensorMap : tensors K R →ₗ[ℝ] tensors D T where
  toFun v := ⟨fun a b => A (v.val a b), fun a b => congr_arg A (v.property.1 a b),
    fun a b => (H _).symm.trans (congr_arg A (v.property.2.1 a b)), fun s a b => by dsimp; rw [← h,v.property.2.2,map_smul]⟩
  map_add' v w := Subtype.ext (funext fun a => funext fun b => map_add A (v.val a b) (w.val a b))
  map_smul' c v := Subtype.ext (funext fun a => funext fun b => map_smul A c (v.val a b))
end Transfer

def tensorProjection (H : S.RealSpin) : RawTwo G →ₗ[ℝ] TableTwo H := tensorMap (fromPol S) (fun s v => (spinQ_fromPol v H s).symm) (fun v => (conjQ_fromPol v H).symm)
def vectorProjection (H : S.RealSpin) : RawOne G →ₗ[ℝ] TableOne H := vectorMap (fromPol S) (fun s v => (spinQ_fromPol v H s).symm) (fun v => (conjQ_fromPol v H).symm)
set_option maxRecDepth 4000 in
lemma tensorProjection_onto (H : S.RealSpin) : Surjective (tensorProjection H) := fun v =>
  ⟨tensorMap (equivariantSection H) (fun s x => (section_turn s x H).symm) (fun x => section_color x H) v,
    Subtype.ext (funext fun a => funext fun b => section_right (v.val a b) H)⟩
set_option maxRecDepth 4000 in
lemma vectorProjection_onto (H : S.RealSpin) : Surjective (vectorProjection H) := fun v =>
  ⟨vectorMap (equivariantSection H) (fun s x => (section_turn s x H).symm) (fun x => section_color x H) v,
    Subtype.ext (funext fun a => section_right (v.val a) H)⟩


lemma dim_four (h : G.Simple) (H : S.RealSpin) : Module.finrank ℝ (TableTwo H) ≤ 4 := by
  haveI : FiniteDimensional ℝ (Label G 4) := Module.Finite.trans ℂ _
  have he := (tensorProjection H).finrank_range_le
  rw [LinearMap.range_eq_top.mpr (tensorProjection_onto H), finrank_top] at he
  exact he.trans (finrank_two h)

open Maxwell in
lemma equation_killed (b : Axis) : fromPol (Climb.Bel L) (eom G b)=0 := by
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  apply (Maxwell.projectionExact L.grid).1
  have he : Maxwell.snap L.grid 5 ((L.coord 5).coords (eom G b)) = 0 := Subtype.ext (by
    change observable G 5 ((L.coord 5).coords.symm ((L.coord 5).coords _))=0; rw [LinearEquiv.symm_apply_apply]; exact eom_null b)
  exact he ▸ (residual G 5).zero_mem

lemma dim_free_five (h : G.Simple) (H : (Climb.Bel L).RealSpin) : Module.finrank ℝ (TableOne H) ≤ 2 := by
  haveI : FiniteDimensional ℝ (Label G 5) := Module.Finite.trans ℂ _
  haveI : Module.Finite ℝ ↥(RawOne G) := inferInstance
  haveI : Module.Finite ℝ ↥(vectorProjection H).ker := FiniteDimensional.finiteDimensional_submodule (K:=ℝ) (V:=↥(RawOne G)) _
  have he := LinearMap.finrank_range_add_finrank_ker (K:=ℝ) (V:=↥(RawOne G)) (V₂:=↥(TableOne H)) (vectorProjection H)
  rw [LinearMap.range_eq_top.mpr (vectorProjection_onto H),finrank_top] at he
  have hx : (vectorProjection H).ker ≠ ⊥ := fun hz => eom_nonzero h (congr_arg Subtype.val ((Submodule.mem_bot ℝ).mp
    (show (⟨eom G,eom_rows G⟩ : RawOne G) ∈ ⊥ from hz ▸ (show _ ∈ (vectorProjection H).ker from
      LinearMap.mem_ker.mpr (Subtype.ext (funext (fun i => equation_killed i)))))))
  have ht := finrank_one h; have hq := mt (Submodule.finrank_eq_zero (R:=ℝ) (M:=↥(RawOne G)) (S:=(vectorProjection H).ker)).mp hx
  omega

lemma compare_five {H : S.RealSpin} {A : (Climb.Bel L).RealSpin} (h : G.Simple) (U : Spin.change S 5) (hz : Spin.realH H A U) :
    Module.finrank ℝ (TableOne H) ≤ 2 := by
  let P := vectorMap (U.symm.toLinearMap.restrictScalars ℝ) (show ∀ s x, U.symm (spinQ H s x) = spinQ A s (U.symm x) from
    fun s x => U.injective (by rw [U.apply_symm_apply,show U (spinQ A s (U.symm x)) = spinQ H s (U (U.symm x)) from hz.1 s _,U.apply_symm_apply]))
    (show ∀ x, U.symm (conjQ H x) = conjQ A (U.symm x) from fun x => U.injective (by rw [U.apply_symm_apply]; simpa [conjQ] using (hz.2 (U.symm x)).symm))
  exact LinearMap.finrank_le_finrank_of_injective (f:=P) (fun v w he => Subtype.ext (funext fun a => U.symm.injective
    (congr_fun (congr_arg Subtype.val he) a))) |>.trans (dim_free_five h A)

lemma dim_four_eq {H : S.RealSpin} {A : (Climb.Bel L).RealSpin} (h : G.Simple) (U : Spin.change S 4) (hz : Spin.realH H A U)
    (ht : Module.finrank ℝ (TableTwo A) = 4) : Module.finrank ℝ (TableTwo H) = 4 := by
  apply (dim_four h H).antisymm
  let P := tensorMap (U.toLinearMap.restrictScalars ℝ) (show ∀ s x, U (spinQ A s x) = spinQ H s (U x) from hz.1)
    (show ∀ x, U (conjQ A x) = conjQ H (U x) from hz.2)
  exact ht.ge.trans (LinearMap.finrank_le_finrank_of_injective (f:=P) (fun v w he => Subtype.ext (funext fun a => funext fun b =>
    U.injective (congr_fun (congr_fun (congr_arg Subtype.val he) a) b))))

def labelStress : Coeff →ₗ[ℝ] RawTwo G := (stress G).codRestrict (RawTwo G) (stress_rows G)
def tableStress (H : S.RealSpin) : Coeff →ₗ[ℝ] TableTwo H := tensorProjection H ∘ₗ labelStress
lemma tableStress_at (H : S.RealSpin) (w : Coeff) (a b : Axis) : (tableStress H w).val a b =
    S.project 4 ((L.coord 4).coords (stress G w a b)) := rfl

def material (S : Table L) (w : Coeff) : S.Stress := fun a b => fromPol S (stress G w a b)
lemma tableStress_material (H : S.RealSpin) (w : Coeff) : (tableStress H w).val = material S w := rfl
end YM.StressFlux
