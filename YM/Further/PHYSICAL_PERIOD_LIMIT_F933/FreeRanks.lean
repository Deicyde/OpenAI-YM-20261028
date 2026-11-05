import YM.Next.ROTATIONS.Response
import YM.Next.SCHEDULE.Postal
import YM.Push.STRESS_FLUX.Line
import YM.UVNext.COMMON_GRADE_ASSEMBLY.NoSource



/-!
# Interface adapter from the accepted stress finite algebra to the rank bill in COMMON_GRADE

No second free calculation or priced interacting Λ-estimate needed for
this bill! Signed matrix convention coincides here (`two` and `one`
adapters, including real vs complex scalar). At the actual Bel table the
explicit free stress tests in STRESS_FLUX already suffice to calculate
onto and one for the map in UV_STRESS. Needed because Flow and Corr
suppliers must use the same H as this and can't just assume this rank
identity follows from existence of MaxwellData. We analyze any normalized
comparator already issued in the FreeBridge convention; not a canonical
calculation of κ etc, not filled_four, no station assertion.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.PhysicalPeriodLimitF933
open Function Filter Set Analysis Table Ward Climb Maxwell Org
  Next.UVStress UVNext.Grade StressFlux Work.A01
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {L : Register G} {S : Table L} (A : S.RealSpin)

lemma signs (s : Signed) (a : Axis) : Work.A01.eps s a = sign s a := by
  simp [Work.A01.eps,Signed.matrix_at,sign]

lemma two (J : S.Stress) : J ∈ TableTwo A ↔ J ∈ SymSpace A := by
  refine ⟨fun H => sym_mem.mpr ⟨H.1,H.2.1,raw_eq H⟩,fun h => ?_⟩
  obtain ⟨H,B,U⟩ := sym_mem.mp h
  refine ⟨H,B,fun k i j => ?_⟩
  change S.mirror A 4 k _ = _
  rw [Work.A01.tensor_column U]
  simp_rw [signs, RCLike.real_smul_eq_coe_smul (K:=ℂ)]
  rfl

lemma one (V : PolarFields S) : V ∈ TableOne A ↔ V ∈ Vectors A := by
  constructor
  · intro h; refine ⟨h.1,fun k i => ?_⟩
    rw [Work.A01.eps_column,signs]
    exact (h.2 k i).trans (RCLike.real_smul_eq_coe_smul (K:=ℂ) (sign k i) _)
  intro h; refine ⟨h.1,fun k i => ?_⟩
  change S.mirror A 5 k (V i)=_
  rw [h.2 k i,Work.A01.eps_column, signs]
  exact (RCLike.real_smul_eq_coe_smul (K:=ℂ) (sign k i) _).symm

lemma expectation_is (J : S.Stress) (a b : Axis) : expectation S 4 (J a b) = oneStress S J 0 a b := by
  rw [expectation,front_eval]
  unfold oneStress quad; congr 1
  funext i; fin_cases i; rfl

variable {A}
lemma sym_of_centers {J : S.Stress} (h : J ∈ TableTwo A) (he : Centers J) :
    J ∈ KernelSpace A := kernel_mem.mpr ⟨(two A J).mp h,fun i j => by rw [expectation_is,he.center]⟩

lemma skim_formula {H : S.RealSpin} (Q : TableTwo H) : Line.skim H Q = (expectation S 4 (Q.val 0 0)).re := by
  change (average S 0 (Q.val 0 0)).re = _
  rw [expectation_is,average_at]

/-- `FreeTests.div_kernel` checks gradients of the response to a point
probe. Here that derivative is of the actual pair of fields, so vanishes
in divergence exactly on the W supplied with the comparator. -/
lemma tested_div (H : (Bel L).Hierarchy) (V : DiffPlan (Bel L)) (hV : V.Derivatives (Bel L)) (w : StressFlux.Coeff) (i j a : Axis) :
    Maxwell.grad a (StressFlux.signal L w i j i j a 0) (basis 0) =
      frontRead ![ (⟨4, fromPol (Bel L) (StressFlux.pair G i j i j)⟩ : (Bel L).Tag) ]
        (axisLine (basis 0)) 5 (V.deriv 4 a (material (Bel L) w a 0)) := by
  let Q := fromPol (Bel L) (StressFlux.pair G i j i j)
  let q : Fin 1 → (Bel L).Tag := ![⟨4,Q⟩]
  let B := material (Bel L) w a 0
  let x : Points 1 := 0
  have hx (z : E4) : Points.cons z x = axisLine z := by ext1 h; fin_cases h <;> rfl
  have hz : Points.cons (basis 0) x ∈ conf _ := (hx _) ▸ axisLine_in base_ne
  have ht := Work.A01.D_cons H.smooth V hV B q hz a
  rw [front_eval]
  suffices h : StressFlux.signal L w i j i j a 0 = fun z => (Bel L).useAt _ (Points.cons z x) (Fin.cons ⟨4,B⟩ q) by rw [h]; rw [← hx]; exact ht
  unfold StressFlux.signal quad; funext z; rw [hx]
  congr 1; ext1 k; fin_cases k <;> rfl

lemma free_closure (H : (Bel L).Hierarchy) (V : DiffPlan (Bel L)) (hV : V.Derivatives (Bel L)) (h : G.Simple) (hw : V.Orientation H.spin) :
    Surjective (Line.closureMap hw) ∧ Module.finrank ℝ (Line.closureMap hw).ker = 1 := by
  let F : StressFlux.Coeff →ₗ[ℝ] (ℝ × TableOne H.spin) × ℝ :=
    (Line.closureMap hw ∘ₗ tableStress H.spin).prod (LinearMap.proj (R:=ℝ) (3:Fin 4))
  have he : Injective F := by
    apply LinearMap.ker_eq_bot.mp
    refine LinearMap.ker_eq_bot'.mpr fun w hz => ?_
    have hc := congr_arg (fun z : (ℝ × TableOne H.spin) × ℝ => z.1.1) hz
    have hq := congr_arg (fun z : (ℝ × TableOne H.spin) × ℝ => z.1.2.val 0) hz
    have h3 : w 3 = 0 := congr_arg Prod.snd hz
    change Line.skim _ (tableStress H.spin w)=0 at hc
    rw [skim_formula, tableStress_material, expectation_is, oneStress_formula] at hc
    change (∑ a, V.deriv 4 a (material (Bel L) w a 0)) = 0 at hq
    rw [div_kernel (L:=L) h w hc ?_,h3,zero_smul]
    intro i j
    simp_rw [tested_div H V hV, ← map_sum,hq,map_zero]
  -- The codomain cost has ≤ 1+2+1 free real dimensions by the
  -- accepted `dim_free_five` (already after imposing Maxwell equations).
  have ht := LinearMap.finrank_le_finrank_of_injective he
  have hT := dim_free_five (L:=L) h H.spin
  rw [Module.finrank_fin_fun, Module.finrank_prod, Module.finrank_prod,Module.finrank_self] at ht
  have h0 : Module.finrank ℝ (TableOne H.spin) = 2 := by omega
  have hp := LinearMap.finrank_range_add_finrank_ker (K:=ℝ) (V:=StressFlux.Coeff) (V₂:= (ℝ × TableOne H.spin) × ℝ) F
  rw [LinearMap.ker_eq_bot.mpr he,finrank_bot,add_zero, Module.finrank_fin_fun] at hp
  have hu := LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq (S:=F.range) (by rw [hp,Module.finrank_prod,Module.finrank_prod,Module.finrank_self,h0]))
  have hs : Surjective (Line.closureMap hw) := fun y => by obtain ⟨x,hx⟩ := hu (y,0); exact ⟨_,congr_arg Prod.fst hx⟩
  have ha : Module.finrank ℝ (TableTwo H.spin)=4 := by
    rw [← (LinearEquiv.ofBijective (tableStress H.spin) (free_stress_bij h H.spin)).finrank_eq,Module.finrank_fin_fun]
  have hb := LinearMap.finrank_range_add_finrank_ker (K:=ℝ) (V:=↥(TableTwo H.spin)) (V₂:= ℝ × TableOne H.spin) (Line.closureMap hw)
  rw [LinearMap.range_eq_top.mpr hs,finrank_top,ha,Module.finrank_prod,Module.finrank_self,h0] at hb
  exact ⟨hs,by omega⟩

variable {H : (Bel L).Hierarchy} {V : DiffPlan (Bel L)}

lemma from_skim (hG : G.Simple) {B : TableTwo H.spin} (hb : Line.skim H.spin B = 0) : B.val∈KernelSpace H.spin := by
  obtain ⟨w,rfl⟩ := (free_stress_bij hG H.spin).2 B
  rw [skim_formula,tableStress_material,expectation_is,oneStress_formula] at hb
  refine kernel_mem.mpr ⟨(two _ _).mp (tableStress H.spin w).property,fun i j => ?_⟩
  rw [tableStress_material,expectation_is,oneStress_formula]; split
  next => exact Complex.ofReal_eq_zero.mpr hb
  rfl

private abbrev inclStress (H : S.RealSpin) : (↥(KernelSpace H)) →ₗ[ℝ] ↥(TableTwo H) :=
  (KernelSpace H).inclusion (p':=TableTwo H) (fun J h => (two H J).mpr (kernel_mem.mp h).1)

private abbrev inclVector (H : S.RealSpin) : ↥(Vectors H) →ₗ[ℝ] ↥(TableOne H) :=
  (Vectors H).inclusion (p':=TableOne H) (fun J h => (one H J).mpr h)

private def toeKer (h : S.Hierarchy) (V : DiffPlan S) (hw : V.Orientation h.spin) :
    (currentDiv V h.spin hw).ker →ₗ[ℝ] (Line.closureMap hw).ker :=
  ((inclStress h.spin).comp (currentDiv V h.spin hw).ker.subtype).codRestrict _ (fun v => by
    rw [LinearMap.mem_ker]; apply Prod.ext
    · change Line.skim h.spin (inclStress h.spin v.val)=0
      rw [skim_formula]
      change (expectation S 4 (v.val.val 0 0)).re=0
      rw [(kernel_mem.mp v.val.property).2]; rfl
    apply Subtype.ext
    change StressFlux.nabla V v.val.val=0
    exact congr_arg Subtype.val (LinearMap.mem_ker.mp v.property))

private lemma toe_surj (hG : G.Simple) (hw : V.Orientation H.spin) : Surjective (toeKer H V hw) := by
  intro y
  have hy := LinearMap.mem_ker.mp y.property
  let B : KernelSpace H.spin := ⟨y.val.val,from_skim (H:=H) hG (congr_arg Prod.fst hy)⟩
  have hB : B∈(currentDiv V H.spin hw).ker := by
    have hp := congr_arg (fun x => (Prod.snd x : TableOne H.spin).val) hy
    exact LinearMap.mem_ker.mpr (Subtype.ext hp)
  exact ⟨⟨B,hB⟩,Subtype.ext (Subtype.ext rfl)⟩

private def freeD (hG : G.Simple) (hw : V.Orientation H.spin) : (currentDiv V H.spin hw).ker ≃ₗ[ℝ] (Line.closureMap hw).ker :=
  LinearEquiv.ofBijective (toeKer H V hw) ⟨fun _ _ e => Subtype.ext (Subtype.ext (congr_arg (fun z : (Line.closureMap hw).ker => z.val.val) e)),
    toe_surj hG hw⟩

/-- The accepted low finite gradient and H comparison suppliers pay
both linear-algebra receipts on the same W which passed the actual
separated derivative tests. No coupling dependence or σ frame assumed. -/
theorem free_rank (hV : V.Derivatives (Bel L)) (hG : G.Simple) (hw : V.Orientation H.spin) :
    Surjective (currentDiv V H.spin hw) ∧ Module.finrank ℝ ↥(LinearMap.ker (currentDiv V H.spin hw))=1 := by
  obtain ⟨hs,hk⟩ := free_closure H V hV hG hw
  refine ⟨fun x => ?_,(freeD (H:=H) hG hw).finrank_eq.trans hk⟩
  obtain ⟨Y,hH⟩ := hs (0,inclVector H.spin x)
  have hi := congr_arg (fun x => (Prod.snd x : TableOne H.spin).val) hH
  exact ⟨⟨Y.val,from_skim (H:=H) hG (congr_arg Prod.fst hH)⟩,Subtype.ext hi⟩

/-- Remove the Divergence input on this route (normalized `a` coming
from `B70FurtherConnections`). `τ` is real in that theorem, we don't
need its sign in doing this carrier calculation. -/
theorem bills_free {C : Family G} (h : G.Simple) (a : FreeInput C) (τ : ℝ)
    (hw : a.T.J=τ • material (Climb.Bel C.book) weyl) : a.Divergence := by
  obtain ⟨ho,hl⟩ := free_rank (H:=a.kernels) a.lit.pales h a.lit.hers
  apply a.sourced ho hl
  rw [hw]
  apply Submodule.smul_mem
  change (tableStress a.kernels.spin weyl).val∈_
  apply from_skim (H:=a.kernels) h
  rw [skim_formula,tableStress_material,expectation_is,oneStress_formula]; rfl
end YM.Further.PhysicalPeriodLimitF933
