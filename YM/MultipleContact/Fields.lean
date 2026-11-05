import YM.Next.UV_STRESS.Arrange
import YM.Spec.Closed
import YM.Work.A15

/-
Physical filtration splits and single-field detector maps. All moments use Table.useAt of the same kernel or phases respecting its quotient.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MultipleContact
open Set Function Filter MeasureTheory Table Extraction Spec
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff

variable {G:Gauge}{L:Register G}{S:Table L}{d h:ℕ}
variable {P: DiffPlan S} {X:Rotation S}

structure Splitting (P : DiffPlan S) where
  down (d:ℕ) : S.Field (d+1) →ₗ[ℂ] S.Field d
  left (d x) : down d (P.rise (Nat.le_succ d) x)=x

structure Splitting.Covariant (B : Splitting P) (X:Rotation S) (ρ:S.RealSpin) : Prop where
  real d x : S.conj ρ d (B.down d x) = B.down d (S.conj ρ (d+1) x)
  act d K x : X.act d K (B.down d x) = B.down d (X.act (d+1) K x)

section Average
attribute [local instance] YM.Work.A15.compact_ortho

local instance : SecondCountableTopology Ortho := by
  haveI : SecondCountableTopology M4 :=
    inferInstanceAs (SecondCountableTopology (Axis → Axis → ℝ))
  exact inferInstanceAs
    (SecondCountableTopology ↥((Matrix.unitaryGroup Axis ℝ : Set M4)))

local instance : MeasurableSpace Ortho := borel Ortho
local instance : BorelSpace Ortho := ⟨rfl⟩

private def allO : TopologicalSpace.PositiveCompacts Ortho :=
  ⟨⟨Set.univ,isCompact_univ⟩,by simp⟩
private def μ : Measure Ortho := Measure.haarMeasure allO
local instance : μ.IsHaarMeasure := by unfold μ; infer_instance
local instance : IsProbabilityMeasure μ :=
  ⟨@Measure.haarMeasure_self Ortho _ _ _ _ _ allO⟩

variable (B : Splitting P)
variable {ρ:S.RealSpin} (hX:X.Laws P ρ)
include hX

private lemma ct_act {α:Type*}[TopologicalSpace α] (f:α→ Ortho)(g:α→ S.Field d)
    (hf:Continuous f)(hg:Continuous g): Continuous (fun y:α=>X.act d (f y) (g y)):=by
  let b := Module.finBasis ℂ (S.Field d)
  have h' (y) : X.act d (f y) (g y)= ∑ i,b.coord i (g y) • (X.act d (f y) (b i)):=by
     conv_lhs => rw [← b.sum_repr (g y)]
     simp only [map_sum,map_smul]; rfl
  simp_rw [h']
  refine continuous_finsetSum _ fun i _ => ?_
  exact ((b.coord i).continuous_of_finiteDimensional.comp hg).smul ((hX.spin d (b i)).comp hf)

private def orbit_down : S.Field (d+1) → Ortho → S.Field d := fun x K=> X.act d K (B.down d (X.act (d+1) K⁻¹ x))
private lemma orbit_live (x:S.Field (d+1)) : Integrable (orbit_down B (X:=X) x) μ:=by
  refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.of_compactSpace _) (μ:=μ)
  exact ct_act hX _ _ continuous_id ((B.down d).continuous_of_finiteDimensional.comp (ct_act hX _ _ continuous_inv continuous_const))

private def mean : S.Field (d+1) →ₗ[ℂ] S.Field d where
  toFun x := ∫ K:Ortho, orbit_down B (X:=X) x K ∂μ
  map_add' x y := by
    simp_rw [orbit_down, map_add]
    exact integral_add (orbit_live B hX x) (orbit_live B hX y)
  map_smul' c x := by
    simp_rw [orbit_down,map_smul]
    exact MeasureTheory.integral_smul ..

private lemma map_mean {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : S.Field d →ₗ[ℝ] E) (x) :
    F (mean B hX x) = ∫ K:Ortho, F (orbit_down B (X:=X) x K) ∂μ := by
  exact ((LinearMap.toContinuousLinearMap F).integral_comp_comm (orbit_live B hX x)).symm

omit hX in
private def realConj (ρ : S.RealSpin) (d:ℕ) : S.Field d →ₗ[ℝ] S.Field d where
  toFun := S.conj ρ d
  map_add' := map_add _
  map_smul' r u := by
    change S.conj ρ d (r • u) = r • S.conj ρ d u
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ),map_smulₛₗ]; simp

private lemma orthos (H : ∀ d x,S.conj ρ d (B.down d x) = B.down d (S.conj ρ (d+1) x)) :
    ∃ B : Splitting P, B.Covariant X ρ := by
  let U : Splitting P := ⟨fun _=>mean B hX,fun d x=>by
    change (∫ K:Ortho, X.act d K (B.down d (X.act (d+1) K⁻¹ (P.rise _ x))) ∂μ)=x
    have he (K:Ortho) (y:S.Field d): X.act d K (X.act d K⁻¹ y)=y:=by rw [← hX.group,mul_inv_cancel,hX.fixes]
    simp_rw [hX.filtered,B.left,he]
    simp⟩
  refine ⟨U,fun d x=> ?_,fun d P x=> ?_⟩
  · exact (map_mean B hX (realConj ρ d) x).trans (show (∫ K:Ortho, S.conj ρ d (orbit_down B (X:=X) x K) ∂μ) = _ from by
         simp_rw [orbit_down,hX.real,H,hX.real]; rfl)
  refine (map_mean B hX (((X.act d P).toLinearMap).restrictScalars ℝ) x).trans ?_
  trans ∫ K:Ortho, orbit_down B (X:=X) (X.act (d+1) P x) (P*K) ∂μ
  · exact integral_congr_ae (Eventually.of_forall fun K=> by
         change X.act d P (X.act d K (B.down d (X.act (d+1) K⁻¹ x))) = orbit_down _ _ _
         simp [orbit_down,mul_inv_rev,← hX.group,mul_assoc])
  exact (measurePreserving_mul_left μ P).integral_comp (Homeomorph.mulLeft P).measurableEmbedding
    (orbit_down B (X:=X) (X.act (d+1) P x))

end Average
lemma splits (H:S.Hierarchy) (hr:P.Inclusions S)(hc:P.Orientation H.spin) (hX:X.Laws P H.spin) :
    ∃ B:Splitting P,B.Covariant X H.spin :=by
  choose f hf hx hu using fun d:ℕ=>Next.UVStress.signed_section (H:=H) (Nat.le_succ d) hr hc
  exact orthos (P:=P) ⟨f,hf⟩ hX fun d x=>(hx d x).symm
namespace Splitting
variable (B:Splitting P)
def top (v:ℕ): S.Field v→ₗ[ℂ] S.Field v:= match v with
 | 0=>LinearMap.id
 | n+1=> LinearMap.id - ((P.rise (Nat.le_succ n)).comp (B.down n))
def part (w : ℕ) : (h : ℕ)→ S.Field h →ₗ[ℂ] S.Field w
 | 0=> if e:0=w then e ▸ top B 0 else 0
 | n+1=> if e:n+1=w then e ▸ top B (n+1) else (part w n).comp (B.down n)

theorem top_part (h:ℕ):B.part h h=B.top h:=by cases h <;> simp [part]
theorem beyondZero {w h:ℕ}(hw:h<w):B.part w h=0:=by
     induction h with
     | zero=> simp [part,ne_of_lt hw]
     | succ k ih=> rw [part,dif_neg (ne_of_lt hw),ih (by omega)]; simp

theorem part_top {w h:ℕ}(hw:w≠h):B.part w h ∘ₗ B.top h=0:=by
     apply LinearMap.ext; intro x
     cases h with
     | zero=> simp [part,Ne.symm hw]
     | succ k=>
         have he : B.top (k+1) x = x-P.rise (Nat.le_succ k) (B.down k x):=rfl
         rw [LinearMap.comp_apply,part,dif_neg (Ne.symm hw),LinearMap.comp_apply,he,map_sub,B.left,sub_self,map_zero,LinearMap.zero_apply]

theorem recombine (Hs : S.Symmetric)(hr:P.Inclusions S):
   ∀ (h:ℕ) (x:S.Field h), ∑ i:Fin (h+1), P.rise (show i.val ≤ h from i.isLt |> Nat.le_of_lt_succ) ((B.part i.val h) x)=x:=by
   intro h; induction h with
   | zero=>
           intro x
           rw [Fin.sum_univ_succ]; change P.rise (d:=0) le_rfl (B.part 0 0 x)+_=_
           rw [B.top_part,P.arrival Hs hr]; simp [top]
   | succ h ih=>
                 intro x
                 have he (w:Fin (h+1))(e:w.castSucc.val ≤ h+1):P.rise e ((B.part w.castSucc.val (h+1)) x)=P.rise (Nat.le_succ h) (P.rise (show w.val ≤ h from Nat.le_of_lt_succ w.isLt) ((B.part w.val h) (B.down h x))) := by
                    change P.rise (show w.val ≤ h+1 from e) ((B.part w.val (h+1)) x)=_
                    rw [part,dif_neg (by exact ne_of_gt w.isLt : h+1≠w.val),LinearMap.comp_apply,← P.transit Hs hr]
                 rw [Fin.sum_univ_castSucc]; simp_rw [he]
                 rw [← map_sum, ih (B.down h x)]
                 change P.rise _ (B.down _ _) + P.rise (le_refl (h+1)) ((B.part (h+1) (h+1)) x)=_
                 rw [B.top_part,P.arrival Hs hr]; unfold top
                 simp; -- rw [add_sub_cancel]

-- raising a slice into a larger horizon preserves its weight decomposition.
theorem part_rise (Hs : S.Symmetric)(hr:P.Inclusions S) {w h k:ℕ} (hwk:h≤k) (x:S.Field h):
    B.part w k (P.rise hwk x)=B.part w h x:=by
   induction k,hwk using Nat.le_induction with
   | base=>rw [P.arrival Hs hr]
   | succ k he ih=>
       rw [← P.transit Hs hr he (Nat.le_succ k)]
       by_cases hw:w=k+1
       · subst w
         rw [B.top_part,(B.beyondZero (by omega : h < k+1)),LinearMap.zero_apply]; unfold top
         simp [B.left]
       rw [part,dif_neg (Ne.symm hw),LinearMap.comp_apply,B.left,ih]

-- physical weights are ker(down) strata; weight 0 is the full lowest filtration space.
def stratum : (d:ℕ)→ Submodule ℂ (S.Field d)
 | 0=> ⊤
 | d+1=>LinearMap.ker (B.down d)

lemma top_mem {w h:ℕ} (x:S.Field h):B.part w h x∈B.stratum w:=by
    induction h with
    | zero=> cases w with
             | zero=> exact Submodule.mem_top
             | succ i=> simp [part]
    | succ h ih=>
        by_cases he:w=h+1
        · subst w; rw [top_part]; show _ ∈ LinearMap.ker _; unfold top
          simp [B.left]
        rw [part,dif_neg (Ne.symm he),LinearMap.comp_apply]; exact ih _
end Splitting
end YM.MultipleContact
