import YM.Pert.Align.Cancel
import YM.Pert.Align.Schedule

/-! Linearized key covariance with inverse for same Gaussian density and subtraction at the same mark. -/
set_option autoImplicit false
set_option maxRecDepth 4000
noncomputable section
namespace YM.Pert.Align
open Lattice Orb Matrix Full Filter Function Topology Maxwell
variable {G : Gauge} {n : Side}

def picks (f : Module.Dual ℝ (Potential G n)) : Coords G n := f ∘ seed
lemma dot_expand (f : Module.Dual ℝ (Potential G n)) (x : Coords G n) : picks f ⬝ᵥ x = f (expand G n x) := by
  rw [expand_eq,map_sum,dotProduct,picks]; apply Finset.sum_congr rfl; intro i _; rw [map_smul,smul_eq_mul,Function.comp_apply,mul_comm]
lemma dot_inverse (f g : Module.Dual ℝ (Potential G n)) : picks f ⬝ᵥ (covarianceM G n *ᵥ picks g) = jointB G n f g := by
  let z := covarianceM G n *ᵥ picks g
  have he (t : Potential G n): kernelEquiv G n (expand G n z) t = g t := by
    let v := (expand G n).symm t
    rw [←show expand G n v=t from (expand G n).apply_symm_apply t]
    change form (expand G n z) (expand G n v) = g (expand G n v)
    dsimp only [z]
    rw [form_symm,←scalar_formula,←dot_expand,covarianceM,mulVec_mulVec, (precision G n).mul_nonsing_inv (Matrix.isUnit_iff_isUnit_det _ |>.1 (precision_pos ..).isUnit),one_mulVec,dotProduct_comm]
  have hv := (kernelEquiv G n).eq_symm_apply.mpr (LinearMap.ext he)
  rw [dot_expand,hv]
  change f ((kernelEquiv G n).symm g) = covar _ _
  change covar g f = _; rw [covar_formula,covar_formula]; apply form_symm

def kTape (a : Labels.Key G) := (Labels.axes G a.1).coord a.2 ∘ₗ Maxwell.gaugeJet
variable (h : ℝ)
def kField (x : Site n) (a : Labels.Key G) : Coords G n := picks ((Labels.axes G a.1).coord a.2 ∘ₗ YM.Pert.Bare.slope h x a.1)
lemma key_orb (x y : Site n) (a b : Labels.Key G) : kField h x a ⬝ᵥ (covarianceM G n *ᵥ kField h y b) = orbital h x y ((Labels.axes G a.1).coord a.2) ((Labels.axes G b.1).coord b.2) := by unfold kField orbital; rw [dot_inverse]
lemma tay_tape (a b : Labels.Key G) (z : E4) (hz : z≠0) : tayForm z hz ((Labels.axes G a.1).coord a.2) ((Labels.axes G b.1).coord b.2) = legKernel (kTape a) (kTape b) z := rfl
variable {ι : Type} [DecidableEq ι] (o : ι→Site n)
def corrected (i l : ι) (a b : Labels.Key G) : ℝ :=
  kField h (o i) a ⬝ᵥ (covarianceM G n *ᵥ kField h (o l) b) - (if i=l then link h a b else 0)
def indirect (z : ι → E4) (i l : ι) (a b : Labels.Key G) : ℝ := if i=l then 0 else legKernel (kTape a) (kTape b) (z i-z l)
lemma k_lin (x : Site n) (a : Labels.Key G) (v : Coords G n) : PowerSeries.constantCoeff (YM.Pert.Bare.seriesLex h x v a) = (kField h x a ⬝ᵥ v : ℝ) := by rw [kField,dot_expand]; exact YM.Pert.Bare.constant_lex ..
variable (T : Itinerary)
lemma corrected_limit (p : ∀ i:ℕ,ι→Site (T.period i)) (z : ι→E4) (hz : Injective z) (hs : ∀ j, Home T (fun i=>p i j) (z j)) (h4 : ∀ i,4∣(T.period i).val) (j k : ι) (a b : Labels.Key G): Tendsto (fun i=> corrected (T.gap i) (p i) j k a b) atTop (𝓝 (indirect z j k a b)) := by
  by_cases H : j=k
  · subst k; simp_rw [corrected,indirect, if_true,key_orb,shell_exact]; exact orbit_contact T _ (z:=z j) (finale_home T _ _ _ _ _ (hs j) (hs j) h4) _ _
  have hp : z j-z k ≠0 := sub_ne_zero.mpr (hz.ne H)
  simp_rw [corrected,indirect,if_neg H,sub_zero,key_orb,←tay_tape a b _ hp]
  exact orbit_limit T _ _ hp (scene_home T _ _ _ _ (hs j) (hs k)) (finale_home T _ _ _ _ _ (hs j) (hs k) h4) _ _

abbrev wall (G:Gauge) (d : ℕ):= {r : Slot G // r.1 ≤ d}
instance fit {d : ℕ} : Fintype (wall G d) := by
  let f (e : wall G d) : (i : Fin (d+1)) × Fin (legDim G i.val) := ⟨⟨e.val.1,Nat.lt_succ_of_le e.property⟩, e.val.2⟩
  exact Fintype.ofInjective f (fun i j h => Subtype.ext (Sigma.ext (congrArg (Fin.val ∘ Sigma.fst) h) ((Sigma.ext_iff.mp h).2)))
def shellCharge {d:ℕ} (z : ι→E4) (u v : ι × wall G d): ℂ := if u.1=v.1 then 0 else Wick.entry u.2.val v.2.val (z u.1) (z v.1)
end YM.Pert.Align
