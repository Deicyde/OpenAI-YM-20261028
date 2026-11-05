import YM.Pert.Position.Board
import YM.Pert.Position.Actual
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
/-! Finite-position-scheme existence from pointwise leading-orbit rigidity. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 60000
set_option linter.unusedSectionVars false
open scoped Topology Classical
namespace YM.Pert.Position
open Set Function Filter Maxwell Labels MeasureTheory Topology Ward
variable {G : Gauge}
variable (F : Frames G) (d : ℕ)
variable {r : ℕ}
local notation "P" => (fun _ : Fin r => E F d)

abbrev visible (x : Points r) : MultilinearMap ℂ P ℂ := (freeTable F).classMoment (freeTable F) (fun _=> d) x
lemma visible_cont (p : Fin r→E F d) : ContinuousOn (fun x=>visible F d x p) (conf r) :=
  ((freeTable F).class_smooth _ (Maxwell.table_smooth _) (fun j=> (⟨d,p j⟩ : (freeTable F).Tag))).continuousOn

section test
variable (f : Test r)
def wickReading : MultilinearMap ℂ P ℂ where
  toFun p := f.applyTo (fun x=> visible F d x p)
  map_update_add' p i v w := by
    simp_rw [Test.applyTo,MultilinearMap.map_update_add,mul_add]
    exact integral_add (f.smearing (visible_cont F d _)) (f.smearing (visible_cont F d _))
  map_update_smul' p i c v := by
    simp_rw [Test.applyTo,MultilinearMap.map_update_smul, show ∀ x y : ℂ, x*(c • y)= c • (x*y) from fun x y=>show x*(c*y)=_ from mul_left_comm x c y]
    exact integral_smul .. -- test

lemma baring_formula (p : Fin r→E F d) :
    wickReading F d f p = ∑ z : Fin r→ChartIx F d, (∏ j, (baring F d).coord (z j) (p j)) * f.applyTo (fun x=> visible F d x (fun j=>baring F d (z j))) := by
  conv_lhs => rw [← funext fun j => (baring F d).sum_equivFun (p j)] -- might elaborate?
  rw [MultilinearMap.map_sum_finset, Fintype.piFinset_univ]; exact Finset.sum_congr rfl (fun v _ => MultilinearMap.map_smul_univ ..)

private def sampleMap : ContinuousMultilinearMap ℂ P ℂ :=
  ⟨wickReading F d f, by
   change Continuous (fun p=>wickReading F d f p)
   simp_rw [baring_formula]; apply continuous_finset_sum
   intro z _; apply Continuous.mul_const; apply continuous_finset_prod
   exact fun j _ => (((baring F d).coord (z j) |>.toContinuousLinearMap).continuous.comp (continuous_apply j))⟩
end test
structure Section where
  r : ℕ
  p : Fin r → E F d
  f : Test r

abbrev direction (q : Section F d) := ℝ × Buffer F d
-- differentiate a single continuous test
def current (q : Section F d) (B : Buffer F d) (x : Points q.r) := ∑ j : Fin q.r, (visible F d x) (Function.update q.p j (B.val (q.p j)))
def paths (p : Fin r→E F d) : Buffer F d →ₗ[ℝ] (Fin r→E F d) where
  toFun b j := b.val (p j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def feedback (q : Section F d) : Buffer F d →ₗ[ℝ] ℝ := Complex.reCLM.toLinearMap ∘ₗ ((sampleMap F d q.f).restrictScalars ℝ |>.linearDeriv q.p |>.toLinearMap) ∘ₗ paths F d q.p

theorem feedback_eq (q : Section F d) (b : Buffer F d) : feedback F d q b = Complex.re (∑ j : Fin q.r, wickReading F d q.f (Function.update q.p j (b.val (q.p j)))) := by
  dsimp only [feedback, LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
  change Complex.reCLM _ = _
  rw [ContinuousMultilinearMap.linearDeriv_apply]; apply congrArg Complex.re; apply Finset.sum_congr rfl; intro _ _; rfl
lemma current_read (q : Section F d) (b : Buffer F d) : feedback F d q b = Complex.re (q.f.applyTo (current F d q b)) := by
  rw [feedback_eq]; apply congrArg Complex.re
  unfold Test.applyTo current wickReading; simp only [MultilinearMap.coe_mk]
  simp_rw [Finset.mul_sum, integral_finsetSum _ (fun j _=> q.f.smearing (visible_cont F d _))]; rfl -- avoid unfold smearing targets

private lemma feedback_deriv (q : Section F d) (b : Buffer F d) :
    HasDerivAt (fun t : ℝ=> Complex.re (wickReading F d q.f (fun j=> motor F (t•b) (q.p j)))) (feedback F d q b) 0 := by
  let A := (sampleMap F d q.f).restrictScalars ℝ
  let y (t : ℝ) : Fin q.r → E F d := q.p + t • (paths F d q.p b)
  have hy : HasDerivAt y (paths F d q.p b) 0 := by
    unfold y; apply HasDerivAt.const_add; convert! (hasDerivAt_id (0:ℝ)).smul_const (paths F d q.p b) using 1; simp
  have hh : HasFDerivAt A (A.linearDeriv q.p) (y 0) := by rw [show y 0=q.p by simp [y]]; exact A.hasFDerivAt _
  have he := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 (hh.comp_hasDerivAt 0 hy)
  exact he

variable {k : ℕ} (s : Fin k → Section F d) (m : ℕ) (g : (Fin k → ℝ) →ₗ[ℝ] (Fin m→ℝ))
def assemble : Conditions F d m := ⟨k,fun i=>(s i).r,fun i=>(s i).p,fun i=>(s i).f,g⟩

lemma chart_deriv_formula (b : Buffer F d) :
    fderiv ℝ (chart (assemble F d s m g)) (white (assemble F d s m g),0) (0,b) = g (fun i=> feedback F d (s i) b) := by
  let Q := assemble F d s m g
  change fderiv ℝ (chart Q) (white Q,0) (0,b)=_
  let Z := fun t:ℝ=> (white Q,t•b)
  have hZ : HasDerivAt Z (0,b) 0 := by
     unfold Z; convert! (hasDerivAt_const (0:ℝ) (white Q) |>.prodMk ((hasDerivAt_id (0:ℝ)).smul_const b)) using 1;simp
  have he i (q : Buffer F d) : decode Q (white Q) (fun j=> motor F q (Q.columns i j)) = wickReading F d (s i).f (fun j=> motor F q ((s i).p j)) := by rw [baring_formula]; rfl
  have hf : chart Q ∘ Z = (g.toContinuousLinearMap ∘ fun t=> fun i : Fin k=> Complex.re (wickReading F d (s i).f (fun j=>motor F (t•b) ((s i).p j)))) := funext (fun t=> by unfold chart;dsimp [Z];apply congrArg g; apply funext; intro i; rw [he])
  have hw := g.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_pi.mpr fun i=>feedback_deriv F d (s i) b)
  have hz := ((chart_diff Q).differentiable (by simp) (Z 0)).hasFDerivAt.comp_hasDerivAt 0 hZ
  rw [hf] at hz; change _ = g.toContinuousLinearMap _; rw [← hw.deriv, hz.deriv, show Z 0=(white Q,0) by unfold Z; simp]

-- From scalar real readings to the tested complex identity.
def twistSec (q : Section F d) : Section F d := ⟨q.r,q.p,Complex.I • q.f⟩
lemma feedback_twist (q : Section F d) (b : Buffer F d) : feedback F d (twistSec F d q) b = -(q.f.applyTo (current F d q b)).im := by
  rw [current_read]; unfold twistSec -- include r mismatch
  change Complex.re (∫ x : Points q.r, (Complex.I • q.f x) * current F d q b x)= _
  simp_rw [smul_eq_mul,mul_assoc,integral_const_mul]; simp [Test.applyTo, Complex.mul_re]

def Frozen : Prop := ∀ b : Buffer F d, (∀ (r : ℕ) (p : Fin r→E F d) (x : Points r), x∈conf r → ∑ j : Fin r, visible F d x (Function.update p j (b.val (p j))) = 0) → b=0
lemma detected (h : Frozen F d) (b : Buffer F d) (hc : ∀ q : Section F d, feedback F d q b=0) : b=0 := h b (fun r p x hx=> by
  let K (x) := ∑ j : Fin r, visible F d x (Function.update p j (b.val (p j)))
  have hk : ContinuousOn K (conf r) := continuousOn_finset_sum _ (fun _ _=>visible_cont F d _)
  have he (f : Test r) : f.applyTo K=0 := by
    let q : Section F d := ⟨r,p,f⟩
    have ht := feedback_twist F d q b; have hu := current_read F d q b; rw [hc] at ht hu
    apply Complex.ext
    · exact Eq.symm hu
    change (q.f.applyTo (current F d q b)).im=0; exact neg_eq_zero.mp ht.symm
  exact ((Test.weak_null hk).1 he hx))

local notation "W" => Buffer F d
lemma finite_detectors (hf : Frozen F d) : ∃ (k : ℕ) (s : Fin k→Section F d), (LinearMap.pi (fun i=> feedback F d (s i))).ker = ⊥ := by
  let K := feedback F d
  obtain ⟨s,hs,he,_⟩ := Submodule.exists_fun_fin_finrank_span_eq ℝ (Set.range K)
  choose t ht using hs
  have hg i : K (t i)=s i := ht i
  refine ⟨_,t, le_antisymm (fun b hb=> ?_) bot_le⟩
  have hx (q) (hq : q∈Submodule.span ℝ (Set.range K)) : q b=0 := by
    rw [←he] at hq
    -- use annihilation of span
    induction hq using Submodule.span_induction with
    | mem v hv => obtain ⟨i,rfl⟩ := hv; rw [←hg i]; exact congrFun (LinearMap.mem_ker.1 hb) i
    | zero => exact rfl
    | add v z _ _ h g => exact congr_arg₂ (·+·) h g |>.trans (add_zero _)
    | smul r v _ h => exact congrArg (r • ·) h |>.trans (smul_zero r)
  exact (detected F d hf b fun q=> hx _ (Submodule.subset_span ⟨q,rfl⟩)) ▸ Submodule.zero_mem _

lemma square_of_frozen (h : Frozen F d) : ∃ (k : ℕ) (s : Fin k→Section F d) (m : ℕ) (g : (Fin k→ℝ) →ₗ[ℝ] (Fin m→ℝ)), square (assemble F d s m g) ∧ (∀ i, ∃ k : Test ((s i).r), (⇑k : _→ℂ)= (⇑(s i).f : _→ℂ)) := by
  obtain ⟨k,s,h⟩ := finite_detectors F d h
  let f₁ : W →ₗ[ℝ] (Fin k → ℝ) := LinearMap.pi (fun i => feedback F d (s i))
  have hk : f₁.ker=⊥ := h
  obtain ⟨g',hg⟩ := LinearMap.exists_leftInverse_of_injective (K:=ℝ) (V:=W) (V':=Fin k→ℝ) f₁ hk
  letI freeW : Module.Free ℝ W := @Module.Free.of_divisionRing ℝ (Buffer F d) _ _ _
  let B := Module.finBasis ℝ W
  let e : W ≃ₗ[ℝ] (Fin (Module.finrank ℝ W) → ℝ) := B.equivFun
  let H : W ≃L[ℝ] (Fin (Module.finrank ℝ W) → ℝ) := LinearEquiv.toContinuousLinearEquiv (𝕜:=ℝ) (E:=W) (F:=Fin _ → ℝ) e
  let g := H.toLinearMap ∘ₗ g'
  let Q := assemble F d s _ g
  have hs : square Q := by
    refine ⟨H, ?_⟩; ext1 b
    change H b = fderiv ℝ (chart Q) (white Q,0) (0,b)
    rw [chart_deriv_formula]; change H b = H (_)
    exact congrArg H (congrArg (fun (a : W→ₗ[ℝ] W)=>a b) hg).symm
  exact ⟨k,s,_,g,hs,fun i=> ⟨(s i).f,rfl⟩⟩
end YM.Pert.Position
