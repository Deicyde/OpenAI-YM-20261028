import YM.Push.FREE_RESOLVENT.Envelope

/-!
# Flat Taylor tensors with all exponential path payments in the input slots

On the actual affine ℓ_R column (transport by Vbar; NOT pretending
to differentiate the transport in the fine a slot as if this were ℓ^U k(U)).
Unordered lineage labels may have repeated paths; the budget used here is
literal sum of all of them. A local rank or stencil promise could not pay
it. Use finite-order `ContDiffAt` at flat and an auxiliary global real
extension to take ordinary `iteratedFDeriv`. Keep Taylor normalization with
no factorial.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FreeResolvent.Affine
open Lattice Wilson RG Matrix Laurent Bloch Exterior Precision Tree Bid Work.F03 TestD Filter Function Set
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
variable {G : Gauge} {f c n : Side} {S : StepData c f} {k : ℕ} {σ V A : ℝ}

/-- Curvature-coordinate bilinear at two endpoint matrices. -/
def connect (i j : G.ColorIndex) : G.Mat →L[ℝ] G.Mat →L[ℝ] ℝ := by
  let L := LinearMap.mk₂ ℝ (fun x y : G.Mat => G.projectColor (x*G.colorMat (EuclideanSpace.basisFun G.ColorIndex ℝ j)*y) i)
    (fun _ _ _ => by simp only [Matrix.add_mul,map_add,PiLp.add_apply])
    (fun _ _ _ => by simp only [Matrix.smul_mul,map_smul, PiLp.smul_apply])
    (fun _ _ _ => by simp only [Matrix.mul_add,map_add, PiLp.add_apply])
    (fun _ _ _ => by simp only [Matrix.mul_smul,map_smul, PiLp.smul_apply])
  exact LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap.comp L)

private def cord {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (L : E →L[ℝ] E →L[ℝ] ℝ) :=
  ‖L‖
private lemma cord_nn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (L : E →L[ℝ] E →L[ℝ] ℝ) :
    0 ≤ cord L := norm_nonneg L

def ridge (G : Gauge) : ℝ := ∑ i : G.ColorIndex, ∑ j : G.ColorIndex, cord (E:=G.Mat) (connect i j)
lemma ridge_nn (G : Gauge) : 0 ≤ ridge G := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => cord_nn (E:=G.Mat) (connect i j)
lemma ridge_le (i j : G.ColorIndex) : cord (E:=G.Mat) (connect (G:=G) i j) ≤ ridge G :=
  (Finset.single_le_sum (fun b _ => cord_nn (E:=G.Mat) (connect i b)) (Finset.mem_univ j)).trans (Finset.single_le_sum
    (fun a _ => Finset.sum_nonneg (fun b _ => cord_nn (E:=G.Mat) (connect a b))) (Finset.mem_univ i))

def elbow (G : Gauge) (k : ℕ) (σ : ℝ) := 2^k*(ridge G*(patchMoney G k (σ/2) (spaceD G k) k)^2)
lemma elbow_nn (G : Gauge) (k : ℕ) (σ : ℝ) : 0 ≤ elbow G k σ := by unfold elbow; have := ridge_nn G; positivity

lemma path_ceiling (k : ℕ) (S : StepData c f) (s : Signed) (i j : tile G f) (q : RG.Slot)
    (hs : 0 < σ) : Ceiling k (elbow G k σ * Real.exp (σ*q.length)) (fun y => element (rawBackdrop S s y) i j q) := by
  unfold element
  split
  · let R := patchMoney G k (σ/2) (spaceD G k) k
    let E := Real.exp (σ/2*q.walk.length)
    have hr : 0 ≤ R := patch_nn _ k (by linarith) (space_nn ..) k
    have hR : 0 ≤ R*E := mul_nonneg hr (Real.exp_pos _).le
    have ht : Ceiling k (R*E) (fun B : Vec G c 1 => G.mat (travel (rawBackdrop S s B) i.1 q.walk)) := tapestry k S s _ _ (half_pos hs)
    have he := ht.mul (star_ceiling ht) (connect (G:=G) i.2.2 j.2.2) hR hR
    apply he.mono; unfold elbow
    calc
      _ ≤ 2^k * (ridge G*(R*E)*(R*E)) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (ridge_le i.2.2 j.2.2) hR) hR) (by positivity)
      _ = elbow G k σ*Real.exp (σ*q.walk.length) := by rw [show Real.exp (σ*q.walk.length)=E*E by
          unfold E; rw [← Real.exp_add]; congr 1; ring]; unfold elbow R; ring
      _ ≤ elbow G k σ*Real.exp (σ*q.length) := by
        exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_left (by
          unfold RG.Slot.length; simp) hs.le)) (elbow_nn ..)
  apply (Ceiling.ceiling_const (0:ℝ)).mono; rw [norm_zero]; exact mul_nonneg (elbow_nn ..) (Real.exp_pos _).le

def sheetEdge (S : StepData c f) (s : Signed) (W : PathData G) (r : Admit) (i j : tile G f) (q : ℕ) (B : Vec G c 1) :=
  let p := W.row (plaqEquiv.symm i.2.1) q
  if r p.2 then p.1 * element (rawBackdrop S s B) i j p.2 else 0

def slotPrice (G : Gauge) (k : ℕ) (σ : ℝ) (p : ℝ × RG.Slot) := (|p.1| * Real.exp (σ*p.2.length))*elbow G k σ
lemma slot_nn (p : ℝ × RG.Slot) : 0 ≤ slotPrice G k σ p := mul_nonneg (by positivity) (elbow_nn ..)

lemma sheetEdge_ceiling (S : StepData c f) (s : Signed) (W : PathData G) (r : Admit) (i j : tile G f)
    (q k : ℕ) (hs : 0 < σ) :
    Ceiling k (slotPrice G k σ (W.row (plaqEquiv.symm i.2.1) q)) (sheetEdge S s W r i j q) := by
  let p := W.row (plaqEquiv.symm i.2.1) q
  by_cases h : r p.2=true
  · rw [show sheetEdge S s W r i j q = (fun B => p.1 • element (rawBackdrop S s B) i j p.2) from funext fun _ => if_pos h]
    apply ((path_ceiling k S s i j p.2 hs).scale _).mono
    unfold slotPrice p; rw [Real.norm_eq_abs]; apply le_of_eq; ring
  rw [show sheetEdge S s W r i j q = (fun _ => 0) from funext fun _ => if_neg h]; apply Ceiling.mono (Ceiling.ceiling_const _)
  rw [norm_zero]; exact slot_nn _

lemma same_edge (S : StepData c f) (s : Signed) (W : PathData G) (r : Admit) :
    ∀ᶠ B in 𝓝 0, ∀ i j q, sheetEdge S s W r i j q B = edgework S s W r i j q B := by
  filter_upwards [returns (G:=G) S s] with B h
  intro i j q; unfold sheetEdge edgework; rw [h]

lemma polar_edge (S : StepData c f) (s : Signed) (W : PathData G) (r : Admit) (i j : tile G f) (q k : ℕ)
    (hs : 0 < σ) : ContDiffAt ℝ k (edgework S s W r i j q) 0 := by
  exact (sheetEdge_ceiling S s W r i j q k hs).smooth.contDiffAt.congr_of_eventuallyEq ((same_edge S s W r).mono fun _ h => (h i j q).symm)



/-- Only the exponential row hypothesis of W is needed by these derivative estimates. -/
def Sheet (W : PathData G) (σ M : ℝ) := ∀ p, RG.SumBudget (fun i => |(W.row p i).1| * Real.exp (σ*(W.row p i).2.length)) M

section proper
variable {W : PathData G} {σ M : ℝ} (hs : 0 < σ) (hW : Sheet W σ M)
variable (S : StepData c f) (s : Signed) (r : Admit) (i j : tile G f)

include hs hW
lemma proper_sheet (k : ℕ) : Ceiling k (M*elbow G k σ) (fun B : Vec G c 1 => ∑' q, sheetEdge S s W r i j q B) := by
  let T (q) := slotPrice G k σ (W.row (plaqEquiv.symm i.2.1) q)
  let u : ℕ → ℕ → ℝ := fun _ => T
  let F := sheetEdge S s W r i j
  have hf q : Ceiling k (T q) (F q) := sheetEdge_ceiling S s W r i j q k hs
  have hw : Summable T := (hW _).2.1.mul_right _
  have ht (l : ℕ) : (l:ℕ∞) ≤ (k:ℕ) → Summable (u l) := fun _ => hw
  have he (l q : ℕ) (B) (h : (l:ℕ∞) ≤ (k:ℕ)) : ‖iteratedFDeriv ℝ l (F q) B‖ ≤ u l q :=
    (hf q).op l B (by exact_mod_cast h)
  have hg q : ContDiff ℝ ((k:ℕ∞):ℕ∞ω) (F q) := (hf q).smooth
  constructor
  · exact contDiff_tsum hg ht he
  intro l B hl
  have hh : (l:ℕ∞) ≤ (k:ℕ∞) := by exact_mod_cast hl
  rw [iteratedFDeriv_tsum_apply hg ht he hh B]
  have hy := Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => he l i B hh) hw
  apply (norm_tsum_le_tsum_norm hy).trans ((hy.tsum_le_tsum (fun i => he l i B hh) hw).trans ?_)
  unfold u T slotPrice; rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right (hW _).2.2 (elbow_nn ..)

omit hs hW in
lemma written : (fun B => ∑' q, sheetEdge S s W r i j q B) =ᶠ[𝓝 0] (fun B => tracks S s W r B i j) := by
  filter_upwards [same_edge S s W r] with x h; exact tsum_congr (h i j)

lemma tracks_smooth (k : ℕ) : ContDiffAt ℝ k (tracks S s W r) 0 := by
  apply TestD.rectangle_smooth; intro i j
  exact (proper_sheet hs hW S s r i j k).smooth.contDiffAt.congr_of_eventuallyEq (written (W:=W) S s r i j).symm

lemma track_polar {τ : Type*} (l : List τ) (v : τ → Vec G c 1) :
    HasSum (fun q => jet v (edgework S s W r i j q) l 0) (jet v (tracks S s W r) l 0 i j) := by
  let k := l.length
  let F := sheetEdge S s W r i j
  let f := fun B => ∑' q, F q B
  let T (q) := slotPrice G k σ (W.row (plaqEquiv.symm i.2.1) q)
  let u : ℕ → ℕ → ℝ := fun _ => T
  have hf q : Ceiling k (T q) (F q) := sheetEdge_ceiling S s W r i j q k hs
  have hw : Summable T := (hW _).2.1.mul_right _
  have ht (l : ℕ) : (l:ℕ∞) ≤ (k:ℕ∞) → Summable (u l) := fun _ => hw
  have he (l q : ℕ) (B) (h : (l:ℕ∞) ≤ (k:ℕ∞)) : ‖iteratedFDeriv ℝ l (F q) B‖ ≤ u l q :=
    (hf q).op l B (by exact_mod_cast h)
  have hg q : ContDiff ℝ ((k:ℕ∞):ℕ∞ω) (F q) := (hf q).smooth
  rw [← TestD.entry v l (tracks_smooth hs hW S s r k) i j, ← identical v (written (W:=W) S s r i j) l]
  have hh : HasSum (fun q => iteratedFDeriv ℝ k (F q) 0) (iteratedFDeriv ℝ k f 0) := by
    rw [iteratedFDeriv_tsum_apply hg ht he (k:=k) le_rfl 0]
    exact (Summable.of_norm_bounded hw (fun q => he k q 0 le_rfl)).hasSum
  let L := ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Vec G c 1) ℝ (v ∘ l.get)
  have h1 : HasSum (fun q => jet v (F q) l 0) (jet v f l 0) := L.hasSum hh
  have h2 (q : ℕ) : jet v (edgework S s W r i j q) l 0=jet v (F q) l 0 := identical v (A:=edgework S s W r i j q) (B:=F q) ((same_edge S s W r).mono fun _ h => (h i j q).symm) l
  simp_rw [h2]; exact h1
end proper
end YM.FreeResolvent.Affine
