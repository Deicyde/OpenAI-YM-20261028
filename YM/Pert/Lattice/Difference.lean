import YM.Pert.Lattice.Plate
/-! Finitely shifted finite-order curvature differences transported to an actual source site.
Native scalar division by the link coupling once per slot is put in the later field reader. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Bare
open Lattice Function Filter Orb
open scoped Topology ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {j : ℕ}

def walk (r : Fin j→Axis) (s : Finset (Fin j)) := (s.toList.map fun i => posDir (r i))
lemma displaced {X : Type*} [AddCommGroup X] [One X] (r : Fin j → Axis) (s : Finset (Fin j)) (x : Four X) :
    stop x (walk r s) = x + ∑ i ∈ s, (step (r i) : Four X) := by
  have H (l : List (Fin j)) (z : Four X) (h : l.Nodup) : stop z (l.map fun i => posDir (r i)) = z+(∑ i ∈ l.toFinset, step (r i)) := by
    induction l generalizing z with
    | nil => simp [stop]
    | cons a l ih => simp only [List.map_cons,stop,List.toFinset_cons, Step.vec_pos, ih _ (List.nodup_cons.mp h).2]; rw [Finset.sum_insert (by simpa using (List.nodup_cons.mp h).1)]; abel
  simp [walk,H,s.nodup_toList,s.toList_toFinset]

def sign (s : Finset (Fin j)) : ℝ := (-1)^((sᶜ).card)
lemma sign_eq (s : Finset (Fin j)) : sign s = (-1 : ℝ)^(j-s.card) := by simp [sign,Finset.card_compl]
lemma sign_reindexed (σ : Equiv.Perm (Fin j)) (s : Finset (Fin j)) : sign (s.map σ.toEmbedding) = sign s := by simp only [sign_eq,Finset.card_map]

variable (j) in
def diffU {X : Type*} [AddCommGroup X] [One X] (U : Lattice.Links X G.El) (x : Four X) : Response G j := fun i k γ =>
  (j.factorial : ℝ)⁻¹ • ∑ s, sign s • plateU U x (walk γ s) i k
lemma diff_gauge {X : Type*} [AddCommGroup X] [One X] (t : Four X → G.El) (U : Lattice.Links X G.El) (x : Four X) :
    diffU j (gauge t U) x = fun i k γ => G.adjoint (t x) (diffU j U x i k γ) := by
  funext i k γ; simp only [diffU,plate_gauge,map_smul,map_sum]
def rawJet {X : Type*} [AddCommGroup X] [One X] (h : ℝ) (U : Lattice.Links X G.El) (x : Four X) (j : ℕ) : Labels.Taylor G j :=
  h^(-(j+2:ℤ)) • radialMap (j:=j) (diffU j U x)
lemma rawJet_gauge {X : Type*} [AddCommGroup X] [One X] (h : ℝ) (t : Four X → G.El) (U : Lattice.Links X G.El) (x : Four X) :
    rawJet h (gauge t U) x j = Labels.Taylor.paint (t x) (rawJet h U x j) := by
  rw [rawJet,rawJet,map_smul,diff_gauge]; congr 1; exact radial_color _ _

def leading (x : Site n) : Potential G n →ₗ[ℝ] Response G j :=
  LinearMap.pi (fun i => LinearMap.pi (fun k => LinearMap.pi fun r => (j.factorial : ℝ)⁻¹ • ∑ s, sign s • curL (stop x (walk r s)) i k))
@[simp] lemma leading_apply (x : Site n) (v : Potential G n) (i k : Axis) (γ : Fin j→Axis) :
    leading x v i k γ = (j.factorial : ℝ)⁻¹ • ∑ s, sign s • cur v.val (stop x (walk γ s)) i k := by simp only [leading,LinearMap.pi_apply,LinearMap.smul_apply,LinearMap.sum_apply,Pi.smul_apply]; rfl
@[simp] lemma diff_zero (x : Site n) : diffU j (positiveLinks (0:Potential G n)) x = 0 := by
  funext i k γ; unfold diffU; 
  change _ • ∑ s, sign s • plate (G:=G) x (walk γ s) i k 0 = _
  simp only [plate_flat,smul_zero,Finset.sum_const_zero]; rfl
@[simp] lemma rawJet_zero (h : ℝ) (x : Site n) : rawJet h (positiveLinks (0:Potential G n)) x j = 0 := by simp [rawJet]
lemma diff_smooth (x : Site n) : ContDiffAt ℝ ω (fun a : Potential G n => diffU j (positiveLinks a) x) 0 :=
  contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun k => contDiffAt_pi.mpr fun γ =>
    (ContDiffAt.sum (fun s _ => ContDiffAt.const_smul (𝕜:=ℝ) (sign s) (plate_diff (G:=G) x (walk γ s) i k))).const_smul ((j.factorial:ℝ)⁻¹)
set_option maxHeartbeats 600000 in
lemma rawJet_smooth (h : ℝ) (x : Site n) : ContDiffAt ℝ ω (fun a : Potential G n => rawJet h (positiveLinks a) x j) 0 := by
  unfold rawJet
  let K : Response G j →L[ℝ] Labels.Taylor G j := (radialMap (j:=j) (G:=G)).toContinuousLinearMap
  have he := ContinuousLinearMap.contDiff (𝕜:=ℝ) (E:=Response G j) (F:=Labels.Taylor G j) (n:=ω) K
  exact (he.contDiffAt.comp (f:=fun a : Potential G n => diffU j (positiveLinks a) x) (0:Potential G n) (diff_smooth (G:=G) (j:=j) x)).const_smul (h^(-(j+2:ℤ)))
lemma diff_deriv (x : Site n) : HasFDerivAt (𝕜:=ℝ) (f:=fun a : Potential G n => diffU j (positiveLinks a) x) (f':=(leading x).toContinuousLinearMap) (0:Potential G n) := by
  refine hasFDerivAt_pi'.mpr (fun i => hasFDerivAt_pi'.mpr (fun k => hasFDerivAt_pi'.mpr (fun γ => ?_)))
  convert! (HasFDerivAt.sum (x:=(0:Potential G n)) (u:=Finset.univ) (fun s _ => (((plate_diff (G:=G) x (walk γ s) i k).differentiableAt (by simp)).hasFDerivAt.const_smul (sign s)))).const_smul ((j.factorial : ℝ)⁻¹) using 1
  · ext1 z; simp only [diffU,Pi.smul_apply,Finset.sum_apply,plate]
  ext1 v
  change leading x v i k γ= _; rw [leading_apply]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,plate_deriv]; rfl

def topJet (h : ℝ) (x : Site n) (j : ℕ) : Potential G n →ₗ[ℝ] Labels.Taylor G j := h^(-(j+2 : ℤ)) • radialMap ∘ₗ (leading x)
lemma jet_deriv (h : ℝ) (x : Site n) : HasFDerivAt (𝕜:=ℝ) (f:=fun a : Potential G n => rawJet h (positiveLinks a) x j) (f':=(topJet h x j).toContinuousLinearMap) (0:Potential G n) := by
  let L := (radialMap (G:=G) (j:=j)).toContinuousLinearMap
  convert! (L.hasFDerivAt.comp (g:=fun u => L u) (f:=fun a : Potential G n => diffU j (positiveLinks a) x) 0 (diff_deriv ..)).const_smul (h^(-(j+2 : ℤ))) using 1
end YM.Pert.Bare
