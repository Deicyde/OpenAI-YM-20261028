import YM.Pert.Position.Board
import YM.Pert.Position.RawMean
/-! Leading position-conditioned *actual* frames, conditional only on the isolated leading determinant of the user's chosen finite tests; exact equation and convergence (along the same weak sequence) for any query. The columns and symmetries are on the actual theory selected earlier. No all-coupling-power remainder here. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Position
open Set Function Filter MeasureTheory Analysis Maxwell RawLabels Climb Spec Table Ward Extra.FD
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G : Gauge} {C : Family G} {S : Table C.book} {d n : ℕ}
variable (Q : Conditions C.labels d n)

/-- Only test on separated supports (kernel values on diagonals are not used). -/
def CleanProfiles {F : Labels.Frames G} (Q : Conditions F d n) := ∀ i : Fin Q.slots, ∃ t : Test (Q.arity i), (t : Points (Q.arity i) → ℂ) = Q.profiles i

def measured (X : Scaling S) (k : ℕ) (i : Fin Q.slots) (z : inklet Q i) := exactMean X k (fun j => baring _ d (z j)) (Q.profiles i)
lemma measured_tends (hv : CleanProfiles Q) {H : Extraction.Order} {b : Final C H S} (X : Scaling S) (h : FirstExtension b X) : Tendsto (measured Q X) atTop (𝓝 (white Q)) := by
  apply tendsto_pi_nhds.mpr; intro i; refine tendsto_pi_nhds.mpr (fun j => ?_)
  obtain ⟨t,ht⟩ := hv i
  simpa only [measured,white,← ht,bundle] using (exact_tape X h (fun l => baring _ d (j l)) t)

private lemma singleBasis {i : Fin Q.slots} (p : Fin (Q.arity i) → E C.labels d) (M : MultilinearMap ℂ (fun _ : Fin (Q.arity i) => E C.labels d) ℂ) :
    (∑ k : inklet Q i, (Finset.univ.prod (fun j => (baring C.labels d).coord (k j) (p j))) * M (fun j => baring C.labels d (k j)))=M p := by
  have ht (j : Fin (Q.arity i)) := (baring C.labels d).sum_equivFun (p j)
  conv_rhs => rw [←funext ht]
  rw [MultilinearMap.map_sum_finset,Fintype.piFinset_univ]; refine Finset.sum_congr rfl fun z _ => ?_; rw [M.map_smul_univ]; rfl

lemma chart_actual (hs : S.Smooth) (X : Scaling S) (hc : CleanProfiles Q) (b : Buffer C.labels d) (k : ℕ) :
    chart Q (measured Q X k,b) = Q.chisels (fun i=> Complex.re (exactMean X k (fun j => motor C.labels b (Q.columns i j)) (Q.profiles i))) := by
  apply congrArg Q.chisels; funext i; apply congrArg Complex.re
  obtain ⟨t,ht⟩ := hc i
  let B := baring C.labels d
  let p (j : Fin (Q.arity i)) := motor C.labels b (Q.columns i j)
  let f (j : inklet Q i) (x : Points (Q.arity i)) := swivel X k (fun l => B (j l)) x
  let a (z : inklet Q i) := ∏ j, B.coord (z j) (p j)
  have he (j : inklet Q i) : Integrable (fun x => a j * (t x*f j x)) := (t.smearing (swivel_smooth (S:=S) hs X k (fun l => B (j l)))).const_mul _
  change (∑ j : inklet Q i, a j * (∫ x : Points _, Q.profiles i x * f j x)) = ∫ x : Points _, Q.profiles i x * swivel X k p x
  rw [← ht]; simp_rw [← integral_const_mul]; rw [← integral_finsetSum _ (fun i _ => he i)]
  congr; ext1 x; simp_rw [mul_left_comm (a _) _,← Finset.mul_sum]; congr 1
  let M := S.classMoment S (fun _ : Fin (Q.arity i) => d) ((X.r k:ℝ) • x)
  exact singleBasis Q (i:=i) p (M.compLinearMap (fun _=> (X.U k d).toLinearMap))

def testedMean (X : Scaling S) (b : Buffer C.labels d) (k : ℕ) := Q.chisels (fun i=> Complex.re (exactMean X k (fun j => motor C.labels b (Q.columns i j)) (Q.profiles i)))
/-- Exact finite position equations for the bundle, with general test convergence along one common actual-theory sequence. Quantified determinant concerns explicitly only finite leading free data (not any unknown interacting error). -/
theorem actual_square {H : Extraction.Order} {b : Final C H S} (hQ : square Q) (hq' : CleanProfiles Q) (X : Scaling S) (hX : FirstExtension b X) :
   ∃ B : ℕ→Buffer C.labels d, Tendsto B atTop (𝓝 0) ∧
     (∀ᶠ k : ℕ in atTop, IsUnit (motor C.labels (B k)) ∧ testedMean Q X (B k) k= chart Q (white Q,0))∧
     ∀ {m : ℕ} (R : Conditions C.labels d m), CleanProfiles R → Tendsto (fun k : ℕ => testedMean R X (B k) k) atTop (𝓝 (chart R (white R,0))) := by
  obtain ⟨φ,H⟩ := squareSolve Q hQ
  let B := φ ∘ measured Q X
  have he := measured_tends Q hq' X hX
  have hb : Tendsto B atTop (𝓝 0) := (H.fixes) ▸ H.diff.continuousAt.tendsto.comp he
  refine ⟨B,hb,(hb.eventually (invertible_tail C.labels (d:=d))).and ((he.eventually H.curves).mono (fun k hk => ?_)),?_⟩
  · exact (chart_actual Q b.room.kernel.smooth X hq' (B k) _).symm.trans hk
  intro m R hR
  have h' := (measured_tends R hR X hX |>.prodMk_nhds hb)
  exact (((chart_diff R).continuous.tendsto _).comp h').congr (fun k => chart_actual R b.room.kernel.smooth X hR (B k) k)
end YM.Pert.Position
