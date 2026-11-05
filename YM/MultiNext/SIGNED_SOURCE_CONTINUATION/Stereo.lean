import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Pattern
import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Strings
import YM.Next.FOUNDATIONS.LinkBounds

set_option warningAsError false

/-!
# Polynomial position pricing across the gauge & endpoint map

For the moment tests on the unrotated genuine log links.
Bound on position *degree*, incl endpoint displacements even at
recentered x. -/
set_option autoImplicit false
noncomputable section
namespace YM.MultiNext.SignedSource.Broadcast
open Function Filter Finset Tensor Work Set MeasureTheory RG Wilson Lattice Labels Source Drops Analysis
open Powers  Next.Foundations Pattern
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {d n : ℕ}

lemma coats (i : Axis) (v : Snap G d) (k : ℕ) (he : ∀ t : Fin (d-1),k < t.val+2 → v t=0) :
    (fun x : E4 => tempo x i v)∈space E4 (Fiber G d) (k-1) := by
  let X := (ℝ × ℝ) →L[ℝ] E4
  have hp : (fun x : E4 => Pattern.line x i)∈space E4 X 1 := by
    let L := (ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) E4) (ContinuousLinearMap.fst ℝ ℝ ℝ)
    refine Powers.add (show (fun x => L x)∈space E4 X 1 from ?_) (constants _ 1)
    exact residence (f:=fun x => L x) ⟨L.contDiff, fun v x => by simp only [map_smul,pow_one]⟩ le_rfl
  let f (j : Fin (d-1)) (x : E4) := ((v j).val i).compContinuousLinearMap (fun _ => Pattern.line x i)
  have ht j : f j∈space E4 (Tensor.T (ℝ × ℝ) G.Color (j.val+1)) (k-1) := by
    by_cases hk : j.val+1 ≤ k-1
    · convert Powers.many (ContinuousMultilinearMap.compContinuousLinearMapLRight ((v j).val i)) (fun _ x => Pattern.line x i) (k-1)
        (fun _ => 1) (fun _ => hp) (by simp [hk]) using 1
      rfl
    have hx : k < j.val+2 := by omega
    unfold f; rw [he j hx]
    convert constants (0:Tensor.T (ℝ×ℝ) G.Color (j.val+1)) (k-1) using 1
    funext x; ext1 i; rfl
  let L (j : Fin (d-1)) := ContinuousLinearMap.single ℝ (fun j : Fin (d-1) => Tensor.T (ℝ×ℝ) G.Color (j.val+1)) j
  convert Powers.sums Finset.univ (fun j x => L j (f j x)) (fun i _ => carried (L i) (ht i)) using 1
  funext x j
  rw [Finset.sum_apply]; rw [Finset.sum_eq_single j] -- already x
  · simp [L,f,tempo]
  · intro l hl hj; exact Pi.single_eq_of_ne (Ne.symm hj) _
  simp

/-- When all displacements and potentials zero, stereo contributes
no derivative of ANY order. Needed to pay one difference loss at every
link. -/
def pure (G : Gauge) (d : ℕ) : G.Color →L[ℝ] Panel G d := ContinuousLinearMap.inl ℝ _ _
lemma lower {m : ℕ} (x : Fin m → G.Color) (d) : iteratedFDeriv ℝ m (stereo G d) 0 (fun i => pure G d (x i))=0 := by
  let P := pure G d
  have he : stereo G d ∘ P = fun _ => 0 := by
    funext x; change G.plog (G.mat _* run G d 0 * star (G.mat (G.lieExp (x+0))))=0
    simp only [add_zero,(endpoint G d).2.1,mul_one]
    rw [show (P x).1=x from rfl,G.mat_mul_star,G.plog_one]
  have hh := congrArg (fun f => iteratedFDeriv ℝ m f 0 x) he
  change (iteratedFDeriv ℝ m (stereo G d ∘ P) 0) x = _ at hh
  rw [jets_linear P ((scripts G d).1.of_le le_top)] at hh
  change (iteratedFDeriv ℝ m (stereo G d) 0) _ = iteratedFDeriv ℝ m (0:G.Color → G.Color) 0 x at hh
  simp only [Pi.zero_def, iteratedFDeriv_fun_zero,zero_apply] at hh; exact hh

/-- Result evaluated on each link in this type. -/
def sight (x : E4) (j : Axis) (p : E4→G.Color) (v : Snap G d) : Panel G d :=
    (p x,p (x+basis j)-p x,tempo x j v)

lemma channel (m : ℕ) (j : Axis) (p : Fin m → E4 → G.Color) (v : Fin m → Snap G d) (k : Fin m→ℕ)
    (h : ∀ i,p i∈ space E4 G.Color (k i)) (he : ∀ i,∀ t : Fin (d-1),k i < t.val+2 → v i t=0) (hk : ∀ i,1 ≤ k i) :
    let L := ∑ i,k i; let T := iteratedFDeriv ℝ m (stereo G d) 0
    (fun x : E4 => T (fun i => sight x j (p i) (v i)))∈space E4 G.Color (L-1) := by
  intro L T
  let a i x := pure G d (p i x)
  let L₁ : G.Color →L[ℝ] Panel G d := (ContinuousLinearMap.inr ℝ G.Color _).comp (ContinuousLinearMap.inl ℝ G.Color (Fiber G d))
  let L₂ : Fiber G d →L[ℝ] Panel G d := (ContinuousLinearMap.inr ℝ G.Color _).comp (ContinuousLinearMap.inr ℝ G.Color _)
  let b i x := L₁ (p i (x+basis j)-p i x)+L₂ (tempo x j (v i))
  have ht i : a i∈space E4 (Panel G d) (k i) := carried _ (h i)
  have hb i : b i∈space E4 (Panel G d) (k i-1) := Powers.add (carried L₁ (Powers.discrete (basis j) (h i))) (carried L₂ (coats j (v i) (k i) (he i)))
  have hh x : (fun i => sight x j (p i) (v i))=(fun i => a i x)+(fun i => b i x) := by
    funext i; refine Prod.ext ?_ (Prod.ext ?_ ?_)
    all_goals simp [a,b,L₁,L₂,sight,pure]
  simp_rw [hh,T.map_add_univ]
  refine Powers.sums _ _ fun s _ => ?_
  by_cases hx : s=Finset.univ
  · subst s; simp only [Finset.piecewise_univ]; rw [show (fun x => T _)=0 from funext (fun x => lower (fun i => p i x) d)]
    exact (space E4 G.Color _).zero_mem
  let w i := if i∈s then k i else k i - 1
  exact Powers.many T (fun i x => Finset.piecewise s (fun i => a i x) (fun i => b i x) i) (L-1) w
    (fun i => by unfold Finset.piecewise w; split <;> first | exact ht i | exact hb i) (by
      have hu : ∑ i,w i < L := by
        refine sum_lt_sum (fun i _ => ?_) ?_
        · unfold w; split; exacts [le_rfl,Nat.sub_le ..]
        obtain ⟨i,hi⟩ : ∃ i,i∉s := by simpa only [Finset.eq_univ_iff_forall,not_forall] using hx
        exact ⟨_,Finset.mem_univ _, by rw [show w i=k i-1 from if_neg hi]; have h := hk i; omega⟩
      omega)
end YM.MultiNext.SignedSource.Broadcast
