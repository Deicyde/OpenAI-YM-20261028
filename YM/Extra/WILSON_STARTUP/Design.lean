import YM.Extra.WILSON_STARTUP.Face
import YM.Extra.WILSON_STARTUP.Padded


/-!
# A local top-scale path prescription

Use only at m=N; H and tilde-H BOTH identity there. Intended alternate
input to horizon/paths construction, not imposed after solving continuation.
Keep stage-dependent Clip and require direct ≤ 1 (strict < 1 can buy
nondegenerate square root). Linear large-chord clipping and relaxation stay.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonStartup
open Function Filter Work Tensor RG Wilson Lattice Precision Exterior Padded
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
scoped instance plaqNonempty : Nonempty PlaqAxes := ⟨⟨(0,1),by decide⟩⟩

namespace Design
variable (G : Gauge) (p : Clip)

def bulk := 1 - p.direct
def sideRoot := Real.sqrt (bulk p)
def plaquette (b : PlaqAxes) : Slot := ⟨[],b⟩
def panel : Tensor.T G.Color ℝ 4 := bulk p • fourth G

def extractAtom (b : PlaqAxes) {k : ℕ} (T : Tensor.T G.Color ℝ k) : Atom G k where
  leg := fun _ => plaquette b
  coeff := fun v => T fun i => EuclideanSpace.basisFun G.ColorIndex ℝ (v i)

def four (i : ℕ) := extractAtom G (name PlaqAxes i) (if fixed PlaqAxes i then panel G p else 0)

def top : PathData G where
  row := fun b i => (if i=0 then sideRoot p else 0, plaquette b)
  loop := fun i => extractAtom G (name PlaqAxes i) 0
  cubic := fun i => extractAtom G (name PlaqAxes i) 0
  quartic := four G p

variable {G} {n : Side} {k : ℕ}

theorem panel_invariant (u : G.El) (x : Fin 4 → G.Color) :
    panel G p (fun i => G.adjoint u (x i)) = panel G p x := by
  unfold panel fourth; rw [smul_apply, smul_apply, coeff_adjoint]

theorem extract_poly (b : PlaqAxes) (T : Tensor.T G.Color ℝ k) (x : Fin k → G.Color) :
    (extractAtom G b T).poly x = T x := by
  let e := EuclideanSpace.basisFun G.ColorIndex ℝ
  have he (v : G.Color) : ∑ i, v i • e i = v := e.sum_repr v
  have hb := T.map_sum_finset (fun i j => x i j • e j) (fun _ => Finset.univ)
  rw [Fintype.piFinset_univ] at hb
  simp_rw [he,T.map_smul_univ,smul_eq_mul] at hb
  simpa only [extractAtom,Atom.poly,mul_comm] using hb.symm

theorem extract_magnitude_zero (b : PlaqAxes) : (extractAtom G (k:=k) b 0).magnitude = 0 := by
  simp [Atom.magnitude, extractAtom]

theorem at_plaquette (b : PlaqAxes) (x : Site n) (U : Config G n) : (plaquette b).atSite U x = G.curvature (faceValue U (x,b)) := by
  rw [F03.atSite_path]
  simp [F03.slotFace, plaquette,Slot.offset,stop,travel]

-- use whole square, not just anchor. Includes the wrap.
theorem footprint (T : Tensor.T G.Color ℝ k) (hk : k≠0) (b : PlaqAxes) (x : Site n) :
    (extractAtom G b T).footprint x = touched (x,b) := by
  have hb : (plaquette b).stencil = {0,step b.val.1,step b.val.1+step b.val.2,step b.val.2} := by
    ext y; simp only [Slot.stencil, plaquette,Slot.offset,stop,visits,square,Step.vec_pos,Step.vec_neg,zero_add,
      show (step b.val.1:Cover)+step b.val.2+ -step b.val.1 = step b.val.2 by abel,
      add_neg_cancel]
    simp; tauto
  have he : (extractAtom G b T).stencil = (plaquette b).stencil := by
    haveI : Nonempty (Fin k) := ⟨⟨0,Nat.pos_of_ne_zero hk⟩⟩
    ext i
    simp only [Atom.stencil, extractAtom, Finset.mem_insert,Finset.mem_biUnion, Finset.mem_univ,true_and,exists_const]
    rw [hb]; simp
  rw [Atom.footprint, he, hb, four_visit]; simp [add_comm x, add_assoc]

theorem extract_unmasked (T : Tensor.T G.Color ℝ k) (b : PlaqAxes) (x : Site n) (U : Config G n) :
    (extractAtom G b T).unmasked U x = diagonal T (G.curvature (faceValue U (x,b))) := by
  unfold Atom.unmasked; rw [extract_poly]; simp only [extractAtom,at_plaquette,diagonal]

theorem ell_top (b : Cell n) (U : Config G n) : (top G p).ell U b = sideRoot p • G.curvature (faceValue U b) := by
  unfold PathData.ell; rw [tsum_eq_single 0]; swap
  · intro i hi; simp [PathData.ellTerms, top, hi]
  simp [PathData.ellTerms, top, at_plaquette]

theorem ell_sq (hp : p.direct ≤ 1) (U : Config G n) (b : Cell n) : ‖(top G p).ell U b‖ ^ 2 = bulk p * ‖G.curvature (faceValue U b)‖^2 := by
  rw [ell_top,norm_smul,sideRoot,bulk,Real.norm_of_nonneg (Real.sqrt_nonneg _),mul_pow,Real.sq_sqrt (sub_nonneg.mpr hp)]

theorem extract_invariant (T : Tensor.T G.Color ℝ k) (b : PlaqAxes)
    (h : ∀ u x,T (fun i => G.adjoint u (x i)) = T x) : (extractAtom G b T).Invariant :=
  fun u x => by rw [extract_poly,extract_poly]; exact h ..

theorem normal (hp : p.direct ≤ 1) : (top G p).metric_zero p := by
  have h (i j : PlaqAxes) : (top G p).symbol0 i j = if i=j then sideRoot p else 0 := by
    unfold PathData.symbol0; rw [tsum_eq_single 0 (fun b hb => by simp [top,plaquette,hb])]; rfl
  intro i j
  rw [Finset.sum_eq_single i]; rotate_left
  · intro b _ hb; rw [h,if_neg hb,zero_mul]
  · simp
  rw [h,h,if_pos rfl]; split_ifs with h₁
  · rw [← sq,sideRoot,bulk,Real.sq_sqrt (sub_nonneg.mpr hp)]; ring
  · simp

theorem budgets (hp : p.direct ≤ 1) (σ C Λ : ℝ) (hσ : 0 < σ) (hΛ : 0 ≤ Λ)
    (hC : |sideRoot p| * Real.exp (σ * 4) ≤ C)
    (hT : ∑ i : PlaqAxes, (extractAtom G i (panel G p)).budget σ ≤ C) : (top G p).Bounds p σ C Λ := by
  have hE (k : ℕ) : ∀ i : ℕ, (extractAtom G (k:=k) (name PlaqAxes i) 0).budget σ = 0 := fun i => by
    rw [Atom.budget, extract_magnitude_zero,zero_mul]
  have h0 : 0 ≤ C := (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le).trans hC
  refine ⟨hσ,fun b => ?_,?_,?_,?_,fun i => ?_,fun i j => ?_,normal p hp,fun b x => ?_,fun b x => ?_⟩
  · dsimp only [top,plaquette,Slot.length,List.length_nil,Nat.zero_add]
    refine ⟨fun _ => by positivity, (hasSum_single 0 (fun b hb => ?_)).summable, ?_⟩
    · simp [hb]
    rw [tsum_eq_single 0 (fun b hb => by simp [hb])]
    simpa using hC
  · simp only [top,hE]; exact ⟨fun _ => le_rfl,summable_zero,by simpa using hΛ⟩
  · simp only [top,hE]; exact ⟨fun _ => le_rfl,summable_zero,by simpa using h0⟩
  · refine Padded.budget (α:=PlaqAxes) ?_ (fun i => ?_) hT
    · intro i; dsimp [top,four]; split <;> first | rfl | exact hE _ _
    unfold Atom.budget Atom.magnitude; positivity
  · refine ⟨extract_invariant _ _ (by simp), extract_invariant _ _ (by simp), extract_invariant _ _ ?_⟩
    intro u x; split
    · exact panel_invariant p ..
    simp
  · exact (hasSum_single 0 (fun b hb => by simp [top,plaquette,hb])).summable
  · unfold PathData.loop_coeff; simp [top,extractAtom]
  · unfold PathData.loop_coeff; simp [top,extractAtom]

-- Denotational atom sums

theorem extract_placed_zero (b : PlaqAxes) (t : BudgetPoint) (x : Site n) (U : Config G n) :
    (extractAtom G (k:=k) b 0).placed t U x = 0 := by
  unfold Atom.placed
  rw [show (fun V => (extractAtom G (k:=k) b 0).unmasked V x) = fun _ => 0 from
    funext fun V => by simp [extract_unmasked,diagonal]]
  by_cases h : Healthy t.threshold ((extractAtom G (k:=k) b 0).footprint x) U
  · exact masked_eq _ _ _ _ h
  · exact masked_ne _ _ _ _ h

theorem core_top (b : BudgetPoint) (x : Site n) (U : Config G n) :
    PathData.atomSeries (top G p).cubic b U x = 0 ∧ PathData.atomSeries (top G p).loop b U x = 0 ∧
      PathData.atomSeries (top G p).quartic b U x = ∑ i : PlaqAxes, masked b.threshold (touched (x,i))
        (fun V => diagonal (panel G p) (G.curvature (faceValue V (x,i)))) U := by
  simp only [PathData.atomSeries, top,extract_placed_zero,tsum_zero,true_and]
  refine totals (α:=PlaqAxes) ?_
  intro i; dsimp [four]; split
  · rw [Atom.placed,footprint _ (by decide)]; simp only [extract_unmasked]
  exact extract_placed_zero ..

theorem uncut_top (U : Config G n) : uncut (top G p).cubic U = 0 ∧
    uncut (top G p).quartic U = ∑ i : Cell n, diagonal (panel G p) (G.curvature (faceValue U i)) := by
  simp only [uncut, top,extract_unmasked,diagonal,zero_apply,tsum_zero,Finset.sum_const_zero,true_and]
  rw [Fintype.sum_prod_type]; refine Finset.sum_congr rfl fun x _ => totals (α:=PlaqAxes) ?_
  intro i; dsimp only [four]; split <;> exact extract_unmasked ..

theorem principal_top (U : Config G n) (hp : p.direct ≤ 1) :
    quadratic p (top G p) U + uncut (top G p).cubic U + uncut (top G p).quartic U +
      ∑ i : Cell n, bulk p * residual G i U = energy U := by
  rw [(uncut_top p U).1,(uncut_top p U).2,add_zero]
  unfold quadratic energy; simp_rw [ell_sq p hp]; rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  simp only [panel,residual,surplus,bulk,diagonal,smul_apply,smul_eq_mul]; ring
end Design
end YM.WilsonStartup
