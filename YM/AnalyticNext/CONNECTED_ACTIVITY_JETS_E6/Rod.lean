import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Shell

/-!
# Support-aware affine rows

For the Gaussian references of the hit estimates here we use the
following *variation* of E: flat truncated F/I tangent, later rotated
and with parallel transport. Hitting uses VALUE estimates and doesn't
require taking an affine derivative around the actual V for the
extracted row. (Physical remainder subtracts the very same row.)
Does not declare that this is already the row to use in other
kinetic/stationary computations! These are for estimating actual
integrals. Also export full vs truncated estimates. Need check any
kinetic/β call separately.
-/

set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations Matrix
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f}
open Work.F03 Work.E03
namespace SliceRows

abbrev Rod (c f : Side) := Twin f ⊕ Bond c

def focus (S : StepData c f) : Rod c f → Site c
  | .inl p => S.ratio.parent p.1.1
  | .inr b => b.1

def toLog (x : Directions G n) : LogField G n := fun i => x ((Work.E03.poleEquiv n).symm i)

lemma at_pole (x : Directions G n) (e : Bond n) : toLog x (pole e)=x e :=
  congr_arg x ((Work.E03.poleEquiv n).symm_apply_apply e)

lemma collects (x : Directions G n) : collect G (toLog x) = x := funext fun i => at_pole x i
lemma logged (x : LogField G n) : toLog (collect G x) = x := by
  funext i
  obtain ⟨p,rfl⟩ := (poleEquiv n).surjective i; rw [show poleEquiv n p=pole p from rfl,at_pole]; rfl

lemma counted (x : Directions G n) : ‖toLog x‖=‖x‖ := by
  apply le_antisymm
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => norm_le_pi_norm x _
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => by rw [← at_pole x i]; exact norm_le_pi_norm ..

lemma edits (x : Directions G n) : represent (toLog x) = increment 1 x := by rw [represent,collects]

/-- Local linear currency in the applied cut. Doesn't require Cut
summability just to define a function. -/
def ellCut (A : PathData G) (R : ℕ) (x : LogField G f) (p : Cell f) :=
    ∑' i : ℕ, if (A.row p.2 i).2.length ≤ R then (A.row p.2 i).1 • faceCurl (slotFace (A.row p.2 i).2 p.1) x else 0

def bareCut (q : Clip) (A : PathData G) (R : ℕ) (x : LogField G f) (p : Twin f) :=
    if p.2 then ellCut A R x p.1 else Real.sqrt q.direct • faceCurl p.1 x

/-- PURE tangents (so the Z one takes zero output). Inputs before tree
selection, to pay the forest invariants after selection. -/
def barField (T : Tube G S) (R : ℕ) (x : Directions G f) : Rod c f → G.Color :=
    Sum.elim (bareCut T.high T.up R (toLog x)) (zLin S (toLog x) 0)

lemma curl_eq (x : Directions G f) (p : Cell f) : faceCurl p (toLog x) =
    let y := p.1; let i:=p.2.1.1; let j:=p.2.1.2
    x (y+step i,j)-x (y,j)-(x (y+step j,i)-x (y,i)) := by
  dsimp only
  ext q
  change (_ *ᵥ parts G 1 _ q) _ = x _ q-x _ q-(x _ q-x _ q)
  rw [d_plaquettes]; unfold parts
  simp only [show ∀ y i, toLog x (y,coord i)=x (y,i) from fun y i => at_pole x (y,i)]

lemma phi_linear (a : Directions G f) (i : Cell f) : ‖faceCurl i (toLog a)‖ ≤ 4 * ‖a‖ := by
  rw [curl_eq]; dsimp only
  apply (norm_sub_le _ _).trans
  apply (add_le_add (norm_sub_le _ _) (norm_sub_le _ _)).trans
  linarith only [norm_le_pi_norm a (i.1+step i.2.1.1,i.2.1.2), norm_le_pi_norm a (i.1,i.2.1.2),
    norm_le_pi_norm a (i.1+step i.2.1.2,i.2.1.1), norm_le_pi_norm a (i.1,i.2.1.1)]

lemma zLin_eq (S : StepData c f) (x : LogField G f) (b : Bond c) :
    zLin S x 0 b = (-Real.sqrt S.kernel.penalty) • (∑ i, probe S (pole b) i • x i) := by
  ext i; simp only [zLin, Pi.zero_apply, neg_smul, zero_sub, smul_neg]
  have h := (map_sum (LinearMap.comp (LinearMap.proj i) (WithLp.linearEquiv 2 ℝ _).toLinearMap : G.Color →ₗ[ℝ] ℝ)
    (fun j => probe S (pole b) j • x j) univ)
  simp_rw [map_smul] at h
  apply congr_arg (fun a : ℝ => -(Real.sqrt S.kernel.penalty * a)) h.symm

section real
variable {A : PathData G} {Q : Clip} {σ C Λ : ℝ}

lemma ecut_sum (h : A.Bounds Q σ C Λ) (R : ℕ) (x : LogField G f) (p : Cell f) :
    Summable fun i : ℕ => if (A.row p.2 i).2.length ≤ R then
      (A.row p.2 i).1 • faceCurl (slotFace (A.row p.2 i).2 p.1) x else 0 := by
  apply Summable.of_norm_bounded (Work.F03.ellLine_summable A h p x |>.norm)
  intro i; split
  next => exact le_rfl
  next => rw [norm_zero]; exact norm_nonneg _

lemma bar_add (T : Tube G S) (h : T.up.Bounds Q σ C Λ) (R : ℕ) (x y : Directions G f) (p : Rod c f) :
    barField T R (x+y) p = barField T R x p + barField T R y p := by
  rcases p with p|b
  · dsimp only [barField, Sum.elim, bareCut]; split
    next hp =>
      unfold ellCut; rw [← Summable.tsum_add (ecut_sum h ..) (ecut_sum h ..)]
      apply tsum_congr; intro i; split
      next hi => simp only [curl_eq, Pi.add_apply,smul_sub,smul_add]; abel
      next hi => simp only [zero_add]
    next hp => simp only [curl_eq,Pi.add_apply,smul_sub,smul_add]; abel
  simp only [barField, Sum.elim, zLin_eq, toLog, Pi.add_apply, smul_add,Finset.sum_add_distrib]

lemma bar_smul (T : Tube G S) (h : T.up.Bounds Q σ C Λ) (R : ℕ) (x : Directions G f) (s : ℝ) (p : Rod c f) :
    barField T R (s • x) p=s • barField T R x p := by
  rcases p with p|b
  · dsimp only [barField, Sum.elim, bareCut]; split
    next hp =>
      unfold ellCut; rw [← Summable.tsum_const_smul s (ecut_sum h ..)]
      apply tsum_congr; intro i; split
      next hi => simp only [curl_eq, Pi.smul_apply, ← smul_sub]; rw [smul_comm]
      next hi => simp only [ smul_zero]
    next hp => simp only [curl_eq, Pi.smul_apply, ← smul_sub]; rw [smul_comm]
  simp only [barField, Sum.elim, zLin_eq,toLog,Pi.smul_apply,Finset.smul_sum, smul_comm s]; try simp only [Finset.smul_sum]

lemma bar_zero (T : Tube G S) (h : T.up.Bounds Q σ C Λ) (R : ℕ) (p : Rod c f) : barField T R 0 p=0 := by
  simpa only [zero_smul] using bar_smul T h R 0 0 p

lemma recolor (T : Tube G S) (h : T.up.Bounds Q σ C Λ) (R : ℕ) (u : Directions G f) (k : G.El) (x : Rod c f) :
    barField T R (fun i => G.adjoint k (u i)) x = G.adjoint k (barField T R u x) := by
  rcases x with p|b
  · dsimp only [barField, Sum.elim,bareCut]; split
    next hp =>
      unfold ellCut
      let f : G.Color →L[ℝ] G.Color := (G.adjoint k).toContinuousLinearMap
      change _ = f (∑' _, _)
      rw [f.map_tsum (ecut_sum h ..)]; apply tsum_congr; intro i; split
      next hi => simp only [curl_eq, map_smul,map_sub]; rfl
      next hi => rw [map_zero]
    next hp => simp only [curl_eq,map_smul,map_sub]
  simp only [barField, Sum.elim, zLin_eq, toLog,map_smul,map_sum]
end real

section bounded
private lemma curl_local (S : StepData c f) (x y : Directions G f) (p : Cell f)
    (h : ∀ j : Bond f, distAt S j (S.ratio.parent p.1) ≤ 1 → x j = y j) : faceCurl p (toLog x) = faceCurl p (toLog y) := by
  rw [curl_eq, curl_eq]
  dsimp only
  have he i : x (p.1,i) = _ := h (p.1,i) (by simp [distAt,atEdge])
  have hg i j : x (p.1+step i,j) = _ := h (p.1+step i,j) (Work.E03.parent_step S p.1 i)
  rw [hg, he, hg, he]

lemma zLin_local (S : StepData c f) (hs : S.patch.Branches S.kernel G) (x y : Directions G f) (p : Bond c)
    (h : ∀ i : Bond f, distAt S i p.1 ≤ predReach S.patch → x i = y i) :
    zLin S (toLog x) 0 p=zLin S (toLog y) 0 p := by
  let k : S.Choices := Classical.arbitrary _
  let f (v : ℝ) := zTest S k p (v • (toLog x,0))
  have he (v : ℝ) : f v = zTest S k p (v • (toLog y,0)) := by
    unfold f zTest Z
    simp only [Prod.smul_fst,Prod.smul_snd]
    rw [prediction_near_eq hs _ _ k p ?_]; intro i hi
    simp only [represent_link, Pi.smul_apply]
    change G.lieExp (v • toLog x (pole i))=G.lieExp (v • toLog y (pole i))
    rw [at_pole, at_pole, h i hi]
  have hs' : HasDerivAt f (zLin S (toLog x) 0 p) 0 := zTest_deriv hs k p (toLog x,0)
  rw [funext he] at hs'
  exact hs'.unique (zTest_deriv hs k p (toLog y,0))

lemma tangent_local (T : Tube G S) (h : S.patch.Branches S.kernel G) (R : ℕ) (x y : Directions G f) (p : Rod c f)
    (hx : ∀ i : Bond f, distAt S i (focus S p) ≤ R+predReach S.patch+4 → x i = y i) :
    barField T R x p=barField T R y p := by
  rcases p with p|b
  · dsimp only [barField,Sum.elim,bareCut]; split
    next hp =>
      apply tsum_congr; intro i; split
      next hi =>
        congr 1
        apply curl_local S
        intro j hj
        apply hx; let X := T.up.row p.1.2 i
        have hv := Work.E04.slot_separation X.2 p.1.1 (n:=f)
        let y := S.ratio.parent p.1.1; let z := S.ratio.parent (slotFace X.2 p.1.1).1
        have hz : separation y z ≤ X.2.length+1 :=
          (Work.E04.parent_separation S.ratio _ _).trans (Nat.add_le_add_right hv _)
        change X.2.length ≤ R at hi
        change separation z _ ≤ 1 at hj
        exact (separation_triangle y z (atEdge S j)).trans (by omega)
      next hi => rfl
    next hp => rw [curl_local S _ _ _ (fun j he => hx j (he.trans (by omega)))]
  exact zLin_local S h x y b fun j he => hx j (he.trans (by omega))
end bounded
end SliceRows
end YM.ConnectedActivityE6
