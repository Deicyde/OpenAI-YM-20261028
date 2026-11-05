import YM.Corona.Fill
import YM.Vac.Caps
import YM.Work.G07.Calculus



/-!
# Link costs on fixed cover stencils

The direction test grows with distance from the anchor, not a global
threshold-sized ball in link space. Only bound directions at the actual reads.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Work.G07
open RG Lattice Wilson
open scoped ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {k P j a : ℕ} {S : Finset Cover}
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {f g : CoverConfig G → E}

/-- Threshold rate for fixed cover functions: pay `t^j` at all tested orders
plus `t^a` for each derivative. We test on torus configurations via true
lattice expansion around an anchor, for ALL sides. This just bounds functions,
not asserting their support, invariance etc. -/
def Rate (k P : ℕ) (S : Finset Cover) (j a : ℕ) (f : CoverConfig G → E) :=
  ∃ c : ℝ, 0 ≤ c ∧ ∀ b : BudgetPoint, b.power = P → ∀ n : Side, ∀ o : Site n,
    LeftBound k (b.dirBound o) (Healthy b.threshold (S.image fun x => wrap n x + o))
      (b.threshold^a) (c*b.threshold^j) (fun U => f (expandAt o U))

theorem Rate.const (x : E) : Rate k P S 0 a fun _ : CoverConfig G => x := by
  refine ⟨‖x‖, norm_nonneg x, fun b _ n o => ?_⟩
  simp only [pow_zero, mul_one]; exact LeftBound.const (pow_nonneg b.threshold_pos.le _) x

theorem Rate.add (hf : Rate k P S j a f) (hg : Rate k P S j a g) :
    Rate k P S j a fun U => f U + g U := by
  obtain ⟨c,hc,hf⟩ := hf
  obtain ⟨d,hd,hg⟩ := hg
  refine ⟨c+d,add_nonneg hc hd,fun b hb n o => ?_⟩
  rw [add_mul]; exact (hf b hb n o).add (hg b hb n o)

theorem Rate.postcomp (hf : Rate k P S j a f) (L : E →L[ℝ] F) :
    Rate k P S j a fun U => L (f U) := by
  obtain ⟨c,hc,hf⟩ := hf
  refine ⟨‖L‖*c,mul_nonneg (norm_nonneg _) hc,fun b hb n o => ?_⟩
  rw [mul_assoc]; exact (hf b hb n o).postcomp L

theorem Rate.mul {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] {x y : CoverConfig G → R} {i}
    (hx : Rate k P S i a x) (hy : Rate k P S j a y) :
    Rate k P S (i+j) a fun U => x U * y U := by
  obtain ⟨c,hc,hx⟩ := hx
  obtain ⟨d,hd,hy⟩ := hy
  refine ⟨2^k*c*d, by positivity, fun b hb n o => ?_⟩
  rw [pow_add, show 2^k*c*d*(b.threshold^i*b.threshold^j) =
    2^k*(c*b.threshold^i)*(d*b.threshold^j) by ring]
  exact (hx b hb n o).mul (hy b hb n o) (pow_nonneg b.threshold_pos.le _)

def linkPrefix (e : Edge (Site n)) (l : List (Directions G n)) : G.Mat :=
  (l.reverse.map (fun i => G.colorMat (i e))).prod

theorem linkPrefix_cons (e : Edge (Site n)) (A : Directions G n) (l) :
    linkPrefix e (A::l) = linkPrefix e l * G.colorMat (A e) := by
  simp [linkPrefix]

theorem left_link (e : Edge (Site n)) (l : List (Directions G n)) (U : Config G n) :
    leftDerivs (fun V : Config G n => G.mat (V e)) l U = linkPrefix e l * G.mat (U e) := by
  induction l generalizing U with
  | nil => simp [leftDerivs, linkPrefix]
  | cons A l ih =>
    have he : HasDerivAt (fun t : ℝ => G.mat (increment U (t • A) e))
        (G.colorMat (A e) * G.mat (U e)) 0 := by
      simp only [increment, G.mat_mul, Pi.smul_apply, G.mat_lieExp, map_smul]
      simpa using! ((hasDerivAt_exp_smul_const (G.colorMat (A e)) (0:ℝ)).mul_const (G.mat (U e)))
    simp only [leftDerivs, ih, linkPrefix_cons, mul_assoc]
    exact (he.const_mul (linkPrefix e l)).deriv

theorem smooth_link (e : Edge (Site n)) :
    LeftSmooth k (fun V : Config G n => G.mat (V e)) := by
  intro l _ U
  simp only [left_link, increment, G.mat_mul]
  have he : ContDiff ℝ ∞ (fun i : Directions G n => G.mat (G.lieExp (i e))) :=
    (G.exp_jet.of_le (by simp)).comp (contDiff_apply ..)
  exact contDiff_const.mul (he.mul contDiff_const)

theorem rate_link (e : Edge Cover) :
    Rate k P S 0 1 (fun V : CoverConfig G => G.mat (V e)) := by
  let R : ℕ := Finset.univ.sup fun i => (e.1 i).natAbs
  let B : ℝ := max 1 (G.colorScale * (1+R)^P)
  have hone : 1 ≤ B := le_max_left _ _
  have hbnn : 0 ≤ B := zero_le_one.trans hone
  refine ⟨‖(1:G.Mat)‖*B^k, by positivity, fun b hb n o => ?_⟩
  let q : Edge (Site n) := (wrap n e.1+o,e.2)
  simp only [pow_zero, pow_one, mul_one]
  refine ⟨smooth_link q, by positivity, fun l hl hs U _ => ?_⟩
  have ht := b.threshold_pos.le
  have hh : separation q.1 o ≤ R := by
    change separation (wrap n e.1 + o) o ≤ R
    rw [separation, add_sub_cancel_right]
    exact Finset.sup_le fun i _ => (Corona.lap ..).trans <|
      Finset.le_sup (f:=fun i => (e.1 i).natAbs) (Finset.mem_univ _)
  have hi (A : Directions G n) (hA : b.dirBound o A) :
      ‖G.colorMat (A q)‖ ≤ B * b.threshold := by
    calc
      ‖G.colorMat (A q)‖ = G.colorScale * ‖A q‖ := G.colorMat_norm _
      _ ≤ G.colorScale * (b.threshold * (1+(separation q.1 o : ℝ))^b.power) :=
        mul_le_mul_of_nonneg_left (hA q) G.colorScale_pos.le
      _ ≤ G.colorScale * (b.threshold * (1+R)^P) := by
        rw [hb]
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ ht) G.colorScale_pos.le
        gcongr
      _ ≤ B * b.threshold := by
        rw [mul_comm b.threshold, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) ht
  have hp (v : List (Directions G n)) (hv : ∀ i∈v,b.dirBound o i) :
      ‖linkPrefix q v‖ ≤ ‖(1:G.Mat)‖ * (B * b.threshold)^v.length := by
    induction v with
    | nil => simp [linkPrefix]
    | cons A v ih =>
      rw [linkPrefix_cons, List.length_cons, pow_succ, ← mul_assoc]
      exact (norm_mul_le ..).trans <|
        mul_le_mul (ih (fun i hh => hv i (List.mem_cons_of_mem _ hh))) (hi A (hv A (by simp)))
          (norm_nonneg _) (by positivity)
  change ‖leftDerivs (fun V : Config G n => G.mat (V q)) l U‖ ≤ _
  rw [left_link, Gauge.frob_mul_eq _ _ (G.mat_mul_star _)]
  apply (hp l hs).trans
  rw [mul_pow, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hone hl) (norm_nonneg _)) (pow_nonneg ht _)

theorem Rate.inv_mat {u : CoverConfig G → G.El}
    (h : Rate k P S 0 1 fun U => G.mat (u U)) : Rate k P S 0 1 fun U => G.mat ((u U)⁻¹) := by
  exact h.postcomp (starL' ℝ).toContinuousLinearMap

theorem rate_path (x : Cover) (w : Walk) :
    Rate k P S 0 1 (fun V : CoverConfig G => G.mat (travel V x w)) := by
  induction w generalizing x with
  | nil => exact Rate.const _
  | cons d w ih =>
    have hd : Rate k P S 0 1 (fun V : CoverConfig G => G.mat (d.read V x)) := by
      rcases d with ⟨i,h|h⟩
      · exact rate_link (x,i)
      · exact (Rate.inv_mat (u:=fun V : CoverConfig G => V (x-step i,i)) (rate_link _))
    exact hd.mul (ih _)

theorem Rate.curved {u : CoverConfig G → G.El}
    (h : Rate k P S 0 1 fun U => G.mat (u U)) : Rate k P S 0 1 fun U => G.curvature (u U) := by
  let L : G.Mat →L[ℝ] G.Mat := ContinuousLinearMap.id ℝ _
  let K := G.projectColor.toContinuousLinearMap
  let M := (starL' ℝ (A:=G.Mat)).toContinuousLinearMap
  exact h.postcomp (K.comp ((1/2 : ℝ) • (L - M)))

theorem raw_slot (s : Slot) : Rate k P S 0 1 (s.eval (G:=G)) := by
  let u := fun V : CoverConfig G => travel V 0 s.walk
  let f := fun V : CoverConfig G => faceValue V (s.offset,s.plaq)
  have h : Rate k P S 0 1 fun U => G.mat (u U) := rate_path ..
  have hf : Rate k P S 0 1 fun U => G.mat (f U) := rate_path ..
  have hh : Rate k P S 0 1 fun U => G.mat (u U * f U * (u U)⁻¹) :=
    (h.mul hf).mul h.inv_mat
  rw [show s.eval (G:=G) = (fun U => G.curvature (u U * f U * (u U)⁻¹)) from
    funext fun U => (G.curvature_conjugate ..).symm]
  exact hh.curved

theorem slot_bound (s : Slot) (hs : s.stencil ⊆ S) (t : ℝ) (o : Site n) (U : Config G n)
    (hU : Healthy t (S.image (fun x => wrap n x + o)) U) :
    ‖s.eval (expandAt o U)‖ ≤ t := by
  let A : Atom G 1 := ⟨fun _ => s, fun _ => 1⟩
  refine healthy_leg A o U t (Finset.disjoint_of_subset_left (Finset.image_subset_image ?_) hU) 0
  intro x hx
  simp only [Atom.stencil, Finset.mem_insert, Finset.mem_biUnion] at hx
  rcases hx with rfl|⟨i,-,hh⟩
  · refine hs <| Finset.mem_union_left _ (List.mem_toFinset.mpr ?_)
    show (0:Cover) ∈ visits 0 s.walk
    cases s.walk <;> simp [visits]
  exact hs hh

/-- Pay one threshold for a slot EVEN for the value term, using health. For
positive order, the stronger raw bound on the derivatives already suffices. -/
theorem paid_slot (s : Slot) (hs : s.stencil ⊆ S) : Rate k P S 1 0 (s.eval (G:=G)) := by
  obtain ⟨c,hc,h⟩ := raw_slot (S:=S) (k:=k) (P:=P) (G:=G) s
  have hpos : 0 ≤ max 1 c := le_trans (by norm_num) (le_max_left _ _)
  refine ⟨max 1 c, hpos, fun b hb n o => ?_⟩
  have hh := h b hb n o
  have ht := b.threshold_pos.le
  simp only [pow_zero, pow_one] at hh ⊢
  refine ⟨hh.smooth, mul_nonneg hpos ht, fun l hl hd U hU => ?_⟩
  simp only [one_pow, mul_one]
  cases l with
  | nil =>
    exact (slot_bound s hs _ _ _ hU).trans <|
      le_mul_of_one_le_left ht (le_max_left _ _)
  | cons A l =>
    refine (hh.bound _ hl hd U hU).trans ?_
    rw [mul_one]
    have he : b.threshold ^ (A :: l).length ≤ b.threshold := by
      simpa only [pow_one] using pow_le_pow_of_le_one ht b.threshold_le
        (show 1 ≤ (A :: l).length by simp)
    exact mul_le_mul (le_max_right _ _) he (pow_nonneg ht _) hpos

end YM.Work.G07
