import YM.Push.RELAY_MARK.Avoid
import YM.Work.G03

/-!
# Linearized force sampler

Choose an arbitrary transport path to the positive source link. The transported
gradient from `.Wilson` is a literal *linear combination of Slots*, not
an abstract Euler current. Then compute its Peg linearization on the radial
Snap. At top homogeneous degree the large-cover-address symbol (prove by
scaling) is the negative ordinary Maxwell divergence. Keep both incidences
around each transverse axis. At finite mesh we retain the actual transverse
difference; making no assumption it equals the divergence integrand on arbitrary
higher jets too. Cf. .
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.Mark
open Function Set Filter MeasureTheory Wilson Lattice RG Source Source.Drops Work.G03 Labels InnerProductSpace
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators InnerProductSpace
variable {G : Gauge} {n : Side} {j d : ℕ}

section Force
variable (U : CoverConfig G) (w : Walk)

def atStem (w : Walk) (p : PlaqAxes) : Slot := ⟨w,p⟩
def backStem (w : Walk) (b : Axis) (p : PlaqAxes) : Slot := ⟨w ++ [negDir b],p⟩

lemma stem_up (b : Axis) (p : PlaqAxes) :
    G.adjoint (travel U 0 w) (stem U (stop 0 w) b p) = (atStem w p).eval U - (backStem w b p).eval U := by
  rw [stem,map_sub,← G.adjoint_mul]
  simp only [atStem,backStem,Slot.eval,travel_append,travel,Step.neg_read,mul_one,Slot.offset,
    stop_append,stop,Step.vec_neg,sub_eq_add_neg]

/-- Transfer signs at the positive link, including the order of plaquettes. -/
def hereTerm {V : Type*} [AddGroup V] (v : Slot → V) (w : Walk) (ν : Axis) (p : PlaqAxes) :=
    if p.val.1=ν then v (atStem w p)-v (backStem w p.val.2 p)
    else if p.val.2=ν then -(v (atStem w p)-v (backStem w p.val.1 p)) else 0

lemma force_stems (ν : Axis) : force U w (stop 0 w,ν)=∑ p : PlaqAxes, hereTerm (fun s => s.eval U) w ν p := by
  rw [force,field,map_sum]
  apply Finset.sum_congr rfl; intro p _
  rw [flux,hereTerm]; split
  next h => exact stem_up ..
  next h =>
    split
    next he => rw [map_neg]; exact congr_arg Neg.neg (stem_up ..)
    next he => rw [map_zero]

def linearForce (H : Hol G) (d : ℕ) (w : Walk) (ν : Axis) :=
    ∑ p : PlaqAxes, hereTerm (Blurb H d) w ν p

lemma force_glow (H : Hol G) (w : Walk) (ν : Axis) (h : Peg H d) (A : Snap G d) :
    linearForce H d w ν A = ∑ p : PlaqAxes, hereTerm (glow A) w ν p := by
  rw [linearForce,sum_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold hereTerm; split
  next h' => simp [h.initial]
  next h' => split <;> simp [h.initial]
end Force

section Discrete

lemma castPos_prev (x : Cover) (b : Axis) : castPos (x-step b)=castPos x-basis b := by
  apply eq_sub_of_add_eq; rw [← castPos_step, sub_add_cancel]

lemma samples (A : Snap G d) (u : Slot) : glow A u =
    ∑ k ∈ Finset.range (d-1), net (expand d A k) u.plaq.val.1 u.plaq.val.2 (castPos u.offset) 1 := by
  unfold glow
  rw [square_sum]; simp only [edge_sum,castPos_step]
  simp_rw [net,partial_eq_diff,Finset.sum_sub_distrib]; abel

def transverse (A : Taylor G j) (p : PlaqAxes) (b : Axis) (x : E4) :=
    net A p.val.1 p.val.2 x 1 - net A p.val.1 p.val.2 (x-basis b) 1

def incidence {V : Type*} [Zero V] [Neg V] (ν : Axis) (p : PlaqAxes) (F : Axis → V) :=
    if p.val.1=ν then F p.val.2 else if p.val.2=ν then -F p.val.1 else 0

lemma single_shot (A : Snap G d) (w : Walk) (ν : Axis) (p : PlaqAxes) :
    hereTerm (glow A) w ν p = ∑ k ∈ Finset.range (d-1), incidence ν p
      (fun b => transverse (expand d A k) p b (castPos (stop 0 w))) := by
  have ht (b) : (backStem w b p).offset=stop 0 w-step b := by simp [backStem,Slot.offset,stop_append,stop,sub_eq_add_neg]
  unfold hereTerm incidence; split
  next h =>
    rw [samples,samples,ht,castPos_prev,← Finset.sum_sub_distrib]; rfl
  next h =>
    split
    next he => rw [samples,samples,ht,castPos_prev,← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]; rfl
    simp

lemma shots (H : Hol G) (h : Peg H d) (A : Snap G d) (w : Walk) (ν : Axis) :
    linearForce H d w ν A =
      ∑ k ∈ Finset.range (d-1), ∑ p : PlaqAxes, incidence ν p (fun b => transverse (expand d A k) p b (castPos (stop 0 w))) := by
  rw [force_glow _ _ _ h]; simp_rw [single_shot]; rw [Finset.sum_comm]
end Discrete

section Limit

/-- Averaging the ordinary derivative over one more transverse interval;
keep the exact order of the averages fixed. -/
def trail (A : Taylor G j) (a b i : Axis) (x : E4) (t : ℝ) :=
  ∫ s : ℝ in 0..1, ∫ r : ℝ in 0..1, ∫ u : ℝ in 0..1,
    Maxwell.grad i (Maxwell.grad a (A.value b))
      (x + (t*s) • basis b + (t*r) • basis a + (t*(u-1)) • basis i)

lemma smooth_grad (A : Taylor G j) (a b : Axis) : ContDiff ℝ ∞ (Maxwell.grad a (A.value b)) :=
  contDiff_iff_contDiffAt.mpr fun _ => Maxwell.grad_smooth a (Tensor.diag_smooth _ ∞).contDiffAt (by simp)
lemma smooth_partial (A : Taylor G j) (a b i : Axis) : ContDiff ℝ ∞ (Maxwell.grad i (Maxwell.grad a (A.value b))) :=
  contDiff_iff_contDiffAt.mpr fun _ => Maxwell.grad_smooth i (smooth_grad A a b).contDiffAt (by simp)

lemma continuous_trail (A : Taylor G j) (a b i : Axis) : Continuous (fun p : E4 × ℝ => trail A a b i p.1 p.2) := by
  unfold trail
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  unfold uncurry
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  unfold uncurry
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact (smooth_partial A a b i).continuous.comp (by fun_prop)

private lemma avg_shift (A : Taylor G j) (a b i : Axis) (z : E4) (t : ℝ) :
    t • (∫ u : ℝ in 0..1, Maxwell.grad i (Maxwell.grad a (A.value b)) (z+(t*(u-1)) • basis i)) =
      Maxwell.grad a (A.value b) z - Maxwell.grad a (A.value b) (z-t • basis i) := by
  let q (u : ℝ) := z+(t*(u-1)) • basis i
  let f := Maxwell.grad a (A.value b)
  have h (u : ℝ) : HasDerivAt (fun v : ℝ => f (q v)) (t • Maxwell.grad i f (q u)) u := by
    have he : HasDerivAt q (t • basis i) u := by
      simpa only [mul_one,Pi.add_apply,zero_add] using!
        (hasDerivAt_const u z).add ((((hasDerivAt_id' u).sub_const 1).const_mul t).smul_const (basis i))
    apply HasDerivAt.congr_deriv (((smooth_grad A a b).differentiable (by simp) (q u)).hasFDerivAt.comp_hasDerivAt u he)
    rw [ContinuousLinearMap.map_smul]; rfl
  have hc : Continuous q := by unfold q; fun_prop
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => h u)
    (((smooth_partial A a b i).continuous.comp hc).const_smul t |>.intervalIntegrable (a:=0) (b:=1) ..)
  rw [intervalIntegral.integral_smul] at he
  simpa only [← sub_eq_add_neg,q, sub_self,zero_sub, mul_zero, zero_smul,add_zero,mul_neg,
    mul_one,neg_smul] using he

lemma shift_partial (A : Taylor G j) (a b i : Axis) (x : E4) (t : ℝ) :
    t • trail A a b i x t = meanPartial A a b x t - meanPartial A a b (x-t • basis i) t := by
  let g (z : E4) (s r : ℝ) := Maxwell.grad a (A.value b) (z + (t*s) • basis b + (t*r) • basis a)
  have h (s r : ℝ) : t • (∫ u : ℝ in 0..1, Maxwell.grad i (Maxwell.grad a (A.value b))
      (x + (t*s) • basis b + (t*r) • basis a + (t*(u-1)) • basis i)) = g x s r - g (x - t • basis i) s r := by
    rw [avg_shift]; unfold g
    congr 2; abel
  have ht (z : E4) : Continuous (uncurry (g z)) := (smooth_grad A a b).continuous.comp (by fun_prop)
  have he (z : E4) : Continuous (fun s => ∫ r in 0..1, g z s r) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (ht z) ..
  rw [trail,← intervalIntegral.integral_smul]
  have hm (s : ℝ) : t • (∫ r : ℝ in 0..1, ∫ u : ℝ in 0..1,
      Maxwell.grad i (Maxwell.grad a (A.value b)) (x + (t*s) • basis b + (t*r) • basis a + (t*(u-1)) • basis i)) =
        ∫ r : ℝ in 0..1,g x s r - g (x-t • basis i) s r := by
    rw [← intervalIntegral.integral_smul]; simp_rw [h]
  simp_rw [hm]
  have hi (z : E4) (s : ℝ) : IntervalIntegrable (g z s) volume 0 1 :=
    ((ht z).comp (continuous_const.prodMk continuous_id)).intervalIntegrable ..
  have hd (s : ℝ) := intervalIntegral.integral_sub (hi x s) (hi (x-t • basis i) s)
  simp_rw [hd]
  rw [intervalIntegral.integral_sub ((he x).intervalIntegrable ..) ((he (x-_)).intervalIntegrable ..)]; rfl

def arc (A : Taylor G j) (p : PlaqAxes) (b : Axis) (x : E4) (t : ℝ) :=
    trail A p.val.1 p.val.2 b x t - trail A p.val.2 p.val.1 b x t

def line (A : Taylor G j) (ν : Axis) (p : PlaqAxes) (x : E4) (t : ℝ) :=
    incidence ν p fun i => arc A p i x t

lemma scale_arc (A : Taylor G j) (p : PlaqAxes) (b : Axis) (x : E4) (t : ℝ) :
    t • arc A p b (t • x) t = t^j • transverse A p b x := by
  have he (a c : Axis) : meanPartial A a c (t • x-t • basis b) t = t^j • meanPartial A a c (x-basis b) 1 := by
    rw [← smul_sub,scale_partial]
  rw [arc,smul_sub,shift_partial,shift_partial,scale_partial,scale_partial,he,he]; unfold transverse net
  simp only [smul_sub]; abel

lemma scale_line (A : Taylor G j) (ν : Axis) (p : PlaqAxes) (x : E4) (t : ℝ) :
    t • line A ν p (t • x) t = t^j • incidence ν p (fun b=>transverse A p b x) := by
  unfold line incidence
  split
  next h => exact scale_arc ..
  next h => split <;> simp [scale_arc]

lemma continuous_line (A : Taylor G j) (a : Axis) (p : PlaqAxes) : Continuous (fun x : E4 × ℝ => line A a p x.1 x.2) := by
  unfold line incidence
  by_cases h : p.val.1=a
  · simp only [h,↓reduceIte]; exact (continuous_trail ..).sub (continuous_trail ..)
  by_cases he : p.val.2=a
  · simp only [h,he,↓reduceIte]; exact ((continuous_trail ..).sub (continuous_trail ..)).neg
  simp only [h,he,↓reduceIte]; exact continuous_const

lemma arc_zero (A : Taylor G j) (p : PlaqAxes) (b : Axis) (x : E4) :
    arc A p b x 0 = Maxwell.grad b (Tensor.diagonal (Maxwell.takeCurl A p.val.1 p.val.2)) x := by
  rw [Maxwell.takeCurl_diag]
  have he (a b : Axis) := (smooth_grad A a b).differentiable (by simp) x -- both
  simp only [arc,trail,zero_mul,zero_smul, add_zero,intervalIntegral.integral_const,
    sub_zero,one_smul]
  change _ = fderiv ℝ (Maxwell.grad p.val.1 (A.value p.val.2)-Maxwell.grad p.val.2 (A.value p.val.1)) x _
  rw [fderiv_sub (he _ _) (he _ _)]; rfl
end Limit

section Signing

-- At mesh zero Bianchi orientation means the sign of transverse direction contributes minus either way
private lemma grad_anti (A : Taylor G j) (i a b : Axis) (x : E4) :
    Maxwell.grad b (Tensor.diagonal (Maxwell.takeCurl A i a)) x = -Maxwell.grad b (Tensor.diagonal (Maxwell.takeCurl A a i)) x := by
  rw [(Maxwell.closedCurl A).antisymmetric i a]
  change fderiv ℝ (-Tensor.diagonal (Maxwell.takeCurl A a i)) x _ = _
  rw [fderiv_neg]; rfl

lemma continuum_current (A : Taylor G j) (ν : Axis) (x : E4) :
    ∑ p : PlaqAxes, line A ν p x 0 = - ∑ b : Axis, Maxwell.grad b (Tensor.diagonal (Maxwell.takeCurl A b ν)) x := by
  classical
  let v (b : Axis) := -Maxwell.grad b (Tensor.diagonal (Maxwell.takeCurl A b ν)) x
  have hν : v ν=0 := by
    unfold v; rw [Maxwell.takeCurl_diag]; simp [Maxwell.grad,Analysis.D]
  let w (p : PlaqAxes) (b : Axis) := if p.val=(b,ν) ∨ p.val=(ν,b) then v b else 0
  have he (p : PlaqAxes) : line A ν p x 0 = ∑ b : Axis, w p b := by
    rcases p with ⟨⟨a,b⟩,hp⟩; change a < b at hp
    by_cases ha : a=ν
    · subst a
      rw [Finset.sum_eq_single b]
      · unfold line incidence; split
        next h =>
          dsimp only; rw [arc_zero]; simp only [w, or_true,↓reduceIte]; exact grad_anti ..
        next h => exact False.elim (h rfl)
      · intro i _ hi; simp [w, Ne.symm hi,hp.ne']
      simp
    by_cases hb : b=ν
    · subst b
      rw [Finset.sum_eq_single a]
      · unfold line incidence; split
        next h => exact False.elim (ha h)
        next h =>
          split
          next h => dsimp only; rw [arc_zero]; simp only [w, true_or,↓reduceIte]; rfl
          next h => exact False.elim (h rfl)
      · intro i _ hi; simp [w, Ne.symm hi,ha]
      simp
    simp [w, line, incidence,ha,hb]
  have hl (b : Axis) : ∑ p : PlaqAxes, w p b = v b := by
    by_cases hb : b=ν
    · subst b; simp [w,hν]
    let p := PlaqAxes.ordered b ν hb
    have hp (q : PlaqAxes) : (q.val=(b,ν) ∨ q.val=(ν,b)) ↔ q=p := by
      rcases lt_or_gt_of_ne hb with h|h
      · have hh : p.val=(b,ν) := by simp [p,PlaqAxes.ordered,h.le]
        have hx : q.val≠(ν,b) := by rintro ht; have hi:=q.property; rw [ht] at hi; exact h.asymm hi
        simp only [hx,or_false]; exact ⟨fun ht => Subtype.ext (ht.trans hh.symm),fun ht => ht.symm ▸ hh⟩
      have hh : p.val=(ν,b) := by simp [p,PlaqAxes.ordered,h.le]
      have hx : q.val≠(b,ν) := by rintro ht; have hi:=q.property; rw [ht] at hi; exact h.asymm hi
      simp only [hx,false_or]; exact ⟨fun ht => Subtype.ext (ht.trans hh.symm),fun ht => ht.symm ▸ hh⟩
    simp [w,hp]
  simp_rw [he]; rw [Finset.sum_comm]; simp_rw [hl]; rw [← Finset.sum_neg_distrib]

lemma top_shell (A : Jet G) (k : ℕ)
    (h : ∀ (x : Cover) (ν : Axis), ∑ l ∈ Finset.range (k+1), ∑ p : PlaqAxes,
      incidence ν p (fun b => transverse (A l) p b (castPos x)) = 0) :
    ∀ (ν : Axis) (x : E4), ∑ b : Axis, Maxwell.grad b (Tensor.diagonal (Maxwell.takeCurl (A k) b ν)) x=0 := by
  intro ν x
  let f := fun p : E4 × ℝ => ∑ l ∈ Finset.range (k+1), p.2^(k-l) • (∑ q : PlaqAxes, line (A l) ν q p.1 p.2)
  have he (t : ℝ) (ht : 0<t) (y : Cover) : f (t • castPos y,t)=0 := by
    suffices hh : t • f (t • castPos y,t)=0 by exact (smul_eq_zero.mp hh).resolve_left ht.ne'
    calc
      _ = ∑ l ∈ Finset.range (k+1), t^k • ∑ q : PlaqAxes, incidence ν q (fun b => transverse (A l) q b (castPos y)) := by
        unfold f; rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        change t • (t^(k-i) • _) = _
        rw [smul_comm t,Finset.smul_sum]; simp_rw [scale_line]
        rw [← Finset.smul_sum,smul_smul,← pow_add,Nat.sub_add_cancel (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]
      _ = 0 := by rw [← Finset.smul_sum,h,smul_zero]
  have hc : Continuous f := by
    unfold f; exact continuous_finsetSum _ fun i _ => (continuous_snd.pow _).smul (continuous_finsetSum _ fun _ _ => continuous_line ..)
  have hv : Tendsto (fun t : ℝ => f (t • castPos (index t x),t)) (𝓝[>] 0) (𝓝 (f (x,0))) :=
    (hc.tendsto _).comp ((shrink_grid x).prodMk_nhds (tendsto_id.mono_left nhdsWithin_le_nhds))
  have hu : f (x,0)=0 := tendsto_nhds_unique_of_eventuallyEq hv tendsto_const_nhds <|
    eventually_nhdsWithin_of_forall fun t ht => he t ht _
  rw [show f (x,0)=∑ q : PlaqAxes, line (A k) ν q x 0 by
    unfold f; rw [Finset.sum_range_succ,Finset.sum_eq_zero (f:=fun i => _)]
    · simp
    intro i hi; dsimp only; rw [zero_pow (Nat.sub_ne_zero_of_lt (Finset.mem_range.mp hi)),zero_smul],
    continuum_current,neg_eq_zero] at hu
  exact hu

/-- In annihilator of all transported force linearizations on this degree cut:
last Taylor variable is on-shell. `w` doesn't matter at linear order, even when
constrained around the measured bond. No asserting the lower components are
on-shell when there are higher ones present. -/
lemma force_kernel_last (H : Hol G) (j : ℕ) (hp : Peg H (j+2)) (A : Snap G (j+2))
    (h : ∀ (e : Edge Cover) (w : Walk), stop 0 w=e.1 → avoids 0 w e → linearForce H (j+2) w e.2 A=0) :
    A ⟨j,by omega⟩ ∈ LinearMap.range Maxwell.gaugeJet := by
  let a := A ⟨j,(by omega)⟩
  have he : Maxwell.takeCurl a ∈ Maxwell.onShell G.Color j := by
    refine ⟨Maxwell.closedCurl _,?_⟩
    rw [show a=expand (j+2) A j by simp [a, expand]]
    refine top_shell _ _ (fun x i => ?_)
    obtain ⟨w,hw,hW⟩ := circumvent (x,i) 0 x
    have hi := h (x,i) w hw hW
    rw [shots H hp A w i, hw, show (j+2)-1=j+1 by omega] at hi; exact hi
  exact ⟨⟨_,he⟩, Maxwell.potential.symm_apply_apply a⟩
end Signing
end YM.Push.Mark
