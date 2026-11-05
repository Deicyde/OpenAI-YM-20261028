import YM.ProjectorNext.PROJECTOR_CALIBRATION.Unpack
import YM.Push.CUTOFF_PROJECTORS.Bank

/-! # The equation expression on the actual torus setup -/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Calibration
open Lattice Wilson RG Source Source.Drops Function Filter Labels Next.Foundations Push Push.CutoffProjectors Tensor
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff InnerProductSpace
variable {G : Gauge} {H : Hol G} {d : ℕ}
namespace Machine
variable (M : Machine H d) (F : Labels.Frame G d)
variable {n : Side} {s : Finset Cover}

lemma rate_port (h : M.Release s) (hn : Opened s n) (o : Site n) (x : F.Coeff) (U : Config G n) (e : Edge (Site n)) (j : G.ColorIndex) :
    Packet.derivative (fun Z => M.weights F o x Z e j) e j U =
      ∑ i : F.Index, ∑ w : M.Outlet, if e=M.port o w then x i *
        left (M.valve F i w (colors G j)) (M.address w) (colors G j) (expandAt o U) else 0 := by
  change deriv (fun t : ℝ => M.weights F o x (increment U (t • Packet.forward e j)) e j) 0 = _
  simp_rw [weights_eval]
  apply HasDerivAt.deriv
  refine HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum (A:=fun w t => if e=M.port o w then
    x i * M.valve F i w (colors G j) (expandAt o (increment U (t • Packet.forward e j))) else 0) fun w _ => ?_
  by_cases he : e=M.port o w
  · subst e; simp only [↓reduceIte]
    have ht := M.released F w i j s h
    have hh (t : ℝ) : M.valve F i w (colors G j) (expandAt o (increment U (t • Packet.forward (M.port o w) j))) =
        M.valve F i w (colors G j) (pushLink (expandAt o U) (Pi.single (M.address w) (colors G j)) t) :=
      matched_increment _ ht.supported hn o U (M.address w) (h.start w) (colors G j) t
    simp_rw [hh]
    exact (ht.authentic (expandAt o U) (M.address w) (colors G j)).const_mul _
  simp_rw [if_neg he]; exact hasDerivAt_const ..

private lemma along_edge {E I : Type*} [DecidableEq E] [Fintype E] [Fintype I] {m : E} (x : I → E → ℂ) :
    ∑ e, ∑ j, (if e=m then x j e else (0:ℂ)) = ∑ j,x j m := by rw [Finset.sum_comm]; simp

private lemma engines {I E W J : Type*} [Fintype I] [Fintype E] [DecidableEq E] [Fintype W] [Fintype J]
    (p : W → E) (t : I → ℂ) (a b : I → W → J → ℂ) (g : E → J → ℂ) (β : ℂ) :
    ∑ e, ∑ j, ((∑ i, ∑ w, if e=p w then t i*a i w j else 0) * g e j - β * (∑ i, ∑ w, if e=p w then t i*b i w j else 0)) =
      ∑ i, t i*((∑ w, ∑ j, a i w j*g (p w) j) - β*(∑ w, ∑ j,b i w j)) := by
  let f (e : E) (j i w) := if e=p w then t i*(a i w j*g e j - β*b i w j) else 0
  have hx (e j) : (∑ i, ∑ w, if e=p w then t i*a i w j else 0) * g e j - β*(∑ i, ∑ w, if e=p w then t i*b i w j else 0) =
      ∑ i, ∑ w, f e j i w := by
    simp_rw [Finset.sum_mul,Finset.mul_sum,← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun w _ => ?_
    unfold f; split_ifs <;> ring
  simp_rw [hx, show ∀ e, ∑ j, ∑ i, ∑ w,f e j i w = ∑ i, ∑ w, ∑ j,f e j i w from fun e => by
    rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm]
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]; unfold f
  have he (w : W) : (∑ e, ∑ j, if e=p w then t i*(a i w j*g e j-β*b i w j) else 0) = _ :=
    along_edge (m:=p w) (fun j e => t i*(a i w j*g e j-β*b i w j))
  simp_rw [he,mul_sub,Finset.mul_sum,Finset.sum_sub_distrib]

lemma on_torus (h : M.Release s) (hn : Opened s n) (o : Site n) (x : F.Coeff) (U : Config G n) (β : ℝ) :
    (∑ (e : Edge (Site n)), ∑ j : G.ColorIndex,
      (M.weights F o x U e j * ↑(Packet.derivative energy e j U : ℝ) -
        (β:ℂ)⁻¹ * Packet.derivative (fun Z => M.weights F o x Z e j) e j U)) =
      ∑ i : F.Index, x i*(M.energyLeg F i (expandAt o U)-(β:ℂ)⁻¹*M.divLeg F i (expandAt o U)) := by
  let a := fun (i : F.Index) (w : M.Outlet) j => M.valve F i w (colors G j) (expandAt o U)
  let b := fun (i : F.Index) (w : M.Outlet) j => left (M.valve F i w (colors G j)) (M.address w) (colors G j) (expandAt o U)
  let g := fun (e : Edge (Site n)) j => (↑(inner ℝ (colors G j) (Calibration.gradient U e.1 e.2)) : ℂ)
  simp_rw [rate_port M F h hn, weights_eval, Calibration.packet_energy]
  rw [engines (M.port o) x a b g (β:ℂ)⁻¹]
  have he (i : F.Index) (w : M.Outlet) : ∑ j, a i w j*g (M.port o w) j = M.valve F i w (gradient (expandAt o U) (M.address w).1 (M.address w).2) (expandAt o U) := by
    have hx := M.energyContract F (expandAt o U) w i
    rw [gradient_at] at hx ⊢; exact hx
  simp_rw [he]; rfl

private lemma sumFit {K I : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    (w : Finset I) (f : I → CoverConfig G → K) (h : ∀ i∈w, Empirical s (f i)) :
    Empirical s fun U => ∑ i∈w,f i U := by
  classical
  induction w using Finset.induction_on with
  | empty => simp; exact Empirical.constant _
  | insert a w ha ih =>
    simp only [Finset.sum_insert ha]; exact ((h a (by simp)).pair (ih fun i hi => h i (by simp_all))).comp (L:=fun p => p.1+p.2) (contDiff_fst.add contDiff_snd)

lemma release_energy (h : M.Release s) (i : F.Index) : Empirical s (M.energyLeg F i) := by
  let f (w : M.Outlet) j U := M.valve F i w (colors G j) U
  have he : M.energyLeg F i = fun U => ∑ w : M.Outlet, ∑ j : G.ColorIndex,
      f w j U * (inner ℝ (colors G j) (Calibration.gradient U (M.address w).1 (M.address w).2) : ℝ) :=
    funext fun U => Finset.sum_congr rfl fun w _ => (M.energyContract F U w i).symm
  rw [he]
  refine sumFit _ _ fun w _ => sumFit (K:=ℂ) _ (fun (j : G.ColorIndex) (U : CoverConfig G) => f w j U * (inner ℝ (colors G j) (gradient U (M.address w).1 (M.address w).2) : ℝ)) fun j _ => ?_
  exact ((M.released F w i j s h).pair (h.force w)).comp (L:=fun p => p.1 * Complex.ofRealCLM ((innerSL ℝ (colors G j)) p.2))
    (contDiff_fst.mul (Complex.ofRealCLM.contDiff.comp ((innerSL ℝ (colors G j)).contDiff.comp contDiff_snd)))

lemma release_div (h : M.Release s) (i : F.Index) : Empirical s (M.divLeg F i) := by
  unfold divLeg; refine sumFit _ _ fun w _ => sumFit _ _ fun j _ => (M.released F w i j s h).retains (M.address w) (colors G j)

variable {C : Family G} (M₀ : Machine C.params d) {N p : ℕ} (E : Packet C d N p)

/-- The genuine local formula for the particle J after unwrapping.
Multiplication by `a_N^d`, as used when computing the readout. -/
theorem undressed (h : M₀.Release s) (hn : Opened s (C.side N p)) (he : M₀.lined E)
    (x : equationSpace (C.labels.level d)) (U : Config G (C.side N p)) :
    (C.S.a N:ℂ)^d * E.Jorigin x U =
      let F := C.labels.level d; let t : ℝ := (C.path.levels.clock.threshold N)
      let Z := expandAt (0:Site (C.side N p)) U
      ∑ i : F.Index, (↑(t⁻¹ ^ (F.grades i).2) : ℂ)*x.val i *
        (M₀.energyLeg F i Z-(C.beta N p : ℂ)⁻¹*M₀.divLeg F i Z) := by
  unfold Packet.Jorigin; rw [← mul_assoc,mul_inv_cancel₀ (pow_ne_zero d (Complex.ofReal_ne_zero.mpr (C.S.a_pos N).ne')),one_mul]
  simp_rw [threaded M₀ E he x, on_torus M₀ (C.labels.level d) h hn]; rfl

/-- And directly on the finite test used by the bank. -/
theorem amount_eq (h : M₀.Release s) (hn : ∀ x∈s,∀ a : Axis, 20*((x a).natAbs+1)≤(C.side N p).val)
    (he : M₀.lined E) (x : equationSpace (C.labels.level d)) (i : Lens G d) :
    E.amount x i =
      let F := C.labels.level d; let t : ℝ := (C.path.levels.clock.threshold N)
      iteratedDeriv (i.2:ℕ) (fun u => let Z := C.params.links d (t • i.1) u
        ∑ j : F.Index, (↑(t⁻¹ ^ (F.grades j).2) : ℂ)*x.val j *
        (M₀.energyLeg F j Z-(C.beta N p : ℂ)⁻¹*M₀.divLeg F j Z)) 0 := by
  dsimp only
  unfold Packet.amount
  let F := C.labels.level d
  let t : ℝ := C.path.levels.clock.threshold N
  apply congr_arg (fun y => iteratedDeriv (i.2:ℕ) y 0)
  funext u; rw [undressed M₀ E h (opened s hn) he]; dsimp only
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [fitsTest s (M₀.energyLeg F j) (M₀.release_energy F h j).supported hn 0 C.params d (t • i.1),
      fitsTest s (M₀.divLeg F j) (M₀.release_div F h j).supported hn 0 C.params d (t • i.1)]

end Machine
end YM.ProjectorNext.Calibration
