import YM.Extra.MULTISOURCE_TRAJECTORIES.Algebra
import YM.Further.THRESHOLD_SOURCE_RESTART.Capital
import YM.Push.ABSOLUTE_SUMS.Breadth
/-!
# Restricted fundamental exponential in deployment Poly

Product rule even with the default non-submultiplicative sup norm.
Consume dynamic parameters through derivatives ONLY for the expansion
verification; not using fine/coarse direction bounds of scalar estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.ThresholdSourceRestart.Clusters
open Function Filter Set MeasureTheory Wilson RG Lattice Marker Overlay
open Push.Corrected
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {V : Type*} [Fintype V] [DecidableEq V] {R : Census V}

-- exp retaining exactly marker nilpotence
abbrev thick (x : Poly R) := x.part R.quiet
def light (x : Poly R) := x-Poly.send R.quiet (thick x)
omit [Fintype V] in
lemma light_weight (x : Poly R) : thick (light x)=0 := by simp [light,thick,Extra.Trajectories.part_sub]

def electric (X : Poly R) := (Complex.exp (thick X)) • Poly.pass (light X)

lemma no_power : electric (0 : Poly R)=1 := by simp [electric,thick,light,Extra.Trajectories.pass_zero]
lemma add_power (x y : Poly R) : electric (x+y)=electric x*electric y := by
  have he : light (x+y)=light x+light y := by simp only [light,thick,Poly.part_plus,Extra.Trajectories.send_add]; abel
  unfold electric; rw [he,Extra.Trajectories.pass_add (light_weight x) (light_weight y),
    show thick (x+y)=_ from Poly.part_plus _ _ R.quiet, Complex.exp_add,Algebra.smul_mul_assoc,
    Algebra.mul_smul_comm,smul_smul]
lemma power_cancel (x : Poly R) : electric (-x)*electric x=1 := by rw [← add_power, neg_add_cancel,no_power]
lemma power_cont : Continuous (electric (V:=V) (R:=R)) := (Complex.continuous_exp.comp (Poly.part_cont _)).smul
    (Poly.pass_cont.comp (continuous_id.sub ((Bands.sends _).comp (Poly.part_cont _))))

section Deriv
local instance : NormedSpace ℝ (Poly R) := inferInstanceAs (NormedSpace ℝ (R.Mode → ℂ))
local instance : SMulCommClass ℝ ℂ (Poly R) := inferInstanceAs (SMulCommClass ℝ ℂ (R.Mode→ℂ))

variable {f g : ℝ → Poly R} {x y : Poly R} {t : ℝ}
-- continuous law applies to Poly with a consistent topology; componentwise derivation
omit [Fintype V] in
lemma speed : HasDerivAt f x t ↔ ∀ i, HasDerivAt (fun s => (f s).part i) (x.part i) t :=
    hasDerivAt_pi
omit [Fintype V] in
lemma current_product (h : HasDerivAt f x t) (h' : HasDerivAt g y t) : HasDerivAt (fun v=>f v * g v)
    (x*g t+f t*y) t := by
  apply speed.mpr; intro i
  have he (s : R.Mode) (b : R.Mode) : HasDerivAt
      (fun v => if Poly.merges s b i then (f v).part s*(g v).part b else 0)
      ((if Poly.merges s b i then x.part s*(g t).part b else 0)+(if Poly.merges s b i then (f t).part s*y.part b else 0)) t := by
    split
    · exact ((speed.mp h) s).fun_mul ((speed.mp h') b)
    simpa using hasDerivAt_const t (0:ℂ)
  simp only [Poly.part_mul,Poly.part_plus,Poly.part_mul,← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => he i j
omit [Fintype V] in
lemma injected {a : ℝ → ℂ} {b : ℂ} (ht : HasDerivAt a b t) : HasDerivAt (fun u => Poly.bead R (a u))
    (Poly.bead R b) t := by
  apply speed.mpr; intro i
  change HasDerivAt (fun u => Poly.part (Poly.send _ _) _) (Poly.part (Poly.send R.quiet _) i) t
  simp_rw [Poly.part_send]; split; exact ht; exact hasDerivAt_const ..
omit [Fintype V] in
lemma powered (h : HasDerivAt f x t) (i : ℕ) : HasDerivAt (fun u => f u^i) ((i:ℂ) • (f t^(i-1)*x)) t := by
  induction i with
  | zero => simp only [Nat.cast_zero,pow_zero,zero_smul]; exact hasDerivAt_const ..
  | succ n ih =>
    simp_rw [pow_succ, Nat.add_sub_cancel]
    convert current_product ih h using 1
    push_cast; rw [Algebra.smul_mul_assoc]
    cases n with
    | zero => simp
    | succ n =>
      rw [add_smul _ 1, one_smul, show f t^(n+1-1)*x*f t= f t^(n+1)*x by rw [pow_succ, Nat.add_sub_cancel]; ring]

lemma permanent (X Y : Poly R) (h : thick X=0) (he : thick Y=0) : X^Fintype.card V * Y=0 := by
  ext i; rw [Poly.part_nil,Poly.part_mul]; refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  split
  next hb =>
    by_cases hz : b=R.quiet
    · subst b; rw [show Y.part R.quiet=0 from he,mul_zero]
    rw [Poly.high X h _ a ?_,zero_mul]
    have ha := Finset.card_le_univ i.val
    have hh : i.val.card=a.val.card+b.val.card := hb.2 ▸ Finset.card_union_of_disjoint hb.1
    have ht : 0<b.val.card := Finset.card_pos.mpr <| Finset.nonempty_iff_ne_empty.mpr (fun h => hz (Subtype.ext h))
    omega
  rfl

lemma smooth_power (h : HasDerivAt f x t) (hp : thick (f t)=0) (hx : thick x=0) :
    HasDerivAt (fun s => Poly.pass (f s)) (Poly.pass (f t)*x) t := by
  let b (i : ℕ) := (i.factorial:ℂ)⁻¹ • ((i:ℂ) • (f t^(i-1)*x))
  have he (i : ℕ) : HasDerivAt (fun s => (i.factorial:ℂ)⁻¹ • (f s)^i) (b i) t :=
    (powered h i).const_smul ((i.factorial:ℂ)⁻¹)
  -- boundary term of the truncated polynomial derivative
  let c := Fintype.card V
  have ht : ∑ i∈Finset.range (c+1), b i=Poly.pass (f t)*x := by
    rw [Finset.sum_range_succ',Poly.pass, Finset.sum_mul, Finset.sum_range_succ]
    have h' j : b (j+1) = (j.factorial:ℂ)⁻¹ • f t^j * x := by
      rw [Algebra.smul_mul_assoc]; unfold b; rw [smul_smul,Nat.add_sub_cancel]
      congr 1; rw [Nat.factorial_succ, Nat.cast_mul]; push_cast; field_simp
    rw [show b 0=0 by simp [b], Algebra.smul_mul_assoc ((Fintype.card V).factorial:ℂ)⁻¹ _ x,permanent _ _ hp hx, smul_zero,add_zero,add_zero]
    apply Finset.sum_congr rfl; intro i _; exact h' i
  rw [← ht]; exact HasDerivAt.fun_sum (fun i _ => he i)

/-- Only used for verifying this unforced gas series. -/
lemma express_deriv (h : HasDerivAt f x t) : HasDerivAt (electric ∘ f) (electric (f t)*x) t := by
  let H (b : ℝ) := Poly.bead R (Complex.exp (thick (f b)))
  have he : HasDerivAt H (Poly.bead R (Complex.exp (thick (f t))*thick x)) t := injected (speed.mp h R.quiet).cexp
  have hh : HasDerivAt (fun b=>light (f b)) (light x) t := h.sub (injected (R:=R) (speed.mp h _))
  have v := current_product he (smooth_power hh (light_weight _) (light_weight _))
  rw [show electric ∘ f=fun b=>H b * Poly.pass (light (f b)) from funext fun b=> (Poly.product_bead ..).symm]
  convert v using 1
  rw [electric, ← Poly.product_bead,map_mul]; unfold H
  change _ = _ + _ * ( _ * (x - Poly.bead R (thick x)))
  ring
end Deriv
end YM.Further.ThresholdSourceRestart.Clusters
