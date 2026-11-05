import YM.Push.LOOP_COEFFICIENT.Grids
import YM.Push.LOOP_COEFFICIENT.LogKernel

/-! # Alias-pair mesh error and operator norm utilities -/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Function Matrix Set Filter Lattice Bloch Complex Laurent RG Exterior
open scoped Topology BigOperators ContDiff
variable {E F a b d : Type} [Fintype E] [Fintype F] [Fintype a] [Fintype b] [Fintype d] [DecidableEq a] [DecidableEq b] [DecidableEq d]
    {c f L : Side} {g : Ratio c f} {A : Grid f E a} {B : Grid c F b} {M : Matrix E F ℂ} {X : Matrix E E ℂ} {V : Profiles g.count a b} {U : Momentum → Matrix a a ℂ} {C η tol : ℝ}

omit [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] [DecidableEq d] in
lemma entry_cost {X : Matrix a d ℂ} {Y : Matrix d b ℂ} {C D : ℝ} (hX : ∀ i j, ‖X i j‖≤C) (hY : ∀ i j, ‖Y i j‖≤D) (i j) : ‖(X*Y) i j‖ ≤ Fintype.card d * (C * D) := by
  rw [Matrix.mul_apply]; refine (norm_sum_le ..).trans ((Finset.sum_le_sum (g:=fun _ => C*D) (fun k _ => by rw [norm_mul]; exact mul_le_mul (hX i k) (hY k j) (norm_nonneg _) ((norm_nonneg _).trans (hX i k)))).trans_eq (by simp))

open scoped Matrix.Norms.L2Operator in
lemma collect_bound {V : Profiles L a b} {p} {C M : Site L → ℝ}
    (hc : ∀ l, ‖(V (-p) (-l)).transpose‖ ≤ C l ∧ ‖V p l‖ ≤ C l) (hm : ∀ l, ‖U (aliasAt p l)‖ ≤ M l) :
    ‖collectPair V U p‖ ≤ (L.val:ℝ)^4 * ∑ l, C l ^2 * M l := by
  rw [collectPair,norm_smul,norm_pow,Complex.norm_natCast]; gcongr
  exact (norm_sum_le ..).trans (Finset.sum_le_sum fun l _ => (op_cost (op_cost (hc l).1 (hm l)) (hc l).2).trans_eq (by ring))

/-- Raw expansion cost. Counting constants here may be paid at fixed L. -/
def pullCost (L : Side) (a : Type) [Fintype a] (C : ℝ) := (L.val:ℝ)^8 * (C * Fintype.card a)^2
omit [DecidableEq a] in
lemma pullCost_nonneg : 0 ≤ pullCost L a C := by unfold pullCost; positivity

omit [Fintype b] in
lemma Projects.compares (h : Projects g A B M V) (hc : ∀ p, star p=p → ∀ l i j, ‖V p l i j‖ ≤ C) (hX : Compares A A X U tol) :
    Compares B B (M.transpose * X * M) (collectPair V U) (pullCost g.count a C * tol) := by
  constructor
  · exact pullPair_closed h hX.off
  intro p k hp i j; obtain ⟨z,rfl,rfl⟩ := hp
  rw [pullPair_sample h hX.off z]; dsimp only [collectPair]
  simp only [Matrix.smul_apply,Matrix.sum_apply,← smul_sub,← Finset.sum_sub_distrib,norm_smul,norm_pow,Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (Finset.sum_le_sum (g:=fun _ => Fintype.card a * ((Fintype.card a * (C * tol)) * C)) fun l _ => ?_)) (by positivity) |>.trans_eq ?_
  · let K := sample A A X (-aliasSite g z l) (aliasSite g z l) - U (aliasAt (quant c z) l)
    have hK (i j) : ‖K i j‖ ≤ tol := hX.price (alias_match g z l) i j
    rw [← Matrix.sub_apply,← Matrix.sub_mul,← Matrix.mul_sub]
    exact entry_cost (entry_cost (X:=(V (-quant c z) (-l)).transpose) (fun x y => hc _ (quant_matches c z).neg.bar _ y x) hK) (hc _ (quant_matches c z).bar l) i j
  simp [pullCost]; ring

omit [Fintype b] [DecidableEq b] in
lemma profile_bound (Cros : Cross L a b) (h : Row.strip Cros η C) (hη : 0 ≤ η) {p : Momentum} (hp : star p=p) (l : Site L) (i j) :
    ‖profile Cros p l i j‖ ≤ Fintype.card (Co L a) * (((L.val:ℝ)^4)⁻¹ * C) := by
  apply entry_cost (Y:=Row.read Cros p) (fun x y => ?_) (fun i j => ?_)
  · rw [Matrix.smul_apply,norm_smul,norm_inv,norm_pow,Complex.norm_natCast]; refine mul_le_of_le_one_right (by positivity) ?_
    simp only [returned, conjTranspose_apply,aliasBlock, of_apply,norm_star,hp]; split
    next => rw [mode_real _ _ (by rw [← alias_conj,hp])]
    simp
  apply (Row.constant_strip _ h i j).estimate
  intro i; have he := congr_fun hp i; rw [show (p i).im = 0 from Complex.conj_eq_iff_im.mp he,abs_zero]; exact hη

def axisCost (L : Side) (C : ℝ) := Fintype.card (Co L (TypeFace 1)) * (((L.val:ℝ)^4)⁻¹ * |C|)
lemma axis_bound {G : Gauge} {X : Cross L (TypeFace 1) (TypeFace 1)} (h : Row.strip X η C) (hη : 0 ≤ η) {p : Momentum} (hp : star p=p) (l : Site L) (i j : Axes G) : ‖axisProfile G X p l i j‖ ≤ axisCost L C := by
  unfold axisProfile paintSymbol; simp only [Matrix.of_apply]; split
  · exact (profile_bound _ h hη hp ..).trans (by unfold axisCost; gcongr; exact le_abs_self C)
  unfold axisCost; rw [norm_zero]; positivity

omit [Fintype a] in
lemma Compares.neg (h : Compares A A X U tol) : Compares A A (-X) (-U) tol := by simpa using h.smul (-1)
omit [Fintype a] in
lemma Compares.sub {Y U' tol'} (h : Compares A A X U tol) (h' : Compares A A Y U' tol') : Compares A A (X-Y) (U-U') (tol+tol') := by simpa only [sub_eq_add_neg] using h.add h'.neg
end YM.Push.Loops
