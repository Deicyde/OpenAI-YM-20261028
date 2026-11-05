import YM.Push.LOOP_COEFFICIENT.Envelope
import YM.Push.LOOP_COEFFICIENT.LoopPorts


/-! # Two extra L powers on the inherited contribution -/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Function Filter Set Matrix Lattice Laurent Bloch RG Precision Exterior
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] {L : Side} {η σ C D M : ℝ} {p : Momentum}

def mass (l : Site L) := (1:ℝ)+pdist l
lemma mass_one (l : Site L) : 1 ≤ mass l := by unfold mass; simp
lemma mass_neg (l : Site L) : mass (-l) = mass l := by simp only [mass,pdist_neg]

/-- ℓ² (not ℓ^∞) over aliases of **raw** polarizations with two extra fine shifts.
Only required on a complex centered cube; weight uses integer max-component
separation, not a norm of coarse momentum. Uniform `M` required for the
irrelevant coupling estimate. -/
def Spread (V : Loops.Profiles L a b) (η M : ℝ) : Prop := ∀ p ∈ Center η, ∃ w : Site L → ℝ, (∀ l, Entries (V p l) (w l)) ∧
    ∑ l, (mass l ^2 * w l)^2 ≤ (M/(L.val:ℝ))^2
lemma alias_norm (hp : p∈Center η) (l : Site L) : ‖aliasAt p l‖ ≤ ((3*Real.pi+η)/L.val) * mass l := by
  have he := (abs_nonneg _).trans_lt (hp.1 0)
  have h1 := mass_one l
  rw [aliasAt,mon, ← smul_add, norm_smul,norm_inv,Complex.norm_natCast,inv_mul_eq_div,mul_comm _ (mass l),← mul_div_assoc,div_le_div_iff_of_pos_right (side_pos _)]
  refine (norm_add_le ..).trans ?_
  have hr : ‖Laurent.reciprocal (Lattice.lift l)‖ ≤ 2*Real.pi*(pdist l) := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_; simp only [reciprocal,norm_mul,Complex.norm_two,Complex.norm_real,Complex.norm_intCast,← Int.cast_abs]
    rw [Real.norm_of_nonneg Real.pi_pos.le,← Int.natCast_natAbs, Int.cast_natCast]; gcongr; exact component_le l i
  unfold mass; nlinarith [norm_in_center hp,Real.pi_pos,mul_nonneg (add_nonneg Real.pi_pos.le he.le) (Nat.cast_nonneg (α:=ℝ) (pdist l))]

variable {V : Loops.Profiles L a b} {U : Momentum → Matrix a a ℂ}
omit [DecidableEq a] [Fintype b] in
private lemma one_collect (hu : ∀ l : Site L, Entries (U (aliasAt p l)) (C * mass l ^4)) (hv : Spread V η M) (hp : p∈Center η) (hC : 0 ≤ C) :
    Entries (collectPair V U p) ((Fintype.card a : ℝ)^2 * L.val^2 * M^2 * C) := by
  obtain ⟨w,hw,h⟩ := hv p hp; obtain ⟨v,hv,h'⟩ := hv (-p) (center_neg hp)
  have hv' : ∑ l, (mass l ^2 * v (-l))^2 ≤ (M/L.val)^2 := by
    conv at h' => lhs; rw [← Equiv.sum_comp (Equiv.neg (Site L))]
    simpa [mass_neg] using h'
  have he : ∑ l, v (-l)*(C*mass l^4)*w l ≤ C * (M/L.val)^2 := by
    calc
      _ ≤ ∑ l,C / 2 * ((mass l^2*v (-l))^2+(mass l^2*w l)^2) := Finset.sum_le_sum fun l _ => by nlinarith [mul_nonneg hC (sq_nonneg ((mass l^2*v (-l))-(mass l^2*w l)))]
      _ ≤ C / 2 * ((M/L.val)^2+(M/L.val)^2) := by rw [← Finset.mul_sum, Finset.sum_add_distrib]; gcongr
      _ = _ := by ring
  refine ((Entries.sum Finset.univ (fun l _ => (((hv (-l)).transpose.mul (hu l)).mul (hw l)))).smul _).mono ?_
  rw [norm_pow, Complex.norm_natCast]; let d := (Fintype.card a : ℝ)
  change (L.val:ℝ)^4 * ∑ l, d * (d * (v (-l) * (C * mass l^4)) * w l) ≤ _
  simp_rw [show ∀ l, d * (d * (v (-l) * (C * mass l^4)) * w l) = d^2 * (v (-l)*(C*mass l^4)*w l) from fun l => by ring,← Finset.mul_sum]
  calc
    _ ≤ (L.val:ℝ)^4*(d^2*(C*(M/L.val)^2)) := by gcongr
    _ = _ := by dsimp [d]; field_simp



open scoped Matrix.Norms.L2Operator





variable {R : LoopData G L} {W : PathData G} {H : Precision.Bed}



end YM.Push.Loops
