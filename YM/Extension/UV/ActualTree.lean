import YM.Extension.UV.HeartLimit
/-!
Compare the actual K in ANY realized Horizon.Suffices (including the producer) by the diagonal
crossing algebra, not by assuming the unretained metric path addresses already agree with a
chosen covariance formula. Equality only on potentials here, not full row away from them.
Counting conventions on each actual pair of period sides.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extension.UV.Linear
open Function Lattice RG Laurent Exterior Bloch Metric Next.Free Precision
open scoped Topology BigOperators
variable {G:Gauge} {A:Levels G} {c f : Side}

lemma K_transpose {n : Side} (J : Matrix (Body 2 n) (Body 2 n) ℝ) (h:J.transpose=J) : (Precision.K J).transpose=Precision.K J := by
  unfold Precision.K; rw [Matrix.transpose_mul,Matrix.transpose_mul,h,Matrix.transpose_transpose,Matrix.mul_assoc]

lemma mixed_action (S : StepData c f) (W W' : Matrix (Body 1 f) (Body 1 c) ℝ) (H : Matrix (Body 2 f) (Body 2 f) ℝ) (J: Matrix (Body 2 c) (Body 2 c) ℝ) (h : Inputs S W H J) :
  W'.transpose*Precision.K H*W + (S.kernel.penalty) • ((1-mean S*W').transpose*(1-mean S*W))=Precision.K J:=by
  have hv : 1-mean S*W=S.kernel.penalty⁻¹ • Precision.K J := by rw [h.dual]; abel
  calc
    _ = W'.transpose*(mean S).transpose*Precision.K J+(1-mean S*W').transpose*Precision.K J := by
      rw [Matrix.mul_assoc _ (Precision.K H) W,h.primal,hv,Matrix.mul_smul,smul_smul,mul_inv_cancel₀ S.kernel.penalty_pos.ne',one_smul,Matrix.mul_assoc]
    _ = _:= by rw [← Matrix.add_mul,Matrix.transpose_sub,Matrix.transpose_mul]; simp

lemma unique_K {S : StepData c f} {W W'} {H H' J J'} (h : Inputs S W H J) (h' : Inputs S W' H' J') (hK : Precision.K H=Precision.K H')
    (hh : H.transpose=H) (hj : J.transpose=J) : Precision.K J=Precision.K J' := by
  have h₁ := mixed_action S W W' H J h
  have h₂ := mixed_action S W' W H' J' h'
  have ht := (congr_arg Matrix.transpose h₁)
  rw [Matrix.transpose_add,Matrix.transpose_smul,Matrix.transpose_mul,Matrix.transpose_mul,Matrix.transpose_mul,K_transpose _ hh,K_transpose _ hj,Matrix.transpose_transpose,Matrix.transpose_transpose,← Matrix.mul_assoc,hK] at ht
  exact ht.symm.trans h₂

/-- The K presented on potentials (ordinary unmodified metric via the Bed). -/
def Kactual (M : Horizon A) (N m p : ℕ) := Precision.K ((M.H N m).metric.acts (A.S.side m p))

def rawH (A:Levels G) (N m p : ℕ) := (record (pulse A.clock.kernel.penalty (location A N m))).acts (A.S.side m p)

lemma canonical_top (A : Levels G) (n : ℕ) (l : ℕ) : rawH A n n l=1 := by
  unfold rawH; rw [loc_top]
  let k := A.clock.kernel.penalty
  let v := Train.top (A.clock.J n)
  have h := (heart_saves k A.clock.kernel.penalty_pos (A.clock.adm n) (fun _:Unit=> v)).1.whole ()
  have ht := (heart_true k A.clock.kernel.penalty_pos (A.clock.adm n) v).1
  exact (Whole.eq_on h (Whole.coin _) (fun p hp=> ((ht.echo p hp).trans ((top_metric k A.clock.kernel.penalty_pos _ (base_subset_realCube zone_pos hp)).2.trans (read_unit _ _).symm))) _).trans (Work.F08.acts_unit _)

lemma canonical_step (N m p : ℕ) (hm : m<N) : ∃ W, Inputs (A.clock.op m p) W (rawH A N (m+1) p) (rawH A N m p) := by
  let P := destination A N m
  have hx := (Flight.tangent (P:=P) A.clock.kernel (A.clock.adm m) (A.S.oneStep m p).exact_size).1
  change Inputs (A.clock.op m p) _ (rawH A N (m+1) p) _ at hx
  unfold rawH
  rw [loc_land A N m hm]
  exact ⟨_,hx⟩

lemma K_formula {S:MapPrices} {M : Horizon A} (h:M.Suffices S) (n m l : ℕ) (hh:m≤ n) : Kactual M n m l=Precision.K (rawH A n m l) := by
  induction hh using Nat.decreasingInduction with
  | self =>
    have he := (h.all n n le_rfl (A.S.side n l)).same
    unfold Kactual Precision.K; rw [Matrix.mul_assoc,he,h.top,canonical_top]; simp
  | of_succ m hm ih =>
    obtain ⟨W,hW⟩ := canonical_step (A:=A) n m l hm
    unfold Kactual
    exact unique_K (h.crossings n m l hm).trial hW ih (h.all n (m+1) (by omega) _).symmetric.1 (h.all n m (by omega) _).symmetric.1
end YM.Extension.UV.Linear
