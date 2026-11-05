import YM.Push.LOOP_COEFFICIENT.Frame.Banner

/-!
# Patch-shift recipes on coarse cell grids
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Frames
open Function Set Filter Matrix Lattice Laurent RG Bloch Complex Block Portal
open scoped Topology ContDiff BigOperators Matrix.Norms.L2Operator
variable {a b c d E F : Type} [Fintype a] [Fintype b] [Fintype c] [Fintype d] [Fintype E] [DecidableEq a] [DecidableEq b] [DecidableEq c] [DecidableEq d] [DecidableEq E] [DecidableEq F] [Fintype F]
  {n L : Side} {η D C A : ℝ} {T : Grid n F c} {B : Grid n E b}

structure Atlas (a b : Type) where
  point : a → Cover
  leaf : a → b

namespace Atlas
variable (R : Atlas a b)
def fetch (B : Grid n E b) (x : Site n) : Matrix a E ℝ := of fun i j => if B j = (x+wrap n (R.point i), R.leaf i) then 1 else 0
def scan (q : Momentum) : Matrix a b ℂ := of fun i j => if R.leaf i=j then mode q (R.point i) else 0
omit [Fintype a] [Fintype b] [DecidableEq a] in
lemma fetch_eval (x : Site n) (v : E → ℝ) i : (R.fetch B x *ᵥ v) i = v (B.symm (x+wrap n (R.point i),R.leaf i)) := by simp [mulVec,dotProduct,fetch,B.apply_eq_iff_eq_symm_apply,ite_mul]
omit [Fintype a] [DecidableEq a] in
lemma scan_eval (q) (v : CSpace b) (i : a) : (R.scan q *ᵥ v) i = mode q (R.point i) * v (R.leaf i) := by simp [scan,mulVec,dotProduct,ite_mul]
omit [Fintype a] [DecidableEq a] in
lemma loads (B : Grid n E b) : Loads B (R.fetch B) R.scan := by
  intro x q k hq v; ext1 i
  simp only [Pi.smul_apply, smul_eq_mul,scan_eval]
  rw [mulVec,dotProduct]; simp [cmat_apply,approached,fetch, apply_ite (fun x : ℝ => (x:ℂ)), B.apply_eq_iff_eq_symm_apply,ite_mul,plane_apply,cell_add,hq.read,mul_assoc]
omit [DecidableEq a] in
lemma beam : ∃ C>0,Banner R.scan η C := by
  let K := 1 + ∑ i, Real.exp (η*size (R.point i)); have hK : 0<K := by unfold K; positivity
  let M := matrixCost a b; have hM := matrixCost_nonneg a b
  refine ⟨1+M*K,by dsimp only [M]; positivity, by dsimp only [M]; positivity,fun q _ => analyticMatrix (fun i j => by simp only [scan,Matrix.of_apply]; split; unfold mode; fun_prop; exact contDiffAt_const),fun _ _ _ => by ext; simp [scan],fun q hq => (matrix_norm hK.le (fun i j => ?_)).trans (le_add_of_nonneg_left zero_le_one)⟩
  simp only [scan,of_apply]; split; swap; simpa using hK.le
  exact ((reward _ _ _ fun j => (hq j).le).trans (Finset.single_le_sum (fun k (_ : k∈Finset.univ) => (Real.exp_pos (η*size (R.point k))).le) (Finset.mem_univ i))).trans (le_add_of_nonneg_left zero_le_one)
end Atlas

def combine {R : Type*} (M : Matrix a c R) (N : Matrix b c R) := Matrix.of (Sum.elim (fun i => M i) (fun i => N i))
omit [Fintype a] [Fintype b] [Fintype c] [DecidableEq a] [DecidableEq b] [DecidableEq c] in
lemma cmat_combine (M : Matrix a c ℝ) (N : Matrix b c ℝ) : cmat (combine M N) = combine (cmat M) (cmat N) := by ext (i|j) a <;> rfl
variable {M : Site n → Matrix a F ℝ} {N : Site n → Matrix b F ℝ} {U : Momentum → Matrix a c ℂ} {V : Momentum → Matrix b c ℂ}
omit [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] [DecidableEq F] in
lemma Loads.join (hm : Loads T M U) (hn : Loads T N V) : Loads T (fun x => combine (M x) (N x)) (fun q => combine (U q) (V q)) := by intro x q k hq v; rw [cmat_combine]; ext1 (i|i); exact congr_fun (hm _ hq _) i; exact congr_fun (hn _ hq _) i
omit [DecidableEq a] [DecidableEq b] [DecidableEq c] in
lemma mag_combine (M : Matrix a c ℂ) (N : Matrix b c ℂ) (x : CSpace c) : mag (combine M N *ᵥ x)^2 = mag (M *ᵥ x)^2 + mag (N *ᵥ x)^2 := (mag_sum _).symm
omit [DecidableEq a] [DecidableEq b] in
lemma op_combine (M : Matrix a c ℂ) (N : Matrix b c ℂ) (h₁ : ‖M‖≤A) (h₂ : ‖N‖ ≤ C) : ‖combine M N‖ ≤ A+C := by
  have ha := (norm_nonneg _).trans h₁; have hc := (norm_nonneg _).trans h₂
  refine op_of_mag _ (add_nonneg ha hc) fun x => le_of_sq_le_sq ?_ (mul_nonneg (add_nonneg ha hc) (mag_nonneg _))
  rw [mag_combine,add_mul]; have he := mag_nonneg x
  nlinarith [(mag_op M x).trans (mul_le_mul_of_nonneg_right h₁ he),mag_nonneg (M *ᵥ x), (mag_op N x).trans (mul_le_mul_of_nonneg_right h₂ he),mag_nonneg (N *ᵥ x)]
omit [DecidableEq a] [DecidableEq b] in
lemma Banner.join (h : Banner U η A) (h' : Banner V η C) : Banner (fun q => combine (U q) (V q)) η (A+C) := by
  refine ⟨add_nonneg h.nonneg h'.nonneg, fun q hq => analyticMatrix (fun i j => ?_),fun q hq x => congr_arg₂ combine (h.periodic q hq x) (h'.periodic q hq x),fun q hq => op_combine _ _ (h.bound q hq) (h'.bound q hq)⟩; cases i; exact analyticComponent (h.smooth _ hq) _ _; exact analyticComponent (h'.smooth _ hq) _ _
omit [Fintype a] [DecidableEq a] [DecidableEq E] [DecidableEq F] in
lemma Loads.trans {X : Momentum → Matrix b c ℂ} {Q : Momentum → Matrix a b ℂ} {L : Matrix E F ℝ} {W : Site n → Matrix a E ℝ} (hx : ∀ q k, Matches q k → Routed B T k k (cmat L) (X q)) (h : Loads B W Q) : Loads T (fun y => W y * L) (fun q => Q q * X q) := by
  intro y q k hq v; rw [cmat_mul,← Matrix.mulVec_mulVec,(hx _ _ hq).vector, h y hq, Matrix.mulVec_mulVec]
omit [DecidableEq b] in
lemma Banner.mul {X : Momentum → Matrix b c ℂ} {Y : Momentum → Matrix c d ℂ} (h : Banner X η A) (h' : Banner Y η C) : Banner (fun q => X q * Y q) η (A*C) := ⟨mul_nonneg h.nonneg h'.nonneg,fun q hq => analyticMul (h.smooth q hq) (h'.smooth _ hq), fun q hq x => congr_arg₂ (· * ·) (h.periodic q hq x) (h'.periodic q hq x), fun q hq => op_cost (h.bound q hq) (h'.bound _ hq)⟩
omit [DecidableEq a] in
lemma Banner.weaken (h : Banner U η A) (ha : A≤C) : Banner U η C := ⟨h.nonneg.trans ha,h.smooth,h.periodic,fun _ hq => (h.bound _ hq).trans ha⟩
end YM.Push.Loops.Frames
