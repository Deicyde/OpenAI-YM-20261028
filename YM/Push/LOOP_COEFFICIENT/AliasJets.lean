import YM.Push.LOOP_COEFFICIENT.KineticLines

/-!
# True column profiles from translation rows and alias pullback of the transverse jet

Principal & nonprincipal jet hypotheses refer to raw output wave amplitudes,
not the unitary DFT in either volume.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Function Filter Matrix Complex Bloch Laurent Lattice Exterior
open scoped Topology ContDiff BigOperators Matrix.Norms.L2Operator
variable {G : Gauge} {L : Side} {a b c : Type} [Fintype a] [Fintype b] [Fintype c] [DecidableEq a] [DecidableEq b] [DecidableEq c]
  {η C : ℝ} {p : Momentum}

lemma alias_diff (k : Site L) : ContDiff ℂ ω (fun p => aliasAt p k) := by unfold aliasAt; fun_prop
lemma alias_shift (k : Site L) (p : Momentum) (x : Cover) : ∃ y : Cover, aliasAt (p+reciprocal x) k = aliasAt p (k+wrap L x) + reciprocal y := by
  obtain ⟨y,hy⟩ := ((mon_matches k).add (quant_matches L x)).canonical
  exact ⟨y,by simp only [aliasAt,smul_add,add_assoc, ← hy,quant]; rw [add_comm _ (mon k)]⟩
lemma alias_tube (k : Site L) {p : Momentum} (hp : p∈Tube η) : aliasAt p k ∈ Tube (η/L.val) := by
  have he i := congr_fun (real_frequency k) i
  intro i
  simpa [aliasAt, Complex.conj_eq_iff_im.mp (he i),inv_mul_eq_div,abs_div] using div_lt_div_of_pos_right (hp i) (show (0:ℝ)<L.val by positivity)

lemma collect_analytic {V : Profiles L a b} {U : Momentum → Matrix a a ℂ} (hu : ∀ k : Site L, ContDiffAt ℂ ω U (aliasAt p k))
    (hv : ∀ k, ContDiffAt ℂ ω (fun p => V (-p) k) p ∧ ContDiffAt ℂ ω (fun p => V p k) p) : ContDiffAt ℂ ω (collectPair V U) p :=
  (ContDiffAt.sum (f:= fun k (z : Momentum) => (V (-z) (-k)).transpose * U (aliasAt z k) * V z k) (fun k _ => analyticMul
    (analyticMul (analyticTranspose (hv (-k)).1) ((hu k).comp p (alias_diff k).contDiffAt)) (hv k).2)).const_smul _

omit [DecidableEq a] [DecidableEq b] [Fintype b] in
lemma collect_periodic {V : Profiles L a b} {U : Momentum → Matrix a a ℂ} (hu : ∀ (k : Site L) y, U (aliasAt p k + reciprocal y) = U (aliasAt p k))
    (x : Cover) (hv : ∀ k, V (-p + reciprocal (-x)) k = V (-p) (k + wrap L (-x)) ∧ V (p + reciprocal x) k = V p (k + wrap L x)) :
    collectPair V U (p+reciprocal x) = collectPair V U p := by
  unfold collectPair; conv_rhs => rw [← Equiv.sum_comp (Equiv.addRight (wrap L x))]
  congr 1; refine Finset.sum_congr rfl fun k _ => ?_
  obtain ⟨y,hy⟩ := alias_shift k p x
  rw [hy,hu,show -(p+reciprocal x) = -p + reciprocal (-x) by rw [reciprocal_neg]; abel,(hv _).1,(hv _).2,map_neg, ← neg_add]; rfl

lemma profile_diff {A : Cross L a b} (h : Row.strip A η C) (hη : 0<η) (hp : p∈Tube (η/2)) (k : Site L) :
    ContDiffAt ℂ ω (fun p => profile A p k) p := by
  have he : ContDiffAt ℂ ω (returned (aliasBlock L a)) p := by
    apply analyticMatrix; intro i j; simp only [returned,Matrix.conjTranspose_apply,aliasBlock,of_apply]; split
    · simp_rw [alias_adj,mode,← Complex.exp_neg,aliasAt]; fun_prop
    exact contDiffAt_const
  exact analyticMatrix (fun i j => analyticComponent (analyticMul (he.const_smul (((L.val:ℂ)^4)⁻¹)) (row_analytic h hη hp)) (k,i) j)

omit [DecidableEq b] [Fintype b] in
lemma profile_shift (A : Cross L a b) (k : Site L) (x : Cover) (p : Momentum) : profile A (p+reciprocal x) k = profile A p (k+wrap L x) := by
  ext i j; obtain ⟨y,hy⟩ := alias_shift k p x
  simp only [profile,Matrix.submatrix_apply,aliasMatrix,Row.periods,Matrix.mul_apply,Matrix.smul_apply,returned,aliasBlock,Matrix.conjTranspose_apply, apply_ite (star:ℂ→ℂ), of_apply,alias_adj,hy,mode_phase,mode_periodic,mul_one]

lemma axis_diff {A : Cross L (TypeFace 1) (TypeFace 1)} (h : Row.strip A η C) (hη : 0<η) (hp : p∈Tube (η/2)) (k : Site L) :
    ContDiffAt ℂ ω (fun p => axisProfile G A p k) p := analyticMatrix fun i j => by
  unfold axisProfile paintSymbol; simp only [Matrix.of_apply]; split
  · exact analyticComponent (profile_diff h hη hp k) _ _
  exact contDiffAt_const
lemma axis_shift (A : Cross L (TypeFace 1) (TypeFace 1)) (k : Site L) (x : Cover) (p : Momentum) : axisProfile G A (p+reciprocal x) k = axisProfile G A p (k+wrap L x) := congr_arg (paintSymbol G) (profile_shift A k x p)

variable {X : Momentum → Matrix a b ℂ} {Y : Momentum → Matrix b c ℂ} {r s : ℕ}
def channelD (X : Momentum → Matrix a b ℂ) (p : Momentum) (n : ℕ) : Matrix a b ℂ := of fun i j => lineD (fun z => X z i j) p n
def UnderMatrix (X : Momentum → Matrix a b ℂ) (p : Momentum) (n : ℕ) := ∀ i j, Below (fun z => X z i j) p n
omit [DecidableEq a] [DecidableEq b] [Fintype a] [Fintype b] in
lemma UnderMatrix.zero (X : Momentum → Matrix a b ℂ) (p : Momentum) : UnderMatrix X p 0 := fun _ _ => below_zero
omit [DecidableEq a] [DecidableEq b] [Fintype a] [Fintype b] in
lemma UnderMatrix.one (h : X 0 = 0) : UnderMatrix X p 1 := fun i j => below_one (congr_fun (congr_fun h i) j)
omit [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] in
lemma channel_zero : channelD X p 0 = X 0 := by ext; simp [channelD]
variable (hX : ContDiffAt ℂ ω X 0) (hY : ContDiffAt ℂ ω Y 0)
include hX
omit [DecidableEq a] in
lemma channel_one_smul (k : ℂ) : channelD X (k • p) 1 = k • channelD X p 1 := by
  ext i j; exact (line_one (analyticComponent hX i j) _).trans ((map_smul ..).trans (congr_arg (k • ·) (line_one (analyticComponent hX i j) _).symm))
omit [DecidableEq a] in
lemma channel_two_smul (k : ℂ) : channelD X (k • p) 2 = k^2 • channelD X p 2 := by
  ext i j; simp [channelD,line_two (analyticComponent hX i j),pow_two,mul_assoc]
include hY
omit [DecidableEq a] in
lemma UnderMatrix.mul (h : UnderMatrix X p r) (h' : UnderMatrix Y p s) : UnderMatrix (fun z => X z * Y z) p (r+s) := by
  intro i j n hn; simp only [Matrix.mul_apply,line_sum _ _ (fun k _ => (analyticComponent hX i k).mul (analyticComponent hY k j))]
  exact Finset.sum_eq_zero fun k _ => Below.mul (analyticComponent hX i k) (analyticComponent hY k j) (h i k) (h' k j) n hn
omit [DecidableEq a] in
lemma UnderMatrix.product (h : UnderMatrix X p r) (h' : UnderMatrix Y p s) : channelD (fun z => X z * Y z) p (r+s) =
    ((r+s).choose r:ℂ) • (channelD X p r * channelD Y p s) := by
  ext i j; simp only [channelD,Matrix.of_apply,Matrix.mul_apply,Matrix.smul_apply, smul_eq_mul,Finset.mul_sum,
    line_sum _ _ (fun k _ => (analyticComponent hX i k).mul (analyticComponent hY k j)),
    fun k => Below.product (analyticComponent hX i k) (analyticComponent hY k j) (h i k) (h' k j),mul_assoc]

structure AliasJet (V : Profiles L a a) : Prop where
  base : V 0 0 = (L.val:ℂ)⁻¹ • 1
  high (k : Site L) : k ≠ 0 → ∀ p, UnderMatrix (fun z => V z k) p 2

omit hX hY [DecidableEq a] [DecidableEq b] [Fintype a] [Fintype b] in
lemma under_negate {n : ℕ} (h : UnderMatrix X (-p) n) : UnderMatrix (fun z => (X (-z)).transpose) p n := by intro i j m hm; simpa [lineD] using h j i m hm

variable {V : Profiles L a a} {U : Momentum → Matrix a a ℂ}
omit hX hY
lemma collect_mark (hV : ∀ k : Site L, ContDiffAt ℂ ω (fun z => V z k) 0) (hU : ∀ k : Site L, ContDiffAt ℂ ω U (aliasAt 0 k))
    (h : AliasJet V) (h' : ∀ p, UnderMatrix U p 2) (p : Momentum) : channelD (collectPair V U) p 2 = channelD U p 2 := by
  let D k z := V z k; let P (k : Site L) (z : Momentum) := (V (-z) (-k)).transpose; let T (k : Site L) (z : Momentum) := U (aliasAt z k)
  have hd k : ContDiffAt ℂ ω (D k) 0 := hV k
  have ht k : ContDiffAt ℂ ω (T k) 0 := (hU k).comp 0 (alias_diff k).contDiffAt
  have hp k : ContDiffAt ℂ ω (P k) 0 := analyticTranspose ((show ContDiffAt ℂ ω (fun z => V z (-k)) (-0) by simpa using hd (-k)).comp (f:=(-·)) 0 (by fun_prop))
  let m (k : Site L) (z : Momentum) := P k z * T k z * D k z
  have hm (k) : ContDiffAt ℂ ω (m k) 0 := analyticMul (analyticMul (hp k) (ht k)) (hd k)
  let l := (L.val:ℂ)⁻¹
  have hT (i j : a) (n : ℕ) : lineD (fun z => T 0 z i j) p n = lineD (fun z => U z i j) (l • p) n := by simp only [lineD,T,aliasAt, mon_zero,add_zero,smul_comm _ l,l]
  have ht' : UnderMatrix (T 0) p 2 := fun i j k hk => (hT i j k).trans (h' (l • p) i j k hk)
  have hP : UnderMatrix (P 0 * T 0) p 2 := by
    simpa using! UnderMatrix.mul (hp 0) (ht 0) (UnderMatrix.zero _ p) ht'
  have h0 : channelD (m 0) p 2 = l^4 • channelD U p 2 := by
    have : channelD (T 0) p 2 = l^2 • channelD U p 2 := (Matrix.ext fun i j => hT i j 2).trans (channel_two_smul (by simpa [aliasAt] using hU 0) l)
    rw [UnderMatrix.product (r:=2) (s:=0) (analyticMul (hp 0) (ht 0)) (hd 0) hP (UnderMatrix.zero _ _), show channelD (fun z => P 0 z * T 0 z) p 2 = _ from (show channelD (fun z => P 0 z * T 0 z) p 2 = channelD (P 0) p 0 * channelD (T 0) p 2 from by simpa using! UnderMatrix.product (hp 0) (ht 0) (UnderMatrix.zero _ _) ht')]
    simp only [this,channel_zero,P,D,neg_zero,h.base,Matrix.transpose_smul,Matrix.transpose_one,Nat.add_zero,Nat.choose_self,Nat.cast_one,Matrix.smul_mul,Matrix.mul_smul,Matrix.one_mul,Matrix.mul_one,smul_smul]
    congr 1; ring
  have hM (k : Site L) (hk : k≠0) i j : lineD (fun z => m k z i j) p 2 = 0 := by
    apply UnderMatrix.mul (analyticMul (hp k) (ht k)) (hd k) (UnderMatrix.mul (hp k) (ht k) (under_negate (h.high (-k) (neg_ne_zero.mpr hk) (-p))) (UnderMatrix.zero _ p)) (h.high k hk p) i j 2 (by decide)
  ext i j; have he := congr_fun (congr_fun h0 i) j
  unfold channelD at he ⊢
  simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,collectPair, ← show ∀ k z, m k z = (V (-z) (-k)).transpose * U (aliasAt z k) * V z k from fun k z => rfl, Matrix.sum_apply, line_const_mul, line_sum _ _ (fun k _ => analyticComponent (hm k) i j)]
  rw [Fintype.sum_eq_single 0 (fun k hk => hM k hk i j), show lineD (fun z => m 0 z i j) p 2 = l^4 * _ from he, ← mul_assoc]
  simp [l]
end YM.Push.Loops
