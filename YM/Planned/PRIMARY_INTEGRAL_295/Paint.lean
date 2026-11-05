import YM.Planned.PRIMARY_INTEGRAL_295.Bijets

/-!
# Reproducing all mixed flat moments

E `pmom`: use true analytic aliases and linear position polarizations.
Line tests in the power family suffice including zero modes. No assumed
zero moment on a pure column. Retain exact formula for every chart-stencil
client, in vector colors (real underlying space).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Carrier
open Function Filter Set Lattice Laurent RG Precision Bloch Exterior Work.F08 Next.Free Place ContinuousMultilinearMap
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {j t n : ℕ}

private def inner (n : ℕ) (p : E4) : Tensor.T RouteProbe ℝ n :=
    (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compContinuousLinearMap (fun _ => ContinuousLinearMap.apply ℝ ℝ p)
private lemma inner_apply (n : ℕ) (p : E4) (v : Fin n → RouteProbe) :
    inner n p v = ∏ i, v i p := rfl
private lemma inner_norm (n : ℕ) (p : E4) : ‖inner n p‖ ≤ ‖p‖^n := by
  refine opNorm_le_bound (by positivity) fun x => ?_
  rw [inner_apply,norm_prod]; refine (Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => (x i).le_opNorm p)).trans ?_
  rw [Finset.prod_mul_distrib,mul_comm]; simp

private def passage (n : ℕ) (q : Cover → ℝ) (v : E4) := ∑' z, q z • inner n (v+seat z)

private lemma inner_summable {σ C : ℝ} (hσ : 0<σ) {q : Cover→ℝ} (hq : Width σ C q) (v : E4) (n) :
    Summable fun z => ‖q z • inner n (v+seat z)‖ := by
  have he := width_income hσ hq n
  apply (he.2.1.mul_left ((1+‖v‖)^n)).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro z
  have hv := ((norm_add_le v (seat z)).trans (add_le_add_right (shade_seat z) _)).trans
    (show ‖v‖+(size z : ℝ) ≤ (1+‖v‖)*(1+size z) by nlinarith [norm_nonneg v,Nat.cast_nonneg (α:=ℝ) (size z)])
  rw [norm_smul]; refine (mul_le_mul_of_nonneg_left ((inner_norm ..).trans (pow_le_pow_left₀ (norm_nonneg _) hv n)) (norm_nonneg _)).trans_eq ?_
  rw [mul_pow,mul_left_comm]; rfl

private lemma passage_spec {σ C : ℝ} (hσ : 0<σ) {q : Cover→ℝ} (hq : Width σ C q) (v : E4) (u : Fin n→RouteProbe) :
    HasSum (fun z=> q z * ∏ i,u i (v+seat z)) (passage n q v u) := by
  have ht := (inner_summable hσ hq v n).of_norm.hasSum
  exact (ContinuousMultilinearMap.apply ℝ _ ℝ u).hasSum ht

private lemma passage_sym {σ C : ℝ} (hσ : 0<σ) {q : Cover→ℝ} (hq : Width σ C q) (v : E4) (n : ℕ) : Tensor.Sym (passage n q v) := by
  intro x s
  rw [← (passage_spec hσ hq v (x ∘ s)).tsum_eq, ← (passage_spec hσ hq v x).tsum_eq]; refine tsum_congr fun z => ?_
  exact congr_arg (q z * ·) (Equiv.prod_comp s (fun a => x a _))

lemma axes_eq (k : ℝ) (hk : 0<k) (P : Flight j t) (ht : 4≤t)
    (x : Cover) (a b : Axis) (v : Fin n→RouteProbe) (hn : n<j) :
    let q z := member (linesOf P k) z a b
    let s := (P.L.val:ℝ)⁻¹ • seat x
    ∑' z,q x z * ∏ i, v i (seat ((cellar P.L x)+z))=∑' z,q 0 z * ∏ i,v i (s+seat z) := by
  classical
  obtain ⟨σ,C,hσ,hC⟩ := stored P k hk ht
  intro q s; let p := cellar P.L x
  have hr (i : Cover) : Width σ C (q i) := hC _ _
  have he : passage n (q x) (seat p) = passage n (q 0) s := by
    apply Tensor.ext_diag _ _ (passage_sym hσ (hr _) _ _) (passage_sym hσ (hr _) _ _);
    funext l; unfold Tensor.diagonal; rw [← (passage_spec hσ (hr _) _ _).tsum_eq,← (passage_spec hσ (hr _) _ _).tsum_eq]
    have hh := pure_moment k hk P ht x a b l n hn
    dsimp only at hh
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    conv_rhs => arg 1; intro i; rw [mul_comm]
    conv_lhs => arg 1; intro i; rw [mul_comm]
    simp_rw [seat_add] at hh; exact hh
  simp_rw [seat_add]
  rw [(passage_spec hσ (hr x) (seat _) v).tsum_eq,(passage_spec hσ (hr 0) s v).tsum_eq]; exact DFunLike.congr_fun he v

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Root moment translated on continuous E4 arrays. Keep `a b` input and
output spatial index separately. -/
def respond (q : Cover→ℝ) (v : E4) (f : E4→E) : E := ∑' z,q z • f (v+seat z)

private def waveBoard (v : Fin n → Axis) (A : Tensor.T E4 E n) := A fun i => basis (v i)
private def portProj (v : Fin n → Axis) (j : Fin n) : RouteProbe := EuclideanSpace.proj (v j)
private def paintBoard (A : Tensor.T E4 E n) (v : Fin n → Axis) (x : E4) := (∏ i, portProj v i x) • waveBoard v A

omit [CompleteSpace E] in
private lemma paintSee (A : Tensor.T E4 E n) (x : E4) : Tensor.diagonal A x=∑ v, paintBoard A v x := by
  unfold Tensor.diagonal
  have ht : ∑ i : Axis,x i • basis i = x := by ext1; simp
  calc
    _ = A (fun _ => ∑ i : Axis,x i • basis i) := congr_arg A (funext fun _ => ht.symm)
    _ = _ := by rw [A.map_sum (fun _ a => x a • basis a)]; simp_rw [A.map_smul_univ]; rfl

omit [CompleteSpace E] in
private lemma respond_read {σ C : ℝ} (hσ : 0<σ) {q : Cover→ℝ} (hq : Width σ C q) (p : E4) (M : Tensor.T E4 E n) :
    respond q p (Tensor.diagonal M) = ∑ v : Fin n → Axis, (∑' z,q z * ∏ i, portProj v i (p+seat z)) • waveBoard v M := by
  let f z (v : Fin n→Axis) := q z*∏ i,portProj v i (p+seat z)
  have hx (v : Fin n→Axis) : Summable fun z => f z v := (passage_spec hσ hq p (portProj v)).summable
  unfold respond; simp_rw [paintSee,Finset.smul_sum,paintBoard, smul_smul]
  rw [Summable.tsum_finsetSum (fun v _ => (hx v).smul_const _)]
  simp_rw [show ∀ v : Fin n→Axis, (∑' z,f z v • waveBoard v M)=(∑' z,f z v) • waveBoard v M from fun v => (hx v).tsum_smul_const _]; rfl

omit [CompleteSpace E] in
lemma respond_pure (k : ℝ) (hk : 0<k) (P : Flight j t) (ht : 4≤t) (hn : n < j) (x : Cover) (a b : Axis)
    (f : E4→E) (hf : f∈exactDegree E n) :
    let q z := member (linesOf P k) z a b
    let y := seat (cellar P.L x)
    let s := (P.L.val:ℝ)⁻¹ • seat x
    respond (q x) y f = respond (q 0) s f := by
  obtain ⟨A,rfl⟩ := can_write.1 hf
  obtain ⟨σ,C,hσ,hC⟩ := stored P k hk ht
  intro q y s; have hr (i : Cover) : Width σ C (q i) := hC _ _
  rw [respond_read hσ (hr x) .., respond_read hσ (hr 0) ..]; apply Finset.sum_congr rfl; intro i _
  apply congr_arg (· • waveBoard i A); have he := axes_eq k hk P ht x a b (portProj i) hn; dsimp only at he
  simp_rw [seat_add] at he; exact he

omit [CompleteSpace E] in
lemma field_pure (k : ℝ) (hk : 0<k) (P : Flight j t) (ht : 4≤t) (f : E4 → Axis → E)
    (hf : f ∈ exactDegree (Axis→E) n) (hn : n < j) (x : Cover) (i : Axis) :
    applyLine (linesOf P k) (verdict f) x i = ∑ a : Axis,
      respond (member (linesOf P k) 0 i a) ((P.L.val:ℝ)⁻¹ • seat x) (fun z => f z a) := by
  unfold applyLine stream verdict; refine Finset.sum_congr rfl fun a _=> ?_
  have he := respond_pure k hk P ht hn x i a (fun z => f z a) (linear_pure (ContinuousLinearMap.proj a) hf)
  simp_rw [seat_add]; exact he
end YM.Planned.PrimaryIntegral295.Carrier
