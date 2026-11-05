import YM.Push.LOOP_COEFFICIENT.Block.Priced
import YM.Push.LOOP_COEFFICIENT.Block.Reserve
import YM.Push.LOOP_COEFFICIENT.Block.Spend

/-!
# Sufficient per-alias field-vertex prices with H² external profiles
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Block
open Function Set Filter Matrix Metric Lattice Laurent RG Bloch Precision Wilson Complex Portal
open scoped Topology ContDiff Matrix.Norms.L2Operator BigOperators
variable {L : Side} {η C A : ℝ} {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [Fintype d]

omit [DecidableEq a] in
lemma normalize_bil {M : Matrix a b ℂ} (hC : 0≤C) (h : ∀ x y, mag x≤1 → mag y≤1 → ‖x ⬝ᵥ M *ᵥ y‖≤ C) : ‖M‖≤C := by
  rw [l2_opNorm_def]; apply ContinuousLinearMap.opNorm_le_of_unit_norm hC; intro y hy
  let x := star (M *ᵥ y.ofLp)
  change mag (M *ᵥ y.ofLp) ≤ C; rw [← mag_bar]; change mag x ≤ C
  rcases (mag_nonneg x).eq_or_lt with he|he
  · simpa [← he] using hC
  have ht : ‖(((mag x)⁻¹:ℝ):ℂ)‖ = (mag x)⁻¹ := norm_real _ |>.trans (Real.norm_of_nonneg (by positivity))
  have hh := h (((mag x)⁻¹:ℝ) • x) y.ofLp (by change mag ((((mag x)⁻¹:ℝ):ℂ) • x) ≤ _; rw [mag_smul,ht,inv_mul_cancel₀ he.ne']) (show mag y.ofLp ≤ 1 from hy.le)
  change ‖((((mag x)⁻¹:ℝ):ℂ) • x) ⬝ᵥ _‖ ≤ C at hh; rw [smul_dotProduct,norm_smul,ht,dot_self,norm_real,Real.norm_of_nonneg (sq_nonneg _),← mag_bar (M *ᵥ y.ofLp),pow_two] at hh; rwa [show star (M *ᵥ y.ofLp)=x from rfl,inv_mul_cancel_left₀ he.ne'] at hh

variable {X : Vertex c a b} {Y : Profiles L c d} {v u : Weight L} (hv : ∀ q i,0<v q i) (hu : ∀ q i,0<u q i)
def rate (Y : Profiles L c d) (p : Momentum) (z : CSpace d) (j : Site L) := (L.val:ℝ)*‖Y p j *ᵥ z‖
structure Toll (v u : Weight L) (X : Vertex c a b) (Y : Profiles L c d) (η A : ℝ) : Prop where
  base q i : q∈Tube η → v (-q) (-i)*u q i * ‖X.base (aliasAt q i)‖ ≤ A
  one q p z i j : Active₁ (Tube η) q p → p∈Tube η → ‖z‖≤1 → v (-(q+p)) (-(i+j))*u q i * ‖X.one (aliasAt q i) (aliasAt p j) (Y p j *ᵥ z)‖ ≤ A * ((heft L (-(q+p)) (-(i+j)))⁻¹ * rate Y p z j + (heft L q i)⁻¹ * rate Y p z j + (heft L (-(q+p)) (-(i+j)))⁻¹ * (heft L q i)⁻¹ * (heft L p j * rate Y p z j))
  two q p s z w i j l : Active₂ (Tube η) q p s → p∈Tube η → s∈Tube η → ‖z‖≤1 → ‖w‖≤1 → v (-(q+p+s)) (-(i+(j+l)))*u q i * ‖X.two (aliasAt q i) (aliasAt p j) (aliasAt s l) (Y p j *ᵥ z) (Y s l *ᵥ w)‖ ≤ A * ((heft L (-(q+p+s)) (-(i+(j+l))))⁻¹*(heft L q i)⁻¹ * rate Y p z j * rate Y s w l)

private def chunks {L : Side} {a : Type} [Fintype a] (x : CSpace (Co L a)) (i : Site L) := mag (beam i x)
private def heavy {L : Side} {a : Type} [Fintype a] (q : Momentum) (x : CSpace (Co L a)) (i : Site L) := (heft L q i)⁻¹ * chunks x i
private def bright {L : Side} {c d : Type} [Fintype c] [Fintype d] (Y : Profiles L c d) (p : Momentum) (z : CSpace d) (j : Site L) := heft L p j * rate Y p z j
omit [DecidableEq a] [DecidableEq b] in
private lemma sum_one (ha : 0≤A) {K} (hK : 0<K) (he : ∀ q∈Tube η, ∑ i, (heft L q i)⁻¹^6 ≤ K) (h : Provision Y η A) {q s : Momentum} (hq : Active₁ (Tube η) q s) (hs : s∈Tube η) {x : CSpace (Co L a)} {y : CSpace (Co L b)} {z} (hx : mag x≤1) (hy : mag y≤1) (hz : ‖z‖≤1) :
    ∑ i,∑ j, ((heavy (-(q+s)) x (-(i+j))*rate Y s z i*chunks y j + chunks x (-(i+j))*rate Y s z i*heavy q y j) + heavy (-(q+s)) x (-(i+j))*bright Y s z i*heavy q y j) ≤ 3*(1+K+A)^3 := by
  let N := 1+K+A; have hN : 1≤N := by unfold N; linarith
  have hm := (h.first hs hz (he s hs)).trans (show K+A ≤ N by unfold N; linarith)
  have hm' := (h.second hs hz (he s hs)).trans (show K+A ≤ N by unfold N; linarith)
  let o := -(q+s)
  have ho := tube_neg hq.2
  have hx' := (beam_second hx (he o ho)).trans (show K+1≤N by unfold N; linarith)
  have hy' := (beam_second hy (he _ hq.1)).trans (show K+1≤N by unfold N; linarith)
  have H₁ {a : Type} [Fintype a] (x : CSpace (Co L a)) (i) := (show 0 ≤ chunks x i from mag_nonneg _)
  have H₂ {a : Type} [Fintype a] (x : CSpace (Co L a)) p (i) := (show 0 ≤ heavy p x i from mul_nonneg (inv_pos.mpr (heft_pos ..)).le (mag_nonneg _))
  have H₃ i := (show 0 ≤ rate Y s z i from mul_nonneg (by positivity) (norm_nonneg _))
  have H₄ i := (show 0 ≤ bright Y s z i from mul_nonneg (heft_pos ..).le (H₃ _))
  have h1 := young₃ (heavy o x) (rate Y s z) (chunks y) hN (by norm_num : (1:ℝ)≤3/2) (by norm_num : (1:ℝ) ≤6/5) (by norm_num : (1:ℝ)≤2) (by norm_num) (H₂ _ _) H₃ (H₁ _) hx' hm (by simpa [chunks] using! (beam_first hy).trans hN)
  have h2 := young₃ (chunks x) (rate Y s z) (heavy q y) hN (by norm_num : (1:ℝ)≤2) (by norm_num : (1:ℝ) ≤6/5) (by norm_num : (1:ℝ)≤3/2) (by norm_num) (H₁ _) H₃ (H₂ _ _) (by simpa [chunks] using! (beam_first hx).trans hN) hm hy'
  have h3 := young₃ (heavy o x) (bright Y s z) (heavy q y) hN (by norm_num : (1:ℝ)≤3/2) (by norm_num : (1:ℝ) ≤3/2) (by norm_num : (1:ℝ)≤3/2) (by norm_num) (H₂ _ _) H₄ (H₂ _ _) hx' hm' hy'
  simp only [Finset.sum_add_distrib]; exact (add_le_add (add_le_add h1 h2) h3).trans_eq (by unfold N; ring)
omit [DecidableEq a] [DecidableEq b] in
private lemma sum_two (ha : 0≤A) {K} (hK : 0<K) (he : ∀ q∈Tube η, ∑ i, (heft L q i)⁻¹^6 ≤ K) (h : Provision Y η A) {q p s : Momentum} (hq : Active₂ (Tube η) q p s) (hp : p∈Tube η) (hs : s∈Tube η) {x : CSpace (Co L a)} {y : CSpace (Co L b)} {z w} (hx : mag x≤1) (hy : mag y≤1) (hz : ‖z‖≤1) (hw : ‖w‖≤1) :
    ∑ j,∑ l,∑ i, heavy (-(q+p+s)) x (-(i+(j+l)))*rate Y p z j*rate Y s w l*heavy q y i ≤ (1+K+A)^4 := by
  let N := 1+K+A; have hN : 1≤N := by unfold N; linarith
  have hm := (h.first hs hw (he s hs)).trans (show K+A ≤ N by unfold N; linarith)
  have hm' := (h.first hp hz (he p hp)).trans (show K+A ≤ N by unfold N; linarith)
  let o := -(q+p+s)
  have ho := tube_neg hq.2.2.2
  have hx' := (beam_second hx (he o ho)).trans (show K+1≤N by unfold N; linarith)
  have hy' := (beam_second hy (he _ hq.1)).trans (show K+1≤N by unfold N; linarith)
  have H₂ {a : Type} [Fintype a] (x : CSpace (Co L a)) p (i) := (show 0 ≤ heavy p x i from mul_nonneg (inv_pos.mpr (heft_pos ..)).le (mag_nonneg _))
  have H₃ p z i := (show 0 ≤ rate Y p z i from mul_nonneg (by positivity) (norm_nonneg _))
  simpa only [add_comm (_:Site L) ((_+_):Site L)] using young₄ (heavy o x) (rate Y p z) (rate Y s w) (heavy q y) hN (H₂ _ _) (H₃ _ _) (H₃ _ _) (H₂ _ _) hx' hm' hm hy'

variable (hA : 0≤A) (hC : 0≤C) (hL : Odd L.val) (hY : Provision Y η C) (hX : Toll v u X Y η A)
include hv hu hA hC hY hX
private lemma alias_op_one {K} (hK : 0<K) (he : ∀ q∈Tube η,∑ i,(heft L q i)⁻¹^6 ≤ K) {q p z} (hq : Active₁ (Tube η) q p) (hp : p∈Tube η) (hz : ‖z‖≤1) : ‖(weigh (distributed L a v hv).dual (distributed L b u hu) (induce X Y)).one q p z‖ ≤ A*(3*(1+K+C)^3) := by
  refine normalize_bil (by positivity) fun x y hx hy => ?_
  rw [one_pair]
  let o := -(q+p)
  apply (norm_sum_le ..).trans ((Finset.sum_le_sum (fun i _ => norm_sum_le ..)).trans ?_)
  have ht (i j) := hX.one q p z i j hq hp hz
  have hx' (i : Site L) := mag_nonneg (beam i x); have hy' (i : Site L) := mag_nonneg (beam i y)
  have h₀ i j := mul_nonneg (hv o (-(i+j))).le (hu q i).le
  calc
    _ ≤ ∑ j,∑ i,A*((heavy o x (-(j+i))*rate Y p z j*chunks y i + chunks x (-(j+i))*rate Y p z j*heavy q y i) + heavy o x (-(j+i))*bright Y p z j*heavy q y i) := Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ => by
      rw [norm_mul,Complex.norm_real]; refine (mul_le_mul_of_nonneg_left (mag_pair ..) (norm_nonneg _)).trans ?_; rw [Real.norm_of_nonneg (h₀ i j), ← mul_assoc,← mul_assoc]
      refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (ht i j) (hx' _)) (hy' _)).trans_eq ?_
      unfold heavy chunks bright o; rw [add_comm j i]; ring
    _ ≤ _ := by simp_rw [← Finset.mul_sum]; gcongr; exact sum_one hC hK he hY hq hp hx hy hz
private lemma alias_op_two {K} (hK : 0<K) (he : ∀ q∈Tube η,∑ i,(heft L q i)⁻¹^6 ≤ K) {q p s z w} (hq : Active₂ (Tube η) q p s) (hp : p∈Tube η) (hs : s∈Tube η) (hz : ‖z‖≤1) (hw : ‖w‖≤1) : ‖(weigh (distributed L a v hv).dual (distributed L b u hu) (induce X Y)).two q p s z w‖ ≤ A*(1+K+C)^4 := by
  refine normalize_bil (by positivity) fun x y hx hy => ?_
  rw [two_pair]; let o := -(q+p+s)
  apply (norm_sum_le ..).trans ((Finset.sum_le_sum (fun i _ => (norm_sum_le ..).trans (Finset.sum_le_sum (fun j _ => norm_sum_le ..)))).trans ?_)
  have ht i j l := hX.two q p s z w i j l hq hp hs hz hw
  have hx' (i : Site L) := mag_nonneg (beam i x); have hy' (i : Site L) := mag_nonneg (beam i y)
  have h₀ i j l := mul_nonneg (hv o (-(i+(j+l)))).le (hu q i).le
  calc
    _ ≤ ∑ j,∑ l,∑ i,A*(heavy o x (-(i+(j+l)))*rate Y p z j*rate Y s w l*heavy q y i) := Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun i _ => by
      rw [norm_mul,Complex.norm_real]; refine (mul_le_mul_of_nonneg_left (mag_pair ..) (norm_nonneg _)).trans ?_; rw [Real.norm_of_nonneg (h₀ i j l),← mul_assoc, ← mul_assoc]
      refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (ht i j l) (hx' _)) (hy' _)).trans_eq ?_
      unfold heavy chunks o; ring
    _ ≤ _ := by simp_rw [← Finset.mul_sum]; gcongr; exact sum_two hC hK he hY hq hp hs hx hy hz hw

omit hv hu hY hX in
lemma charge_of_toll (a b c d : Type) [Fintype a] [Fintype b] [Fintype c] [Fintype d] [DecidableEq a] [DecidableEq b] (η : ℝ) : ∃ B : ℝ,0<B ∧ ∀ {L : Side} {X : Vertex c a b} {Y : Profiles L c d} {u v} (hv : ∀ q i,0<v q i) (hu : ∀ q i,0<u q i), Odd L.val → Provision Y η C → Toll v u X Y η A → Charge (distributed L a v hv).dual (distributed L b u hu) (induce X Y) η B := by
  obtain ⟨K,hK,H⟩ := energy_sum η
  let N := 1+K+C; let B := (1+A)*(1+3*N^3+N^4)
  have hN : 0<N := by unfold N; positivity
  refine ⟨B,by unfold B; positivity,fun {L X Y u v} hv hu hL hy hx => ⟨by unfold B; positivity,fun _ h => (induced_base v u hv hu X Y hA (fun i => hx.base _ i h)).trans ?_,fun _ _ _ hq hp hz => (alias_op_one hv hu hA hC hy hx hK (H hL) hq hp hz).trans ?_, fun _ _ _ _ _ hq hp hs hz hw => (alias_op_two hv hu hA hC hy hx hK (H hL) hq hp hs hz hw).trans ?_⟩⟩
  · unfold B; nlinarith [pow_pos hN 3, sq_nonneg (N^2),mul_nonneg hA (pow_pos hN 3).le, mul_nonneg hA (pow_pos hN 4).le]
  · unfold B; rw [div_one]; change A*(3*N^3) ≤ _; nlinarith [pow_pos hN 3,pow_pos hN 4,mul_nonneg hA (pow_pos hN 4).le]
  unfold B; rw [one_pow,div_one]; change A*N^4 ≤ _; nlinarith [pow_pos hN 4,pow_pos hN 3,mul_nonneg hA (pow_pos hN 3).le]
end YM.Push.Loops.Block
