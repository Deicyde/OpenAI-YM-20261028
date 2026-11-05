import YM.Branch.Center

/-!
# Unique cluster minimum modulo left multiples

Patch optimizer gate . Don't require a connected input image,
no data size in the cutoff. Recenter the already EXISTING global minima using
nearest group point to their averages (those averages rotate also). Now the
difference of the averages lies in the NORMAL slice. Each coordinate solves a
nearest-point problem with self term included. Hence in this gauge the strict
derivative bound for nearest points gives contraction in max norm for comparing
two minimizers, after separately showing centroid estimate ⇒ applicability.
We don't track analyticity/Hessian bounds of the branch here; doesn't use seed
theory or tree Hessian.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Branch

open Function Filter Set NormedSpace Submodule
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators NNReal

attribute [local instance] Gauge.frobInner

/-- Include the trivial self terms. -/
structure Pairs (n L : Type*) (G : Gauge) where
  W : n → n → L → G.El
  mirror : Equiv.Perm L
  reflect : ∀ i j k, W j i (mirror k) = (W i j k)⁻¹
  same : ∀ i k, W i i k = 1

namespace Pairs
variable {n L : Type*} [Fintype n] [Fintype L] {G : Gauge} (A : Pairs n L G)

def term (h : n → G.El) (x y : n) (l : L) := G.price (h x * A.W x y l * (h y)⁻¹)

def cost (h : n → G.El) := avg fun x => avg fun y => avg fun l => A.term h x y l

def Solves (h : n → G.El) := ∀ g, A.cost h ≤ A.cost g

def centroid (h : n → G.El) := avg fun i => G.mat (h i)

def feedback (h : n → G.El) (x : n) := avg fun y => avg fun l => G.mat (h y * (A.W x y l)⁻¹)

omit [Fintype n] in
lemma opposite (h : n → G.El) (x y) : (∑ i, A.term h y x i) = ∑ i, A.term h x y i := by
  rw [← Equiv.sum_comp A.mirror]
  congr 1
  ext i; rw [term,A.reflect, term, show h y * (A.W x y i)⁻¹ * (h x)⁻¹ = (h x * A.W x y i * (h y)⁻¹)⁻¹ by group, G.price_inv]

lemma moves (h : n → G.El) (c : G.El) : A.cost (fun i => c*h i) = A.cost h := by
  have he (x y k) : A.term (fun i => c*h i) x y k = A.term h x y k := by
    unfold term
    rw [show c*h x * A.W x y k * (c*h y)⁻¹ = c*(h x * A.W x y k * (h y)⁻¹)*c⁻¹ by group,G.price_conj]
  simp_rw [cost, he]

omit [Fintype L] in
lemma turns (h : n → G.El) (c : G.El) : centroid (fun i => c * h i) = G.mat c * centroid h := by
  simp [centroid,avg, Finset.mul_sum]

variable [Nonempty n] [Nonempty L]

lemma min_cov {h : n → G.El} (hs : A.Solves h) (x : n) (k : G.El) :
    ∑ y, ∑ l, A.term h x y l ≤ ∑ y, ∑ l, G.price (k * A.W x y l * (h y)⁻¹) := by
  classical
  let g := update h x k
  let t (p : n → G.El) i j := ∑ l, A.term p i j l
  let M := Finset.univ.erase x
  have hn : 0 < (Fintype.card n : ℝ) := by exact_mod_cast Fintype.card_pos
  have hm : 0 < (Fintype.card L : ℝ) := by exact_mod_cast Fintype.card_pos
  have eq (p : n → G.El) : A.cost p = (Fintype.card n:ℝ)⁻¹ * (Fintype.card n:ℝ)⁻¹ * (Fintype.card L:ℝ)⁻¹ * ∑ i, ∑ j, t p i j := by
    simp only [cost,avg, smul_eq_mul,← Finset.mul_sum,t,mul_assoc]
  have eq' (p : n → G.El) : (∑ i, ∑ j, t p i j) = (∑ i ∈ M, ∑ j ∈ M, t p i j) + 2*(∑ i, t p x i) := by
    calc
      _ = (∑ i ∈ M, ∑ j, t p i j) + ∑ j, t p x j := by rw [Finset.sum_erase_add _ _ (Finset.mem_univ x)]
      _ = (∑ i ∈ M, ((∑ j ∈ M, t p i j)+t p i x)) + ∑ j, t p x j := by
        unfold M; simp
      _ = _ := by
        rw [Finset.sum_add_distrib]
        have he : (∑ i ∈ M, t p i x) = ∑ i, t p x i := by
          rw [← Finset.sum_erase_add _ _ (Finset.mem_univ x), show t p x x = 0 by simp [t, term,A.same], add_zero]
          exact Finset.sum_congr rfl fun i _ ↦ A.opposite p _ _
        rw [he]; ring
  have he := hs g
  rw [eq,eq, mul_le_mul_iff_right₀ (by positivity), eq', eq'] at he
  have hh (i) (hi : i ∈ M) : g i = h i := update_of_ne (Finset.ne_of_mem_erase hi) ..
  have hd (i) (hi : i ∈ M) (j) (hj : j ∈ M) : t h i j = t g i j := by simp only [t, term, hh i hi, hh j hj]
  rw [Finset.sum_congr rfl fun i hi ↦ Finset.sum_congr rfl fun j hj ↦ hd i hi j hj,
    add_le_add_iff_left,mul_le_mul_iff_right₀ (by positivity)] at he
  apply he.trans
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  unfold term g
  by_cases h' : i = x
  · subst i
    simp only [update_self, A.same,mul_one,mul_inv_cancel, G.price_one]
    exact (G.price_range _).1
  simp [h']

lemma self_consistent {h : n → G.El} (hw : A.Solves h) (x : n) : G.Nearest (h x) (A.feedback h x) := by
  let N : ℝ := Fintype.card n
  let M : ℝ := Fintype.card L
  let w (_ : n × L) := N⁻¹*M⁻¹
  let f (p : n × L) := h p.1 * (A.W x p.1 p.2)⁻¹
  have hn : 0 < N := by unfold N; exact_mod_cast Fintype.card_pos
  have hm : 0 < M := by unfold M; exact_mod_cast Fintype.card_pos
  have he : ∑ i, w i = 1 := by
    simp only [w, Finset.sum_const,Finset.card_univ,Fintype.card_prod,Nat.cast_mul,nsmul_eq_mul]
    change N*M*_ = 1
    field_simp
  have eq : A.feedback h x = ∑ i, w i • G.mat (f i) := by
    unfold w f
    rw [Fintype.sum_prod_type]
    simp_rw [feedback,avg,N,M,Finset.smul_sum, smul_smul]
  rw [eq, min_iff w he]
  intro v
  have hx (k : G.El) : (∑ i, w i * G.price (f i*k⁻¹)) = N⁻¹*M⁻¹*∑ y, ∑ l, G.price (k * A.W x y l * (h y)⁻¹) := by
    unfold w f
    rw [Fintype.sum_prod_type]
    have ht (y l) : h y*(A.W x y l)⁻¹*k⁻¹ = (k*A.W x y l*(h y)⁻¹)⁻¹ := by group
    simp_rw [ht,G.price_inv,←Finset.mul_sum]
  rw [hx,hx]
  exact mul_le_mul_of_nonneg_left (A.min_cov hw x v) (by positivity)

section compare

lemma compare_energy {d : ℝ} (hw : ∀ x y k, ‖G.mat (A.W x y k)-1‖ ≤ d)
    {h : n → G.El} (hs : A.Solves h) :
    (avg fun i => avg fun j => ‖G.mat (h i)-G.mat (h j)‖^2) ≤ 4*d^2 := by
  have eq (p : n → G.El) :
      avg (fun x => avg fun y => avg fun l => ‖G.mat (p x * A.W x y l)-G.mat (p y)‖^2) = G.repDim*(2*A.cost p) := by
    simp_rw [← price_diff,cost,← avg_mul,term]
  have hcost :
      avg (fun x => avg fun y => avg fun l => ‖G.mat (h x * A.W x y l)-G.mat (h y)‖^2) ≤ d^2 := by
    calc
      _ = _ := eq h
      _ ≤ G.repDim*(2*A.cost 1) := by gcongr; exact hs _
      _ = _ := (eq 1).symm
      _ ≤ avg (fun _ : n => avg fun _ : n => avg fun _ : L => d^2) := avg_mono fun i => avg_mono fun j => avg_mono fun k => by
        simp only [Pi.one_apply, G.mat_one, one_mul]
        have hd := hw i j k
        exact (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans hd)).mpr hd
      _ = d^2 := by simp only [avg_const]
  have ha (i j : n) : (‖G.mat (h i) - G.mat (h j)‖^2) ≤ (avg fun k => 2*d^2+2*‖G.mat (h i * A.W i j k)-G.mat (h j)‖^2) := by
    apply (avg_const (n:=L) _).symm.le.trans
    refine avg_mono fun k => ?_
    have hh := norm_sub_le_norm_sub_add_norm_sub (G.mat (h i)) (G.mat (h i * A.W i j k)) (G.mat (h j))
    rw [show ‖G.mat (h i)-G.mat (h i * A.W i j k)‖ = ‖G.mat (A.W i j k)-1‖ by
      rw [norm_sub_rev,G.mat_mul, show _ * _-G.mat _ = G.mat (h i) * (G.mat (A.W i j k)-1) by rw [mul_sub,mul_one], Gauge.mul_frob_eq _ _ (G.mat_star_mul _)] ] at hh
    have hj := hw i j k
    have hn := norm_nonneg (G.mat (h i)-G.mat (h j))
    dsimp only
    nlinarith [norm_nonneg (G.mat (A.W i j k)-1), norm_nonneg (G.mat (h i*A.W i j k) - G.mat (h j)), sq_nonneg (d-‖G.mat (h i*A.W i j k) - G.mat (h j)‖)]
  apply (avg_mono (g := fun i => _) fun i => avg_mono fun j => ha i j).trans
  simp_rw [avg_add,avg_mul,avg_const]
  linarith

lemma cluster {d : ℝ} (hd : 0 ≤ d) (hw : ∀ x y k, ‖G.mat (A.W x y k)-1‖ ≤ d)
    {h : n → G.El} (hs : A.Solves h) (hr : G.Nearest 1 (centroid h)) :
    ‖centroid h-1‖ ≤ 2*d := by
  obtain ⟨i, hi⟩ := le_avg (fun i => avg fun j => ‖G.mat (h i)-G.mat (h j)‖^2)
  apply (hr (h i)).trans
  have he := hi.trans (A.compare_energy hw hs)
  rw [norm_sub_rev]
  unfold centroid
  have hh : (avg fun j => G.mat (h i)-G.mat (h j)) = G.mat (h i)-avg fun j => G.mat (h j) := by rw [avg_sub, avg_const]
  rw [← hh]
  have hk := (avg_sq (fun j => G.mat (h i)-G.mat (h j))).trans he
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).1
  nlinarith [hk]

lemma closeness {d : ℝ} (hd : 0 ≤ d) (hw : ∀ x y k, ‖G.mat (A.W x y k)-1‖ ≤ d)
    {h : n → G.El} (hs : A.Solves h) (hr : G.Nearest 1 (centroid h)) (x : n) : ‖A.feedback h x-1‖ ≤ 3*d := by
  have hh : ‖A.feedback h x-centroid h‖ ≤ d := by
    simp only [feedback,centroid,← avg_sub]
    apply (norm_avg _).trans
    apply le_trans _ (avg_const (n:=n) d).le
    refine avg_mono fun i => ?_
    dsimp only; rw [show (avg fun l => G.mat (h i*(A.W x i l)⁻¹))-G.mat (h i) = avg fun l => G.mat (h i*(A.W x i l)⁻¹)-G.mat (h i) by rw [avg_sub,avg_const]]
    apply (norm_avg _).trans
    apply le_trans _ (avg_const (n:=L) d).le
    refine avg_mono fun k => ?_
    dsimp only
    rw [← Gauge.frob_mul_eq (G.mat (h i*(A.W x i k)⁻¹)-G.mat (h i)) (G.mat (A.W x i k)) (G.mat_mul_star _)]
    rw [sub_mul, ← G.mat_mul, mul_assoc,inv_mul_cancel,mul_one,norm_sub_rev,
      show G.mat (h i)*G.mat _-G.mat _ = G.mat (h i) * (G.mat (A.W x i k)-1) by rw [mul_sub,mul_one], Gauge.mul_frob_eq _ _ (G.mat_star_mul _)]
    exact hw ..
  exact (norm_sub_le_norm_sub_add_norm_sub _ (centroid h) _).trans (by linarith [A.cluster hd hw hs hr])

lemma changes (h k : n → G.El) (x : n) (u : ℝ) (hu : ∀ i, ‖G.mat (h i)-G.mat (k i)‖ ≤ u) :
    ‖A.feedback h x-A.feedback k x‖ ≤ u := by
  simp only [feedback,← avg_sub]
  apply (norm_avg _).trans
  apply le_trans _ (avg_const (n:=n) u).le
  refine avg_mono fun i => ?_
  apply (norm_avg _).trans
  apply le_trans _ (avg_const (n:=L) u).le
  refine avg_mono fun l => ?_
  dsimp only
  rw [G.mat_mul,G.mat_mul,← sub_mul, Gauge.frob_mul_eq _ _ (G.mat_mul_star _)]
  exact hu _

lemma weak_changes {d : ℝ} (hw : ∀ x y k, ‖G.mat (A.W x y k)-1‖ ≤ d) (h k : n → G.El) (x : n) (u : ℝ)
    (hu : ∀ i, ‖G.mat (h i)-G.mat (k i)‖ ≤ u) :
    ‖(A.feedback h x-A.feedback k x)-(centroid h-centroid k)‖ ≤ u*d := by
  have hh (A : G.El) : ‖G.mat A⁻¹ - 1‖=‖G.mat A-1‖ := by
    rw [← Gauge.frob_mul_eq (G.mat A⁻¹-1) (G.mat A) (G.mat_mul_star _), sub_mul, one_mul,
      ← G.mat_mul, inv_mul_cancel,G.mat_one,norm_sub_rev]
  simp only [feedback,centroid,← avg_sub]
  apply (norm_avg _).trans
  apply le_trans _ (avg_const (n:=n) _).le
  refine avg_mono fun i => ?_
  dsimp only
  let f := fun l => G.mat (h i * (A.W x i l)⁻¹)-G.mat (k i * (A.W x i l)⁻¹)
  let g := G.mat (h i)-G.mat (k i)
  change ‖avg f-g‖ ≤ _
  rw [show avg f-g = avg fun l => f l-g by rw [avg_sub f (fun _ => g),avg_const]]
  apply (norm_avg _).trans
  apply le_trans _ (avg_const (n:=L) _).le
  refine avg_mono fun l => ?_
  dsimp only
  have hx : f l = g*G.mat (A.W x i l)⁻¹ := by simp only [f,g, sub_mul, G.mat_mul]
  rw [hx, show _*_ - g = g*(G.mat (A.W x i l)⁻¹-1) by rw [mul_sub,mul_one]]
  apply (norm_mul_le _ _).trans
  rw [hh]
  exact mul_le_mul (hu i) (hw ..) (norm_nonneg _) ((norm_nonneg _).trans (hu i))
end compare
end Pairs

section
/-- cutoff independent of patch order and data size. -/
lemma align (G : Gauge) : ∃ d : ℝ, 0 < d ∧ ∀ (n L : Type) [Fintype n] [Fintype L]
    [Nonempty n] [Nonempty L] (A : Pairs n L G), (∀ x y k, ‖G.mat (A.W x y k)-1‖ ≤ d) →
    ∀ h k, A.Solves h → A.Solves k → ∃ c : G.El, ∀ i, c*h i=k i := by
  obtain ⟨δ,hδ,H⟩ := G.nearest_approximate (1/4) (by norm_num)
  let d := min (δ/4) (1/4)
  have hd : 0<d := lt_min (by linarith) (by norm_num)
  have hd' : 3*d < δ := by linarith [show d ≤ δ/4 from min_le_left ..]
  refine ⟨d,hd,fun n L _ _ _ _ A hw h k hh hk => ?_⟩
  have eq {p q : n → G.El} (hp : A.Solves p) (hr : G.Nearest 1 (Pairs.centroid p))
      (hq : A.Solves q) (hs : G.Nearest 1 (Pairs.centroid q)) : p = q := by
    classical
    obtain ⟨x,-,hx⟩ := Finset.exists_max_image Finset.univ (fun i => ‖G.mat (p i)-G.mat (q i)‖) Finset.univ_nonempty
    let u := ‖G.mat (p x)-G.mat (q x)‖
    have hg (i) : ‖G.mat (p i)-G.mat (q i)‖ ≤ u := hx _ (Finset.mem_univ _)
    let B := A.feedback p x - A.feedback q x
    obtain hi := H (A.feedback p x) (A.feedback q x) ((A.closeness hd.le hw hp hr x).trans_lt hd')
      ((A.closeness hd.le hw hq hs x).trans_lt hd') (p x) (q x) (A.self_consistent hp x) (A.self_consistent hq x)
    have he : G.lie.starProjection (Pairs.centroid p-Pairs.centroid q) = 0 := by
      rw [show Pairs.centroid p-Pairs.centroid q = (Pairs.centroid p-1)-(Pairs.centroid q-1) by abel]
      exact (G.lie.starProjection_apply_eq_zero_iff).mpr (sub_mem (G.nearest_normal_one hr) (G.nearest_normal_one hs))
    have hu : ‖G.lie.starProjection B‖ ≤ u*d := by
      apply le_trans _ (A.weak_changes hw p q x u hg)
      have hx := G.lie.norm_starProjection_apply_le (B-(Pairs.centroid p-Pairs.centroid q))
      rwa [map_sub, he,sub_zero] at hx
    funext i
    apply G.mat_injective; apply sub_eq_zero.mp; apply norm_le_zero_iff.mp
    apply (hg i).trans
    have H₁ := norm_le_insert' (G.mat (p x)-G.mat (q x)) (G.lie.starProjection B)
    simp only [NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat] at hi
    have H₂ := A.changes p q x u hg; change ‖B‖ ≤ u at H₂
    have hy : u*d ≤ u*(1/4) := mul_le_mul_of_nonneg_left (min_le_right ..) (norm_nonneg _)
    change ‖G.mat (p x)-G.mat (q x)-G.lie.starProjection B‖ ≤ _*‖B‖ at hi
    change u ≤ _ at H₁
    linarith only [H₁,H₂,hy,hu,hi]
  obtain ⟨a,ha⟩ := G.nearest_exists (Pairs.centroid h)
  obtain ⟨b,hb⟩ := G.nearest_exists (Pairs.centroid k)
  have H₁ : ∀ i, a⁻¹*h i=b⁻¹*k i := congr_fun (eq (p := fun i => a⁻¹*h i) (q := fun i => b⁻¹*k i)
    (fun c => by rw [A.moves]; exact hh c) (by
      rw [Pairs.turns,← inv_mul_cancel a]; exact (G.nearest_left a⁻¹ a _).mpr ha) (fun c => by rw [A.moves]; exact hk c) (by
      rw [Pairs.turns,← inv_mul_cancel b]; exact (G.nearest_left b⁻¹ b _).mpr hb))
  exact ⟨b*a⁻¹,fun i => by rw [mul_assoc,H₁ i, mul_inv_cancel_left]⟩
end
end YM.Branch
