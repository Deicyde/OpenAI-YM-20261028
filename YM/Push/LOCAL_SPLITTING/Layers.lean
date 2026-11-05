import YM.Corona.Halo
import YM.Push.LOCAL_SPLITTING.Response


/-!
# Telescoping localized probes and per-layer prices before projection

Absolute (not decaying!) per-layer costs pre-side and explicit truncation at
the true period in native sites. This direct kernel construction does not
deliver uniform-in-volume summable layer costs or `Output`/RG improvement.
Can use components/price lemmas individually or tighten estimates. No ties
or winding exclusions, no division by a Taylor piece, no assumption of a
true marginal depending on local fine variables only.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Local.Kernel
open Function Filter Lattice Wilson RG Source Labels MeasureTheory Next.Foundations
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side}

theorem responsePrice_ge (G : Gauge) (β : ℝ) (k j : ℕ) {r : ℝ} (hr : 0 ≤ r) : 1 ≤ responsePrice G β k j r := by
  have H (k : ℕ) {C : ℝ} (hC : 1 ≤ C) (i) : 1 ≤ invRate k C i := by
    induction i with
    | zero => rfl
    | succ i ih =>
      exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_mul_of_one_le_of_one_le ih ih)) hC)
  have ht := one_le_pow₀ (n:=k) (noiseFactor_ge G β k j hr)
  exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_mul_of_one_le_of_one_le ht (H k ht k))

theorem responsePrice_mono (G : Gauge) (β : ℝ) (k : ℕ) {i j : ℕ} {r : ℝ} (hr : 0 ≤ r) (hi : i≤j) : responsePrice G β k i r ≤ responsePrice G β k j r := by
  have H (m : ℕ) {C a : ℝ} (h : 0 ≤ C) (ha : C ≤ a) : 0 ≤ invRate k C m ∧ invRate k C m ≤ invRate k a m := by
    induction m with
    | zero => exact ⟨zero_le_one,le_rfl⟩
    | succ m ih =>
      obtain ⟨h1,h2⟩ := ih; simp only [invRate]; constructor
      · positivity
      have := h1.trans h2; gcongr
  let C (i : ℕ) := (noiseFactor G β k i r)^k
  have h₁ : 0 ≤ C i := by unfold C; positivity [noiseFactor_ge G β k i hr]
  have ht : C i ≤ C j := by
    unfold C; apply pow_le_pow_left₀ (zero_le_one.trans (noiseFactor_ge _ _ _ _ hr))
    unfold noiseFactor scorePrice; gcongr; positivity [pairingNorm_nonneg G, G.colorScale_pos]
  obtain ⟨h1,h2⟩ := H k h₁ ht
  unfold responsePrice; change 2^k*(C i*invRate k (C i) k) ≤ _; gcongr; exact h₁.trans ht

def layer (o : Site c) (i : ℕ) := halo i {o}
def count (i : ℕ) := (i+i+1)^4

theorem layer_origin (o : Site c) (i : ℕ) : o ∈ layer o i := halo_subset i _ (Finset.mem_singleton_self _)

theorem layer_sub (o : Site c) {i j : ℕ} (h : i ≤ j) : layer o i ⊆ layer o j := Corona.halo_mono h (Finset.Subset.refl _)

theorem layer_dist (o x : Site c) {i : ℕ} : x∈layer o i ↔ separation x o ≤ i := by simp [layer,halo_spec,separation_comm o x]



theorem layer_size (o : Site c) (i : ℕ) : (layer o i).card ≤ count i := by simpa [layer,count] using Corona.halo_size {o} i

theorem layer_edges (o : Site c) (i : ℕ) : (edges (layer o i)).card ≤ count i * 4 := by
  have h : edges (layer o i) ⊆ layer o i ×ˢ Finset.univ := fun x hx => by simp only [Finset.mem_product,Finset.mem_univ,and_true]; exact (Finset.mem_filter.mp hx).2.1
  refine (Finset.card_le_card h).trans ?_; simp only [Finset.card_product]; exact Nat.mul_le_mul_right _ (layer_size o i)

theorem layer_tiles (o : Site c) (B : BudgetPoint) (i : ℕ) : coverNumber B.B (layer o i) ≤ count i := le_trans (Corona.cover_mono (Corona.halo_mono (Nat.le_mul_of_pos_right i B.B_pos) (Finset.Subset.refl {o})) B.B) (Corona.tile o i B.B B.B_pos)

section Pieces
variable (S : StepData c f) (β : ℝ) (D : Config G f → ℝ) (F : Config G f → ℂ) (o : Site c)

def localField (i : ℕ) := response S β D F (edges (layer o i))
def older (i : ℕ) := if i=0 then 0 else localField S β D F o (i-1)
def gap (i : ℕ) := if i≤c.val then localField S β D F o i - older S β D F o i else 0



def fieldPrice (G : Gauge) (u : ℝ) (B : BudgetPoint) (i : ℕ) := responsePrice G u B.order (count i*4) (B.threshold*(1+i)^B.power)

theorem fieldPrice_ge (G : Gauge) (u : ℝ) (B : BudgetPoint) (i : ℕ) : 1 ≤ fieldPrice G u B i := responsePrice_ge _ _ _ _ (by positivity [B.threshold_pos])

variable {D F}

theorem gap_regular (h : Good S D F) (B : BudgetPoint) (i : ℕ) : B.Regular (layer o i) (gap S β D F o i) := by
  unfold gap older; split
  · apply regular_sub (response_regular _ _ _ h); split
    · exact regular_const _
    exact regular_larger (response_regular _ _ _ h) (layer_sub o (Nat.sub_le ..))
  exact regular_const _

theorem field_value (V : Config G c) {a : ℝ} (h : Good S D F) (ha : ∀ U, ‖F U‖ ≤ a*D U) (i : ℕ) : ‖localField S β D F o i V‖ ≤ a := by
  simpa only [leftDerivs,responsePrice,invRate,pow_zero,one_mul,localField] using bound_response β (edges (layer o i)) V h (le_refl 0) ha 0 [] le_rfl (by simp)

theorem gap_bill (h : Good S D F) (B : BudgetPoint) {a : ℝ} (ha : ∀ U, ‖F U‖ ≤ a*D U) (i : ℕ) :
    B.supBounds o (layer o i) (gap S β D F o i) (if i ≤ c.val then 2*fieldPrice G (β*S.kernel.penalty) B i * a else 0) ∧
    ∀ U, ‖gap S β D F o i U‖ ≤ if i≤c.val then 2*a else 0 := by
  let C := fieldPrice G (β*S.kernel.penalty) B i
  have hp := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (ha 1)) (h.positive _)
  unfold gap; split
  · have he j (hj : j ≤ i) : B.supBounds o (layer o j) (localField S β D F o j) (C*a) := by
      apply bound_weaken (budget_response β o (layer o j) (R:=(i:ℝ)) (by positivity) (fun x hx => by exact_mod_cast ((layer_dist o x).mp hx).trans hj) B h ha) (mul_le_mul_of_nonneg_right (responsePrice_mono _ _ _ (by positivity [B.threshold_pos]) ?_) hp)
      apply (layer_edges o j).trans; unfold count; gcongr
    have hC := zero_le_one.trans (fieldPrice_ge G (β*S.kernel.penalty) B i)
    unfold older; split
    · simp only [sub_zero]; exact ⟨bound_weaken (he i le_rfl) (by change _ ≤ 2*C*a; nlinarith [mul_nonneg hC hp]),fun V => (field_value _ _ _ _ h ha i).trans (by linarith)⟩
    exact ⟨bound_weaken (bound_sub (response_regular _ _ _ h) (regular_larger (response_regular _ _ _ h) (layer_sub o (Nat.sub_le i 1))) (he i le_rfl) (bound_larger (he (i-1) (Nat.sub_le i 1)) (layer_sub _ (Nat.sub_le i 1)))) (by change _ ≤ 2*C*a; linarith),fun V => (norm_sub_le ..).trans ((add_le_add (field_value S β o V h ha i) (field_value S β o V h ha (i-1))).trans (by linarith))⟩
  exact ⟨by simpa only [norm_zero] using! (bound_const (G:=G) (B:=B) (o:=o) (X:=layer o i) (0:ℂ)),fun V => by simp⟩
end Pieces
end YM.Push.Local.Kernel
