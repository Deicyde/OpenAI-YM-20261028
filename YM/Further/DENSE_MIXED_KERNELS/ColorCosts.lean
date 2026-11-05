import YM.Extra.MULTISOURCE_BOUNDS.Inheritance
import YM.Further.DENSE_MIXED_KERNELS.View


/-!
# Entry costs for colors/marks

Regular on the actual Healthy domain. κ convention used at input.
Invoice roots at own origin after passing the inspection test through
System's projection to the price with support power tests.
We buy optional variant choices for every old address, not just one
charged address per site. Volume/parameter-independent uses still need
get these **local** costs with the right clocks.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.DenseMixedKernels
open Function Filter Finset MeasureTheory Lattice RG Wilson Precision Labels Marker Overlay Extra.Multi Extra.Multi.Merger Tree
 
open scoped NNReal ENNReal Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G : Gauge} {m n : Side} {V : Type} [DecidableEq V] {R : Census V}
    {α : Type} {g : Ratio m n} {A : Rep G n} (D : Bands R A) {σ : α→Pieces}

structure ForkShape (g : Ratio m n) (o : V → Site m) (Y : Layer G V m) (B r : ℕ) (auth : Y.Id→Pieces) : Prop where
  center i : o i=g.parent (D.origins i)
  mark i : Y.names i=bids D (auth i)
  reach i : (inspected (blocks D (auth i))).image g.parent ⊆ Y.supp i
  halo i : Y.supp i ⊆ halo (r*B) ((inspected (blocks D (auth i))).image g.parent)

variable {x : α} {Γ : ℝ} {e : Pieces→ℝ} {r B M : ℕ} {o : V → Site m}

lemma lives (hD : D.Active) (M) (a : Pieces) : 0 < coverNumber M (blocks D a) := by
  have hh : (blocks D a).Nonempty := by
    rcases a with i|i
    · obtain ⟨v,hv⟩ := hD.proper i; exact ⟨_,hD.pins i _ hv⟩
    exact (A.activities.forced i.1).inventory_ne.mono (A.activities.forced i.1).inventory_sup
  have he := Corona.pays (blocks D a) M; contrapose! he
  rw [le_zero_iff.mp he,zero_mul]; exact Finset.card_pos.mpr hh

lemma fires (hD : D.Active) (he : Inbox D Γ e) (a : Pieces) : (bids D a).Nonempty ∧
    (0<e a → ∀ i∈ bids D a,D.origins i∈blocks D a) := by
  rcases a with i|i
  · exact ⟨hD.proper _, fun _ => hD.pins i⟩
  exact ⟨hD.occurs ..,fun hv j hj => hD.retained i.1 i.2 (fun hx => (hv.ne' (he.blank i.1 i.2 hx))) j hj⟩

/-- Transfering the incoming mask lookup once into the complete stencil on
this step. Does not guarantee any comparability of Supports in non-hat units. -/
theorem spread {Y : Layer G V m} {σ : Y.Id → Pieces} (hD : D.Active) (F : ForkShape D g o Y B r σ)
    (hB : 0<B) {k l : ℕ} {w : Y.Id→ℝ} (hw : ∀ i,0≤w i) (hf : ∀ i, SumBudget (fun j => if σ j=i then w j else 0)
      (Γ * (1+(coverNumber M (blocks D i):ℝ))^l)) (C : ℝ) (hC : 0≤C) {b : ℝ} {e : Pieces→ℝ} (he : Inbox D b e)
    {u : ℝ} {d z : ℕ} (hs : r+5≤z) (hΓ : C*Γ ≤ u) (hp : 0≤u) (hd : k+l≤d) :
    Fork (bids D) (blocks D) Y.names Y.supp o g z B M d e
      (fun j => C*(1+(coverNumber M (blocks D (σ j)):ℝ))^k * w j * e (σ j)) u := by
  let X := blocks D
  let fee j := C*(1+(coverNumber M (blocks D (σ j)):ℝ))^k * w j * e (σ j)
  have he' j : 0≤fee j := mul_nonneg (mul_nonneg (by positivity) (hw _)) (he.pos _)
  refine ⟨σ, fun j hj => ?_,fun i => ?_⟩
  · have hA : 0< e (σ j) := by contrapose! hj; rw [le_antisymm hj (he.pos _),mul_zero]
    obtain ⟨⟨v,hv⟩,hh⟩ := fires D hD he (σ j)
    refine ⟨F.mark j,v,F.mark j ▸ hv, F.center v ▸ (F.reach j (
      mem_image_of_mem _ (mem_union_left _ (hh hA v hv)))),?_⟩
    intro x hx
    obtain ⟨u,hu,hy⟩ := halo_spec.mp (Extra.Multi.System.inspected_budget g _ hB r (F.halo j hx))
    exact halo_spec.mpr ⟨u,hu,hy.trans (Nat.mul_le_mul_right _ hs)⟩
  let x := 1+(coverNumber M (X i):ℝ)
  let K := C*x^k
  have hK : 0≤K := by unfold K x; positivity
  apply Budget.mono (Budget.scale (hf i) (mul_nonneg hK (he.pos i)))
  · intro j; split; exact he' _; rfl
  · intro j; split_ifs with hj; swap; rw [mul_zero]
    unfold K x; rw [hj]; exact le_of_eq (by ring)
  have hv : 1≤x := le_add_of_nonneg_right (by positivity)
  unfold K
  calc
    _ = C*Γ*x^(k+l)*e i := by rw [pow_add]; unfold x; change _=C*Γ*(_*_)*_; dsimp only [X]; ring
    _ ≤ u*x^(k+l)*e i := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hΓ (by positivity)) (he.pos i)
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hv hd) hp) (he.pos i)
end YM.Further.DenseMixedKernels
