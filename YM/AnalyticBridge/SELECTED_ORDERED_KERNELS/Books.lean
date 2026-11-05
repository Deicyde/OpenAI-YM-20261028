import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Fields

/-!
# Lie budgets on an actual Config argument (on fixed decision germs)

Two ways of spending besides fixed-slot rows/columns: simultaneous star
locality sums including Taylor positions, and testing the ordered operator
on full directions of polynomial growth. `ChangedBook` applies to the
**pointwise** difference (e.g. tree2 minus tree1 inverse), retaining one
extra location. Given smoothness for both choices separately this is also
the difference of the `leftDerivs`. These APIs do not give a neighborhood
of applicability *of the estimates* from a check at one configuration.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SelectedOrderedKernels
open Lattice Wilson RG Function WardBin.Lies Exterior FreeResolvent Affine Mark TestD
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {n : Side} {j k k' : ℕ} {X ι κ : Type*} [Fintype ι] [Fintype κ]

structure Book (D : Cost X) (a₁ : ι → X) (b : κ → X) (a : Edge (Site n) → X) (k : ℕ) (d γ : ℝ)
    (M : ℕ → ℝ) (F : Config G n → Matrix ι κ ℝ) (V : Config G n) : Prop where
  smooth : Germ k F V
  nonneg j : j ≤ k → 0 ≤ M j
  bill j (z : Pins G n j) : j ≤ k → Bill (positions D (a ∘ edge) d) D a₁ b (List.ofFn z) γ (M j) (ordered F V z)

structure ChangedBook (D : Cost X) (a₁ : ι → X) (b : κ → X) (a : Edge (Site n) → X) (k : ℕ) (d η γ : ℝ)
    (v : X) (M : ℕ → ℝ) (F : Config G n → Matrix ι κ ℝ) (V : Config G n) : Prop where
  smooth : Germ k F V
  nonneg j : j ≤ k → 0 ≤ M j
  hit j (z : Pins G n j) : j ≤ k → Noticed D a₁ b (positions D (a ∘ edge) d) η γ v (List.ofFn z) (M j) (ordered F V z)

variable {V : Config G n} {F H : Config G n → Matrix ι κ ℝ} {D : Cost X} {a : Edge (Site n) → X} {x o v : X}
  {a₁ : ι → X} {b : κ → X} {d δ γ η e m Q s fee Y γ' η' : ℝ} {P : ℕ} {M N : ℕ → ℝ}

lemma due_mono (D : Cost X) (x : X) (a : Edge (Site n) → X) (z : Pins G n j) (he : δ ≤ d) :
    due D a δ x z ≤ due D a d x z := by simp only [due,Stars.pays]; exact Real.exp_monotone (mul_le_mul_of_nonneg_right he (Stars.rays_nn ..))

omit [Fintype ι] in
lemma discount {A : Matrix ι κ ℝ} {z : Pins G n j}
    (h : Rates (positions D (a ∘ edge) d) D a₁ b (List.ofFn z) γ m A) (hd : δ ≤ d) :
    Rates (positions D (a ∘ edge) δ) D a₁ b (List.ofFn z) γ m A := by
  constructor; intro i; apply le_trans ?_ (h.rows i)
  exact mul_le_mul_of_nonneg_right (due_mono D _ _ z hd)
    (Finset.sum_nonneg fun j _ => mul_nonneg (D.weight_nn ..) (abs_nonneg _))

namespace Book

variable (h : Book D a₁ b a k d γ M F V)
include h



lemma mono (hδ : δ ≤ d) (hγ : γ' ≤ γ) (hk : k' ≤ k) (he : ∀ j ≤ k', M j ≤ N j) : Book D a₁ b a k' δ γ' N F V := by
  refine ⟨h.smooth.prod hk,fun j hj => (h.nonneg j (hj.trans hk)).trans (he j hj),fun j z hj => ?_⟩
  have ht := (h.bill j z (hj.trans hk)).mono hγ (he j hj)
  exact ⟨discount ht.row hδ,discount ht.col hδ⟩

theorem fields (l : List (Directions G n)) (hl : l.length ≤ k) (hB : ∀ B ∈ l, admitted D a o P fee B)
    (hs : 0 < s) (hd : s+s ≤ d) (hfee : 0 ≤ fee) (hv : D.Volume (a ∘ edge (G:=G)) s Y) :
    Bill (radial _ D o P) D a₁ b l γ (fieldFee s P fee Y l.length * M l.length) (leftDerivs F l V) :=
  field_bill l (h.smooth.prod hl) (fun w => h.bill _ w hl) hB hs hd hfee (h.nonneg _ hl) hv

theorem total (hj : j ≤ k) {W : ι → κ → Pins G n j → Bool} (hs : 0 ≤ s) (hd : 2*(j+3:ℕ)*s ≤ d)
    (hγ : 2*(j+3:ℕ)*s ≤ γ) (hY : 0 ≤ Y) (hW : ∀ i q z, W i q z=true → x=a₁ i ∨ x=b q ∨ ∃ m, x=a (edge (z m)))
    (hv : D.Volume a₁ s Y) (hw : D.Volume b s Y) (hh : D.Volume (a ∘ edge (G:=G)) s Y) :
    Stars.NearStar j D a₁ b (a ∘ edge) x W s (Stars.crowd j (M j) Y) (fun i q z => ordered F V z i q) := by
  apply Stars.sums_no_mark hs (h.nonneg _ hj) le_rfl hY _ hW hv hw hh
  intro i q z
  have he := (((h.mono (k':=k) hd hγ le_rfl (fun j _ => le_rfl)).bill j z hj).row.entry i q)
  rw [Stars.pays, ← mul_assoc] at he
  unfold Stars.costs; rw [D.self,zero_add,add_comm (D.d ..), mul_add,Real.exp_add]; exact he
end Book

namespace ChangedBook
variable (h : ChangedBook D a₁ b a k d η γ v M F V)
include h

lemma mono (hd : δ ≤ d) (hg : γ' ≤ γ) (he : η' ≤ η) (hk : k' ≤ k) (hm : ∀ j ≤ k', M j ≤ N j) :
    ChangedBook D a₁ b a k' δ η' γ' v N F V := by
  refine ⟨h.smooth.prod hk,fun j hj => (h.nonneg j (hj.trans hk)).trans (hm j hj),fun j z hj => ?_⟩
  constructor; intro i q; obtain ⟨hr,hc⟩ := (h.hit j z (hj.trans hk)).test i q
  have HH (x y : X) : D.weight η' x v * due D a δ x z * (D.weight γ' x y * |ordered F V z i q|) ≤
      D.weight η x v * due D a d x z * (D.weight γ x y * |ordered F V z i q|) := by
    refine mul_le_mul (mul_le_mul (D.weight_mono he ..) (due_mono D x _ z hd) (pay_pos ..).le (D.weight_nn ..))
      (mul_le_mul_of_nonneg_right (D.weight_mono hg ..) (abs_nonneg _))
      (mul_nonneg (D.weight_nn ..) (abs_nonneg _)) (mul_nonneg (D.weight_nn ..) (pay_pos ..).le)
  exact ⟨(HH _ _).trans (hr.trans (hm j hj)), (HH _ _).trans (hc.trans (hm j hj))⟩

lemma bill (z : Pins G n j) (hj : j ≤ k) (ha : D.Volume a₁ (γ-γ') Q) (hb : D.Volume b (γ-γ') Q) :
    Bill (marked D (positions D (a ∘ edge) d) v η) D a₁ b (markedSlots (List.ofFn z)) γ' (Q*(M j)) (ordered F V z) :=
  (h.hit j z hj).financed (h.nonneg _ hj) ha hb

theorem fields (l : List (Directions G n)) (hl : l.length ≤ k) (hB : ∀ B ∈ l, admitted D a o P fee B)
    (hs : 0 < s) (hd : s+s ≤ d) (hfee : 0 ≤ fee) (hY : 0 ≤ Y) (hv : D.Volume (a ∘ edge (G:=G)) s Y)
    (ha : D.Volume a₁ (γ-γ') Q) (hb : D.Volume b (γ-γ') Q) :
    Bill (marked D (radial _ D o P) v η) D a₁ b (markedSlots l) γ' (Q*(fieldFee s P fee Y l.length * M l.length)) (leftDerivs F l V) :=
  field_tagged l (h.smooth.prod hl) (fun w => h.hit _ w hl) hB hs hd hfee (h.nonneg _ hl) hY hv ha hb

/-- No normalization by the period volume in the tag test. Use also with
post-L true active coordinates or identity-completed cut families. -/
theorem total (hj : j ≤ k) (hs : 0 ≤ s) (hd : 2*(j+3:ℕ)*s ≤ d) (he : 2*(j+3:ℕ)*s ≤ η)
    (hγ : 2*(j+3:ℕ)*s ≤ γ) (hY : 0 ≤ Y) (hv : D.Volume a₁ s Y) (hw : D.Volume b s Y) (hh : D.Volume (a ∘ edge (G:=G)) s Y) :
    Stars.NearStar j D a₁ b (a ∘ edge) v (fun _ _ _ => true) s (Stars.crowd j (M j) Y) (fun i q z => ordered F V z i q) := by
  apply Stars.sums_tagged hs (h.nonneg _ hj) le_rfl hY _ hv hw hh
  intro i q z
  have h₀ := (((h.mono (k':=k) hd hγ he le_rfl (fun j _ => le_rfl)).hit j z hj).test i q).1
  rw [Stars.pays, ← mul_assoc] at h₀
  unfold Stars.costs; rw [D.self, zero_add, add_comm (D.d ..), mul_add, Real.exp_add, ← mul_assoc (D.weight ..)]; exact h₀
end ChangedBook

theorem lease (h : ContDiffAt ℝ k (over F V) 0) (hδ : 0 ≤ δ) (hd : k*δ ≤ d) (hM : ∀ j ≤ k, 0 ≤ M j)
    (hf : ∀ j ≤ k, ∀ (p : OrderedFinpartition j) (w : Pins G n p.length),
      Bill (positions D (a ∘ edge) d) D a₁ b (List.ofFn w) γ (M j) (jet (ray G n) (over F V) (List.ofFn w) 0)) :
    Book D a₁ b a k δ γ (fun j => surcharge G j * M j) F V :=
  ⟨smooth_over.mp h, fun j hj => mul_nonneg (surcharge_nn ..) (hM j hj), fun j z hj => frame_bill z (smooth_of_le h hj) hδ
    ((mul_le_mul_of_nonneg_right (Nat.cast_le (α:=ℝ).mpr hj) hδ).trans hd) (hM j hj) (hf j hj)⟩

theorem fromBundle (h : Bundle (ray G n) (positions D (a ∘ edge) d) D a₁ b (over F V) 0 k γ m)
    (hδ : 0 ≤ δ) (hd : k*δ ≤ d) (hM : 0 ≤ m) :
    Book D a₁ b a k δ γ (fun j => surcharge G j * m) F V :=
  lease (M:=fun _ => m) h.smooth hδ hd (fun _ _ => hM) (fun j hj p w => h.bound _ (by rw [List.length_ofFn]; exact p.length_le.trans hj))

theorem leaseChange {F H : Config G n → Matrix ι ι ℝ}
    (hH : ContDiffAt ℝ k (over H V) 0) (hF : ContDiffAt ℝ k (over F V) 0) (hδ : 0 ≤ δ)
    (hd : k*δ ≤ d) (hM : ∀ j ≤ k, 0 ≤ M j) (hf : ∀ j ≤ k, ∀ p : OrderedFinpartition j, ∀ w : Pins G n p.length,
      Lever.Here (ray G n) D a₁ (a ∘ edge) d γ v (List.ofFn w) (M j) (over H V) (over F V)) :
    ChangedBook D a₁ a₁ a k δ d γ v (fun j => surcharge G j * M j) (F-H) V :=
  ⟨(smooth_over.mp hF).sub (smooth_over.mp hH), fun j hj => mul_nonneg (surcharge_nn ..) (hM j hj),
    fun j z hj => frame_here z (smooth_of_le hH hj) (smooth_of_le hF hj) hδ
      ((mul_le_mul_of_nonneg_right (Nat.cast_le (α:=ℝ).mpr hj) hδ).trans hd) (hM j hj) (hf j hj)⟩
end YM.SelectedOrderedKernels
