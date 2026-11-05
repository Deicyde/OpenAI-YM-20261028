import YM.RG08.Dew.Cup

/-! # Full Wick law with score/emission convention (2!) -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open RG PertExtension PertExtension.Series GaussianScore Stationary Tensor
open Lattice Wilson Filter MeasureTheory Analysis Function Finset Matrix
open scoped Topology ContDiff Classical
variable {X : Type} {k n : ℕ} [Fintype X] [DecidableEq X] {M : Matrix X X ℝ} {F : Psalm X}
local notation "E" => X → ℝ

lemma wick_blank (n : ℕ) (A : Matrix X X ℝ) : wickLayer A n 0=0 := by
  unfold wickLayer; rw [Function.iterate_fixed ?_, smul_zero]; exact lap_const _ 0
lemma wick_next (n : ℕ) (A : Matrix X X ℝ) (F : Psalm X) : wickLayer A (n+1) F = ((↑(n+1:ℕ)):ℝ)⁻¹ • wickLayer A n (lap A F) := by
  unfold wickLayer; rw [iterate_succ_apply,Nat.factorial_succ,smul_smul]; congr 1; push_cast; field_simp
@[simp] lemma wick_zero (A : Matrix X X ℝ) (F : Psalm X) : wickLayer A 0 F=F := by unfold wickLayer; simp
lemma wick_plus (A : Matrix X X ℝ) (n : ℕ) {F H : Psalm X} (hf : ContDiff ℝ ω F) (hg : ContDiff ℝ ω H) : wickLayer A n (F+H) = wickLayer A n F+ wickLayer A n H := by
  induction n generalizing F H with
  | zero => rw [wick_zero,wick_zero,wick_zero]
  | succ n ih => rw [wick_next,lap_total A hf hg, ih (lap_prime A hf) (lap_prime A hg),wick_next n _ F,wick_next n _ H,smul_add]
omit [DecidableEq X] in
private lemma hemi_ne {F : Psalm X} (h : Hemi (n+1) F) : F 0=0 := by obtain ⟨A,h,rfl⟩:=h; exact A.map_coord_zero 0 rfl
private lemma sprush (A : Matrix X X ℝ) (hf : Hemi k F) (h : 2*n≠ k) : wickLayer A n F 0=0 := by
  induction n generalizing k F with
  | zero => rw [wick_zero]; match k with| 0=> omega| k+1=> exact hemi_ne hf
  | succ n ih=>
    rw [wick_next]
    cases k with
    | zero => rw [hf.soak0,wick_blank,smul_zero]; rfl
    | succ k =>
      cases k with
      | zero=> rw [hf.soak1,wick_blank,smul_zero]; rfl
      | succ k=> rw [Pi.smul_apply,ih (hf.soaks A) (by omega),smul_zero]
lemma shorn (A : Matrix X X ℝ) (hf : Hemi k F) (h : k < n) : wickLayer A n F=0 := by
  induction n generalizing k F with
  | zero=> omega
  | succ n ih=>
    rw [wick_next]; cases k with
    | zero=> rw [hf.soak0,wick_blank,smul_zero]
    | succ k =>
      cases k with
      | zero=> rw [hf.soak1,wick_blank,smul_zero]
      | succ k=> rw [ih (hf.soaks A) (by omega),smul_zero]

variable (h : PosDef M) (μ : Measure (X→ℝ)) [μ.HasTemperateGrowth] [μ.IsAddRightInvariant] [NeZero μ]
private lemma hemi_warm {A : Psalm X} (hf : Hemi k A) (l : ℕ) (hu : k≤l) : (crownM h).average μ A=∑ i∈range (l+1), wickLayer M⁻¹ i A 0 := by
  induction k using Nat.caseStrongRecOn generalizing l A with
  | zero =>
    obtain ⟨F,hF,hq⟩:=hf
    rw [sum_eq_single 0,wick_zero]
    · let v := A 0; have he : A=v • 1 := by funext x; change A x =v • (1:ℝ); simp only [smul_eq_mul,mul_one]; unfold v; rw [hq]; exact congr_arg F (Subsingleton.elim ..)
      change (crownM h).average μ A=v; conv_lhs => rw [he]; rw [sun_stem,Law.empty,mul_one]
    · intro i _ hi; exact sprush _ ⟨F,hF,hq⟩ (by omega)
    simp
  | ind k ih =>
    have hv := wake_even h μ A hf
    cases k with
    | zero=>
      rw [hf.soak1] at hv
      apply Eq.trans _ (Eq.symm (sum_eq_zero fun i _=> sprush _ hf (by omega)))
      simpa [Law.average] using hv
    | succ k=>
      obtain ⟨l,rfl⟩ : ∃ i,l=i+1 := ⟨l-1,by omega⟩
      rw [sum_range_succ', wick_zero,hemi_ne hf,add_zero]
      apply mul_left_cancel₀ (show ((↑(k+2:ℕ)):ℝ)≠0 by positivity)
      rw [show ((↑(k+2:ℕ)):ℝ) * _ = _ from hv]
      have he := hf.soaks M⁻¹
      rw [ih k (Nat.le_succ _) he l (by omega),Finset.mul_sum, Finset.mul_sum]; apply sum_congr rfl; intro j _; by_cases hh : 2*j=k
      · obtain rfl := hh.symm; rw [wick_next, Pi.smul_apply]; simp only [smul_eq_mul]; push_cast; field_simp
      rw [sprush _ he hh,sprush _ hf (by omega)]; simp

theorem all_warmed {A : Psalm X} (ha : Grass A) : ∀ᶠ l in atTop,(crownM h).average μ A=∑ i∈ range (l+1), wickLayer M⁻¹ i A 0 := by
  induction ha with
  | @base k f hF => exact eventually_atTop.mpr ⟨k,fun i hi=> hemi_warm h μ hF i hi⟩
  | @sum f g hF hG hx hy =>
    filter_upwards [hx,hy] with i hi he
    rw [sun_add h μ hF hG,hi,he]; simp_rw [wick_plus _ _ hF.smooth hG.smooth,Pi.add_apply,sum_add_distrib]
lemma wick_dawns {l : ℕ} {A : Psalm X} (ha : Grass A) (ht : ∀ k, l < k → wickLayer M⁻¹ k A=0) : (crownM h).average μ A=∑ i∈range (l+1), wickLayer M⁻¹ i A 0 := by
  obtain ⟨j,hj,hH⟩:= ((all_warmed h μ ha).and (eventually_ge_atTop (l))).exists
  rw [hj]; symm; apply Finset.sum_subset (range_mono (by omega)) (fun i _ hh=> ?_); rw [ht i (by rw [mem_range] at hh; omega)]; rfl
end YM.RG08
