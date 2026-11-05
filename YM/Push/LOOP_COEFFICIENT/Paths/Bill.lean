import YM.Push.LOOP_COEFFICIENT.Paths.Pieces

/-!
# Absolute cover budgets for local action vertices
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Paths
open Set Function Filter Matrix Metric Lattice Laurent RG Bloch Wilson Work.F02 Complex
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {k : ℕ} {a ι κ : Type} {η σ ρ C D Λ : ℝ} {W : PathData G} {p : Clip} {M : ι → Reader a} {N : κ → Reader a}

lemma Damped.finite (M : ι → Reader a) [Finite ι] (hη : 0<η) (hρ : 0<ρ) (h : ∀ i,ContDiff ℂ ω (M i).value) : ∃ C, Damped M η ρ C := by
  choose B hB using fun i => isCompact_closedBall (0:CSpace (M i).shape) ρ |>.exists_bound_of_continuousOn (h i).continuous.continuousOn
  let g (i : ι) := B i * Real.exp (η*(M i).sizeBound)
  refine ⟨∑' i,g i, hη,hρ,h, g, ⟨fun i => mul_nonneg ((norm_nonneg _).trans (hB i 0 (mem_closedBall_self hρ.le))) (Real.exp_pos _).le, .of_finite, le_rfl⟩,fun i z hz => ?_⟩
  dsimp only [g]; gcongr; apply hB; simpa
lemma Damped.coprod (h : Damped M η ρ C) (h' : Damped N η ρ D) : Damped (Sum.elim M N) η ρ (C+D) := by
  obtain ⟨g,hg,H⟩ := h.bill; obtain ⟨f,hf,F⟩ := h'.bill
  have he : HasSum (Sum.elim g f) ((∑' i,g i)+∑' i,f i) := .sum hg.2.1.hasSum hf.2.1.hasSum
  exact ⟨h.width,h.radius,fun i => Sum.rec (motive:=fun i => ContDiff ℂ ω ((Sum.elim M N i).value)) h.smooth h'.smooth i, Sum.elim g f,⟨fun i => by cases i <;> first | apply hg.1 | apply hf.1,he.summable,he.tsum_eq.trans_le (add_le_add hg.2.2 hf.2.2)⟩,fun i => by cases i <;> first | apply H | apply F⟩
lemma Damped.group [Fintype κ] {N : κ × ι → Reader a} {C : κ → ℝ} (hη : 0<η) (hρ : 0<ρ) (h : ∀ j, Damped (fun i => N (j,i)) η ρ (C j)) : Damped N η ρ (∑ i,C i) := by
  choose g hg H using fun j => (h j).bill
  have he : 0 ≤ uncurry g := fun i => (hg i.1).1 i.2
  have ht := summable_prod_of_nonneg he |>.mpr ⟨fun i => (hg i).2.1, .of_finite⟩
  exact ⟨hη,hρ,fun i => (h i.1).smooth i.2, uncurry g,⟨he, ht, ht.tsum_prod.trans_le ((tsum_fintype _).trans_le (Finset.sum_le_sum fun i _ => (hg i).2.2))⟩, fun i => H i.1 i.2⟩

def amplify (c : ℂ) (f : Film a) := { f with value := fun z => c * f.value z, inside := fun h => congr_arg _ (f.inside h) }
lemma Damped.amplify [Fintype a] {M : ι → Film a} (h : Damped (fun i => (M i).reader) η ρ C) (c : ℂ) : Damped (fun i => (Paths.amplify c (M i)).reader) η ρ (‖c‖*C) := by
  obtain ⟨g,hg,H⟩ := h.bill
  exact ⟨h.width,h.radius,fun i => contDiff_const.mul (h.smooth i), _,⟨fun i => mul_nonneg (norm_nonneg _) (hg.1 i),hg.2.1.mul_left ‖c‖,(tsum_mul_left (a:=‖c‖)).trans_le (mul_le_mul_of_nonneg_left hg.2.2 (norm_nonneg _))⟩,fun i x hx => by change ‖c*(M i).reader.value x‖*_≤_; rw [norm_mul,mul_assoc]; exact mul_le_mul_of_nonneg_left (H i x hx) (norm_nonneg _)⟩


variable (hσ : 0<σ) (hρ : 0<ρ) (h : ∀ b i (z : CSpace (Angles G)), ‖z‖≤ρ → ‖letterAngle b i z - 1‖ ≤ radius (σ/2))

lemma slotConst_nonneg : 0≤slotConst G := mul_nonneg (chargeOp_nonneg (E:=G.Mat) (colorProject G)) (norm_nonneg _)
include hσ hρ h
omit hρ in
lemma row_price {z : Surface G} (hz : ∀ x, ‖z x‖≤ρ) (i j : ℝ × Slot) (s : Signed) : ‖rowPrice (fieldSlot i.2 s z) (fieldSlot j.2 s z)‖ ≤
    (Fintype.card G.ColorIndex * slotConst G ^2) * Real.exp (σ/2*(i.2.length+j.2.length)) := by
  have H (i) (k : G.ColorIndex) := (norm_le_pi_norm (fieldSlot i s z) k).trans (fieldSlot_bound (half_pos hσ) _ (fun b i x => h b i _ (hz x)) s i)
  unfold rowPrice; rw [norm_div,Complex.norm_two]; refine (div_le_self (norm_nonneg _) (by norm_num)).trans ((norm_sum_le ..).trans ((Finset.sum_le_sum (fun k _ => show ‖fieldSlot _ s z k * fieldSlot _ s z k‖ ≤ _ from (norm_mul ..).trans_le (mul_le_mul (H _ k) (H _ k) (norm_nonneg _) (mul_nonneg slotConst_nonneg (Real.exp_pos _).le)))).trans_eq ?_))
  simp [mul_add,Real.exp_add]; ring

def rowCharge (σ : ℝ) (u : ℝ × Slot) := |u.1| * Real.exp (σ*u.2.length)
omit hρ in
lemma rowFilm_bound (i j : ℝ × Slot) (s : Signed) (z : CSpace (rowFilm G s i j).reader.shape) (hz : ‖z‖≤ρ) :
    ‖(rowFilm G s i j).reader.value z‖ * Real.exp (σ/4*(rowFilm G s i j).reader.sizeBound) ≤ (Fintype.card G.ColorIndex * slotConst G ^2) * (rowCharge σ i * rowCharge σ j) := by
  change ‖((i.1*j.1:ℝ):ℂ)*rowPrice _ _‖ * Real.exp (σ/4*(2*(i.2.length+j.2.length):ℕ)) ≤ _
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_mul]
  refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (row_price hσ h (z:=pad z) (fun x => (pad_norm z x).trans hz) i j s) (by positivity : 0≤|i.1| * |j.1|)) (Real.exp_pos _).le).trans_eq ?_
  push_cast; unfold rowCharge; simp only [mul_assoc]; rw [← Real.exp_add]
  rw [show σ/2*(i.2.length+j.2.length) + σ/4*(2*(i.2.length+j.2.length)) = σ*i.2.length+σ*j.2.length by ring,Real.exp_add]; ring
lemma rowFilm_damped (u : ι → ℝ × Slot) (hb : SumBudget (rowCharge σ ∘ u) C) (s : Signed) : Damped (fun z : ι × ι => (rowFilm G s (u z.1) (u z.2)).reader) (σ/4) ρ ((Fintype.card G.ColorIndex * slotConst G ^2) * (C*C)) := by
  let B : ℝ := Fintype.card G.ColorIndex * slotConst G ^2
  have hB : 0≤B := by dsimp only [B]; positivity
  have he := hb.2.1.mul_of_nonneg hb.2.1 hb.1 hb.1
  have hh := he.mul_left B
  refine ⟨by positivity,hρ,fun i => rowFilm_diff .., _,⟨fun i => mul_nonneg hB (mul_nonneg (hb.1 i.1) (hb.1 i.2)),hh,?_⟩,fun i z hz => rowFilm_bound hσ h _ _ s z hz⟩
  rw [tsum_mul_left, he.tsum_prod]; simp_rw [tsum_mul_left,tsum_mul_right]; exact mul_le_mul_of_nonneg_left (mul_le_mul hb.2.2 hb.2.2 (tsum_nonneg hb.1) ((tsum_nonneg hb.1).trans hb.2.2)) hB

omit hρ in
lemma atomFilm_bound (s : Signed) (a : Atom G k) (z : CSpace (atomFilm s a).reader.shape) (hz : ‖z‖≤ρ) :
    ‖(atomFilm s a).reader.value z‖ * Real.exp (σ/4*(atomFilm s a).reader.sizeBound) ≤ slotConst G ^ k * a.budget σ := by
  have he (b : Fin k → G.ColorIndex) : ‖∏ i,fieldSlot (a.leg i) s (pad z) (b i)‖ ≤ slotConst G ^ k * Real.exp (σ/2*a.length) := by
    rw [norm_prod]; refine (Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => (norm_le_pi_norm _ _).trans (fieldSlot_bound (half_pos hσ) _ (fun b i x => h b i _ ((pad_norm z x).trans hz)) s _))).trans_eq ?_
    rw [Finset.prod_mul_distrib,← Real.exp_sum,Atom.length,Nat.cast_sum,Finset.mul_sum]; simp
  change ‖∑ b, ((a.coeff b):ℂ) * _‖ * Real.exp (σ/4*(2*a.length:ℕ)) ≤ _
  refine (mul_le_mul_of_nonneg_right ((norm_sum_le ..).trans (Finset.sum_le_sum (g:=fun i => |a.coeff i| * (slotConst G ^ k * Real.exp (σ/2*a.length))) fun i _ => by rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (he i) (abs_nonneg _))) (Real.exp_pos _).le).trans_eq ?_
  rw [← Finset.sum_mul]; push_cast; rw [mul_assoc _ _ (Real.exp (σ/4*_)), mul_assoc _ (Real.exp _) (Real.exp _),← Real.exp_add,show σ/2*a.length + σ/4*(2*a.length) = σ*a.length by ring]; unfold Atom.budget Atom.magnitude; ring
lemma atomFilm_damped (A : ι → Atom G k) (hb : SumBudget (fun i => (A i).budget σ) C) (s : Signed) : Damped (fun z : ι => (atomFilm s (A z)).reader) (σ/4) ρ (slotConst G ^ k * C) := by
  refine ⟨by positivity,hρ,fun i => atomFilm_diff ..,_, ⟨fun i => mul_nonneg (pow_nonneg slotConst_nonneg _) (hb.1 i), hb.2.1.mul_left _, ?_⟩, fun i z hz => atomFilm_bound hσ h s (A i) z hz⟩
  rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hb.2.2 (pow_nonneg slotConst_nonneg _)
end YM.Push.Loops.Paths
