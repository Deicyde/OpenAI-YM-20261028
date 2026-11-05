import YM.Extra.WEAK_SCALING_ACTLAW.Jets
import YM.Next.EXTRACTION.Basis

/-!
# Finite Wilson comparisons via actual all-subset corrections on a basis

Product
corrections defined recursively by triangular free moment subtraction (i.e.
the coefficients after formally dividing the source by the free moment
series in commuting square-zero variables).

In particular not the simple
product of centered variables.

Wilson expectation of every nonempty
adjustment controlled via full rooted chessboard; multiplication back pays
all free sublist moments, uniform including through projection ties on the
window.

Unit fields represent omitted factors in free sublist tests.

Geometry
of the tiling is part of the *required estimate*, not simply granted for
these patterns.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.WeakScaling
open Set Function MeasureTheory Filter Climb Extraction Cells Wilson Table Ward
open scoped Topology ContDiff
variable {G : Gauge} {C : Family G} {M n d : ℕ} {Q : ℝ}

private def within (v : Fin n → (Free C).Tag) (s : Finset (Fin n)) := fun i =>
    if i ∈ s then v i else (⟨(v i).1,(Free C).unit (v i).1⟩ : (Free C).Tag)

def expected (v : Fin n → (Free C).Tag) (x : Points n) (s : Finset (Fin n)) := disc (within v s) x
lemma entire (v : Fin n → (Free C).Tag) (x) : expected v x Finset.univ = disc v x := by rw [expected,show within v Finset.univ = v by funext i; simp [within]]
lemma expected_bound (v : Fin n → (Free C).Tag) (q : Finset (Fin n)) (hQ : 0 < Q) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ apart Q n, ‖expected v x q‖ ≤ B := by
  obtain ⟨B,hB⟩ := (compact_window Q n).exists_bound_of_continuousOn
    (((Free C).class_smooth (Free C) (Maxwell.table_smooth _) (within v q)).continuousOn.mono
      (show Scaling.window Q n ⊆ conf n from fun x hx => spaced_conf (by positivity) hx.1))
  refine ⟨max 0 B,le_max_left .., fun x hx => (hB x ⟨fun i j he => ?_,hx.1.le⟩).trans (le_max_right ..)⟩
  obtain ⟨a,ha⟩ := hx.2 j i he.symm
  exact ha.le.trans ((dist_pi_le_iff (r:=cubedist (x i) (x j)) dist_nonneg).mp le_rfl a)

variable (b : Stations C) (k N p : ℕ) (v : Fin n → (Free C).Tag) (u : Fin n → Lattice.Cover)

def insertions (I : Finset (Fin n)) (U : Config G (C.side N p)) :=
  ∏ i ∈ I, C.seen (b.name k N p (v i)) (Cells.location C.S (b.grid k) N p (u i)) U

private def smallerSets {α : Type*} [DecidableEq α] (I : Finset α) := I.ssubsets.erase ∅

/-- Corrections on nonempty subsets (value on ∅ unused). Free coefficients
computed at the same rescaled positions. -/
def corrected (I : Finset (Fin n)) (U : Config G (C.side N p)) : ℂ := insertions b k N p v u I U - expected v (b.rescaled k u) I -
    ∑ t ∈ (smallerSets I).attach, expected v (b.rescaled k u) (I \ t.val) * corrected t.val U
termination_by I.card
decreasing_by exact Finset.card_lt_card (Finset.mem_ssubsets.mp (Finset.mem_of_mem_erase t.property))

lemma multiply_back (I : Finset (Fin n)) (U : Config G (C.side N p)) : insertions b k N p v u I U = expected v (b.rescaled k u) I +
    corrected b k N p v u I U + ∑ t ∈ smallerSets I, expected v (b.rescaled k u) (I \ t) * corrected b k N p v u t U := by
  rw [corrected,Finset.sum_attach (smallerSets I) (fun t => expected _ _ _ * corrected _ _ _ _ _ _ t U)]
  ring

lemma moment_le_root {n : Lattice.Side} (T : Tiling n) {β : ℝ} (h : Seam G n β) (F : Config G n → ℂ)
    (hf : Interior (T.chamber 0) F) : ‖moment β F‖ ≤ T.rootTest β F := by
  simpa using T.planted h (fun _ : Unit => 0) (fun _ _ _ => rfl) (fun _ => F) (fun _ => hf)

lemma finite_comparison (h : C.Makes) (x : Points n) (hx : x = b.rescaled k u)
    (I : Finset (Fin n)) (hi : I.Nonempty) (T : Tiling (C.side N p)) (B η : ℝ) (_hη : 0 ≤ η)
    (hB : ∀ s, ‖expected v x s‖ ≤ B)
    (ht : ∀ s ⊆ I, s.Nonempty → let Y := corrected b k N p v u s
      Interior (T.chamber 0) Y ∧ T.rootTest (C.beta N p) Y ≤ η) :
    ‖moment (C.beta N p) (insertions b k N p v u I) - expected v x I‖ ≤ (1 + (smallerSets I).card * B) * η := by
  subst x
  let Y := corrected b k N p v u
  let E := expected v (b.rescaled k u)
  let μ := law G (C.side N p) (C.beta N p)
  have h₁ (s : Finset (Fin n)) (hs : s ∈ smallerSets I) := ht s
    (Finset.mem_ssubsets.mp (Finset.mem_of_mem_erase hs)).subset (Finset.nonempty_iff_ne_empty.mpr (Finset.ne_of_mem_erase hs))
  have h₂ (s : Finset (Fin n)) (hs : s ∈ smallerSets I) : Integrable (fun U => E (I \ s)*Y s U) μ :=
    ((h₁ s hs).1.integrable _).const_mul _
  have he : moment (C.beta N p) (insertions b k N p v u I) - E I = moment (C.beta N p) (Y I) +
      ∑ s ∈ smallerSets I, E (I \ s) * moment (C.beta N p) (Y s) := by
    unfold moment
    simp_rw [multiply_back]
    change (∫ U, (E I + Y I U) + ∑ s ∈ smallerSets I, E (I\s)*Y s U ∂μ) - E I = _
    have hY : Integrable (Y I) μ := (ht I (by rfl) hi).1.integrable (C.beta N p)
    rw [integral_add (show Integrable (fun U => E I + Y I U) μ from (integrable_const (E I)).add hY) (integrable_finsetSum _ h₂),integral_finsetSum _ h₂,
      integral_add (integrable_const _) hY]
    simp only [μ,integral_const, probReal_univ,one_smul,integral_const_mul]; dsimp only [Y,E]; abel
  change ‖_ - E I‖ ≤ _
  have H (s hs he) := (moment_le_root T (seamless h N p) (Y s) (ht s hs he).1).trans (ht s hs he).2
  rw [he]
  apply (norm_add_le ..).trans
  calc
    _ ≤ η + ∑ s ∈ smallerSets I, B * η := by
      gcongr
      · exact H _ (by rfl) hi
      refine (norm_sum_le ..).trans (Finset.sum_le_sum (fun s hs => ?_))
      exact norm_mul_le .. |>.trans (mul_le_mul (hB _) ((moment_le_root T (seamless h N p) _ (h₁ s hs).1).trans (h₁ s hs).2)
        (norm_nonneg _) ((norm_nonneg _).trans (hB I)))
    _ = _ := by simp; ring

variable {b k N p v u} {f : Extraction.Order} {D : ℕ} {ι : ℕ → Type*}

/-- Genuine missing corrected all-subset/root estimates on C. Fit **one**
comparison tiling and use the whole reflected copies with conjugation as in
Seam; the required estimate is uniform on rescaled `apart Q n` generic
placements, at arbitrarily large fixed k late on the ordered cutoffs. Only
basis lists and subsets of their actual slot indices (include repeated labels;
don't identify their markers) needed in this port. The calibration is NOT
retuned in smaller subtests. -/
def RootCosts (b : Stations C) (f : Extraction.Order) (B : ∀ d, Module.Basis (ι d) ℂ ((Free C).Field d))
    (M D : ℕ) (Q : ℝ) := ∀ n, n ≤ M → ∀ d : Caps n, (∀ i, d i ≤ D) → ∀ j : (i : Fin n) → ι (d i),
    let v := fun i => (⟨d i,B (d i) (j i)⟩ : (Free C).Tag)
    ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ u : Fin n → Lattice.Cover, b.rescaled k u ∈ apart Q n → b.rescaled k u ∈ generic n →
      f.late fun N p => ∃ T : Tiling (C.side N p), ∀ s : Finset (Fin n), s.Nonempty →
        let Y := corrected b k N p v u s; Interior (T.chamber 0) Y ∧ T.rootTest (C.beta N p) Y ≤ η

variable {B : ∀ d, Module.Basis (ι d) ℂ ((Free C).Field d)}

private def Small (b : Stations C) (f : Extraction.Order) (Q : ℝ) (Z : ℕ → ℕ → ℕ → (Fin n → Lattice.Cover) → ℂ) :=
    ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ u : Fin n → Lattice.Cover, b.rescaled k u ∈ apart Q n → b.rescaled k u ∈ generic n →
      f.late fun N p => ‖Z k N p u‖ ≤ η

private lemma Small.sum {α : Type*} {Z : α → ℕ → ℕ → ℕ → (Fin n → Lattice.Cover) → ℂ} (c : α → ℂ) (s : Finset α)
    (h : ∀ i ∈ s, Small b f Q (Z i)) : Small b f Q (fun k N p u => ∑ i ∈ s, c i • Z i k N p u) := by
  let B := 1 + ∑ i ∈ s, ‖c i‖
  have hB : 0 < B := add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun i _ => norm_nonneg _)
  intro η hη
  filter_upwards [(eventually_all_finset s).mpr (fun i hi => h i hi (η/B) (by positivity))] with k hk u hu hv
  have he (i) (hi : i ∈ s) : ∀ᶠ w : ℕ × ℕ in f.fuse, ‖Z i k w.1 w.2 u‖ ≤ η/B := hk i hi _ hu hv
  refine ((eventually_all_finset s).mpr he).mono (fun w hw => (norm_sum_le ..).trans
    ((Finset.sum_le_sum (fun i hi => (norm_smul (c i) _).trans_le (mul_le_mul_of_nonneg_left (hw i hi) (norm_nonneg _)))).trans ?_))
  rw [← Finset.sum_mul, mul_div_assoc', div_le_iff₀ hB,mul_comm η]
  gcongr
  simp [B]

private theorem root_entry (H : C.Makes) (h : RootCosts b f B M D Q) (hQ : 0 < Q) (hn : n ≤ M)
    (d : Caps n) (hd : ∀ i, d i ≤ D) (j : (i : Fin n) → ι (d i)) :
    let v := fun i => (⟨d i,B (d i) (j i)⟩ : (Free C).Tag)
    Small b f Q (fun k N p u => b.cost k N p v u - disc v (b.rescaled k u)) := by
  cases n with
  | zero =>
    intro v η hη
    refine Eventually.of_forall fun k u hu he => Eventually.of_forall fun p => Eventually.of_forall fun N => ?_
    change ‖b.cost k _ _ v u - disc v _‖ ≤ η
    rw [Stations.cost,Family.num,disc,show (Free C).useAt (Free C) _ v = 1 from (Maxwell.table_regular _).trivial (fun i => ⟨(v i).1,(Free C).representative _ (v i).2⟩) _]
    simp [hη.le]
  | succ n =>
    intro v η hη
    obtain ⟨A,hA,hx⟩ : ∃ A : ℝ, 0 ≤ A ∧ ∀ s, ∀ x ∈ apart Q (n+1), ‖expected v x s‖ ≤ A := by
      choose A hA hx using fun s => expected_bound v s hQ
      exact ⟨∑ s, A s,Finset.sum_nonneg (fun s _ => hA s), fun s x h => (hx s x h).trans
        (Finset.single_le_sum (fun j _ => hA j) (Finset.mem_univ _))⟩
    let I := (Finset.univ : Finset (Fin (n+1)))
    let L := 1 + (smallerSets I).card * A
    have hL : 0 < L := by dsimp [L]; positivity
    filter_upwards [h _ hn d hd j (η/L) (by positivity)] with k hk u hu hv
    have he : ∀ᶠ w in f.fuse, ∃ T : Tiling (C.side w.1 w.2), ∀ s : Finset (Fin (n+1)), s.Nonempty →
        let Y := corrected b k w.1 w.2 v u s; Interior (T.chamber 0) Y ∧ T.rootTest (C.beta w.1 w.2) Y ≤ η/L := hk u hu hv
    refine (Order.fused f (fun w : ℕ × ℕ => ‖b.cost k w.1 w.2 v u - disc v (b.rescaled k u)‖ ≤ η)).1 ?_
    refine he.mono ?_
    rintro ⟨N,p⟩ ⟨T,hT⟩
    rw [← entire]
    exact (finite_comparison b k N p v u H _ rfl I Finset.univ_nonempty T A (η/L) (by positivity)
      (fun s => hx s _ hu) (fun s _ hs => hT s hs)).trans_eq (mul_div_cancel₀ _ hL.ne')

lemma aligned_of_root [∀ d, Fintype (ι d)] (H : C.Makes) (h : RootCosts b f B M D Q) (hQ : 0 < Q) : AlignedCosts b f M D Q := by
  classical
  intro n hn v hv
  let d : Caps n := fun i => (v i).1
  let w (i : Fin n) := (v i).2
  let J := ∀ i : Fin n, ι (d i)
  letI : Fintype J := Pi.instFintype
  let Z (j : J) := fun i => (⟨d i, B (d i) (j i)⟩ : (Free C).Tag)
  let c := fun j : J => ∏ i, (B (d i)).repr (w i) (j i)
  let Y := fun (v : Fin n → (Free C).Tag) k N p u => b.cost k N p v u - disc v (b.rescaled k u)
  suffices he : Y v = fun k N p u => ∑ i : J, c i • Y (Z i) k N p u by
    change Small b f Q (Y v); rw [he]; exact Small.sum c Finset.univ (fun i _ => root_entry H h hQ hn d hv i)
  funext k N p u
  let g : MatrixTest C d := ((C.ensemble (N:=N) (p:=p) d (location C.S (b.grid k) N p ∘ u)).compLinearMap
    (fun i => (b.coef k (d i) N p).toLinearMap)) - ((Free C).classMoment (Free C) d (b.rescaled k u))
  change g w = ∑ i : J, c i • (g (fun s => B (d s) (i s)))
  have ht i := (B (d i)).sum_repr (w i)
  conv_lhs => rw [← funext ht]
  rw [MultilinearMap.map_sum]; exact Finset.sum_congr rfl fun i _ => g.map_smul_univ _ _

/-- Geometry B root inputs only on the same finite basis, simultaneous at
the indicated width through a whole tested word. No `m` chosen after seeing
individual offsets. Requires separate `Sym` to use on rotations and stars.
-/
def BasisCenter (b : Stations C) (f : Extraction.Order) (B : ∀ d, Module.Basis (ι d) ℂ ((Free C).Field d))
    (M D : ℕ) (Q : ℝ) := ∀ n, n ≤ M → ∀ d : Caps n, (∀ i, d i ≤ D) →
      ∃ A : ℕ → ℝ, (∀ k, 0 ≤ A k) ∧ Tendsto (fun k => (A k)^n*b.delta k) atTop (𝓝 0) ∧
      ∀ᶠ k in atTop, ∃ m j : ℕ, m≤j ∧ C.S.a m < b.r k/Q ∧
        (n:ℝ)*(2*(3*C.S.a j)) < C.S.a m ∧ C.S.a j < b.r k/(4*Q) ∧
        f.late fun N p => ∀ (i : Fin n) (z : ι (d i)), centeredBudget C (b.name k N p ⟨d i,B (d i) z⟩) (A k) j N p

private def spins (h : (Free C).RealSpin) (s : Extraction.Spin.Frame) (v : (Free C).Field d) :=
    let w := (Free C).mirror h d s.1 v
    if s.2 then (Free C).conj h d w else w
private lemma applies {h : (Free C).RealSpin} (hc : ∀ g u, b.coef k d N p ((Free C).mirror h d g u) =
      C.book.mirrorGroup d g (b.coef k d N p u)) (hv : ∀ u, b.coef k d N p ((Free C).conj h d u) = star (b.coef k d N p u))
    (v : (Free C).Field d) (s : Extraction.Spin.Frame) :
    b.name k N p ⟨d,spins h s v⟩ = Extraction.Spin.token C.book (b.name k N p ⟨d,v⟩) s := by
  dsimp only [Extraction.Spin.token,Register.conjugate,Register.move,spins,Stations.name]
  split <;> simp_all

private lemma lump [∀ d, Fintype (ι d)] (B : ∀ d, Module.Basis (ι d) ℂ ((Free C).Field d)) (h : (Free C).RealSpin)
    (v : Fin n → (Free C).Tag) : ∃ L : ℝ, 0 ≤ L ∧ ∀ i s, ∑ z, ‖(B (v i).1).repr (spins h s (v i).2) z‖ ≤ L := by
  obtain ⟨L,hL,hv⟩ := ((eventually_ge_atTop (0:ℝ)).and <| eventually_all.mpr fun i => eventually_all.mpr fun s =>
    eventually_ge_atTop (∑ z, ‖(B (v i).1).repr (spins h s (v i).2) z‖)).exists
  exact ⟨L,hL,hv⟩

private lemma column_combination [Fintype (ι d)] (h : C.Makes) (B : Module.Basis (ι d) ℂ ((Free C).Field d)) (N p m k : ℕ)
    (hN : m ≤ N) (hw : C.ref d ≤ N) (D L : ℝ) (hD : 0 ≤ D)
    (ht : ∀ z, centeredBudget C (b.name k N p ⟨d,B z⟩) D m N p) (v : (Free C).Field d) (hv : ∑ z, ‖B.repr v z‖ ≤ L) :
    centeredBudget C (b.name k N p ⟨d,v⟩) (L*D) m N p := by
  classical
  refine ⟨hN,hw,fun x => ?_⟩
  let T := center C.S p hN x
  let O : (Free C).Field d →ₗ[ℂ] Config G (C.side N p) → ℂ := ((C.linearO N p d x).mk' _).comp (b.coef k d N p).toLinearMap
  have he (i) : Interior (T.chamber 0) (O (B i)) ∧ T.rootTest (C.beta N p) (O (B i)) ≤ D := (ht i).choose_spec.2 x
  change Interior _ (O v) ∧ T.rootTest _ (O v) ≤ _
  have hv' := congrArg O (B.sum_repr v)
  simp only [_root_.map_sum,map_smul] at hv'
  rw [← hv']; obtain ⟨hF,hE⟩ := Next.Extract.rooted T _ (seamless h N p) Finset.univ (fun z => O (B z)) (B.repr v)
    (fun i _ => (he i).1)
  refine ⟨hF,hE.trans ((Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_left (he z).2 (norm_nonneg (B.repr v z)))).trans ?_)⟩
  rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right hv hD

theorem center_of_basis [∀ d, Fintype (ι d)] {H : (Free C).RealSpin} (h : C.Makes)
    (hH : ∀ k d, d≤D → Sym b f H k d) (hC : BasisCenter b f B M D Q) : CenterCosts b f M D Q := by
  intro n hn v hv
  let d := fun i => (v i).1
  obtain ⟨A,hA,hlim,he⟩ := hC n hn d hv
  obtain ⟨L,hL,ht⟩ := lump B H v
  have hl : Tendsto (fun k => (L*A k)^n * b.delta k) atTop (𝓝 0) := by
    simpa only [mul_zero,mul_pow,mul_assoc] using hlim.const_mul (L^n)
  refine ⟨fun k => L*A k, fun k => mul_nonneg hL (hA k),hl,he.mono ?_⟩
  rintro k ⟨m,j,h₁,h₂,h₃,h₄,h₅⟩
  have h₀ : ∀ᶠ w : ℕ × ℕ in f.fuse, ∀ i z, centeredBudget C (b.name k w.1 w.2 ⟨d i,B (d i) z⟩) (A k) j w.1 w.2 := h₅
  have hs (i : Fin n) : ∀ᶠ w in f.fuse, let c := b.coef k (d i) w.1 w.2
      (∀ g u, c ((Free C).mirror H _ g u) = C.book.mirrorGroup _ g (c u)) ∧ (∀ u, c ((Free C).conj H _ u) = star (c u)) ∧
        c ((Free C).unit _) = C.refUnit _ := hH k (d i) (hv i)
  have hf (z : ℕ) := (cofin_fst f).eventually (eventually_ge_atTop z)
  refine ⟨m,j,h₁,h₂,h₃,h₄, (Order.fused f (fun w => ∀ i s, centeredBudget C
    (Extraction.Spin.token C.book (b.name k w.1 w.2 (v i)) s) (L*A k) j w.1 w.2)).1 ?_⟩
  filter_upwards [h₀,eventually_all.mpr hs,hf j,eventually_all.mpr (fun i => hf (C.ref (d i)))] with w hw hs hj hr i s
  have hh := applies (hs i).1 (hs i).2.1 (v i).2 s
  rw [← show (⟨(v i).1,(v i).2⟩ : (Free C).Tag) = v i from Sigma.eta _, ← hh]
  exact column_combination h (B (d i)) w.1 w.2 j k hj (hr i) _ _ (hA k) (hw i) _ (ht i s)

/-- Finite comparison estimates only on the indicated basis (plus separate
coefficient norm and H/real/unit receipts) produce the cutoff inputs of act. -/
theorem finite_of_basis [∀ d, Fintype (ι d)] {H : (Free C).RealSpin} (h : C.Makes) (hQ : 0 < Q)
    (hb : ∀ k d, ∃ A : ℝ, 0 ≤ A ∧ ∃ p₀ : ℕ, ∀ p ≥ p₀, ∀ᶠ j in atTop, ‖b.coef k d (f.mesh j) p‖ ≤ A)
    (hH : ∀ k d, d≤D → Sym b f H k d) (hC : BasisCenter b f B M D Q) (hr : RootCosts b f B M D Q) :
    FiniteCosts b f H M D Q := ⟨hb,hH,center_of_basis h hH hC,aligned_of_root h hr hQ⟩
end YM.Extra.WeakScaling
