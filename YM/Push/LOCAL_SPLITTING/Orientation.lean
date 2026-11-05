import YM.Push.LOCAL_SPLITTING.Mixed
import YM.Work.F03.Flat
import YM.Work.H03

/-!
# Signed placement transport of supports, pre-mask extensions and charges

Ordered derivatives pay a displayed constant *before* the torus size. Stencil and
cover cost of the full transformed support (not the smallest support of the value).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Local
open Function Lattice Wilson RG Source Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff

variable {G : Gauge} {n : Side}

def turnSites (s : Signed) (b : Site n) : Equiv.Perm (Site n) := s.actEquiv.toEquiv.trans (Equiv.addRight b)

@[simp] theorem turn_sep (s : Signed) (b x y : Site n) :
    separation (turnSites s b x) (turnSites s b y) = separation x y := by simp [show ⇑(turnSites s b) = affine s b from rfl,affine]

private theorem end_turn (s : Signed) (b x : Site n) (i : Axis) :
    affine s b (x+step i) = affine s b x + ((posDir i).rotate s).vec := by
  rw [Lattice.Step.vec_rotate, Lattice.Step.vec_pos, affine,affine,s.act_add, add_right_comm]

theorem agrees_pull (s : Signed) (b : Site n) {K : Type*} [Group K] {U V : Links (Per n) K} {X : Support n}
    (h : Agrees (X.image (turnSites s b)) U V) : Agrees X (pull s b U) (pull s b V) := by
  rintro ⟨x,i⟩ hx hy
  have hb : affine s b x ∈ X.image (turnSites s b) := Finset.mem_image_of_mem (turnSites s b) (a:=x) hx
  have he : affine s b (x+step i) ∈ X.image (turnSites s b) := Finset.mem_image_of_mem (turnSites s b) (a:=x+step i) hy
  rw [end_turn] at he
  unfold pull; cases hq : ((posDir i).rotate s) with | mk a t =>
  rw [hq] at he; cases t
  · exact h (affine s b x,a) hb he
  have hv : affine s b x-step a ∈ X.image (turnSites s b) := by simpa only [show (⟨a,true⟩ : Lattice.Step)=negDir a from rfl, Lattice.Step.vec_neg, sub_eq_add_neg] using he
  exact congr_arg Inv.inv (h (affine s b x-step a,a) hv (by change affine s b x-step a+step a ∈ X.image _; rw [sub_add_cancel]; exact hb))

theorem uses_pull {Z : Sort*} {X : Support n} {f : Config G n → Z} {t : ℝ}
    (h : UsesFinal t X f) (s : Signed) (b : Site n) : UsesFinal t (X.image (turnSites s b)) (fun U => f (pull s b U)) := by
  intro U V huv hx; refine h _ _ (agrees_pull s b huv) (Finset.image_injective (turnSites s b).injective ?_)
  rwa [Finset.image_inter _ _ (turnSites s b).injective, Finset.image_inter _ _ (turnSites s b).injective,
    show ⇑(turnSites s b) = affine s b from rfl, Work.H03.flags_send, Work.H03.flags_send]

theorem pull_gauge {K : Type*} [Group K] (s : Signed) (b : Site n) (U : Links (Per n) K) (g : Site n → K) :
    pull s b (gauge g U) = gauge (g ∘ turnSites s b) (pull s b U) := by
  funext e
  simp only [pull,Lattice.Step.gauge_read, ← end_turn]; rfl

theorem invariant_pull {Z : Type*} {f : Config G n → Z}
    (h : GaugeInvariant f) (s : Signed) (b : Site n) : GaugeInvariant (f ∘ pull s b) := fun g U => by
  simp only [comp_apply,pull_gauge,h _ _]

theorem healthy_pull (s : Signed) (b : Site n) (t : ℝ) (X : Support n) (U : Config G n) :
    Healthy t (X.image (turnSites s b)) U ↔ Healthy t X (pull s b U) := by
  unfold Healthy; rw [← Work.H03.flags_send s b]; exact Finset.disjoint_image (turnSites s b).injective

theorem nonwrapping_turn (s : Signed) (b o : Site n) (X : Support n) :
    Nonwrapping (X.image (turnSites s b)) (turnSites s b o) ↔ Nonwrapping X o := by simp [Nonwrapping]

section Mass
variable (r : Equiv.Perm (Site n)) (hr : ∀ i j, separation (r i) (r j) = separation i j)
include hr

theorem halo_map (b : ℕ) (A : Support n) : halo b (A.image r) = (halo b A).image r := by
  ext i; obtain ⟨i,rfl⟩ := r.surjective i
  simp [halo_spec,hr]

theorem cover_map (b : ℕ) (X : Support n) : coverNumber b (X.image r) = coverNumber b X := by
  have he (r : Equiv.Perm (Site n)) (hr : ∀ i j, separation (r i) (r j) = separation i j) (X) :
      coverNumber b (X.image r) ≤ coverNumber b X := by
    obtain ⟨D,⟨h1,h2⟩,hD⟩ := coverNumber_realized b X
    have ht : covers b (X.image r) (D.image r) := by
      unfold covers; rw [halo_map r hr]; refine ⟨Finset.image_subset_image h1,?_⟩
      simp only [Finset.forall_mem_image]; intro i hi j hj
      refine (h2 _ hi _ hj).lift (f:=r) ?_
      rintro x y ⟨hx,hy,h⟩; exact ⟨Finset.mem_image_of_mem _ hx, Finset.mem_image_of_mem _ hy, (hr ..).trans_le h⟩
    exact (Corona.list_cost _ ht).trans ((Finset.card_image_le).trans_eq hD)
  apply le_antisymm (he r hr X)
  simpa [← Finset.image_comp] using he r.symm (fun i j => by simpa using (hr (r.symm i) (r.symm j)).symm) (X.image r)
end Mass

section Jets
private def movedDirs (s : Signed) (b : Site n) (A : Directions G n) : LR G n :=
  ((fun e => if s.flip e.2 then 0 else A (affine s b e.1, s.perm e.2)),
    fun e => if s.flip e.2 then -A (affine s b e.1-step (s.perm e.2), s.perm e.2) else 0)

private theorem pull_increment (s : Signed) (b : Site n) (U : Config G n) (A : Directions G n) (t : ℝ) :
    pull s b (increment U (t • A)) = mix (pull s b U) (t • movedDirs s b A) := by
  ext i
  simp only [pull,Lattice.Step.rotate, Lattice.Step.read,Lattice.Step.used,posDir,Bool.false_xor, mix, increment, movedDirs]
  split <;> simp [*,Work.F03.exp_neg_color]

private theorem pull_jets {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (s : Signed) (b : Site n) (U : Config G n) (f : Config G n → Y) (l : List (Directions G n)) :
    leftDerivs (f ∘ pull s b) l U = mixJets f (l.map (movedDirs s b)) (pull s b U) := by
  induction l generalizing U with
  | nil => rfl
  | cons A l ih => simp [mixJets,leftDerivs,ih,pull_increment]

theorem chart_pull {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (s : Signed) (b : Site n) {U : Config G n} {f : Config G n → Y} {k : ℕ}
    (hf : Chart k f (pull s b U)) : Chart k (f ∘ pull s b) U := by
  apply chart_comp (x:=(0 : Directions G n)) (W:=fun v => pull s b (increment U v)) (by simpa [Work.G07.at_zero_increment] using hf)
  intro l
  simp only [pull, Lattice.Step.read]; split
  · simp only [G.mat_inv,increment,G.mat_mul]
    exact ((starL' ℝ : G.Mat ≃L[ℝ] G.Mat).contDiff.comp ((G.exp_jet.comp (contDiff_apply ..)).mul contDiff_const)).contDiffAt
  exact ((G.exp_jet.comp (contDiff_apply ..)).mul contDiff_const).contDiffAt

private theorem dir_price (B : BudgetPoint) (s : Signed) (b o : Site n) (V : Config G n) (p : Directions G n)
    (h : B.dirBound (turnSites s b o) p) :
    let D (A : Directions G n) := ∀ l, ‖A l‖ ≤ (2:ℝ)^B.power * (B.threshold * (1+(separation l.1 o : ℝ))^B.power)
    D (movedDirs s b p).1 ∧ D (rotateRight V (movedDirs s b p).2) := by
  dsimp only
  constructor
  · intro l
    dsimp only [movedDirs]; split
    · rw [norm_zero]; positivity [B.threshold_pos]
    have he := h (turnSites s b l.1,s.perm l.2)
    simp only [turn_sep] at he; exact he.trans (le_mul_of_one_le_left (by positivity [B.threshold_pos]) (one_le_pow₀ (by norm_num)))
  rintro ⟨x,i⟩; rw [rotateRight, G.norm_adjoint]; dsimp only [movedDirs]; split
  · rw [norm_neg]
    let q := turnSites s b x-step (s.perm i)
    have h1 : separation q (turnSites s b o) ≤ 1+separation x o := by
      apply (separation_triangle q (turnSites s b x) _).trans
      rw [turn_sep, separation, show q - turnSites s b x = - step (s.perm i) by dsimp [q]; abel, pdist_neg]
      exact Nat.add_le_add_right (pdist_step _) _
    refine (h (q,s.perm i)).trans ?_
    rw [mul_left_comm (2^B.power), ← mul_pow]; apply mul_le_mul_of_nonneg_left _ B.threshold_pos.le
    apply pow_le_pow_left₀ (by positivity)
    change (1:ℝ)+separation q (turnSites s b o) ≤ 2*(1+(separation x o : ℝ))
    exact_mod_cast (show 1+separation q (turnSites s b o) ≤ 2*(1+separation x o) by omega)
  rw [norm_zero]; positivity [B.threshold_pos]

private theorem sum_price {ι Y : Type*} [NormedAddCommGroup Y] (l : List ι) (f : ι → Y) {c : ℝ} (hf : ∀ i∈l, ‖f i‖ ≤ c) :
    ‖(l.map f).sum‖ ≤ (l.length : ℝ)*c := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.length_cons,List.map_cons,List.sum_cons,Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm (_ * c) c]
    exact (norm_add_le ..).trans (add_le_add (hf i (by simp)) (ih fun j hj => hf j (by simp [hj])))

variable {B : BudgetPoint} {X : Support n} {f : Config G n → ℂ} {o : Site n} {a : ℝ}

theorem regular_pull (h : B.Regular X f) (s : Signed) (b : Site n) : B.Regular (X.image (turnSites s b)) (f ∘ pull s b) := by
  have ht (U) (hU : Healthy B.threshold (X.image (turnSites s b)) U) : Chart B.order (f ∘ pull s b) U :=
    chart_pull s b (h.smooth _ ((healthy_pull ..).mp hU))
  exact ⟨fun _ _ hu => h.sites _ _ (agrees_pull s b hu), h.borel.comp (continuous_pull ..).measurable, invariant_pull h.symmetry s b, ht,
    fun U hu A _ hl => left_has A hl (ht U hu)⟩

/-- Universal finite-budget factor including the negative-link endpoint shift
and all terms of the ordered-derivative reversal. -/
def turnCost (k P : ℕ) := ((2:ℝ)*2^P)^k

theorem bound_pull (h : B.Regular X f) (hc : B.supBounds o X f a) (s : Signed) (b : Site n) :
    B.supBounds (turnSites s b o) (X.image (turnSites s b)) (f ∘ pull s b) (turnCost B.order B.power*a) := by
  let r := (2:ℝ)^B.power
  refine ⟨mul_nonneg (pow_nonneg (by positivity) _) hc.1, fun U hu l hl hD => ?_⟩
  let V := pull s b U
  have hv : Healthy B.threshold X V := (healthy_pull ..).mp hu
  let Q := l.map (movedDirs s b)
  let D (A : Directions G n) := ∀ e, ‖A e‖ ≤ r*(B.threshold * (1+(separation e.1 o : ℝ))^B.power)
  have he := convert_mem V D Q (by simp only [Q,List.forall_mem_map]; exact fun p hp => dir_price B s b o V p (hD p hp))
  have hj (q) (hq : q∈convertOrder V Q) : ‖leftDerivs f q V‖ ≤ r^l.length*a := by
    have heq : q.length = l.length := (he q hq).1.trans (List.length_map _)
    rw [← heq]; exact bound_rescale_dirs hc h V hv q (heq.trans_le hl) r (by positivity) (he q hq).2
  have hs : ∀ p∈Q, ∀ q∈Q, ∀ i, p.1 i = 0 ∨ q.2 i = 0 := by
    simp only [Q,List.forall_mem_map]; intro p _ q _ i; dsimp only [movedDirs]; split <;> simp_all
  rw [pull_jets s b, mix_convert V Q f hs (h.smooth _ hv) ((List.length_map _).trans_le hl)]
  apply (sum_price (convertOrder V Q) _ hj).trans
  simp only [convert_length,List.length_map,Q,Nat.cast_pow,Nat.cast_ofNat,← mul_assoc, r,← mul_pow,turnCost]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ (by norm_num))) hl) hc.1
end Jets
end YM.Push.Local
