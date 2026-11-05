import YM.AnalyticBridge.MARGINAL_MULTIPLIER_3B1D.Fields

/-!
Full pointwise jet / tag-window change compiler for a local Gaussian factor.
At actual exponential values (not paying exp of a derivative budget), growth
per differentiated slot only on the charts. One predicate on all bindings and
arguments before using the product; see `Sector`/client files for checks.
This does NOT differentiate the final flag indicators.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.MarginalMultiplier3b1d.Kernel
open Function Filter Lattice RG Wilson Next.SectorChange Pressure Push.SectorMeasure Precision
  FiniteMatrix Push.Local Next.Foundations
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {I J ρ : Type} [Fintype I] [Fintype J] [Fintype ρ]
    {P : Location f I J} {h h' : Kernel G c I J ρ} {q : Chi} {Z : ChartRatio G}
    {k : ℕ} {V : Config G c} {D : Directions G c → Prop} {t g d a b B C : ℝ}

def aperture (k : ℕ) (a t d C : ℝ) := compositionCost k ((t/d)*a)*C
def broken (k : ℕ) (a b t d C : ℝ) := aperture k a t d C*((1+k)*((t/d)*b))

private lemma rescale_link (e : Exposure S P h h' g t k D V B a b) (ht : 0 < t) (hd : 0 < d) (i : I) :
    Compare k D V ((d⁻¹:ℝ) • (h.stage g · i)) ((d⁻¹:ℝ) • (h'.stage g · i)) ((t/d)*a) ((t/d)*b) 1 := by
  have hx := (e.stage i).smul_const_left (t/d)
  rw [abs_of_pos (div_pos ht hd)] at hx
  simpa only [Pi.smul_apply, Pi.smul_def, smul_smul, show (t/d)*t⁻¹=d⁻¹ by field_simp] using hx

private lemma scaled_jets {i : I} (he : Compare k D V ((d⁻¹:ℝ) • (h.stage g · i)) ((d⁻¹:ℝ) • (h'.stage g · i)) ((t/d)*a) ((t/d)*b) 1)
    {φ : G.Color → ℝ} (hC : ∀ x y, Towers k φ φ x y C (C*‖x-y‖)) :
    Compare k D V (fun W => φ ((d⁻¹:ℝ) • h.stage g W i)) (fun W => φ ((d⁻¹:ℝ) • h'.stage g W i)) (aperture k a t d C) (broken k a b t d C) 1 := by
  have ht : ‖d⁻¹ • h.stage g V i - d⁻¹ • h'.stage g V i‖ ≤ (t/d)*b := he.swing.value
  have h := he.chain (hC ..)
  have h0 := zero_le_one.trans (compositionCost_one k he.west.nn)
  refine h.weaker le_rfl ?_ le_rfl
  rw [broken,aperture,mul_assoc (compositionCost ..)]; apply mul_le_mul_of_nonneg_left _ h0
  apply (add_le_add_left (mul_le_mul_of_nonneg_left ht ((hC 0 0).nn.1)) _).trans_eq
  ring

lemma chart_estimate (e : Exposure S P h h' g t k D V B a b) (ht : 0<t) (hC : GuardCost q Z k d C) :
    Compare k D V (h.chartLog q Z d g) (h'.chartLog q Z d g) (Fintype.card I*(aperture k a t d C*d^2)) (Fintype.card I*(broken k a b t d C*d^2)) 1 := by
  have he i := scaled_jets (rescale_link e ht hC.pos i) hC.log
  simp_rw [dilate,smul_inv_smul₀ hC.pos.ne'] at he
  apply Compare.univ _ zero_le_one; intro i
  exact (he i).weaker (le_of_eq (by rw [aperture,aperture,mul_assoc])) (le_of_eq (by unfold broken aperture; ring)) le_rfl

private lemma raise {F : Config G c → ℝ} (h : Bound k D V F C 1) (he : ‖F V‖ ≤ 1) : Bound k D V F 1 (1+C) := by
  have ht := h.nn
  have hh : 1≤1+C := le_add_of_nonneg_right ht
  refine ⟨h.smooth,zero_le_one,zero_le_one.trans hh,fun l hl hu => ?_⟩
  cases l with
  | nil => simpa [leftDerivs] using he
  | cons i l =>
    simpa only [one_mul] using (h.simple (i::l) hl hu).trans ((le_add_of_nonneg_left (by norm_num : (0:ℝ)≤1)).trans (le_self_pow₀ hh (List.cons_ne_nil i l |> fun e => (List.length_pos_iff_ne_nil.mpr e).ne')))

def door_err (I : Type) [Fintype I] (k : ℕ) (a b t d C : ℝ) := Fintype.card I*broken k a b t d C
def door_growth (I : Type) [Fintype I] (k : ℕ) (a t d C : ℝ) := Fintype.card I*(1+aperture k a t d C)
lemma doors_estimate (e : Exposure S P h h' g t k D V B a b) (ht : 0<t) (hC : GuardCost q Z k d C) :
    Compare k D V (doors q d ∘ h.stage g) (doors q d ∘ h'.stage g) 1 (door_err I k a b t d C) (door_growth I k a t d C) := by
  have he i := scaled_jets (rescale_link e ht hC.pos i) hC.base
  have hv (x : G.Color) : broad q 1 (d⁻¹ • x)=broad q d x := by rw [← broad_scale q hC.pos, one_mul,smul_inv_smul₀ hC.pos.ne']
  simp_rw [hv] at he
  have ht (x : G.Color) : ‖broad q d x‖ ≤ 1 := (Real.norm_of_nonneg (broad_range q x d).1).trans_le (broad_range q x d).2
  let A := aperture k a t d C
  let L := broken k a b t d C
  have H (i : I) : Compare k D V (fun W => broad q d (h.stage g W i)) (fun W => broad q d (h'.stage g W i)) 1 L (1+A) :=
    ⟨raise (he i).west (ht _),raise (he i).east (ht _), (he i).swing.weaker le_rfl (le_add_of_nonneg_right (he i).west.nn)⟩
  simpa [doors,Function.comp_def,door_growth,door_err] using Compare.prod Finset.univ (fun i _ => H i)

variable {M C' u v H α ε : ℝ} {R : Rep G f} {s w r o : Finset ℕ} {m n ℓ δ : ℕ → ℝ}
def choice (R : Rep G f) (w : Finset ℕ) (i : ℕ) := if i∈w then R.activities.E i else (0:Config G f → ℝ)

def Transfer (s w r : Finset ℕ) (R : Rep G f) (S : StepData c f) (P : Location f I J) (h h' : Kernel G c I J ρ) (k : ℕ) (V : Config G c) (m n : ℕ → ℝ) :=
    w ⊆ s ∧ r ⊆ s ∧ ∀ i∈s, Diagonals k R.p (R.activities.reg i).site (h.atLinks S P (coupling R.beta) V) (h'.atLinks S P (coupling R.beta) V)
      (choice R w i) (choice R r i) (m i) (n i)
def Freeze (o : Finset ℕ) (R : Rep G f) (S : StepData c f) (P : Location f I J) (h h' : Kernel G c I J ρ) (V : Config G c) (ℓ δ : ℕ → ℝ) :=
  ∀ i∈o, let u := h.heavy S P R i; let v := h'.heavy S P R i
    ‖u V‖ ≤ ℓ i ∧ ‖v V‖ ≤ ℓ i ∧ ‖u V-v V‖ ≤ δ i ∧ u ∘ increment V =ᶠ[𝓝 0] (fun _ => u V) ∧ v ∘ increment V =ᶠ[𝓝 0] (fun _ => v V)

private lemma subtotal (h : Kernel G c I J ρ) (S : StepData c f) (P : Location f I J) (R : Rep G f) {w s : Finset ℕ} (hw : w⊆s) (W : Config G c) :
    ∑ i ∈ w,h.light S P R i W = ∑ i ∈ s, (choice R w i ∘ h.atLinks S P (coupling R.beta)) W := by
  apply Eq.trans _ (Finset.sum_subset hw (by intros; simp [choice, *]))
  exact Finset.sum_congr rfl (fun i hi => by simp only [choice,if_pos hi,Function.comp_apply,light])

def lamp (k : ℕ) (u v : ℝ) (s : Finset ℕ) (m n : ℕ → ℝ) := ∑ i∈s, (n i+k*m i*u*((1+k)*v))
lemma light_estimate (e : Exposure S P h h' (coupling R.beta) R.p.threshold k D V B a b) (hc : Changes G k C) (hp : Polar k M) (hs : Transfer s w r R S P h h' k V m n) :
    Compare k D V (fun W => ∑ i ∈ w, h.light S P R i W) (fun W => ∑ i ∈ r,h'.light S P R i W) (fieldCost G k B a C M * ∑ i∈s,m i)
      (fieldCost G k B a C M * lamp k (pivotCost G k B a C) b s m n) 1 := by
  simp_rw [subtotal h S P R hs.1,subtotal h' S P R hs.2.1,lamp, Finset.mul_sum]
  exact Compare.sum s (fun i hi => through S P e hc hp (hs.2.2 i hi)) zero_le_one

def hard_err (o : Finset ℕ) (ℓ δ : ℕ → ℝ) := ∑ i∈o, δ i * ∏ j∈o.erase i,ℓ j
lemma hard_estimate (e : Freeze o R S P h h' V ℓ δ) : Compare k D V (fun W => ∏ j∈o, h.heavy S P R j W)
    (fun W => ∏ j∈o, h'.heavy S P R j W) (∏ i∈o,ℓ i) (hard_err o ℓ δ) 0 := by
  rw [hard_err,show (0:ℝ)=o.card*0 from (mul_zero _).symm]
  refine Compare.prod o fun i hi => ?_
  obtain ⟨hm,hn,hd,he,ht⟩ := e i hi
  exact (Compare.const _ _ hm hn hd le_rfl).congr he ht

def expenseCost (G : Gauge) (I J ρ : Type) [Fintype I] [Fintype J] [Fintype ρ] (k : ℕ) (t p d C C' M H α a B : ℝ)
    (s : Finset ℕ) (m : ℕ → ℝ) := ledgerCost G I J k α H p + correctionCost G I ρ k α H + Fintype.card I*(aperture k a t d C' * d^2) + fieldCost G k B a C M * ∑ i∈s,m i
def expenseErr (G : Gauge) (I J ρ : Type) [Fintype I] [Fintype J] [Fintype ρ] (k : ℕ) (t d C C' M H α ε a b B : ℝ)
    (s : Finset ℕ) (m n : ℕ → ℝ) := ledgerReaction G I J k α H * ε + correctionReaction G I ρ k α H * ε + Fintype.card I*(broken k a b t d C' * d^2) + fieldCost G k B a C M * lamp k (pivotCost G k B a C) b s m n

/-- Joint two-sheet input at a single base point and *same* parameters,
prices, reads on each side, through all orders. Ground must be certified for
the *actual* full/patched marginal matrices on both sheets even if comparing
a tag and nearby window. Transfer takes fine-scale diagonal tests. Freeze has
only genuine local held-constant factors (no fake differentiation through
unknown K). Occurrences and selection predicates are not differentiated. -/
structure Certified (S : StepData c f) (P : Location f I J) (h h' : Kernel G c I J ρ) (R : Rep G f) (q : Chi) (Z : ChartRatio G) (d : ℝ)
    (k : ℕ) (D : Directions G c → Prop) (V : Config G c) (s w r o : Finset ℕ) (M C C' H α ε B a b : ℝ) (m n ℓ δ : ℕ → ℝ) : Prop where
  polar : Polar k M
  changes : Changes G k C
  chart : GuardCost q Z k d C'
  ground_w : Ground h V H
  ground_e : Ground h' V H
  matrices : Matrices h h' k D V α ε
  fields : Exposure S P h h' (coupling R.beta) R.p.threshold k D V B a b
  transfer : Transfer s w r R S P h h' k V m n
  freeze : Freeze o R S P h h' V ℓ δ

lemma expense_estimate (e : Certified S P h h' R q Z d k D V s w r o M C C' H α ε B a b m n ℓ δ) :
    Compare k D V (h.expense S P R q Z d w) (h'.expense S P R q Z d r) (expenseCost G I J ρ k R.p.threshold (spare Z R.beta) d C C' M H α a B s m)
      (expenseErr G I J ρ k R.p.threshold d C C' M H α ε a b B s m n) 1 :=
  (((ledger_estimate e.matrices e.ground_w e.ground_e (spare Z R.beta)).add (correction_estimate e.matrices e.ground_w e.ground_e)).add
    (chart_estimate e.fields R.p.threshold_pos e.chart)).sub (light_estimate e.fields e.changes e.polar e.transfer)

/-- Ordered local multiplier derivative and perturbation price simultaneously
(no smallness of the whole multiplier assumed). The exponential only contains
base-point valuations **before** taking jets. All other prices polynomial at
fixed k incl dependence on the alphabet cardinalities (apart from actual
product of the undifferentiated absolute hard prices). -/
theorem assembled (e : Certified S P h h' R q Z d k D V s w r o M C C' H α ε B a b m n ℓ δ) (K : ℝ)
    (hK : h.expense S P R q Z d w V ≤ K) (hK' : h'.expense S P R q Z d r V ≤ K) :
    let t := R.p.threshold; let p := spare Z R.beta
    let x := expenseCost G I J ρ k t p d C C' M H α a B s m; let y := expenseErr G I J ρ k t d C C' M H α ε a b B s m n
    let Q := compositionCost k x * Real.exp K
    let F := ∏ i∈o,ℓ i
    Compare k D V (h.multiplier S P R q Z d w o) (h'.multiplier S P R q Z d r o)
      (F*Q) ((door_err I k a b t d C'*F + hard_err o ℓ δ + F*((1+k)*y))*Q) (door_growth I k a t d C'+1) := by
  intro t p x y Q F
  have hE := (expense_estimate e).exp hK hK'
  have ht := ((doors_estimate e.fields R.p.threshold_pos e.chart).mul (hard_estimate e.freeze)).mul hE
  refine ht.weaker (by rw [one_mul]) (le_of_eq ?_) (by rw [add_zero])
  change (_*F+1*_)*Q+(1*F)*(compositionCost k x * ((1+k)*Real.exp K*y)) = _
  unfold Q; ring

/-- Also a guard kills the full local factor (all formal ordered derivatives
there are true zero jets even if the other factors aren't smooth at all).
No use with `≤`: must prove the estimates at equality when needed. -/
lemma blank {h : Kernel G c I J ρ} (S : StepData c f) (P : Location f I J) (R : Rep G f) (q : Chi) (Z : ChartRatio G) {d : ℝ}
    {k : ℕ} {D : Directions G c → Prop} {V : Config G c} (w o : Finset ℕ) {i : I}
    (hd : 0<d) (hf : ContinuousAt (fun y => h.stage (coupling R.beta) (increment V y) i) 0)
    (he : 2*d < ‖h.stage (coupling R.beta) V i‖) : Bound k D V (h.multiplier S P R q Z d w o) 0 0 := by
  rw [← Work.G07.at_zero_increment V] at he
  apply (Bound.const (0:ℝ) (by simp) le_rfl).congr
  filter_upwards [hf.norm.eventually (lt_mem_nhds he)] with y hy
  simp only [Function.comp_apply,multiplier,show doors q d (h.stage (coupling R.beta) (increment V y)) = 0 from
    not_not.mp (fun hv => lt_asymm hy (broad_span q hd _ (every_door q hv i))),zero_mul]
end YM.AnalyticBridge.MarginalMultiplier3b1d.Kernel
