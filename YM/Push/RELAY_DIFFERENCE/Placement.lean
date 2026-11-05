import YM.Bid.Station
import YM.Push.RELAY_DIFFERENCE.Rates
import YM.Work.B04

/-!
# Prove rents from centered array bounds 

This works for any *literal* cutoff cylinder: no representation has to be
run at the bracketing offsets. One method uses the centers of cells of a
FINER link tiling for the bracketing. Apply the seam inequality a second
time at those aligned cells, on the copy estimates with identity in
unused cells and the right orientations. Thus only need RG array bounds for
full CENTERED copies at the finer side. And only the one centered grid at the
true hierarchy origin (use symmetry of actual Wilson law BEFORE invoking RG).
No assumption of calibration at other origins, not even a rule for acting on
the labels of the discrepant cylinder.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.RelayDifference
open Function Set Filter MeasureTheory Extraction Extraction.Lease Wilson Lattice Cells
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {n : Side} {G : Gauge}

/-- Conjugate coefficient and cylinder together. -/
def hand (b : Bool) (z : ℂ) := if b then star z else z
lemma twice (b c : Bool) (z : ℂ) : hand b (hand c z) = hand (b.xor c) z := by
  cases b <;> cases c <;> simp [hand]

def oriented (F : Config G n → ℂ) (b : Bool) (s : Signed) (x : Site n) (U : Config G n) :=
  hand b (F (pull s x U))

open scoped Classical in
/-- In particular reversal uses the *shifted* inverse bond. -/
lemma copied (F : Config G n → ℂ) (b : Bool) (s : Signed) (x : Site n) (T : Tiling n) (i : T.Cell) :
    T.copy i (oriented F b s x) = oriented F ((decide (T.hand i)).xor b) (T.omega i * s) (T.copyMap i x) := by
  funext U
  unfold Tiling.copy oriented
  rw [pull_pull]
  by_cases hp : T.hand i
  · simpa only [hp, hand, Tiling.copyMap, ↓reduceIte, decide_true] using twice true b (F (pull (T.omega i * s) (T.copyMap i x) U))
  simpa only [hp, hand, Tiling.copyMap, ↓reduceIte, decide_false,Bool.false_eq_true] using twice false b (F (pull (T.omega i * s) (T.copyMap i x) U))

@[simp] lemma oriented_zero (F : Config G n → ℂ) : oriented F false 1 0 = F := by
  funext U; simp [oriented, hand]

variable {k N p : ℕ} {S : Schedule}

section Center
local notation "Λ" => S.side N p

/-- Orientations in either tiling never permute the axes. -/
def diag (s : Signed) := s.perm = Equiv.refl _

lemma diag_apply (s : Signed) (h : diag s) {R : Type*} [AddGroup R] (v : Four R) (i : Axis) :
    s.act v i = if s.flip i then - v i else v i := by
  rw [← s.act_at v i]; rw [show s.perm = Equiv.refl _ from h]; rfl
lemma diag_mul {s t : Signed} (hs : diag s) (ht : diag t) : diag (s*t) := by
  unfold diag at *
  rw [Signed.mul_perm, hs,ht]; rfl
lemma diag_comm {s t : Signed} (hs : diag s) (ht : diag t) : t*s=s*t := by
  unfold diag at *
  apply Signed.ext
  · rw [Signed.mul_perm, Signed.mul_perm, hs, ht]
  funext i; rw [Signed.mul_flip, Signed.mul_flip, hs, ht]; exact Bool.xor_comm ..
lemma diag_inv {s : Signed} (hs : diag s) : diag s⁻¹ := by
  unfold diag at *; rw [Signed.inv_perm, hs]; rfl

private lemma maps_center (h : k ≤ N) (s : Signed) (hd : diag s) (x : Site Λ) :
    MapsTo (affine s x) ((center S p h 0).chamber 0) ((center S p h x).chamber 0) := by
  intro y hy i
  let T := center S p h 0
  let d := T.side.val
  let j := d/2
  have he (y : Site Λ) : (center S p h y).starts 0 i = y i - (j:Per Λ) := (center S p h y).starts_zero ▸ rfl
  have ht : (y i + (j:Per Λ)).val < d := by
    specialize hy i; rw [he] at hy
    change (y i - (0 - (j:Per Λ))).val < d at hy
    simpa only [zero_sub, sub_neg_eq_add] using hy
  let b : Per Λ := y i + (j:Per Λ)
  rw [he]; change (s.act y i + x i - (x i - (j:Per Λ))).val < d
  rw [show s.act y i + x i - (x i - (j:Per Λ))=s.act y i + (j:Per Λ) by abel, diag_apply s hd]
  split
  · have hc : b.val < d := ht
    have hh : Odd d := S.toDepth_odd h p
    have hj : j+j+1=d := by obtain ⟨v,hv⟩ := hh; unfold j; omega
    have hm : -y i + (j:Per Λ) = ((↑(j+j-b.val):ℕ):Per Λ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_zmod_val]; unfold b; abel
    rw [hm, ZMod.val_natCast_of_lt]
    · omega
    have hp : d < (S.side N p).val := T.narrow
    omega
  exact ht

lemma center_interior (h : k ≤ N) (s : Signed) (hd : diag s) (χ : Bool) (x : Site Λ)
    {F : Config G Λ → ℂ} (ht : Interior ((center S p h 0).chamber 0) F) :
    Interior ((center S p h x).chamber 0) (oriented F χ s x) := by
  have he := ht.unchanged s x (maps_center h s hd x)
  cases χ
  · exact he
  exact he.real

private lemma rotate_cells (T : Tiling n) (s : Signed) (h : diag s) (i : T.Cell) : T.omega (s.act i)=T.omega i := by
  refine Signed.ext rfl ?_
  funext a
  dsimp only [Tiling.omega]
  rw [diag_apply s h]
  cases s.flip a <;> simp

private lemma grid_copy (h : k ≤ N) (x : Site Λ) (F : Config G Λ → ℂ) (χ : Bool) (s : Signed) (hd : diag s)
    (i : Site (S.side k p)) (U : Config G Λ) :
    let Y := center S p h 0
    let T := center S p h x
    T.copy i (oriented F χ s x) U = hand χ (Y.copy (s⁻¹.act i) F (pull s x U)) := by
  classical
  intro Y T
  have ho : Y.omega (s⁻¹.act i)=T.omega i := rotate_cells Y s⁻¹ (diag_inv hd) i
  have hc : Y.translateBy (s⁻¹.act i) = Y.copyMap (s⁻¹.act i) 0 := by simp only [Tiling.copyMap, affine,Signed.act_zero,zero_add]
  have hp : affine s x (Y.translateBy (s⁻¹.act i)) = T.copyMap i x := by
    rw [hc, show Y.copyMap _ _=_ from copy_home S h _ _, show T.copyMap _ _=_ from copy_home S h _ _]
    -- don't let the Cell notation obscure the scale
    dsimp only [Y,T]
    change affine s x (0+(S.toDepth h p).embed (s⁻¹.act (R:=Per (S.side k p)) i)) = x+_
    rw [affine, zero_add, ← Ratio.signed, Signed.act_inv]; abel
  have ht : Y.hand (s⁻¹.act i) = T.hand i := by unfold Tiling.hand; rw [ho]
  rw [copied]
  unfold Tiling.copy oriented
  rw [pull_pull, hp, ho, ht, diag_comm hd (show diag (T.omega i) from rfl)]
  by_cases he : T.hand i <;> cases χ <;> simp [he,hand]

/-- Centered root invariant. Centered link cells of odd side, coordinate
signs and optional ordinary conjugation. Proof BEFORE any RG comparison. -/
theorem center_price (h : k ≤ N) (x : Site Λ) (F : Config G Λ → ℂ) (χ : Bool) (s : Signed) (hd : diag s)
    (hi : Interior ((center S p h 0).chamber 0) F) (β : ℝ) :
    (center S p h x).rootTest β (oriented F χ s x)=(center S p h 0).rootTest β F := by
  classical
  let T := center S p h x
  let Y := center S p h 0
  let V := Site (S.side k p)
  let B := Y.fullAt fun _ => F
  have ht : T.fullAt (fun _ => oriented F χ s x) = hand χ ∘ (B ∘ pull s x) := by
    funext U
    unfold Tiling.fullAt
    have ho (i : V) : T.copy i _ U = hand χ (Y.copy (s⁻¹.act i) F (pull s x U)) := grid_copy h x F χ s hd i U
    simp_rw [ho]
    have he : ∏ i : V, hand χ (Y.copy (s⁻¹.act i) F (pull s x U)) = ∏ i : V, hand χ (Y.copy i F (pull s x U)) :=
      Equiv.prod_comp (show V ≃ V from s⁻¹.actEquiv.toEquiv) (fun i => hand χ (Y.copy i F (pull s x U)))
    change (∏ i : V, hand χ (Y.copy (s⁻¹.act i) F (pull s x U))) = _
    rw [he]; dsimp only [comp_apply, B, Tiling.fullAt]; cases χ <;> simp [hand] <;> rfl
  change ‖moment β (T.fullAt _)‖ ^ (Fintype.card V : ℝ)⁻¹ = ‖moment β B‖ ^ (Fintype.card V : ℝ)⁻¹
  rw [ht]
  have hv : moment β (B ∘ pull s x) = moment β B :=
    moment_pull _ _ _ _ (Y.manyIntegral β _ (fun _ => hi))
  have he (f : Config G Λ → ℂ) : ‖moment β (hand χ ∘ f)‖ = ‖moment β f‖ := by
    cases χ
    · rfl
    change ‖∫ U, star (f U) ∂law G Λ β‖ = _
    simp_rw [Complex.star_def, integral_conj]; rw [Complex.norm_conj]; rfl
  rw [he,hv]
end Center

/-! ### Passing to every offset with identical coefficients -/

def literal (F : Site n → Config G n → ℂ) := ∀ o b : Site n, F (o+b) = (F o) ∘ translate b

lemma unorient {F : Site n → Config G n → ℂ} (h : literal F) (o : Site n) :
    F o = oriented (F 0) false 1 o := by
  have he := h 0 o
  funext U
  simpa [oriented, hand, pull_one] using congr_fun he U

section Offset
local notation "Λ" => S.side N p

private lemma inside_margin (h : k ≤ N) (T : Tiling Λ) {x : Site Λ} (he : x∈ T.margin 0 (2*Cells.span S h p)) :
    (center S p h x).chamber 0 ⊆ T.chamber 0 := by
  let Y := center S p h x
  intro u hu
  have hh := Y.extent hu (base_point S h x)
  let w := lift (u-x)
  have hz : wrap Λ w + x = u := by rw [show wrap Λ w = u-x from wrap_lift .., sub_add_cancel]
  have hp : ∀ i : Axis, (w i).natAbs < 2*Cells.span S h p := by
    intro i
    refine lt_of_le_of_lt ((component_le (u-x) i).trans hh) ?_
    have ht := Y.side.property
    exact lt_mul_of_one_lt_left ht (by norm_num)
  exact hz ▸ T.fits_stencil he hp

/-- Bound at a bracketing corner (which is itself among the possibly many
centers of a finer grid). -/
theorem corner_root (h : k ≤ N) (T : Tiling Λ) (β A : ℝ) (ht : Cells.span S h p ∣ T.side.val)
    {F : Site Λ → Config G Λ → ℂ} (hs : literal F) (hβ : Seam G Λ β) (ha : Interior ((center S p h 0).chamber 0) (F 0))
    (hb : (center S p h 0).rootTest β (F 0) ≤ A) {o : Site Λ} (he : o ∈ T.chamber 0)
    (hh : o ∈ onCenters S h (homeFor S h T)) : T.rootTest β (F o) ≤ A := by
  classical
  let x := homeFor S h T
  let Y := center S p h x
  choose j hj using fun i => turns S h T hh ht i
  -- The full array of the larger cells is planted in *distinct* Y-cells.
  have hj' (i : T.Cell) : T.copyMap i o = Y.copyMap (j i) x := hj i
  have hw : Injective j := by
    intro u v huv
    have hu := T.enumerate u he
    have hv := T.enumerate v he
    rw [hj',huv,←hj'] at hu
    exact (T.which_chamber hu).symm.trans (T.which_chamber hv)
  let s (i : T.Cell) := (Y.omega (j i))⁻¹ * (T.omega i)
  let b (i : T.Cell) := (decide (Y.hand (j i))).xor (decide (T.hand i))
  let f (i) := oriented (F 0) (b i) (s i) x
  have hd i : diag (s i) := diag_mul (diag_inv (show diag (Y.omega (j i)) from rfl)) (show diag (T.omega i) from rfl)
  have hf i : Interior (Y.chamber 0) (f i) := center_interior h _ (hd i) _ x ha
  have hc i : Y.rootTest β (f i) ≤ A := le_trans (center_price h _ _ _ _ (hd i) ha β).le hb
  have hm (i : T.Cell) : Y.copy (j i) (f i)=T.copy i (F o) := by
    -- work at the same parameters before and after any copies
    dsimp only [f]
    conv_rhs => arg 3; rw [unorient hs o]
    rw [copied,copied,←hj']
    dsimp only [s]; rw [mul_one,mul_inv_cancel_left]
    cases hi : decide (T.hand i) <;> cases he : decide (Y.hand (j i)) <;> simp [b,hi,he]
  have hv := (Y.planted hβ j hw f hf).trans
    (Finset.prod_le_prod (fun i _ => Y.root_nonneg β _) fun i _ => hc i)
  simp only [hm,Finset.prod_const,Finset.card_univ] at hv
  have hA : 0 ≤ A := le_trans (Y.root_nonneg ..) (hc 0)
  apply le_of_pow_le_pow_left₀ T.cells_positive.ne' hA
  rw [T.powering]; exact hv

/-- Quantitative price at all offsets using just ONE finer centered
comparison. `k` is the finer grid level. The coarser cell tiling may be
either seam type. `Interior` of F at its center placement and translation
suffices; microscopic supports may even vary with the cutoff. -/
theorem offset (h : k ≤ N) (T : Tiling Λ) (β A : ℝ) (ht : Cells.span S h p ∣ T.side.val)
    {F : Site Λ → Config G Λ → ℂ} (hs : literal F) (hβ : Seam G Λ β) (ha : Interior ((center S p h 0).chamber 0) (F 0))
    (hb : (center S p h 0).rootTest β (F 0) ≤ A) {o : Site Λ} (he : o ∈ T.margin 0 (3*Cells.span S h p)) :
    Interior (T.chamber 0) (F o) ∧ T.rootTest β (F o) ≤ A := by
  classical
  let d := Cells.span S h p
  have inside (x : Site Λ) (he : x∈T.margin 0 (2*d)) : Interior (T.chamber 0) (F x) := by
    rw [unorient hs x]
    exact (center_interior h 1 (show diag 1 from rfl) false _ ha).enlarges (inside_margin h T he)
  refine ⟨inside _ (Lease.fewer T 0 (by change 2*d ≤ 3*d; omega) he),?_⟩
  choose v j hj hv hr hz hx hg ha' using fun i : Axis => bracket S h T o he i
  let Q (w : Axis → ℕ) i := v i (w i) i
  have ht' w (hw : ∀ i, w i ≤ d) : Q w∈T.margin 0 (2*d) := by
    refine ⟨fun a => (hr a _ (hw a)).1 a,?_⟩
    intro i; exact (hr i _ (hw i)).2 i
  have hp (p : Axis → ℕ) (i : Axis) (l : ℕ) (hl : l+1 ≤ d) : Q (update p i (l+1)) = Q (update p i l) + step i := by
    funext b; by_cases he : b=i <;> simp [Q,he,hz i l hl]
  -- Induct as in Around.interior_from. No nonvanishing condition (use pathway).
  let W (q : Axis → ℕ) := T.rootTest β (F (Q q))
  have hb (D : Finset Axis) (w : Axis → ℕ) (hw : ∀ i, w i ≤ d) (hR : ∀ i∉D, w i=0 ∨ w i=d) : W w ≤ A := by
    induction D using Finset.induction_on generalizing w with
    | empty =>
      refine corner_root h T β _ ht hs hβ ha hb (ht' w hw).1 ?_
      rw [belongs]; intro i
      rcases hR i (by simp) with e|e <;> unfold Q <;> rw [e]
      exacts [hg i, ha' i]
    | @insert i D hi ih =>
      let R (x) := update w i x
      have HH (x) (h : x ≤ d) : ∀ k, R x k ≤ d := fun k => by by_cases he:k=i <;> simp [R,he,hw,h]
      have he (x : ℕ) (h : x=0 ∨ x=d) (t) (ht:t∉D) : R x t=0 ∨ R x t=d := by
        by_cases hf:t=i; subst t;simpa [R]
        simpa [R,hf] using hR t (by simp [hf,ht])
      have hx := T.pathway β hβ (fun x => F (Q (R x))) d i (fun x hx => inside _ (ht' _ (HH _ hx)))
        (fun x hx => by unfold R; rw [hp w i x hx]; exact hs ..) A
        (ih _ (HH _ (Nat.zero_le _)) (he _ (Or.inl rfl))) (ih _ (HH d le_rfl) (he _ (Or.inr rfl)))
        _ (hw i)
      change W (update w i (w i))≤A at hx; simpa using hx
  have hq : Q j=o := by funext i; simp only [Q,hv]
  simpa only [W,hq] using hb Finset.univ j hj (by simp)
end Offset

variable {C : Family G} {f : Extraction.Order}

/-- Enough centered work from a producer to issue rents. No uniform m→infty
price assertion; same rate over arbitrarily fine m in the ordered sense.
Heights/physical scaling included *in the given trial*. Components themselves
may vary with both regulators.
-/
structure CenterRents (F : Trial C) (y : Cutoffs → ℝ) (f : Extraction.Order) : Prop where
  same : ∀ᶠ i in f.fuse, literal (F i.1 i.2)
  billed : ∀ w : ℕ, ∃ k ≥ w, f.late fun N p => ∃ h : k ≤ N,
    Interior ((center C.S p h 0).chamber 0) (F N p 0) ∧
    (center C.S p h 0).rootTest (C.beta N p) (F N p 0) ≤ y (N,p)

/-- Stronger issue: every fixed hierarchy cell side, either type of seam,
every tiling & literal position tested. Eventually-ordered thresholds;
relative margin denominator ANY fixed positive integer. -/
theorem CenterRents.every {F : Trial C} {y : Cutoffs → ℝ} (H : CenterRents F y f) (hc : C.Makes)
    (m J : ℕ) (hJ : 0 < J) : f.late fun N p => ∃ h : m ≤ N, ∀ T : Tiling (C.side N p), T.side.val=Cells.span C.S h p →
      ∀ x∈T.margin 0 (T.side.val/J), Interior (T.chamber 0) (F N p x) ∧ T.rootTest (C.beta N p) (F N p x) ≤ y (N,p) := by
  have hw : ∀ᶠ k in atTop, (3*J:ℕ)*C.S.a k ≤ C.S.a m := by
    have hx := (C.S.shrinks.const_mul ((3*J:ℕ):ℝ)).eventually (ge_mem_nhds
      (show (↑(3*J:ℕ):ℝ) * 0 < C.S.a m from (mul_zero _).trans_lt (C.S.a_pos _)))
    exact hx
  obtain ⟨i,hi⟩ := eventually_atTop.mp ((eventually_ge_atTop m).and hw)
  obtain ⟨k,hk,ht⟩ := H.billed i
  obtain ⟨hr,hS⟩ := hi k hk
  have he := (Order.fused f _).mp H.same
  unfold Order.late at ht he ⊢
  filter_upwards [ht,he] with s hA hB
  filter_upwards [hA,hB] with j hz hl
  obtain ⟨hn,ha,hb⟩ := hz
  let N := f.mesh j
  let p := f.per s
  refine ⟨hr.trans hn, fun T he x hx => ?_⟩
  let t := Cells.span C.S hn p
  have hi : C.S.a N * t = C.S.a k := C.S.embeds_scale (C.S.toDepth hn p)
  have hh : C.S.a N * T.side.val = C.S.a m := he ▸ C.S.embeds_scale (C.S.toDepth (hr.trans hn) p)
  have hw : 3*t ≤ T.side.val/J := by
    apply (Nat.le_div_iff_mul_le hJ).2
    apply (Nat.cast_le (α:=ℝ)).1
    apply le_of_mul_le_mul_left _ (C.S.a_pos N)
    rw [hh]; rw [←hi] at hS; push_cast at *; linarith only [hS]
  exact offset hn T _ _ (he.symm ▸ Around.inherits hr hn) hl (seamless hc N p) ha hb
    (Lease.fewer T 0 hw hx)

theorem CenterRents.rents {F : Trial C} {y : Cutoffs → ℝ} (H : CenterRents F y f) (hc : C.Makes) :
    Lease.rents F (curry y) f :=
  fun j m => ⟨m,le_rfl,(H.every hc m (8*(j+1)) (by omega)).mono fun _ hi =>
    hi.mono fun _ hj => ⟨hj.choose,fun T he _ => hj.choose_spec T he⟩⟩
end YM.Push.RelayDifference
