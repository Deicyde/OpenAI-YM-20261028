import YM.Extra.MULTISOURCE_BOUNDS.Layers
import YM.Extra.MULTISOURCE_BOUNDS.Trajectory

/-!
# Entry from the old marked input and per-source vertex multiplicities

Each source vertex variant already has a complete projected support and
carries its whole old mode. The sum of weights of variants per old address
can cost a fixed polynomial of OLD cover and a one-step loss C (may e.g. be
post-L, paid before invoking this convertor, not asserted bounded by any
stage here). Winding and all positive-weight dependencies must pass the
halo-containment test. Use w/b per name, *not* dividing by b at every later
merger. Old hit bound per marker only; new hit price uniform over volume.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Multi
open Function Filter Lattice RG Source Wilson Overlay Marker Labels MeasureTheory Finset LogTerms Merger
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {n m : Side} {α β V : Type*}

/-- A sufficient input-vertex price on the actual (possibly zero) weights.
No signed re-cancellations. Empty output sources not bought here. -/
structure Fork (names : α → Finset V) (X : α → Support n) (s : β → Finset V) (Y : β → Support m)
    (o : V → Site m) (q : Ratio m n) (r B M k : ℕ) (e : α → ℝ) (g : β → ℝ) (C : ℝ) : Prop where
  bill : ∃ parent : β → α, (∀ j,0 < g j → s j = names (parent j) ∧ ∃ v∈s j,
      o v∈Y j ∧ Y j ⊆ halo (r*B) ((X (parent j)).image q.parent)) ∧
    ∀ i, SumBudget (fun j => if parent j=i then g j else 0) (C * (1+(coverNumber M (X i):ℝ))^k * e i)

def pad (a A : ℝ) (r k : ℕ) := if h : 0<A/2 then Real.exp (a * tilePrice r)*(exp_absorbs k (A/2) h).choose else 1
lemma pad_ge {a A : ℝ} {k r : ℕ} (h : 0 ≤ a) : 1 ≤ pad a A r k := by
  unfold pad; split
  next he => exact one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by positivity)) ((exp_absorbs k _ he).choose_spec.1)
  exact le_rfl

lemma conversion {a A : ℝ} {r k t : ℕ} (ha : 0 < A) :
    Real.exp (a * tilePrice r + (A/2) * t) * (1+(t:ℝ))^k ≤ pad a A r k * Real.exp (A*t) := by
  have h : 0<A/2 := by positivity
  rw [Real.exp_add,pad,dif_pos h,show A*(t:ℝ)= A/2*t+A/2*t by ring,Real.exp_add,mul_assoc,mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left ((exp_absorbs k _ h).choose_spec.2 t) (Real.exp_pos _).le

section
variable {names : α → Finset V} {X : α → Support n} {s : β → Finset V} {Y : β → Support m} {M B : ℕ}
  {o : V → Site m} {q : Ratio m n} {r k : ℕ} {e : α → ℝ} {g : β → ℝ} {C : ℝ}

theorem Fork.rethread (h : Fork names X s Y o q r B M k e g C) (hC : 0 ≤ C) (hg : ∀ i,0 ≤ g i)
    (hB : 0<B) (hM : M ≤ 2*B) {a A b τ : ℝ} (ha : 0≤a) (hA : 0 < A) (hl : 20*a*tilePrice r ≤ (q.count.val:ℝ)*A)
    {w : V → ℝ} (hw : ∀ v,0 ≤ w v) (hτ : 1 ≤ τ) (he : ∀ i,0 ≤ e i)
    (hroot : Rooted names X M A (fun i => duty w (names i)*e i) b) :
    Rooted s Y B a (fun i => duty (fun v => w v/τ) (s i)*g i) ((pad a A r k*C/τ)*b) := by
  intro x
  obtain ⟨f,hf,h⟩ := h.bill
  let price i := duty (fun v => w v/τ) (s i)
  have hp i : 0 ≤ price i := prod_nonneg fun v _ => div_nonneg (hw _) (zero_le_one.trans hτ)
  let v (i : α) := coverNumber M (X i)
  let z i := Real.exp (a*tilePrice r + (A/2)*v i)
  let goal i := if x∈names i then Real.exp (A*v i)*(duty w (names i)*e i) else 0
  let charge j := if x∈s j then Real.exp (a*coverNumber B (Y j))*(price j*g j) else 0
  let Z := pad a A r k*C/τ
  have hZ : 0≤Z := div_nonneg (mul_nonneg (zero_le_one.trans (pad_ge ha)) hC) (zero_le_one.trans hτ)
  have hlocal (i j) (hj : f j=i) : charge j ≤ if x∈names i then (z i*(duty w (names i) / τ))*g j else 0 := by
    have H : 0 ≤ z i*(duty w (names i)/τ)*g j := mul_nonneg (mul_nonneg (Real.exp_pos _).le (div_nonneg (prod_nonneg fun v (_:v∈ names i) => hw v) (zero_le_one.trans hτ))) (hg j)
    by_cases ht : x∈s j ∧ 0<g j
    · obtain ⟨hs,b,hb,-,hh⟩ := hf j ht.2
      rw [hj] at hs hh
      unfold charge; rw [if_pos ht.1,if_pos (hs ▸ ht.1 : x∈names i),←mul_assoc]
      refine mul_le_mul_of_nonneg_right (mul_le_mul (Real.exp_monotone (projection_reserve q hB hM ha hl _ _ hh)) ?_ (hp _) (Real.exp_pos _).le)
        (hg j)
      dsimp only [price,duty]; rw [←hs,← mul_prod_erase _ _ hb,← mul_prod_erase (s j) w hb,div_mul_eq_mul_div]; gcongr
      · exact hw b
      · exact fun i _ => div_nonneg (hw i) (zero_le_one.trans hτ)
      exact div_le_self (hw _) hτ
    have he : charge j=0 := by
      by_cases h : x∈s j
      · simp [charge, le_antisymm (le_of_not_gt (fun h' => ht ⟨h,h'⟩)) (hg j)]
      simp [charge,h]
    rw [he]; split <;> first | exact H | exact le_rfl
  apply Budget.certify
  · intro j; split; exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (hp j) (hg j)); rfl
  intro l
  let I i := l.filter fun j => f j=i
  have ht i : ∑ j∈I i,charge j ≤ Z*goal i := by
    apply (sum_le_sum (fun j hj => hlocal i j (mem_filter.mp hj).2)).trans
    dsimp only [goal]; split_ifs with hi
    · have hk : ∑ j∈I i, g j ≤ C*(1+(v i:ℝ))^k*e i := Eq.trans_le (sum_filter ..) (Budget.cap (h i) l)
      have hh := conversion (a:=a) (t:=v i) (r:=r) (k:=k) hA
      have hy := mul_nonneg (Real.exp_pos (a*tilePrice r+(A/2)*v i)).le (div_nonneg (prod_nonneg fun v (_:v∈names i) => hw v)
        (zero_le_one.trans hτ))
      rw [← mul_sum]; apply (mul_le_mul_of_nonneg_left hk hy).trans
      let L := C*(duty w (names i)/τ*e i)
      have hL : 0 ≤ L := mul_nonneg hC (mul_nonneg (div_nonneg (prod_nonneg fun v (_:v∈names i) => hw v) (zero_le_one.trans hτ)) (he i))
      calc
        _ = L*(z i*(1+(v i:ℝ))^k) := by unfold L duty z; ring
        _ ≤ L*(pad a A r k * Real.exp (A*v i)) := mul_le_mul_of_nonneg_left hh hL
        _ = _ := by unfold L Z; ring
    simp
  calc
    _ = ∑ i∈l.image f,∑ j∈I i,charge j := (sum_fiberwise_of_maps_to (fun i hi => mem_image_of_mem f hi) charge).symm
    _ ≤ _ := (sum_le_sum fun i _ => ht i).trans (Budget.cap (Budget.scale (hroot x) hZ) _)
end

variable [DecidableEq V] {G : Gauge} {P : Rep G n} {R : Census V} (X : Bands R P)

abbrev Pieces := ℕ ⊕ (ℕ × ℕ)
abbrev bids := Sum.elim (fun i => (X.rays i).val) fun j => (tags X j).val
abbrev blocks := Sum.elim X.support (forced P)

/-- Input nonunit point costs. Force divisor included. May request zero cost
for every unused gas entry (avoid budgeting unpinned ghost vertices). -/
structure Inbox (κ : ℝ) (e : Pieces → ℝ) : Prop where
  pos i : 0 ≤ e i
  regular i : ∀ v∈ (X.rays i).val, P.p.supBounds (X.origins v) (X.support i) (X.H i) (e (.inl i))
  gas (i j : ℕ) U : ‖X.entries i j U‖ ≤ κ*e (.inr (i,j))
  blank (i j : ℕ) : X.entries i j = 0 → e (.inr (i,j)) = 0

lemma inbox {κ b : ℝ} (hk : 0<κ) {w : V→ℝ} (hw : ∀ v,0≤w v) (h : Spent entire X w 0 κ (b/2)) :
    ∃ e, Inbox X κ e ∧ Rooted (bids X) (Sum.elim X.support (forced P)) P.p.B P.p.supportExponent
      (fun i => duty w (bids X i)*e i) b := by
  obtain ⟨⟨g,hg,ht,he⟩,⟨q,hq,hr,hq'⟩⟩ := h
  let k (i : ℕ×ℕ) := if X.entries i.1 i.2 ≠ 0 then q i else 0
  have hnn i : 0 ≤ k i := by unfold k; split; exact hq i; rfl
  have HH v := Budget.cap (Budget.scale (hq'.mono hw hnn (fun _ => le_rfl) (fun i => by unfold k; split; rfl; exact hq i) le_rfl v) (inv_pos.mpr hk).le)
  let e := Sum.elim g (fun i => κ⁻¹*k i)
  have hpos : ∀ i,0≤e i := Sum.rec hg fun i => mul_nonneg (inv_pos.mpr hk).le (hnn i)
  refine ⟨e,⟨hpos, fun i => ht i trivial, fun i j U => ?_,fun i j hj => by simp [e,k,hj]⟩,fun v => ?_⟩
  · dsimp only [e,Sum.elim_inr]; rw [mul_inv_cancel_left₀ hk.ne']; unfold k; dsimp only; split
    next hh => exact hr (i,j) trivial U
    next hh => simp [not_ne_iff.mp hh]
  refine Budget.certify (fun i => ?_) fun s => ?_
  · split; exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (prod_nonneg fun _ _ => hw _) (hpos _)); rfl
  have H := add_le_add (Budget.cap (he v) s.toLeft) (HH v s.toRight)
  rw [inv_mul_cancel_left₀ hk.ne',add_zero,show b/2+b/2=b by ring] at H
  rw [← toLeft_disjSum_toRight (u:=s), sum_disjSum]; apply le_trans _ H; apply add_le_add
  · simp [e,duty,Poly.toll]
  apply sum_le_sum; intro i _; dsimp [e]; split_ifs <;> simp [duty,Poly.toll,mul_left_comm]

end YM.Extra.Multi
