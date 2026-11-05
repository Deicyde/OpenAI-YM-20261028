import YM.AnalyticBridge.SECTOR_AFFINE_JETS.Neighborhood
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Windows

/-!
# Entry, view and exponentially small error jets of the chosen principal windows

Use the `Rows.In` addresses even at empty, so don't erase a mode at the zero
Fourier point or integrate a regular array in place of a frozen one. W_i is
literally SectorChange.panels ( with SectorChange's endpoint convention).
Keep boundary rows in compression and preserve width against the origin and
both input slots. Produce full resolvent *and* estimates for all principal
compressions at the same shift. No shift is inserted in the actual covariance
prescription; u is a resolvent parameter for subsequent chain expansions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.SectorAffine

open Filter Function Set Lattice Wilson RG Precision Pressure Tree Exterior
open YM.Next.Fluctuations YM.Next.SectorChange
open YM.Next.SectorChange.Rows YM.Next.SectorChange.Wisps YM.Next.SectorChange.Schur
open YM.Push.Uniform (bolt)
open YM.FreeResolvent (Mark Bundle native Pane.thin Pane.column)
open YM.FreeResolvent.Mark (Bill)
open YM.FreeResolvent.TestD Matrix
open scoped Topology ContDiff BigOperators InnerProductSpace Classical Matrix.Norms.Frobenius

variable {G : Gauge} {P : Patch} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S} {x σ η d M V u : ℝ}

section survey
variable {ι : Type} [Fintype ι] {a : ι → Site c} {t : ι → Set ι} {r : ℕ}
variable [DecidableEq ι]

/-- Survey of blocks whose indices are ordered principal color/link slots. -/
def shipment (h : Bars t a r) : FreeResolvent.Window.Survey (fun i : ι => ↥(t i)) where
  loc _ := Embedding.subtype _
  root i := ⟨i,per_self h i⟩
  atRoot _ := rfl

lemma shipment_near (h : Bars t a r) : (shipment h).Near (native c) a (r:ℝ) := by
  intro i j hj; change (r:ℝ) ≤ ((separation (a i) (a j)):ℝ)
  exact_mod_cast le_of_lt (lt_of_not_ge (show ¬ separation (a i) (a j) ≤ r from
    fun ht => hj ⟨⟨j,h i j ht⟩,rfl⟩))

lemma per_shift (Q : Matrix ι ι ℝ) (h : Bars t a r) (u : ℝ) :
    per t (Q + u • 1) = (shipment h).inspect Q u := by
  ext i j
  let v : (t j) → ι := (↑)
  let H := Q+u • 1
  change per t H i j = FreeResolvent.Pane.column Q v u ⟨j,per_self h j⟩ i
  by_cases hi : i∈t j
  · rw [per_read t H _ hi]; swap; · exact per_self h j
    change (H.submatrix v v)⁻¹ _ _ = _; rw [FreeResolvent.shift_compress v Q u Subtype.val_injective]
    exact (FreeResolvent.Pane.local_entry Q u v Subtype.val_injective ⟨j,per_self h j⟩ ⟨i,hi⟩).symm
  apply (per_zero t H hi).trans
  symm; apply FreeResolvent.Pane.unused
  rintro ⟨q,rfl⟩; exact hi q.property

end survey

section rates
variable {ι : Type} [Fintype ι] {B : PriceCoords G c} {a : ι → Site c}
variable {k : ℕ} {Q : PriceCoords G c → Matrix ι ι ℝ}

/-- At nonnegative shift u. `charges l.length 1 C (drain u)` means
`C / (1+u)` at order zero, `C/(1+u)^2` at positive derivative orders. -/
structure ResolventJets (a : ι → Site c) (B : PriceCoords G c) (k : ℕ) (d C u : ℝ)
    (Q : PriceCoords G c → Matrix ι ι ℝ) : Prop where
  smooth : ContDiffAt ℝ k Q B
  jets (l : List (Coord G c)) : l.length ≤ k →
    Bill (marks G c d) (native c) a a l d (charges l.length 1 C (drain u)) (jet bolt Q l B)

lemma ResolventJets.weaker (hp : ResolventJets a B k d M u Q) {C γ : ℝ} {i : ℕ}
    (hi : i≤k) (hc : M≤C) (hg : γ≤d) (hu : 0≤u) :
    ResolventJets a B i γ C u Q :=
  ⟨smooth_of_le hp.smooth hi, fun l hl => (demark (hp.jets l (hl.trans hi)) hg).mono hg
    (charges_mono _ zero_le_one hc (drain_pos hu).le)⟩

lemma ResolventJets.polar (hp : ResolventJets a B k d M u Q) (hm : 0 ≤ M) (hu : 0 ≤ u) :
    Polar B a a Q k d (M*drain u) :=
  ⟨hp.smooth,fun l hl => (hp.jets l hl).mono le_rfl (charges_lax _ le_rfl (drain_pos hu).le (drain_le hu) hm)⟩

variable [DecidableEq ι]

lemma room_small {n : ℕ} (p : Price σ M η d 1 V 1 n) : d ≤ σ := by
  have he := p.roomEnough.trans p.roomTop
  refine le_trans ?_ he
  apply le_mul_of_one_le_left p.pos.le; push_cast; linarith [show 0 ≤ (n:ℝ) by positivity]

lemma cost_full {u : ℝ} (hu : 0 ≤ u)
    (hp : Polar B a a Q k σ M) (p : Price σ M η d 1 V 1 k) (hv : (native c).Volume a d V)
    (h : YM.FreeResolvent.Gap (Q B) η) : ResolventJets a B k d (meter k k M 1 (rise V η)) u (action Q u) := by
  have hx := price_knowledge hp (room_small p) h
  refine ⟨hx.sees hu p.r0, fun l hl => (hx.cost l hl p hu (Mark.position_move _ _ p.pos.le) hv).mono ?_ le_rfl⟩
  apply le_mul_of_one_le_left p.pos.le; push_cast; linarith [show 0 ≤ (k:ℝ) by positivity]

omit [DecidableEq ι] in
lemma cost_window {u : ℝ} (hu : 0 ≤ u)
    (hp : Polar B a a Q k σ M) (p : Price σ M η d 1 V 1 k) (hv : (native c).Volume a d V)
    (h : YM.FreeResolvent.Gap (Q B) η) {I : Type} [Fintype I] [DecidableEq I]
    (f : I → ι) (he : Injective f) :
    ResolventJets (a ∘ f) B k d (meter k k M 1 (rise V η)) u (action (limitTo Q f) u) :=
  cost_full hu (hp.compress he) p (hv.comp he) (h.submatrix _ he)

/-- window Pi, on active color/link space, including shift. -/
def panelPi (t : ι → Set ι) (Q : Matrix ι ι ℝ) (u : ℝ) : Matrix ι ι ℝ := per t (Q+u • 1)

def panelError (t : ι → Set ι) (Q : Matrix ι ι ℝ) (u : ℝ) := (Q + u • 1)*panelPi t Q u-1

theorem panel_price {r : ℕ} {t : ι → Set ι} (ht : Bars t a r) {u : ℝ} (hu : 0 ≤ u)
    (hp : Polar B a a Q k σ M) (p : Price σ M η d 1 V 1 k) (hv : (native c).Volume a d V)
    (h : YM.FreeResolvent.Gap (Q B) η) :
    let M₀ := meter k k M 1 (rise V η)
    let M₁ := FreeResolvent.tagPrice 1 k M (V*M₀)
    let M₂ := FreeResolvent.tagPrice 1 k M₀ M₁
    let fee := Real.exp (-((k+1:ℕ):ℝ)*d*r)
    let T := fun y => panelPi t (Q y) u
    ResolventJets a B k d (V*M₀) u T ∧
    Polar B a a (fun y => panelError t (Q y) u) k d (M₁*fee*drain u) ∧
    Polar B a a (T-action Q u) k d (M₂*fee*drain u^2) := by
  intro M₀ M₁ M₂ fee T
  have hA := price_knowledge hp (room_small p) h
  have hM : Mark.Move (marks G c d) (native c) d 1 := Mark.position_move _ _ p.pos.le
  let W := shipment ht
  rw [show T = glimpse W Q u from funext fun y => per_shift (Q y) ht u]
  refine ⟨⟨glimpse_smooth hA _ hu p.r0,fun l hl => ?_⟩,?_,?_⟩
  · have he : d ≤ 3*(k+1:ℕ)*d := by
      apply le_mul_of_one_le_left p.pos.le; push_cast; linarith [show 0 ≤ (k:ℝ) by positivity]
    apply (glimpse_rates hA p W hu hM hv l hl).mono he (le_of_eq ?_)
    unfold charges M₀; split <;> ring
  · rw [show (fun y => panelError t (Q y) u) = deficit W Q u from ?_]
    · refine (hA.miss p hu hM hv (shipment_near ht)).mono ?_ ?_
      · exact le_mul_of_one_le_left p.pos.le (by exact_mod_cast Nat.le_add_left 1 k)
      apply le_of_eq; unfold fee M₁ M₀ FreeResolvent.tagPrice; push_cast; ring
    funext i; change _ = (Q i + u • 1)*W.inspect (Q i) u-1
    unfold panelError panelPi; rw [per_shift (Q i) ht]
  refine (hA.discrepancy p hu hM hv (shipment_near ht)).mono le_rfl (le_of_eq ?_)
  unfold M₂ M₁ M₀ fee FreeResolvent.tagPrice; push_cast; ring
end rates
end YM.AnalyticBridge.SectorAffine
