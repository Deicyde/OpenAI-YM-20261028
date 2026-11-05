import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Issued
import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.LocalRows
import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Recenter


/-!
# Pass from receipts with one auxiliary interpolation parameter (NOT a
# physical field) in the additive log chart near B to true Lie costs there

Do NOT expose that interpolation in the physical matrix or read a changed
tagged inverse in a different chart. Both ends of this comparison still
HELD in each of the two Config germs that are being subtracted. The only
shrinking of Taylor mark rate in this conversion is `narrow n d` up front.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SelectedOrderedKernels.Small
open Lattice Wilson RG Precision Tree Exterior Function Filter Topology Bloch Laurent Metric Matrix FreeResolvent Affine
  Lifted TestD Mark Set Lever NoHole WardBin.Lies
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {c f : Side} {n k : ℕ} {S : StepData c f}
  {σ C M d η α V V' r γ : ℝ} {t : S.Choices} {B : Vec G c 1} {W : PathData G}

variable {ι : Type*} [Fintype ι] {a : ι → Site c} {F : Forest S.ratio → Config G c → Matrix ι ι ℝ} {m : ℕ → ℝ} {e : ℝ}

/-- Smooth parametric witness of ordinary derivative comparisons in a
COMMON chart including tag charge. Next proof builds with prior engine and
positive gap on entire segment. -/
def Aux (a : ι → Site c) (n : ℕ) (d γ : ℝ) (m : ℕ → ℝ) (B : Vec G c 1) (V : Config G c)
    (F H : Config G c → Matrix ι ι ℝ) (v : Site c) := ∃ Z : Vec G c 1 × ℝ → Matrix ι ι ℝ,
  (∀ y, Z (y,0) = around B (over F V) y) ∧
  (∀ y, Z (y,1) = around B (over H V) y) ∧ ∀ x ∈ Icc (0:ℝ) 1, ContDiffAt ℝ n Z (0,x) ∧
      ∀ l : List (Option (raw G c)), l.length ≤ n → Bill (park (native c) hearth d v) (native c) a a l γ (m l.length)
        (jet (guides (ray G c)) Z l (0,x))

variable {U : Config G c}
lemma aux_pass (HE : ∀ T H v, changed S T H v → Aux a n d γ m B U (F T) (F H) v)
    (hd : 0 ≤ d) (hk : k<n) (hb : ∀ i, ‖paint G c B i‖ < radius G k) (he : 0 ≤ e) (hm : ∀ j ≤ k, 0 ≤ m j)
    (hp : ∀ j ≤ k, ∀ p : OrderedFinpartition j, m p.length ≤ m j ∧ m (p.length+1) ≤ e) :
    Paid S a k (narrow n d) d γ (fun j => offFee G j*m j) (fun j => offFee G j*e) F (increment U (paint G c B)) := by
  let Q T := around B (over (F T) U); let L := guides (ray G c)
  have h1 T : ContDiffAt ℝ k (over (F T) U) ((paint G c).symm (paint G c B)) := by
    obtain ⟨Z,hT,-,H⟩ := HE T T 0 (fun _ _ => Iff.rfl)
    have hg := smooth_of_le (H 0 (left_mem_Icc.mpr zero_le_one)).1 hk.le
    rw [ContinuousLinearEquiv.symm_apply_apply]; apply (slide _ _ _).mp; rw [← funext hT]
    exact hg.comp (f:=fun y => (y,(0:ℝ))) (0:Vec G c 1) (contDiffAt_id.prodMk contDiffAt_const)
  refine ⟨fun T => offCenter_book hb (h1 T) (narrow_nn n hd) (narrow_use hd hk.le) hm ?_,fun T H v hv =>
    offCenter_entry hb (F:=F H-F T) ((h1 H).sub (h1 T)) (narrow_nn n hd) (narrow_use hd hk.le) (M:=fun _ => e) (fun _ _ => he) ?_⟩
  · obtain ⟨Z,hT,-,H⟩ := HE T T 0 (fun _ _ => Iff.rfl)
    obtain ⟨hz,hc⟩ := H 0 (left_mem_Icc.mpr zero_le_one)
    intro j hj p w
    let l := List.ofFn w
    have hL : l.length ≤ n := List.length_ofFn.trans_le ((p.length_le.trans hj).trans hk.le)
    have ht := hc (l.map some) (by simpa)
    rw [restriction _ _ _ (smooth_of_le hz hL),funext hT,List.length_map] at ht
    rw [ContinuousLinearEquiv.symm_apply_apply, ← jet_translate B]; change Bill _ _ _ _ l _ _ _
    have hz := (hp j hj p).1; rw [← show l.length=p.length from List.length_ofFn] at hz
    refine Bill.mono (M:=m l.length) ?_ le_rfl hz
    constructor <;> constructor <;> intro i <;> rw [show Prod.fst ∘ edge (G:=G) (n:=c)=hearth from rfl, ← parks l (native c) hearth d 0 (a i)]
    · exact ht.row.rows i
    exact ht.col.rows i
  obtain ⟨Z,hT,hH,hZ⟩ := HE T H v hv
  intro j hj p w; let l := List.ofFn w
  have hl : l.length=p.length := List.length_ofFn
  have hL : l.length+1 ≤ n := Nat.succ_le_of_lt (hl.trans_lt ((p.length_le.trans hj).trans_lt hk))
  have h2 (X : Forest S.ratio) : ContDiffAt ℝ l.length (over (F X) U) B := by simpa using smooth_of_le (h1 X) (hl.trans_le (p.length_le.trans hj))
  have hc t (ht : t∈Icc (0:ℝ) 1) := smooth_of_le (hZ t ht).1 hL
  have hr t (ht : t ∈ Icc (0:ℝ) 1) := ((hZ t ht).2 (none::l.map some) (by simpa only [List.length_cons,List.length_map] using hL)).mono (γ:=γ) (N:=e) le_rfl
    (by simpa only [List.length_cons,List.length_map,hl] using (hp j hj p).2)
  change Noticed _ _ _ _ _ _ _ l _ _
  rw [ContinuousLinearEquiv.symm_apply_apply,show over (F H - F T) U = (fun y => over (F H) U y - over (F T) U y) from rfl,
    jet_sub _ l (h2 H) (h2 T), ← jet_translate B, ← jet_translate B (over (F T) U)]
  constructor; intro i y
  have hh := recovers l hc hr i y
  rw [funext hT, funext hH] at hh; exact hh
end YM.SelectedOrderedKernels.Small
