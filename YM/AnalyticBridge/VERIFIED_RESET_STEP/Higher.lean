import YM.AnalyticBridge.VERIFIED_RESET_STEP.Lines
import YM.Extra.ITERATION_NO_LOSS.TermNorm
import YM.Extra.WILSON_STARTUP.Face
import YM.Next.SCHEDULE.Stadium
import YM.Next.SCHEDULE.TensorCost

/-! E final beta replacement on the *same masked* cubic and quartic
channels used in the exponent. No attachment when retaining the signed
difference there. Flux and clipping steps are separate. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset
open Function Filter Set Lattice Wilson RG UVNext.PricedKernels Next.Scheduling Work.F03 Extra.Iteration.Derivs
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {n : Side} {p : BudgetPoint}

abbrev High := ℕ ⊕ ℕ
namespace High
variable (R : PathData G) (d : High) (o : Site n)
-- avoid dependent arity sum in externally used types
def arity : ℕ := d.elim (fun _ => 3) (fun _ => 4)
lemma significant : arity d = 3 ∨ arity d = 4 := by cases d <;> simp [arity]
def term : (d : High) → Atom G (arity d) := Sum.rec (fun i => R.cubic i) fun i => R.quartic i
def home := (term R d).footprint o
def charge := (term R d).magnitude
def length := (term R d).length
def plain (U : Config G n) := (term R d).unmasked U o
def price (p : BudgetPoint) := Wages.startup G (arity d) p.power p.order * charge R d * ((length R d:ℝ)+1)^Wages.grade (arity d) p.power p.order
def fresh (α Δ : ℝ) (U : Config G n) := (-(α+Δ)) * plain R d o U
lemma invariant {c σ C Λ} (h : R.Bounds c σ C Λ) : (term R d).Invariant := by cases d <;>
  first | exact (h.invariant _).2.1 | exact (h.invariant _).2.2
lemma small_home : o ∈ home R d o := Finset.mem_image.mpr ⟨0,Finset.mem_insert_self ..,by simp⟩
lemma price_nn (p : BudgetPoint) : 0 ≤ price R d p := by
  have := Wages.slot_ge G p.power p.order 0; unfold price Wages.startup charge Atom.magnitude; positivity
lemma paid (p : BudgetPoint) : Bill p o (Healthy p.threshold (home R d o)) (price R d p*p.threshold^3) (plain R d o) := by
  apply Bill.le (Wages.fin p (term R d) o)
  rw [Wages.scan]; have hk : 3 ≤ arity d := by have := significant d; omega
  have ht := pow_le_pow_of_le_one p.threshold_pos.le p.threshold_le hk
  simpa only [price,charge,length] using (show _ from calc
    _ = price R d p*p.threshold^arity d := by unfold price charge length; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left ht (price_nn ..))
lemma fresh_bill (p : BudgetPoint) (α Δ : ℝ) : Bill p o (Healthy p.threshold (home R d o))
    (|α+Δ| * (price R d p*p.threshold^3)) (fresh R d o α Δ) := by unfold fresh; simpa only [fresh, abs_neg] using Bill.mul_left (-(α+Δ)) (paid R d o p)
lemma fresh_regular {c σ C Λ} (h : R.Bounds c σ C Λ) (p : BudgetPoint) (α Δ) : p.Regular (home R d o) (fresh R d o α Δ) := by
  have he := canonical_regular (term R d) o p (invariant R d h)
  exact reg_bill (fresh_bill R d o p α Δ) (measurable_const.mul he.borel)
    (fun U V hu => congrArg (_*·) (he.sites U V hu)) (fun k U => congrArg (_*·) (he.symmetry k U))
@[simp] lemma fresh_one (α Δ) : fresh R d o α Δ 1 = 0 := by
  have := significant d
  haveI h : Nonempty (Fin (arity d)) := ⟨⟨0,by omega⟩⟩
  simp [fresh,plain,Atom.unmasked,Atom.poly,atSite_path, WilsonStartup.face_one,G.curvature_unit,zero_pow (by omega : arity d ≠ 0)]
set_option maxHeartbeats 500000 in
lemma plain_limit (v : Dir G n) : Tendsto (fun t : ℝ => plain R d o (line v t) / t^2) (𝓝[≠] 0) (𝓝 0) := by
  let M := term R d
  let u : Exterior.fieldDir G n 1 := fun i => v (i.1,Exterior.axisEquiv.symm i.2)
  have he : Exterior.collect G u = v := funext fun i => congrArg (fun j => v (i.1,j)) (Exterior.axisEquiv.left_inv i.2)
  have H : ∀ t : ℝ, Precision.represent (t • u) = line v t := fun t => congrArg (increment (1:Config G n)) (show Exterior.collect G (t • u) = t • v from congrArg (t • ·) he)
  have hh := atom_limit M o u; simp_rw [H,show ∀ U, M.unmasked U o = plain R d o U from fun U => rfl] at hh
  have hi : arity d - 2 ≠ 0 := by have := significant d; omega
  have ht := hh.mul (((tendsto_id (x:=𝓝 (0:ℝ))).mono_left nhdsWithin_le_nhds).pow (arity d-2))
  rw [zero_pow hi,mul_zero] at ht; refine ht.congr' ?_
  filter_upwards [show ∀ᶠ t : ℝ in 𝓝[≠] 0, t≠0 from self_mem_nhdsWithin] with t ht
  rw [show t^arity d = t^2 * t^(arity d - 2) by rw [← pow_add]; congr 1; omega]; field_simp; rfl
lemma fresh_vanish (hG : G.Simple) {c σ C Λ} (h : R.Bounds c σ C Λ) (p : BudgetPoint) (α Δ) (v w : Dir G n) :
    logHessian (fresh R d o α Δ) v w = 0 := by
  have hh a := tendsto_nhds_unique (hessian_limit hG (fresh_regular R d o h p α Δ) (fresh_one ..) a)
    (show Tendsto _ _ (𝓝 0) by simpa only [fresh,mul_div_assoc,mul_zero] using (plain_limit R d o a).const_mul (-(α+Δ)))
  exact zero_by_diag (fresh_regular R d o h p α Δ) (by linarith [hh v]) (by linarith [hh w]) (by linarith [hh (v+w)])
lemma fresh_sub (α Δ α' Δ' : ℝ) : fresh R d o α Δ - fresh R d o α' Δ' = fresh R d o (α-α') (Δ-Δ') := by funext; simp [fresh]; ring
end High
end YM.AnalyticBridge.VerifiedReset
