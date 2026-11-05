import YM.SectorNext.LARGE_FIELD_REMAINDERS.Geometry
import YM.Work.E02
import YM.Work.E07.Scale
import YM.Work.E08
import YM.Work.E09.Scales


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# On *all* exterior anchors, after removing the assigned rows

algebra still applies here .

Use the unaffected interior
estimate AT t scale, NOT with T as small as t, and even when there were no seeds
at all.

Never clip/tune the forecast defects here.

Works through seams for the true
k, on the true forest; uses the Axial calculation separately on each interior.

This is not after dropping defaults.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Remainder
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree MeasureTheory
  Axial YM.Push.SectorMeasure 
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure

variable {G : Gauge} (P : Teller G) (L : Side) (W : ℝ)

set_option maxHeartbeats 700000 in
/-- Uniform log-scale link/chord estimates across all OUTSIDE cones and
for each regular link even before estimating any work terms. -/
lemma outside_size (hW : 0 < W) : ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ x : ℝ in atTop,
    ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch.L=L → 100*(1+radiusB x) ≤ c.val →
      P.Funds S T → ∀ (F : Forest S.ratio) (A : Stores S) (U : Config G f) (V : Config G c)
      (k : S.Choices), SliceSet S F U → Seeded A U k V x W → Alive S U k →
      let B := radiusB x; let t := fiery G x S.patch.L
      (∀ b : Bond f, remote A B b → G.chord (U b*(replica S.ratio V b)⁻¹) ≤ C*t) ∧
        ∀ (o : Site c), o ∉ A.dome (2*B) →
        ∃ z : Site c → G.El,
          (∀ i : Bond f, separation o (S.ratio.parent i.1) ≤ 2*B/5 →
            G.chord (gauge (z∘S.ratio.parent) U i) ≤ C*(B:ℝ)^5*t) ∧
          (∀ i : Bond c, separation o i.1 ≤ 2*B/5 →
            G.chord (gauge z V i) ≤ C*(B:ℝ)^5*t) := by
  obtain ⟨D,hD,HD⟩ := Work.E02.answer G L P.j P.bind
  let M := (P.j+7)*L.val
  let K : ℝ := (2*(M:ℝ)+1)^4 * Fintype.card PlaqAxes
  let E : ℝ := D*K + 2*W
  let X : ℝ := 16*3^5*(Fintype.card PlaqAxes:ℝ)*2
  have hK : 0 ≤ K := by unfold K; positivity
  have he : 0<E := by unfold E; positivity
  have hX : 0≤X := by unfold X; positivity
  refine ⟨E+X+1,by linarith,?_⟩
  filter_upwards [(betaF_growth').eventually (eventually_gt_atTop 0),
    Work.E01.radiusB_tendsto.eventually_ge_atTop (10*(M+L.val+1)), Work.E07.temp_coarse_le G L] with x hu hB hs
  intro c f S T hL hY hT F A U V k hU hA ha B t
  have h0 : 10*(M+L.val+1) ≤ B := hB
  have hj := hT.atStep; have hh := hT.knobs
  have hM : macroR S.patch=M := by rw [Work.E01.macroR_eq,hj,hL]
  have hsize : 100*macroR S.patch ≤ f.val := by
    have h : c.val ≤ f.val := by
      rw [S.sizes]
      have h := S.patch.L.property; change 0<S.patch.L.val at h
      simpa using Nat.mul_le_mul_left c.val h
    change 100*(1+B) ≤ c.val at hY; omega
  change 100*(1+B) ≤ c.val at hY
  have ht : t>0 := by unfold t; rw [hL]; exact Work.E09.temp_pos hu
  let g := S.ratio
  have hl (r i : ℕ) {o : Site c} (p : Bond f) (ho : o∉A.dome r)
      (hp : separation o (g.parent p.1) ≤ i) (he : i+M+L.val ≤ r) :
      G.chord (U p * (replica g V p)⁻¹) ≤ E*t := by
    have hw (y : Site c) (hy : separation o y ≤ r) : y ∉ A.place :=
      fun hv => ho (halo_spec.mpr ⟨y,hv,(separation_comm ..).trans_le hy⟩)
    have hports : port S (g.parent p.1) U ≤ K*t := by
      unfold K
      rw [← hM]
      refine Work.E08.port_le o r t ht.le (fun a ha => ?_) _ (by rw [hL,hM]; omega)
      exact (exterior_fine hA (hw _ ha)).trans (by change t/2 ≤ t; linarith)
    have hv : wire (S.prediction U k) V (g.parent p.1,p.2) ≤ 2*W*t := exterior_noise hA
      (hw _ (hp.trans (by omega)))
    have hc := HD c f S hh hL hj hsize (by omega) F U hU V p k (uses_all ha _)
    unfold Bid.Cops at hc; dsimp only at hc
    dsimp only [E]; rw [add_mul,mul_assoc]
    apply hc.trans (add_le_add (mul_le_mul_of_nonneg_left hports hD.le) _)
    split
    · positivity
    exact hv
  have hpaid : E*t ≤ (E+X+1)*t := mul_le_mul_of_nonneg_right (by linarith) ht.le
  have hB1 : 1 ≤ B := by omega
  have hB2 : 1 ≤ (B:ℝ) := by exact_mod_cast hB1
  refine ⟨fun b hb => (hl (4*B) 0 b hb (by simp [g]) (by omega)).trans hpaid,?_⟩
  -- first produce the chord estimate on some coarse gauge z
  intro o ho
  let r := B/2
  have hV (y : Site c) (hy : separation o y ≤ r) (j : PlaqAxes) :
      toll V (y,j) ≤ 2*t := by
    have hx : y∉A.place := fun hv =>
      ho (halo_spec.mpr ⟨y,hv,(separation_comm ..).trans_le (hy.trans (by unfold r; omega))⟩)
    rw [← hL] at hs; exact (exterior_output hA (b := (y,j)) hx).trans hs
  obtain ⟨z,hz⟩ := Work.E08.axial_patch o V (2*B/5) r (by unfold r; omega) (by unfold r; omega)
    (2*t) (by positivity) hV
  have hzV (b : Bond c) (hb : separation o b.1 ≤ 2*B/5) : G.chord (gauge z V b) ≤ X*(B:ℝ)^5*t := by
    apply (hz b hb).trans
    have hr : (r:ℝ) ≤ (B:ℝ) := by exact_mod_cast Nat.div_le_self B 2
    calc
      _ ≤ 16*(3*(B:ℝ))^5 * (Fintype.card PlaqAxes:ℝ)*(2*t) := by
        have hL : 0≤2*t := by positivity
        gcongr; linarith
      _ = _ := by unfold X; ring
  have hpay : E*t+X*(B:ℝ)^5*t ≤ (E+X+1)*(B:ℝ)^5*t := by
    have h : 1 ≤ (B:ℝ)^5 := one_le_pow₀ hB2
    have hp : E*t ≤ E*((B:ℝ)^5*t) := mul_le_mul_of_nonneg_left (le_mul_of_one_le_left ht.le h) he.le
    have hh : 0 ≤ (B:ℝ)^5*t := by positivity
    nlinarith only [hp,hh]
  refine ⟨z,fun b hb => ?_,fun _ hh => (hzV _ hh).trans ((le_add_of_nonneg_left (by positivity)).trans hpay)⟩
  have hh : separation o (g.parent b.1) ≤ 2*B/5 := hb
  apply le_trans (b:=E*t+X*(B:ℝ)^5*t) ?_ hpay
  let R := replica g V
  let ψ := z∘g.parent
  have hc : G.chord (gauge ψ R b) ≤ X*(B:ℝ)^5*t := by
    change G.chord (gauge (constantGauge z S.ratio) (replica S.ratio V) b) ≤ _
    rw [copied _ S.patch.odd_side V z]
    unfold replica; split
    · rw [G.chord_one]; positivity
    exact hzV _ hb
  have H : gauge ψ U b = (ψ b.1*(U b*(R b)⁻¹)*(ψ b.1)⁻¹)*gauge ψ R b := by
    unfold Lattice.gauge; group
  change G.chord (gauge ψ U b) ≤ _
  rw [H]; apply (G.chord_triangle ..).trans
  rw [G.chord_conj]
  exact add_le_add (hl (2*B) (2*B/5) b ho hh (by omega)) hc
where
  betaF_growth' := Work.E09.betaF_growth G L

end YM.SectorNext.Remainder
