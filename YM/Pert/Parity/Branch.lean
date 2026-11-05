import YM.Pert.Parity.Pull
/-! Parity on finite-regulator *formal* position responses after the local solve. No passage to coefficient arrays at positive orders is assumed here. Path equivariance on a determining board only needs to hold on actually sourced rows, **not** on arbitrary inconsistent duplicate data. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.Pert.Parity
open Position Labels Full Filter Function Set Topology Maxwell Lattice
open scoped Topology Classical
variable {G : Gauge} {F : Frames G} {d k : ℕ}
/-- Same profiles, negatively graded columns. -/
def reverseRows (Q : Conditions F d k) : Conditions F d k := { Q with columns := fun i j=> Coat F d (Q.columns i j) }
lemma reverse_chart (Q : Conditions F d k) (v : Ledger Q) (b : Buffer F d) : chart (reverseRows Q) (v,b) = chart Q (pull Q v,twice F d b) := by
  apply congrArg Q.chisels; funext i; change (decode Q v (fun j => motor F b _)).re = _
  dsimp only [Prod.fst, Prod.snd]
  rw [pull_def]; simp only [Function.comp_def,twice_motor,Coat_round]; rfl

structure Fair (Q : Conditions F d k) (J : Module.End ℝ (Fin k→ℝ)) : Prop where
  mirrors (L m p t) (b : Buffer F d) :
    chart Q (curve (finite Q L m) p (-t), twice F d b)=J (chart Q (curve (finite Q L m) p t,b))
  center : chart Q (white Q,0) = J (chart Q (white Q,0))

theorem curve_fair {Q : Conditions F d k} {J} (h : Fair Q J) {φ : Ledger Q → Buffer F d} (hc : Reports (chart Q) (white Q) 0 φ) (L : Side) (hQ : CleanProfiles Q) (hL : 1 < L.val) (p) :
    ∀ᶠ i in atTop, ∀ᶠ t in 𝓝 (0:ℝ), φ (curve (finite Q L i) p (-t)) = twice F d (φ (curve (finite Q L i) p t)) := by
  have limitQ := finite_leading Q hQ L hL
  let H := white Q
  let u (i : ℕ) := curve (finite Q L i) p
  have hu (i : ℕ) := curve_diff (finite Q L i) p |>.continuous.tendsto (0:ℝ)
  simp only [curve_zero] at hu; change ∀i,Tendsto (u i) (𝓝 0) (𝓝 (finite Q L i 0)) at hu
  have T : Tendsto (twice F d) (𝓝 0) (𝓝 0):= by convert! (twice_cont F).tendsto 0 using 2; exact (map_zero ..).symm
  have hs : ∀ᶠ (v : Ledger Q × Ledger Q) in 𝓝 (H,H),
       ∀ᶠ w in 𝓝 v, chart Q (w.1,φ w.1)=chart Q (white Q,0) ∧ (chart Q (w.2,twice F d (φ w.1)) = chart Q (white Q,0) ↔ φ w.2 = twice F d (φ w.1)) := eventually_eventually_nhds.2 <| by
    have hp : Tendsto (fun u=>φ u.1 : Ledger Q × Ledger Q→Buffer F d) (𝓝 (H,H)) (𝓝 _) := hc.diff.continuousAt.tendsto.comp continuousAt_fst
    rw [hc.fixes] at hp
    have ht := (continuousAt_snd.prodMk_nhds (T.comp hp)).eventually hc.strict
    exact (continuousAt_fst.eventually hc.curves).and ht
  refine (((limitQ.prodMk_nhds limitQ).eventually hs).mono fun i hi => ?_)
  have hneg : Tendsto (- · : ℝ→ℝ) (𝓝 0) (𝓝 0) := (by simpa using continuous_neg.tendsto (0:ℝ))
  filter_upwards [((hu i).prodMk_nhds ((hu i).comp hneg)).eventually hi] with t ht
  exact ht.2.mp ((h.mirrors ..).trans ((congrArg J ht.1).trans h.center.symm))

lemma reverse_jet {Q : Conditions F d k} {n : ℕ} (R : Conditions F d n) (φ : Ledger Q → Buffer F d) (L : Side) {m j p} (h : ∀ᶠ t in 𝓝 (0:ℝ), φ (curve (finite Q L m) p (-t))= twice F d (φ (curve (finite Q L m) p t))) :
    readJet φ p j (chart (reverseRows R)) (finite Q L m) (finite (reverseRows R) L m)= (-1:ℝ)^j • readJet φ p j (chart R) (finite Q L m) (finite R L m) := by
  let x (t : ℝ) := chart R (curve (finite R L m) p t, φ (curve (finite Q L m) p t))
  have e : (fun t=>chart (reverseRows R) (curve (finite (reverseRows R) L m) p t,φ (curve (finite Q L m) p t))) =ᶠ[𝓝 0] fun t=>x (-t) := h.mono (fun i hi=> by
    unfold x
    change chart (reverseRows R) (curve (finite R L m) p i, _)=_
    rw [reverse_chart]
    apply congrArg (chart R); exact congr_arg₂ Prod.mk (pull_curve R L m p i).symm hi.symm)
  have he := e.iteratedDeriv_eq j
  exact he.trans (iteratedDeriv_comp_neg j x (0:ℝ) |>.trans (by rw [neg_zero];rfl))
lemma position_sign {Q : Conditions F d k} {J} (h : Fair Q J) {φ : Ledger Q → Buffer F d} (hc : Reports (chart Q) (white Q) 0 φ) (L : Side) (hQ : CleanProfiles Q) (hL : 1 < L.val) {m} (R : Conditions F d m)
      (p j : ℕ) : ∀ᶠ i : ℕ in atTop, readJet φ p j (chart (reverseRows R)) (finite Q L i) (finite (reverseRows R) L i)= (-1:ℝ)^j • readJet φ p j (chart R) (finite Q L i) (finite R L i) := (curve_fair h hc L hQ hL p).mono fun _=> reverse_jet R _ _
end YM.Pert.Parity
