import YM.Next.FOUNDATIONS.Reorient
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Average
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Format
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Tails
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Triangle
import YM.Push.CUTOFF_PROJECTORS.Stencil



/-! # Signed-averaged stencil admission: exact formulation and Bill

Rust-proof convention: take `P.Jorigin` equality ON ACTUAL torus assignments
with pull (so negative-link transforms cannot just be swapped silently);
no assumption of Packet.topEquation reorientation or ANY transfer. Give even
concrete signed weights that produce that identity in `Performs`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Calibration
open Lattice RG Wilson Source Function Filter Labels Next.Foundations Push.CutoffProjectors Work Tensor
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff InnerProductSpace
variable {G : Gauge} {d : ℕ}
namespace Machine
variable {C : Family G} (M : Machine C.params d) {N p : ℕ}

/-- Testing stub used ONLY for J identities. No `ComesFrom` asserted. -/
def vane (N p : ℕ) : Packet C d N p where
  weights := (M.weights (C.labels.level d) 0).comp (equationSpace (C.labels.level d)).subtype
  chain _ _ := ⟨0,fun _ => ∅,fun _ => 0,fun _ => 0⟩
  linear_x _ := { map_add := by simp, map_smul := by simp }

variable (E : Packet C d N p)

def Brand := ∀ (x : equationSpace (C.labels.level d)) U,
    E.Jorigin x U = share * ∑ s : Signed, (M.vane N p).Jorigin (steer (C.labels.level d) s⁻¹ x) (pull s 0 U)

private lemma twisted {x : equationSpace (C.labels.level d)} (h : ∀ y∈M.curtain,∀ i : Axis,20*((y i).natAbs+1)≤(C.side N p).val)
    (s : Signed) (i : Lens G d) :
    let n := i.2.val
    let P := M.vane N p
    let t:=C.path.levels.clock.threshold N
    let Q := fun u => ((C.S.a N:ℂ)^d)* P.Jorigin x (pull s 0 (C.params.testLinks d (0 : Site (C.side N p)) (t • i.1) u))
    ContDiffAt ℝ (n:WithTop ℕ∞) Q 0 ∧ iteratedDeriv n Q 0 = P.amount x (tilt s i) := by
  intro n P t Q
  let W:= Packet.sites (C.side N p) M.curtain
  let J : Jet G := (tilt s i).1
  have he (u : ℝ) : Q u = ((C.S.a N:ℂ)^d)*P.Jorigin x (C.params.testLinks d (0 : Site (C.side N p)) (t • J) u) := by
    refine congr_arg (fun y : ℂ => (C.S.a N : ℂ)^d*y) (M.supported_J P M.served (Machine.opened _ h) rfl x _ _ ?_)
    have hx : changedJet (fun i : ℕ => Taylor.turn s.ortho⁻¹ (j:=i)) (t • i.1) = t • J := funext fun v => map_smul (Taylor.turn _ (j:=v)) t _
    have hs := test_rotation C.params d s (0:Site (C.side N p)) 0 (Machine.nonwrap M.curtain h) (le_trans (by decide : 2≤4) (actual_side_ge C.S N p)) (t • i.1) u -- fix size
    rw [hx,affine] at hs; simpa using hs
  rw [funext he]; refine ⟨contDiffAt_const.mul ?_,rfl⟩
  -- arbitrary smooth order from regular_J with an enlarged BudgetPoint
  let b := C.path.levels.budget N
  let b' : BudgetPoint := { b with order:=max i.2.val b.order, order_ge:=b.order_ge.trans (le_max_right ..) }
  have ht := (M.regular_J P M.served (Machine.opened M.curtain h) rfl b' x).smooth 1 (one_healthy _ _ b.threshold_pos.le)
  have hx : ContDiffAt ℝ (n:WithTop ℕ∞) (P.Jorigin x ∘ increment 1) 0 := ht.of_le (Nat.cast_le.mpr (le_max_left ..))
  let Y := testLog C.params d (0:Site (C.side N p)) (t • J)
  have hq : ContDiffAt ℝ (n:WithTop ℕ∞) Y 0 := (testLog_diff ..).of_le le_top
  refine ((show ContDiffAt ℝ (n:WithTop ℕ∞) (P.Jorigin x ∘ increment 1) (Y 0) by rw [show Y 0=0 from testLog_zero ..]; exact hx).comp 0 hq).congr_of_eventuallyEq ?_
  exact (increment_testLog C.params d (0:Site (C.side N p)) (t • J)).fun_comp (P.Jorigin x)

theorem rainbow (h : M.Brand E) (hf : ∀ y∈M.curtain,∀ i : Axis,20*((y i).natAbs+1)≤(C.side N p).val)
    (x : equationSpace (C.labels.level d)) (i : Lens G d) :
    E.amount x i = share * ∑ s : Signed, (M.vane N p).amount (steer (C.labels.level d) s⁻¹ x) (tilt s i) := by
  unfold Packet.amount
  let n:=i.2.val; let P:=M.vane N p
  let f (s : Signed) (u : ℝ) := ((C.S.a N:ℂ)^d)*P.Jorigin (steer (C.labels.level d) s⁻¹ x) (pull s 0 (C.params.testLinks d (0:Site (C.side N p)) ((C.path.levels.clock.threshold N) • i.1) u))
  unfold Brand at h
  -- only rewrite E
  simp_rw [h x,mul_left_comm ((C.S.a N:ℂ)^d) share, Finset.mul_sum]
  have hs (s : Signed) : ContDiffAt ℝ (n:WithTop ℕ∞) (f s) 0 := (twisted M hf s i).1
  change iteratedDeriv n (fun t => ∑ s,share*f s t) 0 = _
  rw [iteratedDeriv_fun_sum (fun s _ => contDiffAt_const.mul (hs s))]
  apply Finset.sum_congr rfl
  intro s _
  rw [iteratedDeriv_const_mul _ (hs s)]
  exact congr_arg _ (twisted M hf s i).2

/-- Alternative admission, enables signed-symmetrized campaigns without
asking Compares in any new norms. -/
structure Rain (A : Campaign C) (N p : ℕ) : Prop where
  stamped : M.Brand (A.packet d N p)
  shards (x : equationSpace (C.labels.level d)) : let Q := (A.packet d N p).chain N x
                                                   ∃ s : Finset ℕ, (∀ j∉s, Q.regular j=0) ∧ ∀ j∈s,Nonwrapping (Q.support j) 0

theorem signs (A : Campaign C) (hG : G.Simple) :
    ∃ c> (0:ℝ), ∀ (W : Bid.Worth), Bid.Bank W C.path.levels → Bid.roomCost C.path.levels W →
    ∀ f : Extraction.Order, f.late (fun N p => M.Rain A N p ∧ (A.packet d N p).Compares W) →
      f.late (fun N p => (A.packet d N p).Separation c) := by
  let F:=C.labels.level d
  obtain ⟨I,ε,c,hε,hc,hz⟩ := spectral_bank d (circle F (M.trophy F)) (circle_triangle F _ (M.certified F))
  -- use smooth_calendar at transformed slots; χ on same path
  let L (i : Fin (Module.finrank ℂ (equationSpace F))) (k : Lens G d) (a : ℝ×ℝ) := share*∑ s : Signed,
    ∑ j : F.Index, ((steer F s⁻¹ (parameters F i)).val j)*M.calendar F j (tilt s k) a.1 a.2
  have hl (i) (k) : Continuous (L i k) := continuous_const.mul (continuous_finsetSum _ fun s _ => continuous_finsetSum _ fun j _ =>
    continuous_const.mul (M.smooth_calendar F j (tilt s k)).continuous)
  have hx (p : ℕ) (i) (k) : ∀ᶠ n : ℕ in atTop, ‖L i k (pair C n p)-L i k 0‖ ≤ ε := by
    refine (((hl i k).tendsto 0).comp (withering A.cutoff hG (fun _ => p))).eventually (p:=fun x => ‖x - L i k 0‖≤ε) ?_
    filter_upwards [Metric.closedBall_mem_nhds (L i k 0) hε] with x hx
    simpa [dist_eq_norm] using hx
  have he (p : ℕ) : ∀ᶠ N : ℕ in atTop, M.Rain A N p → (A.packet d N p).Bill (circle F (M.trophy F)) I ε := by
    filter_upwards [paid C.S M.curtain, eventually_ge_atTop (A.start d p),eventually_all.mpr fun i => eventually_all.mpr (fun k : I => hx p i k)] with N hN hP hL ha
    refine ⟨?_,fun j i hi => ?_⟩
    · intro j; obtain ⟨s,hs,ht⟩ := ha.shards (parameters F j)
      exact Packet.top_of_finite (A.uses _ _ _ hP) A.cutoff _ s hs ht
    rw [M.rainbow _ ha.stamped (hN p), bills_relit]
    have hv (s : Signed) : (M.vane N p).amount (steer F s⁻¹ (parameters F j)) (tilt s i)=_ :=
      M.calendar_eq (M.vane N p) M.served (hN p) rfl (steer F s⁻¹ (parameters F j)) (tilt s i)
    change ‖ share * ∑ s, (M.vane N p).amount (steer F s⁻¹ (parameters F j)) _ - _‖ ≤ _
    have hs (s : Signed) : probe (C.labels.level d) (tilt s i) ((M.trophy F) ((steer (C.labels.level d) s⁻¹) ((parameters (C.labels.level d)) j))) = _ := M.spends F (steer F s⁻¹ (parameters F j)) (tilt s i)
    simp_rw [hv,hs]; exact hL j ⟨i,hi⟩
  refine ⟨c,hc,fun W hb hr f h => h.mono (fun j hh => (hh.and (f.mesh.cofinal.eventually (he _))).mono (fun i hi =>
    hz _ _ _ (hi.2 hi.1.1) A.cutoff W hb hr hi.1.2))⟩
end Machine
end YM.ProjectorNext.Calibration
