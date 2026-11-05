import YM.Push.LOOP_COEFFICIENT.Envelope
import YM.Push.LOOP_COEFFICIENT.Fine.Quanta


/-!
# Unscaled packet and near-origin one- and two-homogeneous envelopes
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Function Set Filter Matrix Metric Lattice Laurent RG Precision Exterior Bloch Wilson Complex Paths Continuum
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator
variable {a b c d : Type} [Fintype a] [Fintype b] [Fintype c] [Fintype d] [DecidableEq a] [DecidableEq b] [DecidableEq c] {V V' : Vertex d a b} {η C M e : ℝ}
namespace Packet
omit [DecidableEq a] in
lemma mono (h : Packet V η C) (he : 0<e) (hη : e≤η) (hC : C≤M) : Packet V e M := ⟨h.toLit.mono hη,he,h.nonneg.trans hC,fun _ hq => (h.zeroBound _ (tube_mono hη hq)).trans hC,fun _ _ _ hq hp hv => (h.oneBound _ _ _ (tube_mono hη hq) (tube_mono hη hp) hv).trans hC,fun _ _ _ _ _ hq hp hs hv hw => (h.twoBound _ _ _ _ _ (tube_mono hη hq) (tube_mono hη hp) (tube_mono hη hs) hv hw).trans hC⟩

omit [DecidableEq a] in
lemma mul {U : Vertex d b c} (h : Packet V η C) (h' : Packet U η M) : Packet (V.mul U) (η/3) (4*C*M) := ((Quanta.of_packet h le_rfl le_rfl).mul (Quanta.of_packet h' le_rfl le_rfl) one_pos).packet h.width ((StripLaw.of_lit h.toLit le_rfl le_rfl).mul (StripLaw.of_lit h'.toLit le_rfl le_rfl))
omit [DecidableEq a] in
lemma add (h : Packet V η C) (h' : Packet V' η M) : Packet (V.add V') η (C+M) := ⟨h.toLit.add h'.toLit,h.width,add_nonneg h.nonneg h'.nonneg,fun _ hq => (norm_add_le ..).trans (add_le_add (h.zeroBound _ hq) (h'.zeroBound _ hq)),fun _ _ _ hq hp hv => (norm_add_le ..).trans (add_le_add (h.oneBound _ _ _ hq hp hv) (h'.oneBound _ _ _ hq hp hv)),fun _ _ _ _ _ hq hp hs hv hw => (norm_add_le ..).trans (add_le_add (h.twoBound _ _ _ _ _ hq hp hs hv hw) (h'.twoBound _ _ _ _ _ hq hp hs hv hw))⟩

end Packet
namespace Fine
variable {G : Gauge}


def RangeAt (S T : Set Momentum) (η r : ℝ) : Prop := S ⊆ Tube η ∧ T ⊆ Tube η ∧ (∀ q∈S, ‖q‖ ≤ r) ∧ (∀ q∈T, ‖q‖≤r)


structure Sleeping (V : Vertex d a b) : Prop where
  base (p i j) : Below (fun p => V.base p i j) p 2
  one : V.one 0 0 = 0

lemma ball_pair (q : Momentum × Momentum) (hq : q ∈ ball (0:Momentum × Momentum) η) : q.1∈ Tube η ∧ q.2∈ Tube η := by rw [Metric.mem_ball,dist_zero_right, Prod.norm_def,max_lt_iff] at hq; exact ⟨ball_tube (by simpa using hq.1),ball_tube (by simpa using hq.2)⟩

variable (d a b) in
omit [DecidableEq a] in
lemma Sleeping.quanta (hη : 0<η) (C M : ℝ) (hC : 0<C) : ∃ D>0,∀ {V : Vertex d a b} {r S T}, Sleeping V → Packet V η C → RangeAt S T η (M*r) → 0<r → r≤1 → Quanta V S T r (D*r^2) := by
  let K := matrixCost a b
  have hK : 0≤K := matrixCost_nonneg ..
  let D := max (max C (K*C*(M/η)^2)) (C/η*M)
  have hD : 0<D := (hC.trans_le (le_max_left ..)).trans_le (le_max_left ..)
  refine ⟨D,hD,fun {V r S T} hs h ha hr _hr' => ?_⟩
  have hb {q} (hq : q∈S) : ‖V.base q‖ ≤ D*r^2 := by
    have he := matrix_norm (Q:=C*(‖q‖/η)^2) (by positivity) (fun i j => schwarz_two hη (f:=fun z => V.base z i j) (fun z hz => ⟨analyticComponent (h.toLit.base _ hz).1 i j,(component_norm ..).trans (h.zeroBound _ hz)⟩) (fun p => hs.base p i j) (ha.1 hq))
    refine he.trans ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (a:=‖q‖/η) (b:=M*r/η) (by positivity) (by gcongr; exact ha.2.2.1 _ hq) 2) hC.le) hK).trans ?_)
    change K*_ ≤ _; rw [show K*(C*(M*r/η)^2) = (K*C*(M/η)^2)*r^2 by ring]; gcongr; exact (le_max_right ..).trans (le_max_left ..)
  refine ⟨by positivity,fun _ hq => hb hq,fun q p v hq hp hv => ?_,fun q p s v w hq hp hs hv hw => (h.twoBound q p s v w (ha.1 hq.1) (ha.2.1 hp) (ha.2.1 hs) hv hw).trans (by rw [mul_div_cancel_right₀ _ (pow_ne_zero _ hr.ne')]; exact (le_max_left C _).trans (le_max_left ..))⟩
  by_cases he : M*r<η
  · let f (z : Momentum × Momentum) := V.one z.1 z.2 v
    have h0 : f 0=0 := DFunLike.congr_fun hs.one v
    have hq' : ‖(q,p)‖ ≤ M*r := max_le (ha.2.2.1 q hq.1) (ha.2.2.2 p hp)
    have ht := Complex.dist_le_div_mul_dist_of_mapsTo_ball (f:=f) (R₁:=η) (c:=0) (R₂:=C) (fun z hz => ((h.toLit.one z.1 z.2 v (ball_pair _ hz).1 (ball_pair _ hz).2).1.differentiableAt (by simp)).differentiableWithinAt)
      (fun z hz => show dist (f z) (f 0) ≤ C by rw [h0,dist_zero_right]; exact h.oneBound _ _ _ (ball_pair _ hz).1 (ball_pair _ hz).2 hv) (show (q,p) ∈ ball 0 η by simpa using hq'.trans_lt he)
    rw [h0,dist_zero_right, dist_zero_right] at ht
    exact ht.trans ((mul_le_mul_of_nonneg_left hq' (by positivity)).trans (by rw [← mul_assoc,show D*r^2/r = D*r by field_simp]; gcongr; exact le_max_right ..))
  refine (h.oneBound _ _ _ (ha.1 hq.1) (ha.2.1 hp) hv).trans ?_
  rw [show D*r^2/r = D*r by field_simp]; exact le_trans (b:=(C/η*M)*r) (by field_simp; nlinarith) (by gcongr; exact le_max_right ..)
end Fine
end YM.Push.Loops
