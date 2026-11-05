import YM.Next.FREE_KERNELS.Wire

/-! # Harmonic accounting (still scaled column convention) -/

set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix
open scoped Topology BigOperators ComplexConjugate
variable {j t : ℕ}
namespace Flight

variable (P : Flight j t) (k : ℝ)
@[simp] lemma toe_zero : P.toe 0=0 := by simp [toe,aliasAt]
@[simp] lemma span_zero : P.span 0=0 := by simp [span]
@[simp] lemma filter_zero : massFilter P.patch 0=1 := by simp [massFilter]
@[simp] lemma signal_zero (S r) : signal S r 0=0 := by unfold signal wedge; simp [tripQ]
@[simp] lemma mirage_zero (S r) : mirage S r 0=0 := by unfold mirage; simp
@[simp] lemma rotor_zero (S) (v : Train j) : rotor S k v 0=0 := by unfold rotor; simp
@[simp] lemma hinges_zero (r : ℕ) : hinges P r 0=1 := by unfold hinges; simp [mask_one]
@[simp] lemma flux_zero (r : ℕ) : flux P r 0=1 := by simp [flux]
@[simp] lemma prior_zero : priorG k P 0=1 := by simp [priorG,mask_one]
@[simp] lemma sluice_zero : sluice k P 0=0 := by simp [sluice]
@[simp] lemma foot_zero : footY k P 0=1 := by simp [footY,yen]
@[simp] lemma pilot_origin : pilot k P 0 0=1 := by
  unfold pilot ahead; rw [if_pos rfl]
  rw [toe_zero, show (Train.bulb k P.wing 0)=(fun _ => 1) from funext fun i => Train.bulb_zero k P.wing i,mask_one]; simp
@[simp] lemma copper_origin : copper k P 0=1 := by simp [copper]
@[simp] lemma wire_origin : wire k P 0 0=1 := by simp [wire]
lemma vanishing_box {l : Site P.L} (hl : l≠0) : massFilter P.patch (aliasAt 0 l)=0 := by
  obtain ⟨i,hi⟩ := step_picks l hl
  have hh : aliasAt 0 l=mon l := by simp [aliasAt]
  rw [cell_step,← hh] at hi
  have he := hinges_rule P l 0 i
  have hx : chip (aliasAt 0 l i)≠0 := sub_ne_zero.mpr hi
  have hg : tripQ P.L (aliasAt 0 l) i≠0 := mul_ne_zero (side_ne _) hx
  rw [show tripQ 1 0 i=0 by simp [tripQ]] at he
  have hu := (mul_eq_zero.mp he).resolve_right hg
  have hv : area P.L (aliasAt 0 l)=0 := by unfold area; exact Finset.prod_eq_zero (i:=i) (Finset.mem_univ _) (by rw [plank, hu, mul_zero])
  unfold massFilter; rw [show P.patch.L=P.L from rfl,hv,zero_pow (?_ : P.patch.J≠0)]; exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (by norm_num) P.patch.order_cut)
lemma vanishing_hinges (r : ℕ) {l : Site P.L} (hl : l≠0) :
    hinges P r (aliasAt 0 l)=0 ∧ flux P r (aliasAt 0 l)=0 := by
  have he := P.vanishing_box (show -l≠0 from neg_ne_zero.mpr hl)
  rw [show aliasAt 0 (-l)=-aliasAt 0 l from by simpa only [neg_zero] using alias_reverse 0 P.odd l] at he
  simp [hinges,flux,P.vanishing_box hl,he]
lemma pilot_none {l : Site P.L} (hl : l≠0) : pilot k P 0 l=0 := by simp [pilot,ahead,hl]
lemma wire_none {l : Site P.L} (hl : l≠0) : wire k P 0 l=0 := by
  unfold wire; rw [if_neg hl]; simp only [stake, mirage_zero,Matrix.mul_zero,zero_add]
  rw [(vanishing_hinges P 2 hl).2]; simp

variable {p : Momentum} (hk : 0 < k) (hp : p ∈ realCube zone)
include hk hp
lemma genuine_alias (l : Site P.L) :
    let q := aliasAt p l
    rotor P.L k P.wing q * pilot k P p l=flux P 1 q * rotor 1 k P.land p ∧
      mirage P.L 1 q * wire k P p l=flux P 1 q * mirage 1 1 p ∧
      wire k P p l * pulse k P.land p * signal 1 1 p = pulse k P.wing q * signal P.L 1 q * pilot k P p l := by
  dsimp only
  by_cases he : p=0
  · subst p
    by_cases hl : l=0
    · subst l
      rw [show aliasAt (0:Momentum) (0:Site P.L)=0 from toe_zero P]; simp
    rw [pilot_none P k hl,wire_none P k hl]; simp
  rw [pilot_match k hk P hp he,wire_match k hk P hp he]; exact ⟨script_cross k hk P hp he l,script_dual k hk P hp he l⟩
lemma genuine_sum : (∑ l : Site P.L, hinges P 1 (aliasAt p l)*pilot k P p l)=1-(k:ℂ)⁻¹ • rotor 1 k P.land p := by
  by_cases he : p=0
  · subst p
    rw [Finset.sum_eq_single (0:Site P.L)]
    · rw [show aliasAt (0:Momentum) (0:Site P.L)=0 from toe_zero P]; simp
    · exact fun b _ hb => by rw [pilot_none P k hb]; simp
    simp
  simp_rw [pilot_match k hk P hp he]; exact script_main k hk P hp he
end Flight
end YM.Next.Free
