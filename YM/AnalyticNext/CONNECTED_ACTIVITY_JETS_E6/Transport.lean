import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Carrier
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Compression

/-!
# Local comparison for the transported stencil rows

Regardless of V outside the lookup. For matrix/spectral estimates use
also single-impulse entry price (color orientation can be arbitrary).
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.SliceRows
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f} {T : Tube G S}
variable {P : Teller G} (hP : P.Funds S T) {C h : ℝ} (hC : 0 < C) (hX : Bounded T P.top.width C)

lemma transport_cost (x y : Site c) (V : Config G c) (h : ℝ) (hh : 0 ≤ h) (B : ℕ) (he : 4*separation x y ≤ B)
    (hx : ∀ e : Bond c, separation x e.1 ≤ B → G.chord (V e) ≤ h) : G.chord (carrier x V y) ≤ B*h := by
  let W (e : Bond c) : G.El := if separation x e.1 ≤ B then V e else 1
  have hv : AgreeNear id x B V W := fun e hi => Eq.symm (if_pos hi)
  rw [carrier_near x y V W B hv he]
  have hw i : G.chord (W i) ≤ h := by
    unfold W; split
    next ht => exact hx i ht
    next ht => rwa [G.chord_one]
  exact (travel_chord W (carriage ..) x h hw).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast (mileage x y).trans he) hh)

include hP hC hX in
lemma comparison (p : Rod c f) (R : ℕ) (u v : Directions G f) {M : ℝ} (hm : 0 ≤ M)
    (h : ∀ i : Bond f, distAt S i (focus S p) ≤ R+predReach S.patch+4 → ‖u i-v i‖ ≤ M) :
    ‖barField T R u p-barField T R v p‖ ≤ C*M := by
  let a i := if distAt S i (focus S p) ≤ R+predReach S.patch+4 then u i-v i else 0
  have he : barField T R u p=barField T R (a+v) p := by
    apply tangent_local T (SectorMeasure.funds_branch hP)
    intro i hi; rw [Pi.add_apply,show a i=u i-v i from if_pos hi,sub_add_cancel]
  have ha : ‖a‖ ≤ M := (pi_norm_le_iff_of_nonneg hm).mpr (by
    intro i; unfold a; split
    next he => exact h i he
    next he => rwa [norm_zero])
  obtain ⟨d,e,H,-⟩ := hP.feeds
  rw [he,bar_add T H,add_sub_cancel_right]
  exact (hX.short a ..).trans (mul_le_mul_of_nonneg_left ha hC.le)

include hP hC hX in
lemma near_base (V : Config G c) (p : Rod c f) (R d : ℕ) (u : Directions G f)
    (he : 4*(R+predReach S.patch+4) ≤ d) {M : ℝ} (hm : 0 ≤ M) (hh : 0 ≤ h)
    (hh' : ∀ i : Bond c, separation (focus S p) i.1 ≤ d → G.chord (V i) ≤ h)
    (hs : ∀ i : Bond f, distAt S i (focus S p) ≤ R+predReach S.patch+4 → ‖u i‖ ≤ M) :
    ‖straightened T R V u p-barField T R u p‖ ≤ C*(2*G.colorScale*(d*h)*M) := by
  have ht := G.colorScale_pos
  refine comparison hP hC hX _ _ _ _ (by positivity) ?_
  intro i hi
  apply (adjoint_norm_sub (carrier (focus S p) V (atEdge S i)) (u i)).trans
  have ho := transport_cost (focus S p) (atEdge S i) V _ hh d ((Nat.mul_le_mul_left 4 hi).trans he) hh'
  gcongr; exact hs i hi

lemma spin_bounded (S : StepData c f) (z : Site c → G.El) (v : Directions G f) : ‖spinRow S z v‖ ≤ ‖v‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr; intro i
  rw [spinRow,G.norm_adjoint]; exact norm_le_pi_norm ..

lemma displacement_bounded (s : Signed) (W : Config G f) (u : Directions G f) : ‖displacement s u W‖ ≤ ‖u‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr; intro i
  rw [size_displacement]; exact norm_le_pi_norm ..

include hX hC in
lemma straightened_cap (V : Config G c) (p : Rod c f) (R : ℕ) (u : Directions G f) :
    ‖straightened T R V u p‖ ≤ C*‖u‖ := (hX.short _ _ _).trans (mul_le_mul_of_nonneg_left (spin_bounded ..) hC.le)

include hX hC in
lemma oriented_cap (V : Config G c) (s : Signed) (p : Rod c f) (R : ℕ) (u : Directions G f) :
    ‖orientedRow T R s p V u‖ ≤ C*‖u‖ := (straightened_cap hC hX _ _ _ _).trans
      (mul_le_mul_of_nonneg_left (displacement_bounded ..) hC.le)

lemma pull_near_small (V : Config G c) (s : Signed) (o : Site c) (d : ℕ) {h : ℝ}
    (hv : ∀ i : Bond c, separation (s.act o) i.1 ≤ d+1 → G.chord (V i) ≤ h) :
    ∀ i : Bond c, separation o i.1 ≤ d → G.chord (pull s 0 V i) ≤ h := by
  intro i hi
  have he := hv (edge s i) (le_trans (projected_wealth s i o) (by omega))
  rw [charge]; split
  · rwa [G.chord_inv]
  exact he

include hX hC hP in
/-- At coordinate far enough to keep a V hull. Compare to the row at
flat V in that gauge. Don't multiply this cost by volume to claim the
spectrum is close. Also handy when corrections turn inverse links. -/
lemma spinning (V : Config G c) (R d : ℕ) (s : Signed) (p : Rod c f) {M : ℝ} (hm : 0 ≤ M) (u : Directions G f)
    (hu : ∀ i : Bond f, distAt S i (s.act (focus S p)) ≤ d+1 → ‖u i‖ ≤ M)
    (he : 4*(R+predReach S.patch+4) ≤ d) {h : ℝ} (hh : 0 ≤ h)
    (hv : ∀ i : Bond c, separation (s.act (focus S p)) i.1 ≤ d+1 → G.chord (V i) ≤ h) :
    ‖orientedRow T R s p V u-orientedRow T R s p 1 u‖ ≤ C*(2*G.colorScale*((d:ℝ)+1)*h*M) := by
  let A := displacement s u (replica S.ratio V)
  let B := displacement s u (1:Config G f)
  have hA : orientedRow T R s p V u = straightened T R (pull s 0 V) A p := rfl
  have hB : orientedRow T R s p 1 u = barField T R B p := by
    unfold orientedRow; rw [replica_one]
    have H : pull s 0 (1:Config G c) = 1 := by funext i; rw [charge]; simp
    rw [H,flat_strip]
  have hz j (H : distAt S j (focus S p)≤R+predReach S.patch+4) :
      ‖A j‖≤M ∧ ‖A j-B j‖ ≤ 2*G.colorScale*h*M := by
    have hl : distAt S (edge s j) (s.act (focus S p)) ≤ d+1 := (projects S s _ _).trans (by omega)
    have h' : G.chord (replica S.ratio V (edge s j)) ≤ h := by
      unfold replica; split
      next hx => rwa [G.chord_one]
      exact hv _ hl
    refine ⟨(size_displacement ..).trans_le (hu _ hl),?_⟩
    unfold A B; dsimp only [displacement]; split
    next hx =>
      simp only [Pi.one_apply, inv_one,G.adjoint_one, neg_sub_neg,norm_sub_rev (u _)]
      apply (adjoint_norm_sub ..).trans; rw [G.chord_inv]; have := G.colorScale_pos; gcongr
      exact hu _ hl
    next hx => rw [sub_self,norm_zero]; have := G.colorScale_pos; positivity
  have ht := near_base hP hC hX (pull s 0 V) p R d A he hm hh (pull_near_small V s _ d hv) (fun i hi => (hz i hi).1)
  have hp := comparison hP hC hX p R A B (by have := G.colorScale_pos; positivity) (fun i hi => (hz i hi).2)
  rw [hA,hB]; exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans ((add_le_add ht hp).trans_eq (by ring))

include hP hC hX in
lemma transported_impulse (V : Config G c) (s : Signed) (p : Rod c f) (R : ℕ) (i : Bond f) (b : G.Color) :
    Real.exp (P.top.width*distAt S i (s.act (focus S p))) * ‖orientedRow T R s p V (Pi.single i b)‖ ≤
       (2*C*Real.exp (P.top.width*(predReach S.patch+7:ℝ))) * ‖b‖ := by
  obtain ⟨i,rfl⟩ := (StepData.sendBonds s 0).surjective i
  let v : Directions G f := Pi.single (edge s i) b
  let o := focus S p
  let w := P.top.width
  let Z := spinRow S (carrier o (pull s 0 V)) (displacement s v (replica S.ratio V))
  have he : Z=Pi.single i (Z i) := by
    funext j; by_cases h : j=i
    · subst j; rw [Pi.single_eq_same]
    have hp : edge s j ≠ edge s i := sendEdge_injective s 0 |>.ne h
    have hh : ‖Z j‖=0 := by
      dsimp only [Z,spinRow]
      rw [G.norm_adjoint,size_displacement]; unfold v; rw [Pi.single_eq_of_ne hp,norm_zero]
    rw [Pi.single_eq_of_ne h]; exact norm_eq_zero.mp hh
  have e : ‖Z i‖=‖b‖ := by unfold Z spinRow; rw [G.norm_adjoint,size_displacement]; unfold v; rw [Pi.single_eq_same]
  have ht := input_decays hP hC hX p i (Z i) R
  rw [← he,e] at ht
  change Real.exp (w*distAt S (edge s i) _)*‖barField T R Z p‖ ≤ _
  calc
    _ ≤ (Real.exp w*Real.exp (w*distAt S i o)) * ‖barField T R Z p‖ := by
      have hp : (distAt S (edge s i) (s.act o):ℝ) ≤ distAt S i o + 1 := by exact_mod_cast projects S s o i
      have hs : 0 ≤ w := P.top.width_pos.le
      rw [← Real.exp_add]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply Real.exp_monotone; nlinarith
    _ ≤ Real.exp w*((2*C*Real.exp (P.top.width*(predReach S.patch+6:ℝ)))*‖b‖) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left ht (Real.exp_pos _).le
    _ = _ := by
      unfold w
      rw [show P.top.width*(predReach S.patch+7:ℝ)=P.top.width+P.top.width*(predReach S.patch+6:ℝ) by ring,
        Real.exp_add]; ring
end YM.ConnectedActivityE6.SliceRows
