import YM.Next.FOUNDATIONS.Readout
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Weights

/-!
# Readout from covariance of transfers

Even equality of densities on the SAME vacuum does *not by definition* give
an equality of `x` entries. (E.g. `Format.projects` says nothing on
wrapping supports; at such an address even holonomy tests of a transformed
regular part would require more reasoning.) Use exact covariance inputs at
the level of the regular **operations** of the chain. Here is one sufficient
cut: covariance term-by-term including indexing/support, before indicators.
These are inputs on the actual remainder tables. They do not mention the
x entries or assume Packet.Oriented. Even at this cut need a proof to extract
the x identities. No forced covariance inputs needed for this particular
cut; test via local holonomy at flat where the marked gas *necessarily*
contributes zero. Use true threshold (no derivatives across its boundary),
the stage's canonical Section for that family, standard star (not OS).
Neither construction of an equivariant algorithm for the physical estimates
nor a rank, uniqueness or retention claim is implicit in these hypotheses.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Equivariance
open Function Filter Labels Lattice Wilson RG Source MeasureTheory Next.Foundations Push.CutoffProjectors
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {n : Side} {d : ℕ} {F : Frame G d}

lemma offFlags (θ : ℝ) (hθ : 0 < θ) : ∀ᶠ U : Config G n in 𝓝 1, flags θ U = ∅ := by
  have hp (p : Face (Per n)) : ∀ᶠ U : Config G n in 𝓝 1, G.chord (faceValue U p) ≤ θ := by
    have he : Continuous fun U : Config G n => G.chord (faceValue U p) := by unfold faceValue; fun_prop
    have ht : G.chord (faceValue (1 : Config G n) p) = 0 := by simp [faceValue,square,travel]
    exact he.continuousAt (ge_mem_nhds (ht.trans_lt hθ))
  filter_upwards [eventually_all.mpr hp] with U hu
  ext i; simp only [flags_spec, Finset.notMem_empty, iff_false,not_exists,not_and,not_lt]; exact fun p _ => hu p

lemma tendsFlat (A : Hol G) (o : Site n) (d : ℕ) (J : Jet G) : Tendsto (A.testLinks d o J) (𝓝 0) (𝓝 1) := by
  have he : Tendsto (testLog A d o J) (𝓝 0) (𝓝 0) := by
    rw [← testLog_zero A d o J]; exact (testLog_diff ..).continuousAt.tendsto
  have hu : Tendsto (increment (1:Config G n)) (𝓝 0) (𝓝 1) := by
    simpa only [Work.G07.at_zero_increment] using
      (show Continuous (increment (1:Config G n)) by unfold increment; fun_prop).tendsto 0
  exact (hu.comp he).congr' (increment_testLog ..).symm

lemma unflagged {P : Coefficient F n} {R : Rep G n} {U : Config G n}
    (h : flags R.p.threshold U = ∅) (i : Finset ℕ) : P.marked R i U = 0 := by
  unfold Coefficient.marked; split
  · rename_i hh
    by_cases hi : i=∅
    · subst i; simp
    obtain ⟨j,hj⟩ := Finset.nonempty_iff_ne_empty.mpr hi
    obtain ⟨x,hx⟩ := (R.activities.forced j).inventory_ne
    have he : x ∈ flags R.p.threshold U := by rw [← hh.2]; exact Finset.mem_biUnion.mpr ⟨j,hj,hx⟩
    simp only [h,Finset.notMem_empty] at he
  rfl

lemma atCore (C : SectionData F) {A : Hol G} (hc : C.Sound A) (o : Site n) (t : ℝ)
    (v : F.Coeff) (U : Config G n) :
    v 0 + C.places (F.scaled t (F.core v)) o U = C.places (F.scaled t v) o U := by
  have he : v = F.core v + v 0 • F.e0 := by
    funext i; by_cases hi : i=0 <;> simp [Frame.core, Frame.e0, Function.update,hi]
  have hu : F.scaled t v = F.scaled t (F.core v) + v 0 • F.e0 := by
    nth_rw 1 [he]; rw [map_add,map_smul,F.scaled_unit]
  rw [hu]
  simp only [SectionData.places,C.eval_linear.map_add,C.eval_linear.map_smul,hc.unit]; simp [add_comm]

lemma noFlagEval {R : Rep G n} {U : Config G n} (h : flags R.p.threshold U = ∅) : (R.eval U : ℂ) ≠ 0 := by
  unfold Rep.eval; rw [Activities.gas_one _ _ h]
  exact Complex.ofReal_ne_zero.mpr (mul_pos (Real.exp_pos _) one_pos).ne'

lemma noFlagCharge (P : Coefficient F n) (o : Site n) (C : SectionData F) {A : Hol G} (hc : C.Sound A)
    {R : Rep G n} {U : Config G n} (h : flags R.p.threshold U = ∅) :
    P.density o C R U = R.eval U * (C.places (F.scaled R.p.threshold⁻¹ P.x) o U + ∑' i, P.regular i U) := by
  have he (B : Support n) : Healthy R.p.threshold B U := by unfold Healthy; rw [h]; simp
  unfold Coefficient.density Coefficient.exponentialEntry Coefficient.maskedTerm
  simp_rw [unflagged h, tsum_zero,mul_zero,add_zero,masked_eq _ _ _ _ (he _), atCore C hc]

/-- Finite-probe argument from actual local sections (including weight zero),
for any placement admitting that same stencil buffer. -/
lemma flat_inj (C : SectionData F) {A : Hol G} (hc : C.Sound A) (o : Site n)
    (hb : ∀ x ∈ C.stencil, ∀ i : Axis, 20*((x i).natAbs + 1) ≤ n.val)
    (u v : F.Coeff) (h : C.places u o =ᶠ[𝓝 (1:Config G n)] C.places v o) : u = v := by
  have he (x : F.Coeff) := placed_reads C o hb hc x
  simp only [Reads, if_pos (nonwrapping_placement C o hb)] at he
  apply F.coords.symm.injective
  refine jet_test_ext _ _ fun J k hk => ((he u J).2.2 k hk).symm.trans ?_
  have ht : (fun t => C.places u o (A.testLinks d o J t)) =ᶠ[𝓝 0] (fun t => C.places v o (A.testLinks d o J t)) :=
    (tendsFlat A o d J).eventually h
  exact (ht.iteratedDeriv_eq k).trans ((he v J).2.2 k hk)

/-- Exact upstream sufficient operations receipt (regular part).
Require termwise, even wrappings, keeping supports even for zero terms, as
in the obligation for label moves. Nothing about `x` here. -/
structure ListsAlong (s : Signed) (b : Site n) (Q Q' : Coefficient F n) where
  π : Equiv.Perm ℕ
  footprint (i) : Q'.support (π i) = (Q.support i).image (affine s b)
  term (i) (U) : Q'.regular (π i) U = Q.regular i (pull s b U)

/-- Ditto for ordinary conjugation of the regular part. -/
structure ListsReal (Q Q' : Coefficient F n) where
  π : Equiv.Perm ℕ
  footprint (i) : Q'.support (π i) = Q.support i
  term (i) (U) : Q'.regular (π i) U = star (Q.regular i U)

section Projection
variable (C : SectionData F) {A : Hol G} (hc : C.Sound A) (o : Site n)
    (hb : ∀ x ∈ C.stencil, ∀ i : Axis, 20*((x i).natAbs + 1) ≤ n.val)
include hc hb

lemma coord_at_pull (s : Signed) (b : Site n) {Q Q' : Coefficient F n}
    {R : Rep G n} (hR : R.eval ∘ pull s b = R.eval)
    (he : Q'.density (affine s b o) C R = Q.density o C R ∘ pull s b)
    (hL : ListsAlong s b Q Q') : Q'.x = turn F s Q.x := by
  let θ := R.p.threshold
  let t := affine s b o
  suffices hz : F.scaled θ⁻¹ Q'.x = F.scaled θ⁻¹ (turn F s Q.x) by
    exact (F.scaled_inv R.p.threshold_pos.ne' _).symm.trans ((congr_arg (F.scaled θ) hz).trans
      (F.scaled_inv R.p.threshold_pos.ne' _))
  have hp : Tendsto (pull s b (K:=G.El)) (𝓝 1) (𝓝 1) := by
    have hx : pull s b (1 : Config G n) = 1 := by funext i; simp [pull,Step.read]
    simpa only [hx] using (continuous_pull (G:=G) s b).tendsto 1
  refine flat_inj C hc t hb _ _ ?_
  filter_upwards [offFlags (G:=G) (n:=n) θ R.p.threshold_pos,hp.eventually (offFlags θ R.p.threshold_pos)] with U hu hV
  have hq := congr_fun he U
  rw [Function.comp_apply,noFlagCharge Q' _ _ hc hu,noFlagCharge Q o _ hc hV,
    show R.eval (pull s b U) = R.eval U from congr_fun hR U, C.placed_signed hc] at hq
  have hy := mul_left_cancel₀ (noFlagEval hu) hq
  conv_lhs at hy => rw [← hL.π.tsum_eq]
  simp_rw [hL.term] at hy
  rw [turn,F.scaling]; exact add_right_cancel hy

lemma coord_at_bar {Q Q' : Coefficient F n} {R : Rep G n}
    (he : Q'.density o C R = star (Q.density o C R)) (hL : ListsReal Q Q') : Q'.x = star Q.x := by
  let θ := R.p.threshold
  suffices hz : F.scaled θ⁻¹ Q'.x = F.scaled θ⁻¹ (star Q.x) by
    exact (F.scaled_inv R.p.threshold_pos.ne' _).symm.trans ((congr_arg (F.scaled θ) hz).trans
      (F.scaled_inv R.p.threshold_pos.ne' _))
  refine flat_inj C hc o hb _ _ ?_
  filter_upwards [offFlags (G:=G) (n:=n) θ R.p.threshold_pos] with U hu
  have hq := congr_fun he U
  rw [Pi.star_apply,noFlagCharge Q' o _ hc hu,noFlagCharge Q o _ hc hu,
    star_mul,star_add,tsum_star,show star (R.eval U : ℂ) = (R.eval U : ℂ) by simp] at hq
  change _ = _ * (R.eval U : ℂ) at hq
  rw [mul_comm _ (R.eval U : ℂ)] at hq
  have hy := mul_left_cancel₀ (noFlagEval hu) hq
  conv_lhs at hy => rw [← hL.π.tsum_eq]
  simp_rw [hL.term] at hy
  rw [scaled_bar,SectionData.places,SectionData.places,hc.ordinary_real]; exact add_right_cancel hy
end Projection
end YM.ProjectorNext.Equivariance
