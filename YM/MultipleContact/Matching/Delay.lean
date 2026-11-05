import YM.MultipleContact.Matching.Spacing
import YM.MergeProof.North.Bardo
import YM.Work.E09.Scales

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.MultipleContact.Matching
open Function Filter Lattice RG Supply Push Pressure Wilson Finset MeasureTheory Push.PriceCompiler
open Extra.Histories Extra.Trajectories Cells MergeProof MergeProof.Ribbons
open scoped Topology BigOperators Classical NNReal
open Asymptotics
variable {G:Gauge}
def Money (a:Levels G):Prop:= ∀ i, ((a.budget (i+1)).supportExponent+1/2)*(↑((2*extra a (a.S.block i) (i+1)+1)^4 :ℕ):ℝ) ≤  Real.sqrt (a.clock.hatBeta (i+1))
lemma warm (L:Side)(G:Gauge) :∀ᶠ x:ℝ in atTop, let y:= Pressure.betaF G x L; (1:ℝ)≤ Pressure.radiusB y:=by
    have ht := YM.Work.E09.betaF_growth G L
    filter_upwards [(Real.tendsto_log_atTop.comp ht).eventually_ge_atTop 1] with x hx
    simp only [comp_apply] at hx
    have hh:=Nat.le_ceil ((Real.log (betaF G x L))^ (2:ℕ)); exact le_trans (by nlinarith : (1:ℝ) ≤ (Real.log (betaF G x L))^2) hh
lemma enlarge (L:Side)(G:Gauge) (n:ℝ) :∀ᶠ x:ℝ in atTop, let y:= betaF G x L; n*↑((2*(1024*L.val*radiusB y)+1)^4 :ℕ) ≤ Real.sqrt y:=by
    have hw:= ((YM.Work.E09.radiusB_small (1/2) one_half_pos 4 |>.comp_tendsto (YM.Work.E09.betaF_growth G L)).const_mul_left (max n 1 * (2049*(L.val:ℝ))^(4:ℕ))).def (show (0:ℝ)<1 by exact zero_lt_one)
    have h: (0:ℝ)<(L.val:ℝ) :=by exact_mod_cast L.pos
    filter_upwards [hw,warm L G,(YM.Work.E09.betaF_growth G L).eventually (eventually_gt_atTop 0)] with x hx hB hY
    simp only [comp_apply,Real.norm_of_nonneg ((Real.rpow_pos_of_pos hY (1/2)).le),one_mul] at hx
    rw [Real.norm_of_nonneg (by positivity), ← Real.sqrt_eq_rpow] at hx
    change 0 < betaF G x L at hY; push_cast
    apply le_trans ?_ hx; have hu:=le_max_left n 1; let B:=radiusB (betaF G x L)
    calc _ ≤ max n 1 * (((2049:ℝ)*L.val* B)^ (4:ℕ)):= mul_le_mul hu (pow_le_pow_left₀ (by positivity) (by have h := mul_le_mul (show (1:ℝ) ≤ L.val by exact_mod_cast L.pos) hB zero_le_one (by positivity); change _ ≤ _* _; linarith) _) (by positivity) (by have hh:=le_max_right n (1:ℝ); positivity)
         _ = _ := by rw [mul_pow]; exact (mul_assoc ..).symm

lemma delay {M:Sheet G} {P:Rolls M} {θ:Protection P} (Z:Delays θ):∃ T₀:Delays θ, DelayLe Z T₀ ∧ ∀ T:Delays θ, DelayLe T₀ T→ ∀ (D:Bar T) (W:Wait D) (a:Levels G), Paid W a→Money a:=by
    let d j:= (M.profile j).supportExponent+1/2
    let L j:= P.L j
    let Q j (x:ℝ):Prop:=d j*↑((2*(1024*(L j).val*radiusB (betaF G x (L j)))+1)^4:ℕ) ≤ Real.sqrt (betaF G x (L j))
    choose r h h' hv using collect_upper Z.betaEntry Q (fun j=>enlarge ..)
    refine ⟨{Z with betaEntry:=r},⟨h',le_rfl,le_rfl,le_rfl⟩,fun T hT D W a ha i=>?_⟩
    let j:= a.clock.J (i+1); have he: Q j (a.clock.hatBeta i):=hv _ _ ((hT.beta j).trans (ha.pays i))
    have hβ:a.clock.hatBeta (i+1)= Pressure.betaF G (a.clock.hatBeta i) (P.L j):= by rw [Extra.Iteration.block_beta,Extra.Iteration.block_eq ha i]
    have hp:= params_eq ha (i+1)
    change ((a.budget (i+1)).supportExponent+1/2:ℝ)*(↑((2*extra a (a.S.block i) (i+1)+1)^4 :ℕ) :ℝ) ≤ _
    rw [show ((a.budget (i+1)).supportExponent:ℝ)+1/2=d j from congr_arg (fun q=>Stage.supportExponent q+1/2) hp]
    unfold extra; rw [show (a.budget (i+1)).B= radiusB (a.clock.hatBeta (i+1)) from rfl,hβ,Extra.Iteration.block_eq ha i]; exact he
end YM.MultipleContact.Matching
