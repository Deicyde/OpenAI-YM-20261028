import YM.Pert.Warp.Shards
/-! Delete distinguishable bare-linear legs until there are no legs. -/
noncomputable section
namespace YM.Pert.Warp
open Align Lattice Orb MeasureTheory ProbabilityTheory Maxwell Function Full Labels Bare Wick Filter Topology
open scoped Topology
variable {N : Side} {G : Gauge} {r d : ℕ} {I : Type*} [DecidableEq I] [Fintype I]
variable (T : Itinerary) (o : ∀i,Grid (T.period i) r) (z : Points r) (tag : I → Fin r) (code : I → CosKey G d)
local notation "zeroOrder" => PowerSeries.constantCoeff (R:=ℂ)

def eqPrice (s : Finset I) (i : ℕ) := zeroOrder ((amplitude (fun _ : Fin r=>d) (T.gap i) Finset.univ) (o i) (root tag code s))
lemma eq_cancel (s : Finset I) (i : ℕ) : s.card • eqPrice T o tag code s i = ∑ a∈s,∑ b∈s.erase a,
   (corrected (T.gap i) (o i) (tag a) (tag b) (code a).val (code b).val : ℝ) * eqPrice T o tag code ((s.erase a).erase b) i := by
  let M : Measure (Hall r (Coords G _) (Aux G d)) := hall G (T.period i) r d (T.gap i)
  haveI : IsGaussian M := hall_G G (T.period i) r d (T.gap i)
  let v a := node (T.gap i) (o i) (tag a) (code a)
  unfold eqPrice; simp_rw [amplitude_zero]
  simp_rw [← node_wage]; exact exchange_s M s v (fun k _ => node_center ..)
lemma earth (hz : z∈conf r) (ho : ∀ j, Home T (fun i=>o i j) (z j)) (ht : ∀ i,4∣(T.period i).val) (s : Finset I) :
    Tendsto (eqPrice T o tag code s) atTop (𝓝 (cut z tag code s)) := by
  induction s using Finset.strongInduction with | H s ih =>
    by_cases hs : s.Nonempty
    · have hi := Finset.card_pos.mpr hs; have hne : (s.card:ℂ)≠0:= by exact_mod_cast Nat.ne_of_gt hi
      have h (a:I) (_:a∈s) (b:I) (_:b∈s.erase a) := ih ((s.erase a).erase b) (lt_of_le_of_lt   (Finset.erase_subset _ _) (Finset.erase_ssubset (by assumption)))
      -- `β` argument not
      have he (a b:I) : Tendsto (fun i:ℕ=> (((corrected (T.gap i) (o i) (tag a) (tag b) (code a).val (code b).val:ℝ):ℂ))) atTop (𝓝 ((indirect z (tag a) (tag b) (code a).val (code b).val:ℝ):ℂ)) := Complex.continuous_ofReal.continuousAt.tendsto.comp (corrected_limit T o z hz ho ht _ _ ..)
      let f(v:ℕ) := eqPrice T o tag code s v
      have H : Tendsto (fun i=>s.card • eqPrice T o tag code s i) atTop (𝓝 (s.card • cut z tag code s)) := by simp_rw [cut_cancel z tag code hz s, eq_cancel]; apply tendsto_finsetSum s; intros a ha; apply tendsto_finsetSum _;intro b hb; exact ((he a b).mul (h a ha b hb))
      have H := H.const_mul ((s.card:ℂ)⁻¹); simpa only [nsmul_eq_mul,inv_mul_cancel_left₀ hne] using H
    · rw [Finset.not_nonempty_iff_eq_empty.mp hs]; have hi (i): (mixed (data G (T.period i)) (Full.auxLaw G d (T.gap i)) r).real Set.univ=1 := by unfold mixed; exact probReal_univ
      unfold eqPrice
      simpa only [cut, amplitude_zero, kick, Finset.prod_empty, hall, hi, integral_const, one_smul,spline,root,Finset.filter_empty,comp_def, map_one,constants] using! (tendsto_const_nhds (f:=atTop) (x:=1)) -- no IsProbability? instances

set_option autoImplicit false
variable (d) (h : ℝ)
def bodies (o : Grid N r) := (MultilinearMap.mkPiAlgebra ℂ (Fin r) (Phi G N)).compLinearMap (fun i=>columnMap d h (o i))
-- Full.space is readiness
def recipe (o : Grid N r) := (vacuumMap G N).compMultilinearMap (bodies (G:=G) d h o |>.codRestrict (Full.space G N) (fun p=>show Ready _ from product_ready (fun _=>d) h Finset.univ o p))
lemma recipe_at (o :Grid N r) (p : Fin r→Pol G) : recipe d h o p=amplitude (fun _=>d) h Finset.univ o p := rfl
end YM.Pert.Warp
