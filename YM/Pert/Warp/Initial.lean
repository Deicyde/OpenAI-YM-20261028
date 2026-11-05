import YM.Pert.Warp.Engine
/-! Identification with the true order-zero coefficient of normalized orbital prescription, mark by mark, using Fubini only for finite Gaussian carriers. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 900000
set_option maxRecDepth 4000
noncomputable section
namespace YM.Pert.Warp
open Align Lattice Orb MeasureTheory ProbabilityTheory Function Full Labels Bare
open scoped Topology
variable {N : Side} {G : Gauge} {r d : ℕ} {I : Type*} [DecidableEq I] [Fintype I]
local notation "zeroOrder" => PowerSeries.constantCoeff (R:=ℂ)
variable (h : ℝ) (o : Grid N r) (tag : I → Fin r) (code : I → CosKey G d)
def root (s : Finset I) (a : Fin r) : Pol G := ∏ i∈s with tag i=a, MvPolynomial.X ((code i).val : Key G)

lemma normalize_zero (f : JetArray (Coords G N)) : zeroOrder (normalize f) = ∫ x,zeroOrder (f x) ∂data G N := by
  have hew := weight_flat (G:=G) (n:=N)
  have hev := vacuum_flat (G:=G) (n:=N)
  rw [Orb.normalize,map_mul,PowerSeries.constantCoeff_inv, expect,← PowerSeries.coeff_zero_eq_constantCoeff]; rw [PowerSeries.coeff_mk, PowerSeries.coeff_zero_eq_constantCoeff] at *; simp [map_mul,hew,hev]

-- height hypothesis enforced in code type. ink for key with high grade would not match full link.
lemma guest_x (x : Aux G d) (z : CosKey G d) : ink x z.val = Complex.I * (guest z x:ℝ) := by unfold ink; rw [dif_pos z.property];rfl
lemma pair_aeval (g : Site N) (x : Coords G N) (u : Aux G d) (z : CosKey G d) : zeroOrder (pairEval h g x u (MvPolynomial.X z.val)) = (strike (kField h g z.val) x : ℝ) + Complex.I * (guest z u:ℝ) := by
  unfold pairEval; rw [MvPolynomial.eval₂Hom_X',map_add,k_lin,PowerSeries.constantCoeff_C,guest_x,strike_eq]
lemma pair_leading (g : Site N) (x : Coords G N) (u : Aux G d) (S : Finset I) : zeroOrder (pairEval h g x u (∏ a∈S, MvPolynomial.X (code a).val)) =
    ∏ a∈S, (↑(firsthand h g (code a).val x) + Complex.I * ↑(guest (code a) u))  := by
  let ψ := MvPolynomial.eval₂Hom PowerSeries.C (fun (z : Key G)=> Bare.seriesLex h g x z + PowerSeries.C (ink u z))
  unfold pairEval; rw [(map_prod ψ (fun a:I=>MvPolynomial.X (code a).val)), map_prod zeroOrder]
  apply Finset.prod_congr rfl;intro a _; exact pair_aeval h g x u _
-- direct `pairEval` definitional evalHom
lemma post_zero (s : Finset I) (i : Fin r) (x) : zeroOrder (column d h (o i) (root tag code s i) x) = (∫ u : Aux G d, (∏ a∈s with tag a=i, flight (Coords G N) (Aux G d) i (firsthand h (o i) (code a).val) (guest (code a)) (x,fun _=>u)) ∂Full.auxLaw G d h) := by
  rw [auxiliary,avg, ←PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_mk]; simp only [PowerSeries.coeff_zero_eq_constantCoeff]; change (∫ z : Aux G d, _ ∂Full.auxLaw ..)=_
  exact integral_congr_ae (Filter.Eventually.of_forall fun z => pair_leading h code (o i) x z (Finset.filter _ s))
lemma joint_prod (s : Finset I) (z : Hall r (Coords G N) (Aux G d)) : (∏ i : Fin r, ∏ a ∈ s with tag a=i, node h o i (code a) (z.1,fun _=>z.2 i)) = ∏ a∈s, node h o (tag a) (code a) z := by
  rw [← Finset.prod_fiberwise s tag (fun a=>node h o (tag a) (code a) z)]
  refine Finset.prod_congr rfl (fun i _ => Finset.prod_congr rfl fun a ha => ?_)
  rw [(Finset.mem_filter.mp ha).2];rfl

lemma amplitude_zero (s : Finset I) : zeroOrder (amplitude (fun _=>d) h (Finset.univ (α:=Fin r)) o (root tag code s)) =
    kick (hall G N r d h) s (fun i=> node h o (tag i) (code i)) := by
  haveI _ := isLaw (G:=G) (n:=N)
  haveI _ := auxGaussian (G:=G) (d:=d) h
  haveI _ := hall_G G N r d h
  let M := hall G N r d h
  let v (i : I) := node h o (tag i) (code i)
  have hv := integral_prod (μ:=data G N) (ν:=Measure.pi (fun _ : Fin r=>auxLaw G d h)) (f:=fun z =>∏ i∈s,v i z) (price_tame M (prod_tame (fun i _=>Orb.Tame.clm (v i))))
  rw [amplitude,normalize_zero]; apply Eq.trans _ hv.symm
  apply integral_congr_ae (Filter.Eventually.of_forall fun x=>?_)
  rw [product,Finset.prod_apply,map_prod]
  let F (i : Fin r) (u) := ∏ a∈s with tag a=i, node h o i (code a) (x,fun _=>u)
  have hx (i) : zeroOrder (column d h (o i) ((root tag code) s i) x) = ∫ u, F i u ∂auxLaw G d h := post_zero ..
  have hi := integral_fintype_prod_eq_prod (μ:=fun _=>auxLaw G d h) F
  have ee (u : Fin r→ Aux G d) := joint_prod h o tag code s (x,u)
  convert! (Finset.prod_congr _ (fun i _=>hx i)).trans (hi.symm.trans _)
  exact rfl
  exact integral_congr_ae (Filter.Eventually.of_forall ee)
end YM.Pert.Warp
