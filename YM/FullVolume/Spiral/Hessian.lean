import YM.FullVolume.Spiral.Neum
/- pre scaling simple bounds. saves `Harvest` across finite cap. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Paint.Tower
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus Next.Foundations Rank
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n m:Side}{Y:Hol G}
open MergeProof MergeProof.Matric FullVolume.Ray Jams Luna
variable {i:ℕ}{F:Labels.Frame G i}{B:BudgetPoint}{q t v a b s c u σ η ξ r:ℝ}{p:sun→ Coefficient F n}{P:Desk G n}{y:F.Coeff}
local notation "A_"=> P.orient
set_option maxHeartbeats 380000
open Forum
open Extra.Histories.InputColumn
open UniformSpace FullVolume.Amp
local notation "I"=> Extra.Histories.InputColumn.Listing
set_option maxRecDepth 3200
open Beam PaidBeam
variable (F)
def amplify (L:Side): F.Coeff≃ₗ[ℂ] F.Coeff where
   toFun := vowel F L
   invFun x j:= ((L.val:ℂ)^(i-(F.grades j).1))⁻¹*x j
   left_inv x:=by funext i; unfold vowel; dsimp only; rw [←mul_assoc,inv_mul_cancel₀,one_mul]; exact pow_ne_zero _ (by exact_mod_cast (Nat.one_le_iff_ne_zero.mp (show 1≤L.val from L.property)))
   right_inv x:=by funext i; unfold vowel; rw [←mul_assoc, mul_inv_cancel₀,one_mul]; exact pow_ne_zero _ (by exact_mod_cast (Nat.one_le_iff_ne_zero.mp (show 1≤L.val from L.property)))
   map_add' a b:=by funext i; simp [vowel,mul_add]
   map_smul' a b:=by funext i; simp [vowel]; ring
-- charges model
abbrev χ (F:Labels.Frame G i):ℝ:=(Fintype.card F.Index)
local notation "L_"=> χ F
lemma coreW (x:F.Coeff): F.coeffSize (F.core x)≤ χ F *‖x‖:=(Work.G08.size_core F x).trans (Size.le_norm F _)
lemma birthAxis (j:F.Index): ‖Size.axis F j‖≤1:= (Size.norm_le F _).trans (le_of_eq (Size.size_axis F j))
lemma pulseV (W:Side) (x:F.Coeff): ‖(amplify F W).symm x‖ ≤ ‖x‖:=by
   let y:=(amplify F W).symm x; have hp: vowel F W y=x:= (amplify F W).apply_symm_apply _; refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j=> ((show ‖y j‖≤‖x j‖ from ?_).trans (norm_le_pi_norm x _)); rw [← hp,vowel,norm_mul,Complex.norm_pow, Complex.norm_natCast]; apply le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ ?_); exact_mod_cast W.property
local notation "A!"=> orbitCost F
-- Beacon connection details.Pic numbers stage.positive rooms.
def chipMult := (Fintype.card (Motion.Tally F):ℝ)*‖(chips F).toContinuousLinearMap‖
lemma incomes (x:F.Coeff): chipPay F x ≤ chipMult F *‖x‖:=by
    let U:= (Motion.chips F).toContinuousLinearMap; calc
        _ ≤ ∑ i:Tally F, ‖U‖*‖x‖:=Finset.sum_le_sum fun i _=> (norm_le_pi_norm (U x) i).trans (U.le_opNorm x)
        _= _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,chipMult]; unfold U; exact (mul_assoc ..).symm
variable (L:Side)(T:sun→ F.Coeff≃ₗ[ℂ]F.Coeff)(E:Heading F)
local notation "φ"=> (s+1)
local notation "λ!"=> (s+1+(3+2*s))
local notation "ι"=> chipMult F
def revenue (F:Labels.Frame G i)(s η r:ℝ):= 4*((orbitCost F)*(orbitCost F)*(s+1)*η)*(χ F) +4*(orbitCost F*(s+1)*η*chipMult F)*(χ F *r)
def densityP (F:Labels.Frame G i)(s ξ u:ℝ):= 4*(ξ*orbitCost F*(s+1+(3+2*s))*u)*χ F
-- remain v1 outgoing μ⋅..
def heat (F:Labels.Frame G i)(s η u ξ r:ℝ):= densityP F s ξ u + 4*(ξ*(s+1+(3+2*s))*η*chipMult F)*(χ F*r)
local notation "ph"=> revenue F s η r
variable {s η u ξ r:ℝ}
local notation "p1" => revenue F s η r
local notation "p2"=> heat F s η u ξ r
local notation "X'"=> F.Coeff
-- iris absolute coefficient price hard.L^0. normalized x label pattern bound
structure Tilts (F: Labels.Frame G i) (L: Side)(T:sun→ F.Coeff≃ₗ[ℂ] F.Coeff)(E:Heading F)(s η r:ℝ):Prop where
   paid(x:F.Coeff):PaidBeam (fun t:sun=> T t x-E.leads L x) (4*(orbitCost F*orbitCost F*(s+1)*η*F.coeffSize (F.core x))+4*(orbitCost F*(s+1)*η*chipPay F x)* (χ F*r))
variable (hv:0≤ s)(hη:0≤η)(hr:0≤ r)(hξ:0≤ξ)(hu:0≤u)
include hv hη hr
lemma rune : 0≤ revenue F s η r:=by
  unfold revenue chipMult; have h:= orbitCost_one_le F; unfold χ; positivity
include hξ hu in
lemma mirageP : 0≤ heat F s η u ξ r:=by
   have h:= orbitCost_one_le F; unfold heat densityP chipMult χ; positivity
variable (he:Tilts F L T E s η r)
abbrev interactive (L:Side)(T:sun→ F.Coeff≃ₗ[ℂ] F.Coeff)(t:sun):= (amplify F L).symm.trans (T t)
local notation "τ"=> interactive F L T
include he
lemma slacks (x:F.Coeff):PaidBeam (fun t:sun=> τ t x-E.map x) ((revenue F s η r)*‖x‖):=by
   let y:=(amplify F L).symm x; have ha: vowel F L y=x:= (amplify F L).apply_symm_apply _
   have h1: F.coeffSize (F.core y) ≤ χ F*‖x‖:= (coreW F _).trans (mul_le_mul_of_nonneg_left (pulseV F L x) (Nat.cast_nonneg _)); have hz:0≤chipMult F:=by exact mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
   have h2:chipPay F y≤ chipMult F *‖x‖:= (incomes F _).trans (mul_le_mul_of_nonneg_left (pulseV F L x) hz)
   have hh:0 ≤ orbitCost F:=zero_le_one.trans (orbitCost_one_le F)
   have hs: E.leads L y= E.map x:=congr_arg E.map ha
   have hP:= he.paid y; rw [hs] at hP
   apply hP.larger; unfold revenue
   apply le_trans (add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ orbitCost F*orbitCost F*(s+1)*η)) (by norm_num: (0:ℝ)≤4)) (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (show 0≤orbitCost F*(s+1)*η by positivity)) (by norm_num)) (mul_nonneg (Nat.cast_nonneg _) hr))) (le_of_eq (by ring))
local notation "bf"=> (u*χ F)
variable (hb : ∀ x,F.coeffSize (E.map.symm x)≤u* F.coeffSize x) (hW:revenue F s η r*(u*χ F) ≤ 1/2)
include hb hW hu
lemma recA (p:sun→ F.Coeff)(hp:PaidBeam p a): PaidBeam (fun t:sun=>(τ t).symm (p t)) (2*(bf)*a):=by
    have h0:= rune F hv hη hr; have hq:Tally F →ℝ:= fun _=>1 -- not needed
    let g:sun→F.Coeff≃ₗ[ℝ]F.Coeff:= fun t=> (interactive F L T t).restrictScalars ℝ; let e:F.Coeff≃ₗ[ℝ] F.Coeff:=E.map.restrictScalars ℝ; have hx(x:F.Coeff): ‖e.symm x‖≤ bf *‖x‖:= (Size.norm_le F _).trans ((hb x).trans ((mul_le_mul_of_nonneg_left (Size.le_norm F x) hu).trans_eq (mul_assoc ..).symm))
    exact PaidBeam.origin g e h0 (mul_nonneg hu (Nat.cast_nonneg _)) hx hW (fun x=> slacks F L T E hv hη hr he x) hp
lemma recB (p:sun→ F.Coeff)(hp:PaidBeam p a): PaidBeam (fun t:sun=> (T t).symm (p t)) (2*(bf)*a):=by
   let y:= recA F L T E hv hη hr hu he hb hW p hp; have he:= transit _ (map_sub (amplify F L).symm) zero_le_one (fun i=>(pulseV F L i).trans_eq (one_mul _).symm) _ y
   rw [one_mul] at he; exact he.stamp (fun i=> show _=_ from ((amplify F L).symm_apply_apply _).symm)
section
variable (Y:Hol G){v:ℝ}{P:Desk G n}
local notation "K"=> MergeProof.Matric.Coin F Y P
variable (Q:sun→ Gram F Y P v)
variable (h:∀ x:F.Coeff,PaidBeam (fun i:sun=> ((((Q i).g) ((T i) x)):Completion (MergeProof.Matric.Coin F Y P))) (4*(ξ*orbitCost F*(s+1+(3+2*s))*u* F.coeffSize (vowel F L (F.core x)))+4*(ξ*(s+1+(3+2*s))*η*chipPay F x)*(χ F *r)))
include h hξ
lemma roses (x:F.Coeff): PaidBeam (fun i:sun=> (((Q i).g x):Completion (MergeProof.Matric.Coin F Y P))) ((heat F s η u ξ r)*(2*(u* χ F))*‖x‖):=by
   have hh : 0 ≤ orbitCost F:= zero_le_one.trans (orbitCost_one_le F); let f:sun → F.Coeff→ Completion (K):= fun i y=> ↑(((Q i).g) ((interactive F L T i) y)); have hR:=recA F L T E hv hη hr hu he hb hW _ (static x); let w:= heat F s η u ξ r
   have hu₀:0≤ w:=mirageP F hv hη hr hξ hu; let v(i:sun):= (interactive F L T i).symm x; have hx(x:F.Coeff):PaidBeam (fun i=> f i x) (w*‖x‖):=by
      let y:=(amplify F L).symm x; have hp: F.coeffSize (vowel F L (F.core y)) ≤ χ F * ‖x‖:=by rw [← Work.G08.core_vowel, show vowel F L y=x from (amplify F L).apply_symm_apply x]; exact coreW _ _
      have hz: chipPay F y ≤ chipMult F * ‖x‖:= (incomes F _).trans (mul_le_mul_of_nonneg_left (pulseV F L x) (show 0≤chipMult F by exact mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)))
      let c:=ξ*(s+1+(3+2*s))*η; refine (h y).larger ?_; unfold w heat densityP; apply le_trans (add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp (show 0≤ ξ*orbitCost F*(s+1+(3+2*s))*u by positivity)) (by norm_num)) (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hz (show 0≤ ξ*(s+1+(3+2*s))*η by positivity)) (by norm_num)) (mul_nonneg (Nat.cast_nonneg _) hr))) (le_of_eq (by ring))
   have hf(i) (x y:F.Coeff): f i (x-y)= f i x-f i y:=by unfold f; rw [map_sub,map_sub]; exact Completion.coe_sub ..
   apply PaidBeam.stamp (f:= fun i=> f i (v i)) ((field f hf hu₀ hx v hR).larger (le_of_eq (mul_assoc ..).symm)); intro i; unfold f v; rw [LinearEquiv.apply_symm_apply]
end
end YM.FullVolume.Paint.Tower
