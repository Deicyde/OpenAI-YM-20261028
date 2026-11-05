import YM.FullVolume.Nectar.Laid
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Nectar
open RG Set Finset Filter Ray Function PhysicalNext.Repeat PhysicalNext.Repeat.Luna.Aank Paint.Tower Amp Beam
open scoped Topology BigOperators Classical ENNReal
open MergeProof MergeProof.Accent Marker Push Push.AbsoluteSums Lattice Wilson
-- valuation preserving for actual α. published Cup form. Pattern stake.Active. Ignore if all-zero.Caps.T across sites. Kernel quiet additional contour if z occupancy. construct separately NOT globally via y same.L.Core.Gloom.
variable {V I:Type}[DecidableEq V] [Fintype V] [Fintype I]{B:Marker.Census V}{G:Gauge}{b:Side}
variable {F:sun→I→ Config G b→Poly B}{S:I→Support b}{p q v t:ℝ}{a:ℕ}{w:V→ℝ}
    {k:Finset B.Mode}{x: V→ Site b}(hw:∀ i,0<w i)
local notation "Ω"=> Config G b
-- stronger exact split.Paid.B.Values all.
include hw
set_option maxHeartbeats 360000 in
lemma curvatureH (h:∀ s:sun, Glacier.Bagged (organs S w k x a p (F s)))(ht:PaidBeam (fun s=>Glacial.fold (Luna.Aank.curtain S w k x a p (F s))) v)(hX:∀ s i,Borne x (S i) (F s i) t)(hp:∀ i∈k,i≠ B.quiet):∃ c:I× ↑k→ℝ, ∑ i:I × ↑k, Real.exp (p*coverNumber a (S i.1))* Poly.toll w i.2.val*c i ≤ v ∧ ∀ i:I× ↑k,Feel (fun s u=>(F s i.1 u).part i.2.val) (c i):=by
    let H(s:sun):= Glacial.fold (Luna.Aank.curtain S w k x a p (F s));let Φ(s:sun):= organs S w k x a p (F s)
    have hr(i:I × B.Mode)(y u):Glacial.evalP ℂ i u (H y)= Φ y i u:=Glacier.unity _ (h y) i u
    obtain ⟨f,hf,hF⟩:= Feel.factored Φ H ht hr
    let e:I× ↑k→ I × B.Mode:= fun i=>(i.1,i.2.val)
    have hi:Injective e:= by intro i j hp; rcases i with ⟨i,l⟩; rcases j with ⟨j,v⟩; exact Prod.ext (show i=j from congr_arg (fun i:I×B.Mode=>i.1) hp) (Subtype.ext (show l.val=v.val from congr_arg (fun i:I×B.Mode=>i.2) hp))
    let a' (i:I× ↥k) := Real.exp (p*coverNumber a (S i.1))*Poly.toll w i.2.val; have hz i:0<a' i:=mul_pos (Real.exp_pos _) (Poly.worth hw _)
    let C i:= (a' i)⁻¹ * f (e i); refine ⟨C,?_,fun i=>?_⟩
    · change ∑ i,a' i*C i ≤ _;unfold C; simp_rw [fun i (x:ℝ) => mul_inv_cancel_left₀ (hz i).ne' x]; rw [← Finset.sum_image hi.injOn]; exact (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _=> (hF i).positives)).trans hf
    have hh := (hF (e i)).scales (a' i)⁻¹
    rw [abs_of_pos (inv_pos.mpr (hz i))] at hh
    apply Eq.mp (congr_arg (fun f=> Feel f (C i)) (funext fun s=> funext fun z=> ?_)) hh
    change (a' i)⁻¹ • Φ s (e i) z = _
    unfold Φ e organs; by_cases ht: Luna.Aank.orbit (S i.1) x -- not open Aank
    · rw [if_pos ⟨i.2.property,ht⟩]; exact inv_smul_smul₀ (hz i).ne' _
    have hb: (F s i.1 z).part i.2.val=0:=by
       by_contra hn
       have hh:= Borne.place (hX s i.1) i.2.val z hn
       have hx:= hp _ i.2.property
       obtain ⟨j,hj⟩:= Finset.nonempty_iff_ne_empty.mpr (show i.2.val.val ≠∅ from fun h=> hx (Subtype.ext h)); exact ht ⟨j, hh (mem_image_of_mem _ hj)⟩
    rw [if_neg (fun h=>ht h.2), smul_zero]; exact hb.symm
omit hw
lemma balanceH {x:B.Mode}{B':BudgetPoint}(h:∀ i,Glacier.Bagged (Luna.Aank.bright S B' x p (F i)))(ht: PaidBeam (fun t:sun=> Glacial.fold (shout S B' x p (F t))) v):∃ c:I→ℝ, ∑ i:I, Real.exp (p*coverNumber B'.B (S i))*c i≤ v∧∀ i,Feel (fun s u=> (F s i u).part x) (c i):=by
    obtain ⟨f,hf,hY⟩:= Feel.factored _ _ ht (fun i y u=> show Glacial.evalP ℂ i u _= _ from (show _=Luna.Aank.bright S B' x p (F y) i u from Glacier.unity _ (h _) _ _));
    let a i:= Real.exp (p * coverNumber B'.B (S i)); have he i:0<a i:= Real.exp_pos _
    let c i:= (a i)⁻¹*f i
    refine ⟨c,?_,fun i=>?_⟩; change ∑ i,a i*((a i)⁻¹*f i)≤_;simp_rw [fun i => mul_inv_cancel_left₀ (he i).ne' (f i)]; exact hf
    have hh:= (hY i).scales (a i)⁻¹; rw [abs_of_pos (inv_pos.mpr (he i))] at hh
    apply Eq.mp (congr_arg (fun f=> Feel f (c i)) (funext fun s=> funext fun z=> ?_)) hh
    exact inv_smul_smul₀ (he i).ne' _
end YM.FullVolume.Nectar
