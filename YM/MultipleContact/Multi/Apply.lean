import YM.MultipleContact.Multi.Positions
import YM.MultipleContact.Bunch.Corridor
/-! Cost of the finite comparator as a bounded quotient field, separately from the joint signed template. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
noncomputable section
namespace YM.MultipleContact.Joins
open Filter Set Function MeasureTheory Extraction Table Ward MergeProof Acme Ribbons Cells Next.UVStress Wilson Lattice Arbor
open Script Scene Bunching
open Accent Matching
open RG Bunching.Cord
open Drama ScheduleRow
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{S:Table C.book}{F:Extraction.Order}
variable {b n m:ℕ}[Inhabited (Fin n)]{V:Fin n → S.Tag}{D:Detector S b}
variable {P:DiffPlan S}(hA:Acme.Aroma C)(hT:Treasury C)(hc:CellHyp C F)(hM:F.PointLimits C S)(H:S.Hierarchy)(hP:P.Derivatives S)(hC:C.Makes)
variable {X:S.Rotation}(hX:X.Oriented S)(hG:G.Simple)
variable {ε:ℝ}(hε:0< ε) (L:Lattice.Side)
def relative (e:Exterior C.book):Points (e.n):=points (fun i:Fin e.n=>e.point i.succ-e.point 0)
private lemma maps_lands (x:Points m)(e:Exterior C.book): Points.across (e.point 0) (Bunching.lands x.ofLp (relative e))=YM.MultipleContact.joint e x:=by
         unfold YM.MultipleContact.joint relative Bunching.lands; ext1 i; refine Fin.addCases ?_ ?_ i
         · intro s; simp
         intro t; simp [Points.tail]
private lemma same_raw (hs : S.Homogeneous) {v:Fin n→ S.Tag} (y:Fin n→E4) (e:Exterior C.book){δ:ℝ}(hy:Injective y) (he': ∀i:Fin e.n,δ≤ ‖e.point i.succ - e.point 0‖)(hx:∀ i,‖y i‖<δ): raw S v (points y) e = many v e.letter y (relative e):=by
    have hu:=joint_clear e he' (points y) hx hy
    rw [← maps_lands] at hu
    have hh:lands y (relative e)∈conf _:=fun i j he=>hu (congr_arg (· + e.point 0) he)
    change S.useAt S _ _= S.useAt S _ _
    rw [← maps_lands]; exact (hs _ _ hh _ (fun i=>⟨(tagsPlaced v e i).1,S.representative _ (tagsPlaced v e i).2⟩)) -- _ hierarchy
def expand (L:Lattice.Side) (n:ℕ):Lattice.Side:=⟨L.val*(n+1),Nat.mul_pos L.pos n.succ_pos⟩
lemma spread {V:Fin m→E4}[Inhabited (Fin m)] {r:ℝ}(h:Band m L r V)(hr:0< r):Near m (expand L 31) (r/8) V:= by
      constructor
      · exact h.1
      refine ⟨fun i j hij=> (by nlinarith only [h.2.1 i j hij,hr]),?_⟩
      intro s
      change _ < 2 * ((L.val*32:ℕ):ℝ)*(r/8); push_cast; have hp:(0:ℝ)< (L.val:ℝ):=by exact_mod_cast L.pos
      nlinarith only [hr,h.2.2 s, mul_pos hp hr]
lemma expand_peer [Inhabited (Fin m)] {v:Fin m → E4}{r:ℝ} (h:Near m L r v)(hr:0<r):Near m (expand L 31) (r/8) v:=spread L ⟨h.1,(by intro a b hh; linarith only [hr,h.2.1 a b hh]),(by
      have hp:(1:ℝ) ≤ L.val:=by exact_mod_cast (Nat.succ_le_of_lt L.pos)
      intro i; nlinarith only [hr,h.2.2 i, mul_le_mul_of_nonneg_right hp hr.le])⟩ hr
include hA hT hC hG hc hP H hX hM hε
lemma apply_cost:
    let d':ℕ:= massOf V;∃ C' ρ₀:ℝ,0 < C' ∧ 0 < ρ₀ ∧ ∀ρ> (0:ℝ),ρ < ρ₀→ ∀y:Fin n→E4,Band n L ρ y → ‖D.apply V (points y)‖ ≤ C' * ρ^(-(d':ℝ)-ε):= by
       intro d'
       obtain ⟨δ,hδ,h⟩ := detector_clearance D
       let ι:= D.probes; let q (e:D.probes):Fin (e.val.n) → C.book.Token:=e.val.letter; let z (e:D.probes):Points (e.val.n):=relative e.val
       have hx (e:D.probes): Points.cons (0:E4) (z e)∈conf _:=by
           suffices hE: (fun i:Fin (e.val.n+1)=>Points.cons (0:E4) (z e) i)=fun i=>e.val.point i-e.val.point 0 by
                exact fun i j he=>e.val.clear (sub_left_injective (show (e.val.point i-e.val.point 0=e.val.point j-e.val.point 0) from (by rw [← congr_fun hE i,← congr_fun hE j];exact he)))
           funext i; exact Fin.cases (sub_self _).symm (fun i=>rfl) i
       let b:ℝ:= -(d':ℝ)-ε
       obtain ⟨r,hr,hnear⟩:= manyOrdinary hX q V (expand L 31) {z} isCompact_singleton (fun k h i=> (Set.mem_singleton_iff.mp h) ▸ hx i) hP H hM hc hC hA hT hG ε hε
       let l:= L.val; have hl:(0:ℝ)<(l:ℝ):=by exact_mod_cast L.pos
       let A':= (LinearMap.toContinuousLinearMap D.decode)
       let K:= (‖A'‖+1)*(1/8:ℝ)^b
       refine ⟨K,min r (δ/(l*4)),by unfold K;exact mul_pos (by linarith only [norm_nonneg A']) (Real.rpow_pos_of_pos (by norm_num) _), lt_min hr (by exact div_pos hδ (mul_pos hl (by norm_num))),fun ρ hρ h' y hy=>?_⟩
       have h₁(e:D.probes): ‖raw S V (points y) e.val‖ ≤ (ρ/8)^b:=by
            have he:= hnear z (mem_singleton _) (fun i:D.probes=>if i=e then (1:ℂ) else 0) (le_of_eq (by rw [Finset.sum_eq_single e]; all_goals first | (intro j _ hj'; simp [hj'])|simp)) (True.intro) (ρ/8) (by positivity) (by linarith only [(lt_min_iff.mp h').1,hρ]) y (spread L hy hρ)
            change ‖Bunching.blend q V (fun i=> if i=e then _ else _) z y‖ ≤ (ρ/8)^(-(d':ℝ)-ε) at he
            rw [same_raw H.translations y _ (fun i j he=>by by_contra hh; exact (hy.2.1 i j hh).not_ge (show ‖y i-y j‖≤ρ/16 from by rw [he,sub_self,norm_zero];exact div_nonneg hρ.le (by positivity))) (h e.val e.property)] -- replace
            · simpa [Bunching.blend,z,q] using! he
            intro i
            nlinarith only [(hy.2.2 i),show ρ*(l*4)<δ from (lt_div_iff₀ (by positivity : 0<(l:ℝ)*4)).mp (by simpa [mul_assoc] using (lt_min_iff.mp h').2),hδ]

       have he:(‖D.apply V (points y)‖:ℝ)=‖A' (fun i=>raw S V (points y) i.val)‖:=rfl
       apply he.trans_le ((A'.le_opNorm _).trans (mul_le_mul_of_nonneg_left ((pi_norm_le_iff_of_nonneg (by positivity)).mpr h₁) (norm_nonneg _)) |>.trans ?_) -- fix
       calc ‖A'‖ * (ρ/8)^b ≤ (‖A'‖+1)*(ρ/8:ℝ)^b:=mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (by positivity) _)
            _ = K*ρ^(-(d':ℝ)-ε):=by rw [show ρ/8=(1/8:ℝ)*ρ by ring, Real.mul_rpow (by norm_num) hρ.le];exact (mul_assoc ..).symm
end YM.MultipleContact.Joins
