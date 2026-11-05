import YM.MergeProof.Canopy
import YM.Next.UV_STRESS.Toward

set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Function Filter Set MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Guard Next.Foundations Local Next.Rank Edition Spindle Extra.Multi Motion
open PhysicalNext.Repeat.Legato.Bandage Cells Extraction Extraction.Lease Exponential Bid Next.Extract RelayDifference Opening
open Labels
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}(H:C.Makes)(B:Stock.Tabs C.path.levels)
variable {f:Extraction.Order}{N p d:ℕ}(V:SectionData (C.labels.level d))(hV:V.Sound C.params)
    {ζ:ℕ→ℕ→ℝ}{E:ℕ→ℝ}{P:ℕ→ℕ→(C.label d≃ₗ[ℂ] C.label d)}{U:ℕ→ℕ→(C.labels.level d).Index→ C.label d}
    (h:Hearth V ζ E P U)
set_option quotPrecheck false
local notation "F"=> C.labels.level d
local notation "T"=> C.localSection d
local notation "Φ"=> C.path
local notation "s'"=> (Size.axis (C.labels.level d))
local notation "ρ"=> Motion.Tally (C.labels.level d)
-- ADDS real marks.Generacy.V.X.L bridge at all translated origins. Need common α for commit P.after.Define Lit second.Pass.
def hallmarks (V:SectionData (C.labels.level d)) (W:Rowe C d):Trial C:=fun i j=> initial V C.path i j (W (i,j))
include hV
lemma region (x:Rowe C d): Stencilled f (hallmarks V x):= by
    refine ⟨V.stencil,Eventually.of_forall (fun i=> ?_)⟩
    let a:=x i 
    refine ⟨fun o b=> ?_, fun o=>?_⟩
    · unfold hallmarks initial; funext U; simp
    unfold hallmarks initial; apply Interior.scale; let u:= (F).scaled (C.path.levels.budget i.1).threshold⁻¹ a; exact ⟨V.placed_invariant hV o _,(V.continuous_places u _).measurable,V.placed_local o _,(V.continuous_places u _).bounded_above_of_compact_support (HasCompactSupport.of_compactSpace _)⟩
set_option maxRecDepth 8000 in
omit hV in
private lemma decor_at (Fr:Labels.Frame G d)(v:Fr.Index→Fr.Coeff) (x:Fr.Coeff) : decor Fr v x=repaint Fr v x:=by
    simp only [decor, LinearMap.coe_mk, AddHom.coe_mk]
-- paint P origins via Mark.Correct triangles
variable (x : Rowe C d)
local notation "Y"=> (fun j:Cutoffs=> (C.factory d j.1 j.2).terminal ((P j.1 j.2) (x j)))
include h B H
-- exact relation to P.Number.Y proof l.Tally. no deriving arbitrary G all m same Dir.Extensors.
set_option maxRecDepth 4000 in
lemma embark (he:Slow C f x): Bid.close C f (upper C Y - hallmarks V x):=by
    let Q (a:ρ) := hallmarks T (fun j=> Motion.patch F a.1 (U j.1 j.2 a.2)) - hallmarks V (fun j=> Motion.patch F a.1 (s' a.2)); let S(a:ρ)(j:Cutoffs):=Motion.chips F (x j) a
    have ht(a:ρ):CenterRents (Q a) (flight C (-(1/16))) f:=by
       apply rotates B (ζ:=ζ) (h.coined f) ((region T (H.sections d) _).sub (region V hV _)) d
       filter_upwards [(cutoff_grows f).eventually h.stamped] with i hi m k hm hk hx hu
       let b:=U i.1 i.2 a.2; let g:=a.1; let A(i'):=(initial V Φ i.1 i.2 i' 0); let f(i'):=(initial T Φ i.1 i.2 i' 0); let O:= center C.S i.2 hu 0; let M := C.beta i.1 i.2
       have hp:= (hi i.2).2.2 a.2 k m hm hk hx g hu
       change O.rootTest M (f (Motion.patch F g b) - A (Motion.patch F g (s' a.2))) ≤ _; apply le_trans ?_ hp; apply le_of_eq; rw [unitsC,_root_.neg_sub]; rw [show dance g (initial V C.path i.1 i.2 (s' a.2) 0-initial T C.path i.1 i.2 b 0) = A (Motion.patch F g (s' a.2)) - f (Motion.patch F g b) from ?_]
       rw [show dance g (A (s' a.2)-f b)=dance g (A (s' a.2))-dance g (f b) from funext fun U=>by unfold dance scalar;split <;>simp]; rw [signed_intro C V hV, signed_intro C T (H.sections d)]
    have hr(j:ρ):Slow C f (S j):=by
       let a:= Motion.share* orbitCost F; have hp:= (Slow.const (C:=C) a).mul (coords_slow x he); refine hp.reduce (Eventually.of_forall fun i=> ?_)
       rw [show S j i=chips F (x i) j from rfl,norm_chips]; exact (mul_le_mul_of_nonneg_left ((BasisCost.coord_le _ _).trans (patch_cost ..)) share_pos.le).trans (le_trans (le_of_eq (mul_assoc _ _ _).symm) (Real.le_norm_self _))
    apply close_change (gather_close H Q S hr (1/16) (by norm_num) ht); apply (Order.fused f (fun i=> gathered Q S i.1 i.2 = (upper C Y-hallmarks V x) i.1 i.2)).mp; filter_upwards [(cutoff_grows f).eventually h.stamped] with i hi
    funext b
    let T0 := P i.1 i.2; let J:ρ→ℂ:= fun s=> S s i; let g (u):= initial V C.path i.1 i.2 u b
    let F' u:=initial T C.path i.1 i.2 u b
    have hx: IsLinearMap ℂ g:= notationL C.path d _ V i.1 i.2 b; have hF:IsLinearMap ℂ F':= notationL C.path d _ T i.1 i.2 b; let f:= IsLinearMap.mk' _ hx; let x':= IsLinearMap.mk' _ hF
    let x'' : Lattice.Site _ → Config G (C.side i.1 i.2)→ℂ:=C.O i.1 i.2 (d:=d) (Y i)
    have hy : x'' b=F' (T0 (x i)):=by unfold x'' Family.O TransferData.cylinder; rw [LinearEquiv.symm_apply_apply]
    change (∑ j:ρ,J j • (x' (Motion.patch F j.1 (U i.1 i.2 j.2)) - f (Motion.patch F j.1 (s' j.2))))= x'' b-f (x i)
    simp_rw [smul_sub,Finset.sum_sub_distrib,←map_smul,←map_sum]
    rw [hy,show T0 (x i)= decor F (U i.1 i.2) (x i) from (hi i.2).1 _,decor_at]
    change x' (repaint F (U i.1 i.2) (x i)) - f (repaint F (s') (x i))= x' _- f (x i)
    rw [show repaint F (s') (x i)=x i from repaint_same F LinearMap.id (fun x i=>rfl) _]
end YM.MergeProof
