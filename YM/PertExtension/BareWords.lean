import YM.PertExtension.BareSlot
import YM.Source.Construction

/-! Real joint stencil insertions at arbitrary site placements on one cutoff.
Engineering prefactors can be included *prior* to the formal calculation.
An exact top-coordinate label identity on a Family (no claim transferring a
cutoff estimate without loss). -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.PertExtension.Orb.SlotEvaluation
open Wilson Lattice Gauge Precision Function Filter Set Metric MeasureTheory RG Supply Labels Source Drops InnerProductSpace
open scoped Matrix.Norms.Frobenius ContDiff Topology Classical BigOperators ENNReal
open Chart Series Series.Radial Series.Tested Bid
variable {G : Gauge}{n : Side}{d : ℕ}{P : ChartRatio G}
variable {F : Labels.Frame G d}{C : SectionData F}{H : Hol G}(h : C.Sound H)(p : pop C)
variable {i : F.Index}{o : Site n}
include h in
lemma scalar_real {u}: ((fieldAt C i o u : ℝ) : ℂ) = C.places (Pi.single i 1) o u := by
  unfold fieldAt
  have he := h.ordinary_real (Pi.single i 1) (expandAt o u)
  have hf : star (Pi.single i 1 : F.Coeff)=(Pi.single i 1 : F.Coeff) := by funext j; simp [Pi.single_apply]
  rw [hf] at he
  exact Complex.ext rfl (Complex.ofReal_im _ |>.trans (Complex.conj_eq_iff_im.mp he.symm).symm)
include h in
@[simp] lemma unit_zero : fieldAt C 0 (n:=n) o=1 := funext fun u=>by unfold fieldAt SectionData.places; change (C.evaluate F.e0 _).re = _;rw [h.unit]; rfl

def joints {I : Type*} (s : Finset I) (t : I→F.Index)(x : I→Site n) (ρ : I→ℝ) (u : Config G n) := ∏ j∈s,ρ j * fieldAt C (t j) (x j) u
include h p
set_option maxHeartbeats 2200000 in
lemma good_joint {I:Type*}(s : Finset I)(t : I→F.Index)(x : I→Site n)(ρ : I→ℝ) :
  PreTest (joints s t x ρ (C:=C)) ∧
     RadialOrder (∑ j∈s, (F.grades (t j)).2) ((restrictedO (joints s t x ρ (C:=C))) ∘ expLinks G (Cotree n)) := by
  let f (j:I):Config G n→ℝ:= fieldAt C (t j) (x j)
  let g :Dir G n→Config G n:=representative
  let B:=joints s t x ρ (C:=C)
  change PreTest B ∧ _
  have he j := pre_field C h p (t j) (x j)
  have H (j):= show PreTest (f j) from (he j).1
  have hc : Continuous B := continuous_finsetProd _ (fun j _=>continuous_const.mul ((H j).continuous))
  have h': ContDiffAt ℝ ∞ (restrictedO B ∘ expLinks G (Cotree n)) 0 := by
     convert! (contDiffAt_prod (t:=s) (f:=fun i x=>ρ i * f i (g x)) (fun j _=>contDiffAt_const.mul ((H j).curved.germ))) using 1
  refine ⟨⟨?_ , ⟨hc.comp continuous_links,h'⟩,hc⟩,?_⟩
  · intro u hu v; unfold B joints; apply Finset.prod_congr rfl fun j _=> congr_arg (fun y=>ρ j*y) ((H j).gauge u hu ..)
  intro A
  have ht := bill_product s (fun j=>(F.grades (t j)).2) (fun i (r:ℝ)=>ρ i*f i (g (r • A))) <| fun j _=>by simpa only [Nat.zero_add] using! bill_mul (bill_const (ρ j)) ((he j).2 A)
  convert! ht using 1
  funext r; simp only [Finset.prod_apply];rfl

lemma joint_finite {I:Type*}(s : Finset I)(t : I→F.Index)(x : I→Site n)(ρ : I→ℝ)(R : LocalRatio P)(en : Even n.val) :
   let O := joints s t x ρ (C:=C)
   let w := ∑ j∈s, (F.grades (t j)).2
   Aspiration (fun r : ℝ=> (r⁻¹)^w*preExpectation O r) (fun j=>diagonalWith P (restrictedO O) (w+j)) := by
  obtain ⟨hp,hv⟩:=good_joint h p s t x ρ
  exact (before_tree_formula en R hp).shift (diag_down R hp.curved hv en)

end YM.PertExtension.Orb.SlotEvaluation

namespace YM.PertExtension
open Wilson Lattice Gauge Precision Function Filter Set Metric MeasureTheory RG Supply Labels Source Drops InnerProductSpace
open scoped Matrix.Norms.Frobenius ContDiff Topology Classical BigOperators ENNReal
open Chart Series Series.Radial Series.Tested Bid

namespace SameColumns
/-! Linear change on actual top labels, not assumed filtration-compatible. At a
single engineering horizon. It costs arbitrary constants in N,p unless
bounded in the full comparison. -/
variable {G : Gauge}(C : Family G){d : ℕ}
local notation "L" => (C.labels.level d)
def reprice (N p : ℕ)(w : (L).Coeff) := (C.factory d N p).terminal <| (L).scaled (C.path.levels.clock.threshold N) (((C.S.a N:ℂ)^d) • w)
lemma reprice_eq (N p : ℕ)(w : (L).Coeff) (o : Site (C.side N p)) :
   C.O N p (reprice C N p w) o = (C.localSection d).places w o := by
  funext u
  let A := C.path.levels.clock.threshold N
  have ha:A⁻¹ ≠0:=inv_ne_zero (C.path.levels.budget N).threshold_pos.ne'
  let T:= C.factory d N p
  unfold Family.O TransferData.cylinder
  change initial (C.localSection d) C.path N p (T.terminal.symm (reprice C N p w)) o u=_
  rw [show T.terminal.symm (reprice C N p w)=_ from T.terminal.symm_apply_apply _]
  unfold initial
  change ((C.S.a N:ℂ)^d)⁻¹ * (C.localSection d).places ((L).scaled A⁻¹ ((L).scaled A (((C.S.a N:ℂ)^d) • w))) o u = _
  have hz y : (L).scaled A⁻¹ ((L).scaled A y)=y:= by
    simpa only [inv_inv] using (L).scaled_inv ha y
  rw [hz]
  have hc : ((C.S.a N):ℂ)≠0:=by exact_mod_cast (C.S.a_pos N).ne'
  have hl := ((C.localSection d).eval_linear.mk' _).map_smul ((C.S.a N:ℂ)^d) w
  rw [show (C.localSection d).places (((C.S.a N:ℂ)^d) • w) o u=((C.S.a N:ℂ)^d)*(C.localSection d).places w o u from congr_fun hl _];field_simp

end SameColumns
end YM.PertExtension
