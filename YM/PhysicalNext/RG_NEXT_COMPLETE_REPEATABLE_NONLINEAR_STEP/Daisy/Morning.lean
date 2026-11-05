import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Daisy.Pint
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lotus.Sofa

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Daisy
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond Mixed Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:Leaf R)(X:Coat T F)(H:Cash W x μ L Q o C T R) (a' : ℝ) (u:ConnectedActivityE6.Alphabet c f→ℝ)
    {q A B b e a χ' v d:ℝ}{j n:ℕ}{χ:Chi} (Ξ : Utopia H j v d r q χ)
open Itinerary Animals
variable {Y t u v:ℝ}{N : March.Captain H j q d v Y A b r B t n χ}(h : Herd H N.conduit A B n)
open Greenbelt March Next.Foundations

def escort (M:Lotus.Leaf R) (χ:Chi) (Q:ChartRatio G) (p:Molecule S)(l: ℕ) (T : Tube G S) (W x K a:ℝ) (V:Config G c):=likely fun r:Greenbelt.Reserve S=> M.picture (prism T x χ K V (allot r)) p W a Q l
local notation "U'" => fun V=> escort M χ Q.table p Q.halo T W x o.K o.a V
local notation "l₀" => M.lotus T x χ o.K W o.a Q.table Q.halo
local notation "cs" => B*persona M H q N.conduit.flair 0 n 0 p
local notation "d0" => jewelDebt M Q L x
include H N h
lemma debtor (hp:(roster p).flags=∅) : LocalOn (H.unionP p) U' ∧ Measurable U' ∧ GaugeInvariant U' ∧
    (fun V=> M.lotus T x χ o.K W o.a Q.table Q.halo V p)=masked (Pressure.temp x) (H.unionP p) U' ∧
    ∀ Y:Config G c,Healthy (Pressure.temp x) (H.unionP p) Y→ Ore Y U' v (d0*(cs)) j:=by
  let X (r:Greenbelt.Reserve S):=prism T x χ o.K 1 (allot r); let f i V:=M.picture (vary (X i) V) p W o.a Q.table Q.halo
  have h' i:= M.tailSpin (a:=o.a) (X i) p (show Intake P T (X i).x R from H.laws.intake) (show Room P S T (X i).x from H.laws.data.room) (show ShellAccess S G _ _ ((X i).width) o.γ from H.laws.data.access) Q.table_exists Q.buys
  have hf i (V:Config G c): M.bloom (prism T x χ o.K V (allot i)) W o.a Q.table Q.halo p=masked (Pressure.temp x) (H.unionP p) (f i) V∧
      (Healthy (Pressure.temp x) (H.unionP p) V→ Ore V (f i) v (B*(d0*persona M H q N.conduit.flair 0 n 0 p)) j):= luminos M (prism _ _ _ _ _ _) N h rfl rfl rfl hp
  let c:= (Fintype.card (Greenbelt.Reserve S):ℝ)
  letI : Nonempty (Forest S.ratio) := Tree.select _ S.patch.odd_side
  have hP:0<c:=by unfold c; positivity
  refine ⟨fun U V h=> congr_arg likely (funext fun i=> (h' i).2.1 U V h),measurable_const.mul (Finset.measurable_fun_sum _ (fun i _=> show Measurable (f i) from (h' i).1)), fun t U=> congr_arg likely (funext fun i=>(h' i).2.2 t U),?_, fun V hU E _ _ _ Z x hx hz=>?_⟩
  · funext V; unfold Leaf.lotus; simp_rw [fun i=> (hf i V).1]; by_cases hv: Healthy (Pressure.temp x) (H.unionP p) V
    · simp_rw [masked_eq _ _ _ _ hv]; rfl
    simp_rw [masked_ne _ _ _ _ hv]; exact Greenbelt.likely_constant _
  apply ((Brush.spree _ (fun i=> f i ∘ Z) _ zero_le_one (fun i (_:i∈univ)=> (hf i V).2 hU _ Z x hx hz)).smul c⁻¹).climb _ le_rfl
  rw [Real.norm_of_nonneg (inv_nonneg.mpr hP.le),sum_const,nsmul_eq_mul,card_univ, inv_mul_cancel_left₀ (show c≠0 from hP.ne')]; exact le_of_eq (mul_left_comm ..)

omit h N
lemma petals (V:Config G c)(i m n:ℕ)(ht : i ≤ p.card-1)(hm: n ≤ Cash.numP p) : |l₀ V p| * (1+H.shapeW p)^m ≤ (jewelDebt M Q L x)*persona M H C H.opt i m n p:=by
  have h₀:0 ≤ persona M H C H.opt i m n p:= earned M H C H.opt H.positive ..
  let I:= (Fintype.card (Greenbelt.Reserve S):ℝ); letI: Nonempty (Forest S.ratio):= Tree.select S.ratio S.patch.odd_side
  have hi:0<I:=by unfold I; positivity
  let F r:=prism T x χ o.K V (allot r)
  let b r:= M.bloom (F r) W o.a Q.table Q.halo p
  have he r: ‖b r‖ * (1+H.shapeW p)^m ≤ (jewelDebt M Q L x)*persona M H C H.opt i m n p:=by
    unfold b Leaf.bloom; split
    next ha=>
      by_cases hp:M.turn.badge S∈p
      swap; · unfold Leaf.steep likely; simp_rw [M.tithe_off _ _ p hp,Finset.sum_const_zero,mul_zero,norm_zero,zero_mul]; exact mul_nonneg (dew M H|>.2.1) h₀
      have hR : H.ticketsP i n 0 p := ⟨ha.1,ht,hm,H.positive_volume p⟩
      let Q0:=∏ i∈p.erase (M.turn.badge S), H.text i; let c:=M.weight * Q0; let A:=planted (F r) p
      have hs (i): ‖M.tithe (A.taggedL i) (own p) W o.a Q.table Q.halo p‖ ≤ c:=
        (norm_integral_le_integral_norm _).trans (by have hx:=(M.tip (A.taggedL i) (own p) H rfl (planted_valid (F r) p) p).2.2; rw [if_pos hp] at hx; exact hx)
      have hv : ‖M.steep A (own p) W o.a Q.table Q.halo p‖≤c:=by
        unfold Leaf.steep likely
        let v:=(Fintype.card S.Choices:ℝ); have h:0<v:=by unfold v; positivity
        rw [norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr h.le)]
        apply le_trans (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (Finset.sum_le_sum fun i _=> hs i)) (inv_nonneg.mpr h.le))
        rw [sum_const,nsmul_eq_mul, card_univ, inv_mul_cancel_left₀ h.ne']
      unfold persona; rw [if_pos ⟨hR,hp⟩]; refine (mul_le_mul_of_nonneg_right hv (pow_nonneg (add_nonneg zero_le_one (H.positive_volume p)) _)).trans_eq ?_
      rw [← mul_prod_erase _ _ hp,nose,← mul_assoc (jewelDebt ..), ← mul_assoc (jewelDebt ..),← (dew M H).2.2]
      unfold c Q0; simp_rw [prod_congr rfl (fun j (hj:j∈p.erase _) => sleeve M H C H.opt j (ne_of_mem_erase hj))]; rfl -- may defeq
    next h=> rw [norm_zero,zero_mul];exact mul_nonneg (dew M H|>.2.1) h₀
  let g:=(1+H.shapeW p)^m; have hh :0≤g:=pow_nonneg (add_nonneg zero_le_one (H.positive_volume p)) _
  change ‖I⁻¹ * ∑ i, b i‖*g≤_; rw [norm_mul,Real.norm_of_nonneg (inv_nonneg.mpr hi.le),mul_assoc]
  apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (norm_sum_le ..) hh) (inv_nonneg.mpr hi.le))
  rw [Finset.sum_mul]; refine (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _=> he i) (inv_nonneg.mpr hi.le)).trans_eq ?_; rw [sum_const,nsmul_eq_mul,card_univ,inv_mul_cancel_left₀ hi.ne']
lemma withermore (V:Config G c)(hp:l₀ V p≠0) :
    Ac.Spark H.supportP p ∧ troupe T R Q.halo (radiusB x) p ∧ M.turn.badge S∈p ∧ enlargement S.ratio Q.halo (radiusB x) (RG.inspected M.crest) ⊆ H.unionP p ∧
    (roster p).flags= RG.flags (Pressure.temp x) V∩ H.unionP p ∧ (H.unionP p).Nonempty:=by
  let X r:=prism T x χ o.K V (allot r); let b (r:Greenbelt.Reserve S):= M.bloom (X r) W o.a Q.table Q.halo p
  obtain ⟨z,hz⟩:∃ z,b z≠0:=by by_contra! he; apply hp; change _* ∑ i, b i=0; simp_rw [he,Finset.sum_const_zero, mul_zero]
  have hF : M.turn.badge S∈p:=by by_contra hn; exact hz (M.bloom_off (X z) p hn)
  unfold b Leaf.bloom at hz; split at hz; swap; · exact (hz rfl).elim
  next he=>
  have hx : enlargement S.ratio Q.halo (radiusB x) (RG.inspected M.crest) ⊆ H.unionP p:=by rw [show enlargement _ _ _ _= areas R T Q.halo (radiusB x) (M.turn.badge S) from (M.turn.badge_area ..).symm]; exact subset_biUnion_of_mem _ hF
  refine ⟨he.1,he.2.1,hF,hx,he.2.2.symm,Finset.Nonempty.mono hx ((Finset.Nonempty.image (f:=S.ratio.parent) ?_).mono (halo_subset _ _))⟩
  suffices H : M.crest.Nonempty from H.mono Finset.subset_union_left
  unfold Leaf.crest; cases M.turn
  · exact ⟨_,(R.activities.reg _).anchor⟩
  exact ((R.activities.forced _).inventory_ne).mono (R.activities.forced _).inventory_sup
end YM.PhysicalNext.Repeat.Daisy
