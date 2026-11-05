import YM.RG05Readout.Address.Fiber
/-!
# High-rank physical scalar steps

The underlying datum composite splitting for root shift. Pays (single-step)
only, retains full trace.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Address
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Bid
open Extra.Histories Push Local Planned.GuardedAtom Guard MergeProof Extra.Histories.Relay Native
open PhysicalNext.Repeat Lotus Motion Trace.Physical Offsets
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical

variable {G:Gauge}
section ops
variable {d:ℕ}{n:Side}{F:Labels.Frame G d}
variable (o:Site n) (S:SectionData F)(R: Rep G n)
lemma local_core (x:F.Coeff) : invoice (Extra.Histories.primary o x) o S R=(fun U=> (R.eval U:ℂ)*part S o R U x,Local.primary S o R.p.threshold x,0):=by
    let P:=Extra.Histories.primary o x
    have hx : P.exponentialEntry o S R=Local.primary S o R.p.threshold x:=by
       funext U; have ht i:P.maskedTerm R i U=0:=congr_fun (map_zero (maskLinear _ _)) _
       change Local.primary S o R.p.threshold x U + ∑' i,P.maskedTerm R i U=_; simp [ht]
    exact Prod.ext (funext (primary_density S R x)) (Prod.ext hx rfl)
lemma core_linear : IsLinearMap ℂ fun x=>invoice (Extra.Histories.primary o x) o S R:=by
    have H(z: ℂ) (x:F.Coeff) (U:Config G n): ((R.eval U:ℂ)*part S o R U (z • x))=z • ((R.eval U:ℂ) *part S o R U x):=by rw [map_smul]; simp only [smul_eq_mul];ring
    constructor
    · intro x y; simp_rw [local_core,map_add]; apply Prod.ext
      · exact funext (fun U=>by simp [mul_add])
      apply Prod.ext
      · rfl
      exact (add_zero _).symm
    intro z x; rw [local_core,local_core]; exact Prod.ext (funext (H z x)) (Prod.ext (map_smul ..) (smul_zero z).symm)
lemma core_expands (x:F.Coeff):invoice (Extra.Histories.primary o x) o S R=∑ i,x i • invoice (Extra.Histories.primary o (Size.axis F i)) o S R:=by
   let A:= (core_linear o S R).mk' _; conv_lhs=> rw [← Size.sum_axes F x]
   change A _=∑ i,x i • A _; simp only [map_sum,map_smul]

def remove (P:Coefficient F n):Coefficient F n:={ P with x:=0 }
lemma removable (P:Coefficient F n) (A:Hol G)(hp:P.Format o A R):(remove P).Format o A R:= ⟨hp.smooth,hp.origin,hp.identity_null,hp.projects,hp.forcing,hp.carried,hp.invariant,hp.supported,hp.borel⟩
lemma bundle (P:Coefficient F n):invoice P o S R=invoice (Extra.Histories.primary o P.x) o S R+invoice (remove P) o S R:=by
    rw [local_core]; let Q:= remove P
    have hx: P.exponentialEntry o S R= Local.primary S o R.p.threshold P.x+Q.exponentialEntry o S R:=by
       funext U; change Local.primary _ _ _ P.x U+(∑' i,P.maskedTerm R i U) =Local.primary S o R.p.threshold P.x U+(Local.primary S o R.p.threshold 0 U+∑' i,P.maskedTerm R i U); rw [map_zero]; exact congr_arg _ (zero_add _).symm
    apply Prod.ext _ (Prod.ext hx (zero_add Q.forced).symm); funext U
    change P.density o S R U=(R.eval U:ℂ)*part S o R U P.x+Q.density o S R U
    rw [Coefficient.density, Coefficient.density,hx,Pi.add_apply,mul_add]; rw [add_assoc]; rfl
lemma scale_n {i:F.Index} (L:Side): F.coeffSize (vowel F L (Size.axis F i)) = (L.val:ℝ)^(d-(F.grades i).1):=by
    rw [Frame.coeffSize,Finset.sum_eq_single i]; simp [vowel,Size.axis]
    intro j _ hj; simp [vowel,Size.axis,hj]; simp
end ops
section
variable (C:Family G)(N m p d:ℕ)
set_option quotPrecheck false
local notation "Z"=>C.path.levels.clock.op m p
local notation "R"=> C.path.rep N p m
local notation "M"=> C.path.rep N p (m+1)
local notation "F"=>C.labels.level d
local notation "Y"=> C.params
local notation "S"=> C.localSection d
local notation "κ"=> kappa C.path
local notation "L"=> C.path.S.block m
local notation "v"=> ((L).val:ℂ)^d
variable (o:Site (C.path.S.side (m+1) p))
variable {a c α β g r J :ℝ} {X:Extra.Histories.Heading (C.labels.level d)} (D:GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m))
local notation "q"=> Pricing S C.path N p m Y
variable (h:C.Makes) (hm:m<N) (ho:(C.path.levels.clock.op m p).ratio.parent o=0) (hw: Pricing (C.localSection d) C.path N p m C.params D X a c α β)(hα:0≤α)
include hm h ho hw hα
-- assembling rough estimate at d=0, no output-layout change
lemma rough (P:Coefficient F (C.side (m+1) p)) (hc:1≤ c)(hβ:0 ≤ β)(hκ: κ (m+1) ≤ 1) (hp:P.Format o Y M)(hP:P.remBound o M (κ (m+1)) r):
     let W:= (F).coeffSize P.x
     let u:=((L).val:ℝ)^d*c; let B':=u*W+α*r
     ∃ Q:Coefficient F (C.side m p), Q.Format 0 Y R∧ Q.remBound 0 R (κ m) B' ∧ Ride (Z) o 0 D v (invoice P o S M) (invoice Q 0 S R) ((1+u+β)*W+ (2+α)*r) ∧ (F).coeffSize Q.x ≤ B':=by
   intro W u B'; let U(i: (F).Index) :=invoice (Extra.Histories.primary o (Size.axis F i)) o S M
   let f(i: (F).Index):=‖P.x i‖*u; have hf(i: (F).Index):∃ R':Coefficient F (C.side m p), R'.Format 0 Y R ∧ R'.remBound 0 R (κ m) (f i) ∧ (F).coeffSize R'.x ≤ f i∧ Ride (Z) o 0 D v (P.x i • U i) (invoice R' 0 S R) (‖P.x i‖*(1+u+β)):=by
       obtain ⟨Q,H,hp',hT,hW,ht⟩:=primary_grant C N m p d o D h hm ho hw i hα hc hβ; let a:=P.x i; have hz : c*(F).coeffSize (vowel F L (Size.axis F i)) ≤ u:=by rw [scale_n,mul_comm]; exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by exact_mod_cast (L).property) (Nat.sub_le ..)) (zero_le_one.trans hc)
       refine ⟨stretch a Q,stretch_format _ H,stretch_rem a (rem_mono hp' hz),?_,?_⟩
       · rw [show (stretch a Q).x=a • Q.x from rfl, Size.smul]; exact mul_le_mul_of_nonneg_left (hW.trans hz) (norm_nonneg _)
       have hx := hT.matchPay a a v (mul_comm ..); rw [max_self] at hx; rw [invoice_stretch]; exact hx.cost (mul_le_mul_of_nonneg_left (add_le_add_left (add_le_add_right hz _) _) (norm_nonneg _))
   let G':=(h.wilson.represents _ p _ hm).good
   have hU(s:Finset ((F).Index)) :∃ T:Coefficient F (C.side m p),T.Format 0 Y R ∧ T.remBound 0 R (κ m) (∑ i∈s,f i) ∧ (F).coeffSize T.x ≤ ∑ i∈s,f i ∧ Ride (Z) o 0 D v (∑ i∈s, P.x i • U i) (invoice T 0 S R) (∑ i∈ s,‖P.x i‖*(1+u+β)):=by
       have hδ:0 < κ m:=Real.sqrt_pos.mpr (forcedPos ..)
       induction s using Finset.induction_on with
       | empty=>
          simp only [Finset.sum_empty]; refine ⟨Extra.Histories.primary 0 0,primary_format _,primary_rem _ hδ,?_,?_⟩
          · simp [Extra.Histories.primary,Frame.coeffSize]
          rw [invoice_zero]; exact Ride.vac
       | @insert i s hi ih=>
          simp only [Finset.sum_insert hi]; obtain ⟨T,hT,hV,hW,hY⟩:=ih; obtain ⟨L',hr,hL,hz,hY'⟩:=hf i
          obtain ⟨hq,hA⟩:=presentation hr hL hT hV; refine ⟨beside L' T,hq,hA,?_,?_⟩
          · rw [reckon]; exact (Size.add ..).trans (add_le_add hz hW)
          rw [invoice_add L' 0 (S) (R) T (h.wilson.represents N p m hm.le).good hL hV]; exact hY'.taller hY hw.soundD (C.path.levels.transition_mass ..) G' (h.wilson.represents N p m hm.le).good
   obtain ⟨T,hT,hZ,hW,hY⟩:=hU Finset.univ; unfold U at hY; rw [← core_expands o S M P.x] at hY
   have hv: ∑ i,f i=u*W:= (Finset.sum_mul ..).symm.trans (mul_comm ..)
   rw [hv] at hW hZ;
   obtain ⟨Q,hF,hQ,hξ,hR⟩:= regular_grant C N m p d o D h hm ho hw (remove P) hα hκ (removable o (M) P Y hp) hP rfl -- binder verify
   obtain ⟨hA,hB⟩:= presentation hT hZ hF hQ; refine ⟨beside T Q,hA,hB,?_,?_⟩
   · rw [bundle o S M P,invoice_add T 0 (S) R Q (h.wilson.represents N p m hm.le).good hZ hQ]; rw [show (1+u+β)* W=∑ i, ‖P.x i‖*(1+u+β) from (mul_comm ..).trans (Finset.sum_mul ..)]
     exact hY.taller hξ hw.soundD (C.path.levels.transition_mass ..) G' (h.wilson.represents N p m hm.le).good
   rw [reckon]; exact (Size.add ..).trans (add_le_add hW hR)
end
end YM.RG05Readout.Address
