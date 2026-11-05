import YM.RG05Readout.UV.Enamel
/-!
# Physical master path starting on real top stencil

A fixed stencil for each field horizon (selected exactly as in C; in our
choice of the finite alphabet, field test at jet weight h_s minus probe weight
of location polynomial). This fixes the coupling/root convention already at
the cutoff; link-coordinate estimation applies from this actual output. Uses
existing calibrated top for all scalar sectors; acquirers requiring polynomial
multisource registration have to exhibit it too on that top representation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Address
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Bid
open Extra.Histories Push Local Planned.GuardedAtom Guard MergeProof Extra.Histories.Relay Native Copper
open PhysicalNext.Repeat Lotus Motion Trace.Physical Offsets
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}(C:Family G)(d N p:ℕ)
local notation "H"=> C.path
local notation "F"=>C.labels.level
local notation "T"=>C.localSection
local notation "Y"=>C.side N p
local notation "R"=> C.path.rep N p N
local notation "J"=> Mark C d
local notation "M"=> Palette C d
set_option quotPrecheck false
def bareK (i:Letter d)(x:C.label (kept i)) : Coefficient (F (kept i)) Y:= (C.factory (kept i) N p).entries N x
def Bare (i: J):= glyph (readJ i.1 0) (invoice (bareK C d N p i.1 (Size.axis (F _) i.2)) 0 (T _) R)
def basisTop : Palette C d→ₗ[ℂ] Tape G Y:= (slide_linear (Bare C d N p)).mk' _

section
variable {C d N p} (h:C.Makes)(hp:∀ j≤d,C.ref j≤ N)
include h hp
lemma basis_paid : Group C N N p d (basisTop C d N p) ((C.path.levels.params N).columns):=by
    let s:= (C.path.levels.params N).columns; let v (i:Letter d) (a:(C.labels.level (kept i)).Index):= bareK C d N p i (Size.axis (F _) a); let τ:=basisTop C d N p
    let t(i:Letter d):=h.calibrated (kept i) N p (hp _ (Nat.sub_le ..)); have he(i:Letter d):C.ref (kept i) ≤ N:= hp _ (Nat.sub_le ..)
    have hf (i : Mark C d) : Printed C d (R) 0 (kappa C.path N) (Bare C d N p i) (ticket i) (ticket i) s:=by
        let e:=kept i.1; let v':=v i.1 i.2
        let u:=Size.axis (C.labels.level (kept i.1)) i.2
        have hV:v'.Format 0 C.params R:= (t i.1).format N (he _) le_rfl _
        have hP: v'.remBound 0 R (kappa C.path N) s:= by
             apply rem_mono ((t i.1).cap N (he i.fst) le_rfl u)
             change s*(F e).coeffSize ((F e).core v'.x) ≤ s; rw [show v'.x=u from (t i.1).bare_coord u]; exact mul_le_of_le_one_right (zero_le_one.trans (C.path.levels.params _).columns_ge) ((Work.G08.size_core ..).trans_eq (Size.size_axis ..))
        have hQ:=printed_one i.1 v' hV hP
        rw [show Trace.Physical.Germ.projection (F (kept i.1)) C.params (R).p.threshold 0 v'= v'.x from ?_,show v'.x=u from (t i.1).bare_coord u] at hQ; exact hQ
        unfold Trace.Physical.Germ.projection; rw [show v'.regular=0 from (t i.1).bare_germ u]; simp only [Pi.zero_apply];
        rw [show Trace.Physical.Germ.vector (F e) C.params (R).p.threshold 0 (0:Config G Y→ℂ)=0 from ?_,tsum_zero,add_zero]
        unfold Trace.Physical.Germ.vector Trace.Physical.Germ.label; split; next h'=>
           rw [show h'.choose=0 from Next.Foundations.JetTest.unique h'.choose_spec ((Next.Foundations.jetTest_zero_iff ..).mpr (fun i=> ⟨contDiffAt_const,fun k _=> by simp⟩)),map_zero,map_zero]
        next=>simp
    obtain ⟨hv,ht⟩:= Trace.Physical.GermGraph.dimensions d N p N h (hp d le_rfl) le_rfl
    refine ⟨fun x:Palette C d=> ⟨x,?_⟩,(C.path.levels.params _).columns_ge⟩
    have H':=Printed.all (Real.sqrt_pos.mpr (forcedPos C.path.levels N)) (h.wilson.represents N p N le_rfl).good Finset.univ hv ht (fun i _=> (hf i).twist hv ht (val x i))
    rw [cardp x, ← Finset.sum_mul, mul_comm _ s] at H'; exact H'
end
/-- Physical densities and exponents encoded slice against root test in native units. -/
def entrance (x : Palette C d)(o:Site Y) (φ:Body) : Goods G Y :=
    ∑ i:Mark C d,val x i • (readJ i.1 0 φ • Local.presented (T (kept i.1)) o (R).p.threshold (Size.axis (F (kept i.1)) i.2))
lemma basis_agrees (h:C.Makes)(hp:∀ j≤d,C.ref j ≤ N) (φ:Body)(U:Config G (C.side N p))(x:Palette C d):
    (basisTop C d N p x φ).fst U=((R).eval U:ℂ)* entrance C d N p x 0 φ U:=by
    let v(i:J):=Size.axis (F (kept i.1)) i.2
    let y(i:J):=(T (kept i.1)).places ((F (kept i.1)).scaled (R).p.threshold⁻¹ (v i)) (0:Site Y) U
    have he(i: J): (Bare C d N p i φ).fst U=((R).eval U:ℂ)* ((readJ i.1 0) φ * y i):=by
         let f:= v i; let ξ:= (F (kept i.1)); let s:=(C.S.a N:ℂ)^(kept i.1)
         let b:= (T (kept i.1)); let t:= bareK C d N p i.1 f
         change readJ i.1 0 φ * t.density 0 b R U=_; rw [show t.density 0 b R U=s*((R).eval U:ℂ)* initial b (H) N p (v i) 0 U from (h.calibrated _ _ _ (hp _ (Nat.sub_le ..))).encode _ _]
         unfold initial; simp only [Pi.smul_apply,smul_eq_mul]; change _*( _ * (s⁻¹*b.places (ξ.scaled _ _) _ U))=_
         rw [show ((H).levels.clock.threshold N)=(R).p.threshold from (by rw [(h.wilson.represents _ _ _ le_rfl).vac];rfl)]
         have ht:s ≠ 0:=pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (C.S.a_pos _).ne'); change _*(_*(s⁻¹*y i))= _; field_simp
    change ( (∑ i:Mark C d, val x i • Bare C d N p i) φ).fst U=_; rw [LinearMap.sum_apply,Prod.fst_sum]
    unfold entrance; simp_rw [Finset.sum_apply];rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun i _=> ?_); change val x i*(Bare C d N p i φ).fst U=((R).eval U:ℂ)*(val x i*(readJ i.1 0 φ*y i)); rw [he]; ring
end YM.RG05Readout.Address
