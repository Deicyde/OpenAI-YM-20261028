import YM.RG05Readout.Address.Tidal
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Address
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Bid
open Extra.Histories Push Local Planned.GuardedAtom Guard MergeProof Extra.Histories.Relay Native
open PhysicalNext.Repeat Lotus Motion Trace.Physical Offsets
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical

variable {G:Gauge} {C:Family G} {N m p d:ℕ}{δ:E4}
set_option quotPrecheck false
local notation "Z"=>C.path.levels.clock.op m p
local notation "R"=> C.path.rep N p m
local notation "M"=> C.path.rep N p (m+1)
local notation "F"=>C.labels.level
local notation "Y"=> C.params
local notation "S"=> C.localSection
local notation "κ"=> kappa C.path
local notation "L"=> C.path.S.block m
local notation "v"=> ((L).val:ℂ)^d
local notation "ℓ"=> (((L).val:ℝ)⁻¹)
variable {s t K u τ α C' :ℝ}{D:GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)} (hp:Cursor C N m p d s K) (h:C.Makes)(hm:m<N)(hx:SoundDoor (C.path.levels.clock.op m p) D)(hδ: δ∈Native.box)
local notation "K0"=>K^3
include hp h hm hx hδ
variable (k:Letter d)(a:ℕ) (Q:Coefficient (C.labels.level (kept k)) (C.side m p)) (y:Three G (C.side (m+1) p)) (o:Site (C.side (m+1) p))
local notation "W"=> F (kept k)
local notation "Si"=> invoice Q 0 (S (kept k)) R
local notation "q"=> Q.x
local notation "ϵ"=> (W).coeffSize q
local notation "χ"=> (((L).val:ℂ)^(kept k))
local notation "Rt"=> (↑(ℓ^depth k):ℂ)
local notation "ε"=> Native.readJ k δ
local notation "P₀"=> Travel C N m p d o D
variable (hZ: Q.Format 0 C.params (C.path.rep N p m))(hP: Q.remBound 0 (C.path.rep N p m) (kappa C.path m) t)
    (ht: Ride (C.path.levels.clock.op m p) o 0 D (((C.path.S.block m).val:ℂ)^(kept k)) y (invoice Q 0 (C.localSection (kept k)) (C.path.rep N p m)) u)
include hP hZ ht
lemma surplus :
    let I':= (Rt) • glyph (recollect d (ε)) y
    ∃ V:Tape G (C.side m p), Course (d:=d) (D:=D) o I' V 0 0 (K*(K*ϵ+(2*K*ϵ+t))) (K*(u+K*ϵ)):=by
    intro P; let f:= recollect d (ε)
    obtain ⟨T,hB,hC,hR,hX,hI⟩:= Cursor.reshape (D:=D) h hm hp Q (Nat.zero_le _) (Nat.sub_le ..) hx hZ hP ht
    let V:= glyph f (invoice T 0 (S 0) R)
    have he : Priced d f K:=fun b t hx=> (recall_read d hδ k b t hx).trans (mul_le_mul_of_nonneg_right hp.earns hx.nonneg) -- likely arg
    have hz:= printed_high (d:=d) (φ:=f) (tail_rec d _) he T hB (rem_mono hC (show _ ≤ 2*K*ϵ+t from (le_of_eq (by ring)))) -- f0
    refine ⟨V,hz.grow (mul_le_mul_of_nonneg_left (add_le_add_left hX _) (zero_le_one.trans hp.fits)),Travel.scaleTo y _ f he k hR⟩

local notation "Ct"=> (Fintype.card (Letter d):ℝ)
def extra (d:ℕ)(K:ℝ):= (Fintype.card (Letter d):ℝ)+K
-- scale D'
lemma primitive (H:∀ j:ℕ,j<a → (W).coeffSize (basisCut W j q)≤α) (hα: 0≤ α):
     let I':= (glyph (readJ k 0) y).comp (Native.pull δ ℓ)
     let t':=K*(K*ϵ+(2*K*ϵ+t))+Ct*K^2*(2*K*ϵ+t)
     ∃ V':Tape G (C.side m p), ∃ x z:Palette C d,Course (D:=D) o I' V' x z t' ((K+Ct*K^3)*(u+K*ϵ)) ∧ size x≤Ct*K^3*ϵ ∧ size (Address.clear C d (depth k+a) (x-chunk k q)) ≤ Ct *K^3*α:=by
    intro I J; let A:=K^2*(2*K*ϵ+t); let g:=readJ k δ; let f(i:Letter d):=(Rt • glyph (g (line i) • readJ i 0) y); let c:=K^3*(u+K*ϵ)
    choose V x z hC hs hD using fun i=>raising hp h hm hx hδ k a Q y o hZ hP ht i H hα
    obtain ⟨T,hT⟩:=surplus hp h hm hx hδ k Q y o hZ hP ht; let L':= (∑ i:Letter d,V i); let h':=(∑ i,x i); let t'':=(∑ i,z i)
    have he(i:Letter d):Travel C N m p d o D (f i) (V i) c:=(hC i).ready
    have hv : Travel C N m p d o D (∑ i,f i) L' (Ct*c):=by simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using Travel.list Finset.univ h hm hx (fun i _=> he i)
    have hF: Printed C d R 0 (κ m) L' h' t'' (Ct*A):=by
       have ha:= hp.sense d le_rfl
       simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using Printed.all (Real.sqrt_pos.mpr (forcedPos C.path.levels m)) (h.wilson.represents N p m hm.le).good Finset.univ ha.order ha.power (fun i _=>(hC i).paid)
    refine ⟨T+L',0+h',0+t'',⟨(hT.paid.addP hF (h.wilson.represents N p m hm.le).good (hp.sense d le_rfl).order (hp.sense d le_rfl).power).grow (le_of_eq (by unfold J A;ring)),?_⟩,?_,?_⟩
    · have hi : I=(Rt) • (glyph (recollect d (ε)) y)+∑ i,f i:=by
          ext1 u'; let Xk:= expands d g u'; unfold I f
          simp only [LinearMap.comp_apply,glyph_apply,LinearMap.add_apply, LinearMap.smul_apply,LinearMap.sum_apply]
          have ht : readJ k 0 (Native.pull δ ℓ u')=Rt • g u':=by
               refine (rate_consider k.2 δ 0 ℓ u').trans ?_
               rw [smul_zero,add_zero]; rfl
          rw [ht, Xk, smul_assoc,add_smul,Finset.sum_smul,smul_add,Finset.smul_sum]; exact add_comm ..
      rw [hi]; refine (hT.ready.add hv h hm hx).extend (le_of_eq ?_); unfold c; ring
    · rw [zero_add, mul_assoc]; apply (size_sum ..).trans; exact (Finset.sum_le_sum (fun i _=> hs i)).trans_eq (by rw [Finset.sum_const, Finset.card_univ,nsmul_eq_mul])
    rw [zero_add]
    have hz:x k=chunk k q:=by simpa using hD k
    let I0:=(Finset.univ:Finset (Letter d)).erase k
    have hj(i: Letter d) (hr:i∈I0) : size (Address.clear C d (depth k+a) (x i)) ≤ K^3 * α:=by
       have h':=hD i; rw [if_neg (Finset.ne_of_mem_erase hr)] at h'; exact h'
    rw [show h'=(∑ i∈ I0,x i)+chunk k q from ?_, add_sub_cancel_right, map_sum, mul_assoc]
    · apply (size_sum ..).trans
      apply le_trans (Finset.sum_le_sum hj)
      rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_univ _)) (mul_nonneg (pow_nonneg (zero_le_one.trans hp.fits) _) hα)
    rw [← hz]; exact (Finset.sum_erase_add _ x (Finset.mem_univ _)).symm
end YM.RG05Readout.Address
