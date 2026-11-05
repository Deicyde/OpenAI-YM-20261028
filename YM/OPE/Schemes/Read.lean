import YM.OPE.Eye.Extract
import YM.OPE.Splitting.Observe

/-!
# Graded reading and lifetime of polarizers
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Function Set Filter Table Lattice RG Wilson MergeProof Ribbons Accent PhysicalNext.Repeat.Legato Source Bid Next.Extract Next.UVStress
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}(U:Spec.Final C F S){I J L : Type}[Fintype I][Fintype J]{φ:Filter L}[φ.NeBot] {T A V : L→ℝ} {x v u a b c d y z : ℝ} {k m j: L→ℕ} (g:I→ C.book.Token) (r:J→ C.book.Token) {X:L→ I→ Cover}{Y:L→J→ E4} {q q':ℕ}
    {P:L→ C.label q}
variable {M} {E : Dash.Bin M} {t} {H} (Base' : Base C F M t E S H) -- inspect implicit M
set_option quotPrecheck false
local notation "Λ" => U.sector.derivatives
variable {R: Prescription U.sector.derivatives}
include U
omit U [φ.NeBot] in
lemma Intervals.inject (h:Intervals φ T a (centerless L) Y)(H:Kept φ T b Y): ∀ᶠ i in φ, Injective (beside (sole (0:E4)) (Y i)):=
    ((Kept.sole φ T (fun _=>0) _).chorus (H.mono (le_max_right a b)) (h.mono (le_max_left a b))).inject

variable (hT:Tendsto T φ atTop) [DecidableEq I]
local notation "w'" => (fun i=>C.S.gridPoint (j i) ∘ X i)
variable (hS: ∀ᶠ i in φ, Survival (C:=C) F (k i) (m i) (j i) (A i) (V i) g (X i) q (P i))

include hS hT Base'
omit U [DecidableEq I] in
lemma whole_grade (hm: Height C.S φ T m x)(hv:RateLE φ T V b): RateLE φ T P (b+q*x) :=by
    -- include `hS` maybe manually
    let f i:= Columns.juice C.path.levels (m i)*(C.S.a (C.ref q)/C.S.a (m i))^q; have he: RateIs φ T f (q*x):= ((Columns.juice_rate_seq C hm.grows hm.pace).mul (((RateIs.const hT (C.S.a_pos (C.ref q))).div hm.mesh).power q)).swap (by ring)
    rw [add_comm b]; apply ((he.pays hT).mul hv).of_norm_le
    filter_upwards [hS,he.pos] with i hi hϕ; obtain ⟨y,Y,h₁,h₂,hy,_,hx⟩:=hi.wins
    apply le_of_tendsto hy.norm
    filter_upwards [hx,((Cards.largeMesh F).eventually_ge_atTop (m i)).filter_mono h₂] with a hA hr using (Columns.whole_origin Base' (Y a) hi.reference hr).trans (mul_le_mul_of_nonneg_left hA hϕ.le)

lemma at_grade {W r D} (L':Package C W r D)(hG:G.Simple)(H:R.Coherent)(u : Mode Λ)(hm:Height C.S φ T m x) (hv:RateLE φ T V b)(he:u.1≤q) : RateLE φ T (fun i=> R.test u q (S.project q (P i))) (b+(q-u.1:ℕ)*x):=by
    let K0 := (R.test u q).comp (S.project q); let K := LinearMap.toContinuousLinearMap K0
    let a:=u.fst
    rcases Nat.eq_zero_or_pos u.fst with ha|ha
    · simp only [ha,Nat.sub_zero]; apply ((RateLE.mul (RateLE.const ‖K‖ hT) ((whole_grade g Base' -- order fix
             hT hS hm hv).norm)).mono (zero_add _|>.le)).of_norm_le; exact Eventually.of_forall (fun i=> K.le_opNorm _)
    let p i:= Columns.fare C (m i) q (a-1); have hz:RateIs φ T p ((q-u.fst:ℕ)*x):= by
       have hc:=Columns.fare_rate (d:=q) (e:=a-1) L'.toTableTickets hm.grows hT hm.pace; rw [show a-1+1=u.fst from Nat.sub_add_cancel ha] at hc; exact hc
    have hZ:P=(fun i=>P i):=rfl; rw [add_comm]; apply (((RateLE.const ‖K‖ hT).mul (hz.pays hT|>.mul hv)).mono (zero_add _|>.le)).of_norm_le
    filter_upwards [hS] with i hi; obtain ⟨y,Y,h₁,h₂,hY,_,hx⟩:= hi.wins
    have he':a-1<a:=by unfold a;omega
    obtain ⟨s, ⟨u',hu⟩,hs⟩:= Columns.limit_cap L'.toTableTickets hG Base' U.phase.transport.injection (he'.trans_le he) Y _ h₂ hi.reference hx hY
    have hK: K s=0:= by
       change R.test u q (S.project q s )=_ -- adjust
       rw [← hu,R.affinity U.room.kernel.laws.toSymmetric U.phase.transport.injection, Prescription.highVan U.room.kernel.laws.toSymmetric U.phase.transport.injection H u he']
    change ‖K (P i)‖≤ _; exact Eq.trans_le (congr_arg (‖·‖) (show K (P i)=K (P i - s) by rw [map_sub,hK,sub_zero])) ((K.le_opNorm _).trans (mul_le_mul_of_nonneg_left hs (norm_nonneg _)))

omit U Base' hS
lemma bearing_lifetime (i:Exterior C.book) : Kept φ T 0 (fun _:L=> bearing i) ∧ Intervals φ T 0 (centerless L) (fun _=> bearing i):=by
    let z:= bearing i; obtain ⟨hp,he,hq⟩:= beside_distinct.mp (bearing_clear i)
    have hf (x y:E4)(h:x≠y){b:ℝ}(hb:0<b):∀ᶠ i in φ, Real.exp (-b*T i) <‖x-y‖:= (RateIs.exp (-b) hT|>.tends (neg_lt_zero.mpr hb) hT).eventually (gt_mem_nhds (norm_pos_iff.mpr (sub_ne_zero.mpr h)))
    exact ⟨fun _ h=> eventually_all.mpr fun i=> eventually_all.mpr fun j=> eventually_all.mpr fun e=> hf _ _ (he.ne e) h, fun _ h=> eventually_all.mpr fun i=> eventually_all.mpr fun j=> hf _ _ (hq i j) h⟩
lemma director_space -- helper arbitrary centered clearance
    {X:L→I→ E4}(hA:extentWithin φ T X a)(hp:Intervals φ T c (centerless L) Y)(hc:c<a): Intervals φ T c X Y:= by
    apply shrinking (q:=fun _=>0) hT hc _ hp; simpa only [sub_zero] using hA
lemma epoch_space {X:L→ I→ E4}(ht:Kept φ T b X)(hA:extentWithin φ T X a)(hp:0<a)(i:Exterior C.book):∀ᶠ k in φ, Injective (beside (X k) (bearing i)):= by
    obtain ⟨h₁,h₂⟩:= bearing_lifetime hT i; have he:=director_space hT hA h₂ hp
    exact ((ht.mono (le_max_left ..)).chorus (h₁.mono (le_max_right ..)) (he.mono (le_max_right ..))).inject

include U hS
-- cost against the fixed detectors; no dependence on exterior probes in their lists
lemma det_cost (h:Org.Grill C F)(u : Mode Λ)(hG: ∀ᶠ i in φ, Screen (w' i))(hA:extentWithin φ T w' a)(he:Kept φ T a w')(hp:0<a)
    (hk:Height C.S φ T k b)(hj:Height C.S φ T j d) (hb:0<b)(hd:b<d)(hv:RateLE φ T A c) :
    RateLE φ T (fun i=> R.ope u (w' i) g 0-R.test u q (S.project q (P i))) c:=by
    let S':= (R.sheet u); let r i (x):= (S' x) * (Prescription.reading S (w' i) g 0 x - S.spectra q (S.project q (P i)) x)
    unfold Prescription.ope Prescription.test; simp_rw [computes,← Finset.sum_sub_distrib,← mul_sub]; apply RateLE.sum hT _; intro x hx
    obtain ⟨h₁,h₂⟩:= bearing_lifetime hT x; have he':=epoch_space hT he hA hp x
    have ha:= see_cost (h:=h) U x.letter hT hS hG he' hv hk hj hd h₂ h₁ hb le_rfl le_rfl (fun _=>none)
    have hf: RateLE φ T (fun i=> Prescription.reading S (w' i) g 0 x-S.spectra q (S.project q (P i)) x) c:=by
       apply (RateLE.mono ha (by norm_num)).congr
       filter_upwards [he'] with i hi;
       -- one_test
       rw [← Prescription.one_test q _ _ U.room.kernel]; unfold Prescription.reading; simp only [sub_zero, if_pos hi, if_pos (bearing_clear _), spectator]; rfl
    exact ((RateLE.const (S' x) hT).mul hf).mono (by simp)
end YM.OPE
