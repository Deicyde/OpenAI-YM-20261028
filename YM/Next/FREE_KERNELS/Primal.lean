import YM.Next.FREE_KERNELS.Dispatch

/-!
# The canonical unmodified quadratic precision and pair, on the finite tori

Physical counting Shoot equations at every ratio of this history, without
stage-size hypotheses on L. These are also the equations used for the exterior
factorizations; so far not modifying the metrics on non-curvatures yet.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix Precision RG
open scoped Topology BigOperators ComplexConjugate
variable {j t : ℕ}

lemma reduce_signal (S : Side) (r) (q : Momentum) : signal 1 r q=(S.val:ℂ)⁻¹ • signal S r q := by rw [scale_signal S,smul_smul,inv_mul_cancel₀ (side_ne _),one_smul]; exact signal_unit ..
lemma reduce_mirage (S : Side) (r) (q : Momentum) : mirage 1 r q=(S.val:ℂ)⁻¹ • mirage S r q := by unfold mirage; rw [reduce_signal S,transpose_smul]
lemma reduce_rotor (S : Side) (k : ℝ) (v : Train j) (q : Momentum) : rotor 1 k v q=toll S 2 • rotor S k v q := by unfold rotor; rw [reduce_mirage S,reduce_signal S,Matrix.smul_mul,Matrix.mul_smul,Matrix.smul_mul,smul_smul,← pow_two,inv_pow]; rfl

namespace Flight
variable (P : Flight j t) (K : KernelChoices)

def duo (k : ℝ) (P : Flight j t) : Towers P.L where
  A0 := meshBook (pilot k) 1 [] P
  T := meshBook (wire k) 2 [] P
  mf := 0
  mn := 0
  o := 0

variable (k : ℝ) (hk : 0<k) {p : Momentum} (hp : p ∈ realCube zone)
include hk hp
lemma scaled_tri (l : Site P.L) :
    let q := aliasAt p l
    let H := pulse k P.wing q; let H' := pulse k P.land p
    let A := toll P.L 1 • pilot k P p l; let T := toll P.L 2 • wire k P p l
    let Q := toll P.L 3 • flux P 1 q
    rotor 1 k P.wing q * A=Q*rotor 1 k P.land p ∧
      mirage 1 1 q*T=Q*mirage 1 1 p ∧ T*H'*signal 1 1 p=H*signal 1 1 q*A := by
  intro q H H' A T Q
  obtain ⟨h1,h2,h3⟩ := genuine_alias P k hk hp l
  unfold A T Q
  have ht : toll P.L 1=(P.L.val:ℂ)⁻¹ := by simp [toll]
  have hb : toll P.L 1 * toll P.L 2=toll P.L 3 := by unfold toll; rw [← _root_.mul_inv]; rw [← pow_add]
  have hv : toll P.L 1*toll P.L 1=toll P.L 2 := by unfold toll; rw [← _root_.mul_inv]; rw [← pow_add]
  refine ⟨?_,?_,?_⟩
  · rw [reduce_rotor P.L k _ q,Matrix.mul_smul,Matrix.smul_mul,Matrix.smul_mul,smul_smul,hb,h1]
  · rw [reduce_mirage P.L 1 q,← ht,Matrix.mul_smul,Matrix.smul_mul,Matrix.smul_mul,smul_smul,mul_comm (toll P.L 2),hb,h2]
  rw [reduce_signal P.L 1 q,← ht,Matrix.smul_mul,Matrix.smul_mul,Matrix.mul_smul,Matrix.mul_smul,Matrix.smul_mul,smul_smul,hv,h3]
lemma scaled_mul : going P p * fromBank P (pilot k) 1 p = 1-(k:ℂ)⁻¹ • rotor 1 k P.land p := by
  unfold going fromBank; rw [alias_inner,← genuine_sum P k hk hp]; refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.smul_mul,Matrix.mul_smul, smul_smul,toll,pow_one,mul_inv_cancel₀ (side_ne _),one_smul]
omit hk hp
lemma adjust_adj :
    ∀ p : Momentum, physical p → (stageVolume P.L)⁻¹ • (going P p)ᴴ = downAlias fun l : Site P.L => toll P.L 3 • flux P 1 (aliasAt p l) := by
  intro p hp; unfold going; rw [alias_up,alias_pay]; congr! 2 with l
  rw [Matrix.conjTranspose_smul, ← flux_herm P _ (alias_real hp l),smul_smul]; unfold toll stageVolume
  congr 1; simp; have he := side_ne P.L; field_simp

variable (ht : 4≤t) {c f : Side} (hc : f.val=c.val*P.L.val)

include ht
lemma tangent :
    let k := K.penalty; let W := pulse k P.wing; let W' := pulse k P.land; let S := visit P K hc
    let V := duo k P; let A := installed (P.visitRatio hc) V.A0; let T := installed (P.visitRatio hc) V.T
    Inputs S A ((record W).acts f) ((record W').acts c) ∧
      T.transpose * d 1 f = d 1 c * mean S ∧ T*((record W').acts c)*d 1 c=(record W).acts f*d 1 f*A := by
  intro k W W' S V A T
  have hj : 4≤j := P.legal
  have hk : 0<k := K.penalty_pos
  let A' p := P.fromBank (pilot k) 1 p; let T' p := P.fromBank (wire k) 2 p
  let r := P.visitRatio hc
  obtain ⟨hA,hT⟩ := secure_both k hk hj ht
  have hX : Runs (readings r (TypeFace 1)) (rotations c (TypeFace 1)) A (solo c A') := P.sail_run hc hA hj 1
  have hY : Runs (readings r (TypeFace 2)) (rotations c (TypeFace 2)) T (solo c T') := P.sail_run hc hT hj 2
  have hQ := phi_run P K hc
  let Q p := downAlias fun l : Site P.L => toll P.L 3 • flux P 1 (aliasAt p l)
  have hv : stageVolume c/stageVolume f=(stageVolume P.L)⁻¹ := by rw [ratio_volume r]; change stageVolume c / (stageVolume c * stageVolume P.L) = _; field_simp [stage_ne]
  have hq : Runs (readings r (TypeFace 1)) (rotations c (TypeFace 1)) (mean S).transpose (solo c Q) := by
    have hh := hQ.back (rotations_crew c _) (readings_crew _ _)
    rw [hv] at hh; unfold solo at hh; rw [fiber_H,fiber_weight] at hh
    have hd (p : Site c) := adjust_adj P _ (show physical (mon p) from real_frequency p)
    simp_rw [hd] at hh; exact hh
  have hK := runs_rotor_fine _ hk hj P.wing r P.odd
  have hK' := runs_rotor _ hk ht P.land c
  have hd := (cobound_true 1).fine r P.odd
  have hd' := (cobound_true 1).coarse c
  have hm (p : Site c) := base_subset_realCube zone_pos (mon_mem c p)
  refine ⟨⟨?_,?_⟩,?_,?_⟩
  · have hh : braceAll r (rotor 1 k P.wing)*solo c A'=solo c Q * solo c (rotor 1 k P.land) := by
      unfold braceAll solo; rw [fiber_mult,fiber_mult]
      congr! 2 with p
      unfold A' Q fromBank; rw [alias_after,alias_then]; exact congr_arg downAlias (funext fun l => (scaled_tri P k hk (hm p) l).1)
    have he := hK.product hX; rw [hh] at he; exact he.lands (hq.product hK') (rotations_crew c _)
  · have he := hQ.product hX
    have hu := (Runs.nil (rotations c (TypeFace 1))).minus (hK'.smult k⁻¹)
    have hh : solo c (going P)*solo c A'=1-(↑(k⁻¹):ℂ) • solo c (rotor 1 k P.land) := by
      unfold solo; rw [fiber_mult,fiber_weight,← fiber_one, fiber_less]; congr! 2 with p
      rw [Complex.ofReal_inv]; exact scaled_mul P k hk (hm p)
    rw [hh] at he; exact he.lands hu (rotations_crew c _)
  · have h1 := (hd.back (readings_crew _ _) (readings_crew _ _)).product hY
    have h2 := hq.product (hd'.back (rotations_crew _ _) (rotations_crew _ _))
    rw [div_self (stage_ne f),one_smul] at h1; rw [div_self (stage_ne c),one_smul] at h2
    have hh : (braceAll r (signal 1 1))ᴴ * solo c T'= solo c Q * (solo c (signal 1 1))ᴴ := by
      unfold braceAll solo; simp only [fiber_H,fiber_mult]
      congr! 2 with p
      unfold Q T' fromBank; rw [alias_after,alias_then]; congr! 2 with l
      rw [← mirage_herm _ _ (alias_real (hm p).1 _),← mirage_herm _ _ (hm p).1]; exact (scaled_tri P k hk (hm p) l).2.1
    rw [hh] at h1; have he := h1.lands h2 (rotations_crew c _)
    apply transpose_injective; simp only [transpose_mul, transpose_transpose]; exact he
  have hW := (heart_true _ hk hj P.wing).1.fine r P.odd
  have hW' := (heart_true _ hk ht P.land).1.coarse c
  have h1 := (hY.product hW').product hd'; have h2 := (hW.product hd).product hX
  have hh : solo c T'*solo c W'*solo c (signal 1 1)=braceAll r W*braceAll r (signal 1 1)*solo c A' := by
    unfold solo braceAll; simp only [fiber_mult]; congr! 2 with p
    unfold T' A' fromBank; rw [alias_then,alias_then,alias_after]
    exact congr_arg downAlias (funext fun l => (scaled_tri P k hk (hm p) l).2.2)
  change Runs _ _ _ (solo c T'*solo c W'*_) at h1; rw [hh] at h1; exact h1.lands h2 (rotations_crew c _)
end Flight
end YM.Next.Free
