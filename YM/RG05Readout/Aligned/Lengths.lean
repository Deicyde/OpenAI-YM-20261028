import YM.RG05Readout.Aligned.Columns

/-!
# Spatial inverse and row-wise bound with engineering powers

For literal-point master coordinates. The bounds apply through the
full tail of observation levels (for EVERY finite horizon), including
the automatically chosen d64 real-covariant prescription. Establishes
an initial inverse on this calibration, using no perturbative assumptions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Aligned
open Filter Function Set Topology OPE Orbits Labels Extra.Histories Charts Motion Extraction
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff
variable {G:Gauge} {C:Family G} {f:Extraction.Order} {S:Table C.book} (U:Spec.Final C f S)
    (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
    {h:C.Makes} {φ:Filter (ℕ×ℕ)}
variable (W:Windows C h φ) (hf:φ ≤ f.fuse) [φ.NeBot]

namespace Windows
open Work.G08 Next.UVStress
set_option quotPrecheck false
local notation "σ" => C.S.scale

lemma ingress_rate (C:Family G): RateLE atTop (C.S.scale) (ingress C) 0 := by
    intro ε he; filter_upwards [Work.D01.columnLogs_le C.path.levels ε he] with i hi
    rw [Real.norm_of_nonneg (zero_le_one.trans (ingress_one _ i))]; exact Real.exp_monotone hi

lemma restore_cost (d:ℕ) : RateLE atTop σ (fun m=> W.restore S d m) (d:ℝ) := by
    let f := LinearMap.toContinuousLinearMap (S.representative d)
    let c := (Fintype.card (C.labels.level d).Index:ℝ)*‖f‖
    have hc: RateLE atTop σ (fun i=> (C.S.a i^d)⁻¹ * ingress C i * c) (d:ℝ) := by
      have hm : Height C.S atTop σ id 1 := level_height tendsto_id
      have hz := (((hm.mesh.power d).inv.pays C.S.divergent).mul (ingress_rate C)).mul (RateLE.const c C.S.divergent)
      simpa only [id_eq,mul_neg, mul_one, neg_neg, add_zero,one_mul] using hz
    apply hc.of_norm_le (Eventually.of_forall fun i =>ContinuousLinearMap.opNorm_le_bound _ ?_ (W.physical_inverse_cost d i))
    unfold c; have hv : 0 < C.S.a i := C.S.a_pos i; have ht : 0 ≤ ingress C i := zero_le_one.trans (ingress_one ..); positivity

variable (hs:Services C f S)
include hf hs W U R
private lemma row_est (d e:ℕ)(hd:e ≤ d)(M:ℕ)(hM:C.ref d≤ M)(x:C.label d):
    let F:= LinearMap.toContinuousLinearMap ((R.cutTest e d).comp (S.project d))
    ‖R.cutTest e d (W.physical S d M x)‖ ≤ ‖F‖*(if e=0 then outgress C d M
       else Columns.fare C M d (e-1)) * C.S.a M^d * (C.labels.level d).coeffSize x := by
    intro F
    let Y:= C.labels.level d
    let v (i:ℕ×ℕ): C.label d:= masterRef h d M i.1 i.2 x -- cutoff i binder
    let a:= W.ref d M x; let s:= C.S.a M^d * Y.coeffSize x
    have hi : ∀ᶠ i:ℕ×ℕ in φ, M ≤ i.1:=(Push.RelayDifference.cutoff_grows f).eventually_ge_atTop M |>.filter_mono hf
    have he : ∀ᶠ i:ℕ×ℕ in φ, quota C d M i.1 i.2 (v i) ≤ s:= hi.mono fun i hi=> (master_quota h d M i.1 i.2 hM hi x).le
    have hz:Tendsto v φ (𝓝 a):= W.ref_tend d M tendsto_const_nhds
    obtain ⟨u,r,D,L⟩:=hs.purchase
    obtain ⟨A,G,B,X,H⟩:=hs.along
    split
    next he0 =>
      have hA : ‖a‖ ≤ outgress C d M*s := le_of_tendsto hz.norm (hi.mono fun i hi => calc
          _ ≤ Y.coeffSize (v i) := Size.norm_le ..
          _ = Y.coeffSize ((window C h d M i.1 i.2).symm (((C.S.a M:ℂ)^d) • x)) := by
             unfold v masterRef; rw [_root_.smul_apply, map_smul]; rfl
          _ ≤ outgress C d M*s := (outer_charge C h d i.1 i.2 M _).trans_eq (by rw [Size.smul]; simp [Y,s,Real.norm_of_nonneg (C.S.a_pos _).le]))
      calc _ = ‖F a‖:=rfl
           _ ≤ ‖F‖*‖a‖:= F.le_opNorm _
           _ ≤ _:=by dsimp only [s,Y] at hA; rw [mul_assoc, mul_assoc]; gcongr
    next he0 =>
      have hD : e-1 < e:=by omega
      obtain ⟨b, ⟨u,ht⟩,hab⟩:= Columns.limit_cap (d:=d) L.toTableTickets hs.simpleGate H R.lifts (hD.trans_le hd) v _ hf hM he hz
      have hu : F b=0 := by
        change R.cutTest e d (S.project d b)=_; rw [← ht,R.cut_rise,R.kills_lower _ _ hD]
      calc _ = ‖F (a-b)‖ := by rw [map_sub,hu,sub_zero]; rfl
           _ ≤ ‖F‖*‖a-b‖ := F.le_opNorm _
           _ ≤ _ := by dsimp only [Y,s] at hab; rw [mul_assoc, mul_assoc]; gcongr

lemma row_cost (d e:ℕ)(hd:e≤d) :
    RateLE atTop σ (fun m=> (LinearMap.toContinuousLinearMap (R.cutTest e d)).comp (W.physical S d m)) (-(e:ℝ)) := by
    let g0:= LinearMap.toContinuousLinearMap ((R.cutTest e d).comp (S.project d))
    let k:ℝ := Fintype.card (C.labels.level d).Index
    let v (i:ℕ):= if e=0 then outgress C d i else Columns.fare C i d (e-1)
    have hm : Height C.S atTop σ id 1 := level_height tendsto_id
    have ht:= C.S.divergent
    obtain ⟨u,r,D,L⟩:=hs.purchase
    have he : RateLE atTop σ v ((d-e:ℕ):ℝ) := by
      by_cases he:e=0
      · subst e
        have hb : RateLE atTop σ (outgress C d) d := by
           change RateLE atTop _ (fun m=> outgress C d m) _
           simpa only [outgress,Real.exp_add, ingress, add_zero] using! (RateLE.exp (d:ℝ) ht).mul (ingress_rate C)
        simpa only [v, if_pos, Nat.sub_zero] using hb
      · simp_rw [v,if_neg he]; simpa only [show e-1+1=e by omega,mul_one,id_eq] using (Columns.fare_rate (v:=id) (d:=d) (e:=e-1) L.toTableTickets tendsto_id ht hm.pace).pays ht
    have hA : RateLE atTop σ (fun i=> ‖g0‖* v i * C.S.a i ^ d*k) (-(e:ℝ)) := by
      have hz := (((RateLE.const ‖g0‖ ht).mul he).mul ((hm.mesh.power d).pays ht)).mul (RateLE.const k ht)
      rwa [Nat.cast_sub hd, add_zero, zero_add, mul_neg,mul_one, sub_add_eq_add_sub,add_neg_cancel,zero_sub] at hz
    refine hA.of_norm_le ?_
    filter_upwards [eventually_ge_atTop (C.ref d)] with i hi
    have hv : 0≤ v i:=by unfold v; split; exacts [zero_le_one.trans (outgress_one ..),(Columns.fare_pos ..).le]
    have ha := C.S.a_pos i; have hk: 0≤ k:=Nat.cast_nonneg _
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun x => ?_)
    have hC :(C.labels.level d).coeffSize x ≤ k*‖x‖:=by simpa only [Frame.coeffSize,nsmul_eq_mul,k] using Pi.sum_norm_apply_le_norm (G:=fun _:(C.labels.level d).Index=>ℂ) x
    apply (row_est U R W hf hs d e hd i hi x).trans
    rw [mul_assoc (a:=‖g0‖ * v i * C.S.a i^d)]
    exact mul_le_mul_of_nonneg_left hC (show 0≤ ‖g0‖ * v i * C.S.a i^d from by positivity)
end Windows
end YM.RG05Readout.Aligned
