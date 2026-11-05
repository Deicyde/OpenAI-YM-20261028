import YM.Extra.SOURCE_HISTORIES.Retained
import YM.OPE.Orbits.Kernel

/-!
# Aligned intermediate reports -- columns and inverse readout

In `Aligned` we first prove results for **literal** placement with the
actual (no joint-address weight yet) column normalization `peek`. Do NOT
identify these numbers with the A convention! These are physical
prerequisites / a simpler intermediate version of the estimates, proving
them e.g. for the actual possibly translated and engineering-normalized
singleton columns already in the common Family.

At ALL fixed finite d,m we take the two-sided priced windows to the same
ordered sublimit (every valid filter admitted below), supplying physical
columns in the true quotient and a quantitative bound on a right inverse.
The consumer may refine as needed. This is not an estimate by a polynomial
of Lambda -- this inverse is for spatial discrepancies.
-/

set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout
open Filter Function Lattice Extraction Topology
open scoped Topology BigOperators Classical

/-- Use only along a prescribed subextraction; no uniform mesh x period
claim is licensed by such limits. -/
lemma bounded_ulim {I Y : Type*} {𝓤 : Ultrafilter I} [NormedAddCommGroup Y] [ProperSpace Y]
    (v : I → Y) (c : ℝ) (h : ∀ᶠ i in (𝓤 : Filter I), ‖v i‖ ≤ c) :
    ∃ x, Tendsto v (𝓤 : Filter I) (𝓝 x) := by
    obtain ⟨f,hf,hn,x,hx⟩ := Next.UVStress.finite_extract v c h
    rw [𝓤.unique hf] at hx
    exact ⟨x,hx⟩

lemma level_height {ι:Type*} {φ : Filter ι} {C:Schedule} {m:ι→ℕ}
    (hm:Tendsto m φ atTop) : OPE.Height C φ (fun i=> C.scale (m i)) m 1 :=
  ⟨hm, tendsto_const_nhds.congr' (((C.divergent.comp hm).eventually_gt_atTop 0).mono
      fun _i hi => (div_self hi.ne').symm)⟩

namespace Aligned
open OPE Orbits Labels Extra.Histories Charts Motion
variable {G:Gauge} {C:Family G} {f:Extraction.Order} {S:Table C.book} (U: Spec.Final C f S)
    (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
variable (h:C.Makes) {φ:Filter (ℕ×ℕ)}
set_option quotPrecheck false
local notation "K" => window C h
local notation "g" => glass C h

/-- These intermediate continuum limits are reported on actual
`Spec.Final` local (literal-point) fields. Keep h C.Makes (proof parameter
only). -/
structure Windows (C:Family G) (h:C.Makes) (φ:Filter (ℕ×ℕ)) where
    iso : ∀ d:ℕ, ℕ → Exchange C d
    price (d m:ℕ) : Tendsto (fun i:ℕ×ℕ => glass C h (d,m) i.1 i.2) φ (𝓝 (pose C (iso d m)))

include h
lemma take_windows (𝓤:Ultrafilter (ℕ×ℕ)) : Nonempty (Windows C h (𝓤:Filter _)) := by
    have he (d m:ℕ) : ∃ Z: Exchange C d,
      Tendsto (fun i:ℕ×ℕ => g (d,m) i.1 i.2) (𝓤:Filter _) (𝓝 (pose C Z)) := by
        let F:= C.labels.level d
        let A := ingress C m * (Fintype.card F.Index : ℝ)
        let B := outgress C d m * (Fintype.card F.Index : ℝ)
        have hb := zero_le_one.trans (ingress_one C m)
        have hb' := zero_le_one.trans (outgress_one C d m)
        have hs (v:C.label d) : F.coeffSize v ≤ (Fintype.card F.Index:ℝ)*‖v‖ := by
          simpa only [Frame.coeffSize,nsmul_eq_mul] using Pi.sum_norm_apply_le_norm (G:=fun _:F.Index=>ℂ) v
        obtain ⟨⟨Z,Q⟩,hz⟩:= bounded_ulim (𝓤:=𝓤) (fun i:ℕ×ℕ => g (d,m) i.1 i.2) (max A B) (by
          filter_upwards with i
          rw [Prod.norm_def,max_le_iff]
          refine ⟨le_trans ?_ (le_max_left ..), le_trans ?_ (le_max_right ..)⟩
          · apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hb (by positivity))
            intro v; exact (Size.norm_le F _).trans (le_trans (incoming C h d i.1 i.2 m v)
               ((mul_le_mul_of_nonneg_left (hs v) hb).trans_eq (mul_assoc ..).symm))
          apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hb' (by positivity))
          intro v; exact (Size.norm_le F _).trans (le_trans (outer_charge C h d i.1 i.2 m v)
               ((mul_le_mul_of_nonneg_left (hs v) hb').trans_eq (mul_assoc ..).symm)))
        have ha := hz.fst_nhds
        have hh := hz.snd_nhds
        have ht : LeftInverse Q Z := fun y=> tendsto_nhds_unique
          (Dash.arcing hh (Dash.arcing ha (tendsto_const_nhds (x:=y)))) (by
            simp only [glass,pose]; apply tendsto_const_nhds.congr; intro i; exact ((K d m i.1 i.2).symm_apply_apply y).symm) -- orientation
        have hu : RightInverse Q Z := fun y=> tendsto_nhds_unique
          (Dash.arcing ha (Dash.arcing hh (tendsto_const_nhds (x:=y)))) (by
            simp only [glass,pose]; apply tendsto_const_nhds.congr; intro i; exact ((K d m i.1 i.2).apply_symm_apply y).symm)
        let Y : Exchange C d := ⟨{ Z.toLinearMap with
             toFun:= Z, invFun:= Q, left_inv:= ht, right_inv:=hu }, Z.cont, Q.cont⟩
        exact ⟨Y,hz⟩
    choose Z hz using he; exact ⟨⟨Z,hz⟩⟩

variable (d m N n: ℕ)
/-- The label of the master column, in actual `ref` coordinates,
with the physical engineering factor put back, threshold units. -/
def masterRef : C.label d →L[ℂ] C.label d :=
    ((C.S.a m:ℂ)^d) • ((K d m N n).symm:Linear C d)
local notation "d₁"=> (C.labels.level d)
local notation "Q"=> masterRef h

lemma window_masterRef (v : C.label d) : K d m N n (masterRef h d m N n v) =
      ((C.S.a m:ℂ)^d) • v := by
    unfold masterRef
    rw [_root_.smul_apply,map_smul]; simp

lemma unit_masterRef (hm:C.ref d ≤ m) (hv:m ≤ N):
    masterRef h d m N n (d₁).e0=C.refUnit d:=
  (K d m N n).injective ((window_masterRef ..).trans (chart_unit C h d N n m hm hv).symm)

lemma master_quota (hm:C.ref d ≤ m) (hv:m ≤ N)(x : C.label d) :
     Next.UVStress.quota C d m N n (Q d m N n x) = (C.S.a m)^d * (d₁).coeffSize x := by
    rw [Next.UVStress.quota, ← peek C h d N n m hm hv, window_masterRef, Size.smul]
    simp only [Complex.norm_pow,Complex.norm_real,Real.norm_of_nonneg (C.S.a_pos _).le]

variable {h} (W:Windows C h φ)

namespace Windows
-- oriented threshold master coordinate, standardized on limit

def ref (d m:ℕ) : C.label d →L[ℂ] C.label d :=
    ((C.S.a m:ℂ)^d) • ((W.iso d m).symm:Linear C d)

def physical (S:Table C.book) (d m:ℕ) : C.label d →L[ℂ] S.Field d :=
    (LinearMap.toContinuousLinearMap (S.project d)).comp (W.ref d m)

lemma ref_tend {v:ℕ×ℕ→ C.label d} {x:C.label d} (hv:Tendsto v φ (𝓝 x)):
    Tendsto (fun i:ℕ×ℕ=>Q d m i.1 i.2 (v i)) φ (𝓝 (W.ref d m x)) := by
    apply ((tendsto_const_nhds (x:=((C.S.a m:ℂ)^d))).smul (Dash.arcing ((W.price d m).snd_nhds) hv))

lemma master_unit [φ.NeBot](hf:φ≤ f.fuse)(S:Table C.book)(ht:C.ref d≤ m):
    W.physical S d m (C.labels.level d).e0=S.unit d := by
    have hv := W.ref_tend d m (v:=fun _=>(C.labels.level d).e0) tendsto_const_nhds
    have he : W.ref d m (C.labels.level d).e0 = C.refUnit d := tendsto_nhds_unique hv (by
      apply tendsto_const_nhds.congr'
      filter_upwards [(Push.RelayDifference.cutoff_grows f).eventually_ge_atTop m |>.filter_mono hf] with i hi
      exact (unit_masterRef h d m i.1 i.2 ht hi).symm
      )
    change S.project d (W.ref d m _)=_; rw [he]; rfl

/-- Exact right inverse on the ACTUAL quotient. For these literal-point
columns in the prescription C, surjectivity on that horizon's quotient can
be obtained before even invoking any Gram/pivot assumption. -/
def restore (S:Table C.book)(d m:ℕ) : S.Field d →L[ℂ] C.label d :=
    (((C.S.a m:ℂ)^d)⁻¹) • ((W.iso d m: Linear C d).comp (LinearMap.toContinuousLinearMap (S.representative d)))

@[simp]
lemma physical_restore (u:S.Field d): W.physical S d m (W.restore S d m u)=u:=by
    let A := (C.S.a m:ℂ)^d; have ht:A ≠ 0:= pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (C.S.a_pos _).ne')
    change S.project d (A • ((W.iso d m).symm (A⁻¹ • W.iso d m (S.representative d u))))=_
    rw [map_smul (W.iso d m).symm,ContinuousLinearEquiv.symm_apply_apply,smul_smul,mul_inv_cancel₀ ht,one_smul,S.rep]

lemma ref_cost [φ.NeBot] (v:C.label d): (d₁).coeffSize (W.iso d m v) ≤
     ingress C m * (d₁).coeffSize v :=
  le_of_tendsto' ((Size.continuous (d₁)).continuousAt.tendsto.comp
     (Dash.arcing ((W.price d m).fst_nhds) (tendsto_const_nhds (x:=v)))) (fun i=> incoming C h d i.1 i.2 m v)

lemma physical_inverse_cost [φ.NeBot](u:S.Field d):
    ‖W.restore S d m u‖ ≤ (C.S.a m ^ d)⁻¹ * ingress C m *
        ((Fintype.card (d₁).Index:ℝ) * ‖LinearMap.toContinuousLinearMap (S.representative d)‖) * ‖u‖:=by
    let Y := LinearMap.toContinuousLinearMap (S.representative d)
    calc _ = (C.S.a m ^ d)⁻¹ * ‖W.iso d m (Y u)‖ := by
                  change ‖((C.S.a m:ℂ)^d)⁻¹ • W.iso d m (Y u)‖=_; rw [norm_smul,norm_inv,Complex.norm_pow,Complex.norm_real,Real.norm_of_nonneg (C.S.a_pos m).le]
         _ ≤ (C.S.a m ^ d)⁻¹ * (ingress C m * (d₁).coeffSize (Y u)) :=
                   mul_le_mul_of_nonneg_left ((Size.norm_le ..).trans (W.ref_cost d m _)) (inv_nonneg.mpr (pow_nonneg (C.S.a_pos m|>.le) _))
         _ ≤ _ := by
           let t := Fintype.card (d₁).Index
           have ha : (d₁).coeffSize (Y u) ≤ (t:ℝ)*‖Y‖*‖u‖ := calc
             _ ≤ t*‖Y u‖ := by simpa only [Frame.coeffSize,nsmul_eq_mul] using Pi.sum_norm_apply_le_norm (G:=fun _:(d₁).Index=>ℂ) (Y u)
             _ ≤ _ := by rw [mul_assoc]; gcongr; exact Y.le_opNorm u
           apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ha
             (zero_le_one.trans (ingress_one C m))) (inv_nonneg.mpr (pow_nonneg (C.S.a_pos m|>.le) _)))
           dsimp only [Y,t]; ring_nf; exact le_rfl

end Windows

end Aligned
end YM.RG05Readout
