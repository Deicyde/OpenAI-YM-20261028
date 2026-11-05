import YM.OPE.Log.Grid
import YM.RG05Readout.Aligned.Lengths
/-!
# Procurement for WM observation geometry

Λ=2+log(hatBeta) is NOT a power of the physical spacing logarithm and
observations must not be moved by polynomial powers of inverse coupling
at will. `brackets` supplies the spatial capture geometry at the ACTUAL
admitted WM radii, with constants for finite fixed shapes. Need an extra
step relative to the enclosing cell in this version of `Ballet`. Doesn't
yet purchase the analytic (e.g. log-price for the overshoot) bounds then
needed for qpta. The `Plot` estimate is for *aligned* offset in this
first version; scale and hull calculations here useful for both.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout
open Filter Topology Set Function
open scoped Topology BigOperators ContDiff Classical
variable {ι : Type} {l:Filter ι} {m j:ι→ℕ} {S:Schedule} {T r : ι→ℝ}
open OPE

private lemma spacing_inf (S:Schedule) (e:ℝ) : ∃ i:ℕ,e < S.scale i:= (S.divergent.eventually_gt_atTop e).exists

/-- least stop with spacing BELOW a given positive physical length. -/
def crossLevel (S:Schedule)(r:ℝ):ℕ:= Nat.find (spacing_inf S (-Real.log r))

lemma pace_crossing (hp:S.Gentle)(ht:Tendsto T l atTop)(hr:RateIs l T r (-1)) :
   let p i:=crossLevel S (r i)
   Height S l T p 1 ∧ ∀ᶠ i in l, S.a (p i)< r i ∧ r i ≤ S.a (p i-1):=by
    intro p; let a i := -Real.log (r i)
    have h : Tendsto r l (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr ⟨hr.tends neg_one_lt_zero ht, hr.pos⟩
    have he := run_towards h
    have hz : Tendsto (fun i=>a i/T i) l (𝓝 1):=by simp only [a,neg_div]; simpa only [neg_neg] using hr.rate.neg -- inspect
    have hv(i): a i < S.scale (p i):= Nat.find_spec (spacing_inf S (a i))
    have hξ := found_up he hz S hp
    obtain ⟨q,hq,hQ⟩:= hξ
    have hx:Tendsto p l atTop:=tendsto_atTop.mpr fun j=>by
       filter_upwards [he.eventually_ge_atTop (S.scale j)] with i hi
       exact (scale_mono S).le_iff_le.mp (le_trans hi (hv i).le)
    constructor
    · exact ⟨hx, tendsto_of_tendsto_of_tendsto_of_le_of_le' hz hq.pace
            ((ht.eventually_gt_atTop 0).mono (fun i hi=> div_le_div_of_nonneg_right (hv i).le hi.le))
            ((ht.eventually_gt_atTop 0).mono (fun i hi=> div_le_div_of_nonneg_right ((scale_mono S).monotone (show p i ≤ q i from Nat.find_min' _ (hQ i))) hi.le))⟩
    filter_upwards [hr.pos,hx.eventually_gt_atTop 0] with i hi hJ
    constructor
    · apply (Real.log_lt_log_iff (S.a_pos _) hi).mp
      apply neg_lt_neg_iff.mp
      rw [← Real.log_inv (S.a (p i))]; exact hv _
    apply (Real.log_le_log_iff hi (S.a_pos _)).mp
    apply neg_le_neg_iff.mp; rw [← Real.log_inv]
    exact not_lt.mp (Nat.find_min (spacing_inf S (a i)) (show p i-1<p i by omega))

variable {G:Gauge} {C:Family G} {X:RG.Levels G} {B M η:ℝ}
open RG
/-- Mast/log convention. -/
def Lambda (X:Levels G)(m:ℕ):= 2+Real.log (X.clock.hatBeta m)
lemma lambda_gt (X:Levels G)(m:ℕ):2<Lambda X m:=lt_add_of_pos_right _ (Real.log_pos (X.fits.delayed _))
lemma lambda_growth (hG:G.Simple) (X:Levels G) : Tendsto (Lambda X) atTop atTop:=
    tendsto_atTop_add_const_left _ _ (Real.tendsto_log_atTop.comp (Next.Rank.Station.hat_rate _ hG))
lemma lambda_rate (hG:G.Simple)(ht:Tendsto T l atTop)(hj:Height X.S l T j 1): RateIs l T (fun i=>Lambda X (j i)) 0 := by
    -- hat budget from schedule, not from un-hatted representation
    have hx : RateLE l T (fun i=> X.clock.hatBeta (j i)) 0 := by
      have hr : RateIs l T (fun i=>X.clock.hatBeta (j i)) 0:= by
          let u:= X.clock.hatBeta; have he:Tendsto (fun i=>Real.log (u i)/X.S.scale i) atTop (𝓝 0):= (Work.I04.hat_receipt X hG).tendsto_div_nhds_zero
          have hp : MergeProof.Ribbons.Note X.S u 0:= ⟨fun i=>zero_lt_one.trans (X.fits.delayed _),he⟩
          exact height0 hp hj
      exact hr.pays ht
    refine RateIs.of_sandwich (RateIs.const ht two_pos)
           ((RateLE.const (2:ℝ) ht).add hx ht) (Eventually.of_forall fun i=> (lambda_gt X _).le) ?_ ht
    exact Eventually.of_forall fun i=> add_le_add_right (Real.log_le_self (zero_le_one.trans (X.fits.delayed _).le)) _

lemma budgetW (X:Levels G)(m:ℕ): ((X.budget m).B : ℝ) < Lambda X m ^ (2:ℕ):=by
    let x:= Real.log (X.clock.hatBeta m)
    have hh:0<x:=Real.log_pos (X.fits.delayed _)
    refine lt_trans (Nat.ceil_lt_add_one (sq_nonneg x)) ?_
    change x^2 + 1 < ((2+x)^2); linarith only [hh]

lemma shelf (hG:G.Simple)(hr:0<η)(hh:4<B): ∀ᶠ i in atTop,
    2*((X.budget i).B:ℝ)^2 < η*Lambda X i^B:=by
    have hb : Tendsto (fun i=> (Lambda X i)^(B-4)) atTop atTop :=
          (tendsto_rpow_atTop (sub_pos.mpr hh)).comp (lambda_growth hG X)
    filter_upwards [(hb.const_mul_atTop hr).eventually_ge_atTop 2] with i hi
    let x:= Lambda X i; have hx:0<x:= zero_lt_two.trans (lambda_gt ..); have he: η*x^(B-4) ≥ 2:=hi
    have h₁ : ((X.budget i).B:ℝ) ^ 2 < (x^2)^2:= pow_lt_pow_left₀ (budgetW ..) (Nat.cast_nonneg _) (by decide)
    change _ < η*x^B
    calc _ < 2*x^(4:ℕ):=(mul_lt_mul_of_pos_left h₁ two_pos).trans_eq (by ring)
         _ ≤ η*x^(B-4)*x^(4:ℕ):= mul_le_mul_of_nonneg_right he (pow_nonneg hx.le _)
         _ = _ := by
           have hk : x^(B-4) * x^(4:ℕ) = x^B:=by
             rw [← Real.rpow_natCast, ← Real.rpow_add hx]; norm_num
           rw [mul_assoc,hk]

/-- Observation length *window*. Wrt the schedule hatted beta. -/
def measured (X:Levels G)(j:ℕ)(r B:ℝ) := X.S.a j * Lambda X j^B ≤ r ∧ r ≤ X.S.a j * Lambda X j^(B+1)

lemma measured_rate (hG:G.Simple)(ht:Tendsto T l atTop)(hj:Height X.S l T j 1)
    (hv:∀ᶠ i in l, measured X (j i) (r i) B) : RateIs l T r (-1):= by
    have hi:= lambda_rate hG ht hj
    exact RateIs.of_sandwich ((hj.mesh.mul (hi.rpow B)).swap (by ring)) (((hj.mesh.mul (hi.rpow (B+1))).swap (by ring)).pays ht) (hv.mono fun _ hi=> hi.1) (hv.mono fun _ hi=>hi.2) ht


namespace Aligned
open MergeProof MergeProof.Accent
variable {I : Type} [Fintype I] {Y:ι→I→ Lattice.Cover}

/-- Two ancestral cells needed when using `joins`, even though we still
reach the same height. -/
def captureAt (C:Family G) (M r:ℝ) := crossLevel C.S ((8*M+2)*r)-1-1
set_option quotPrecheck false
local notation "b₁" => fun i=> captureAt C M (r i)

lemma brackets (hM:0≤M)(ht:Tendsto T l atTop)(hv:RateIs l T r (-1)) :
    Height C.S l T (b₁) 1 ∧ (∀ᶠ i in l, (8*M+2)*r i ≤ C.S.a (captureAt C M (r i)+1) ∧
      C.S.a (captureAt C M (r i)+2)< (8*M+2)*r i) := by
    have hi:0<8*M+2:=by linarith only [hM]
    obtain ⟨hp,hw⟩:= pace_crossing C.path.levels.fits.mesh ht (((RateIs.const ht hi).mul hv).swap (zero_add _)); let a i:=crossLevel C.S ((8*M+2)*r i)
    have hy:= Log.previous ht hp C.path.levels.fits.mesh
    refine ⟨Log.previous ht hy C.path.levels.fits.mesh,?_⟩
    filter_upwards [hw,hp.grows.eventually_ge_atTop 2] with i hi he
    change 2 ≤ a i at he
    change ((8*M+2)*r i ≤ C.S.a (a i-1-1+1)) ∧ C.S.a (a i-1-1+2) < _
    rw [show a i-1-1+2=a i from by omega, show a i-1-1+1=a i-1 from by omega]; exact hi.symm

omit [Fintype I] in
lemma book {k:ℕ}(hG:G.Simple)(ht:Tendsto T l atTop)(hj:Height C.S l T j 1)
    (hr:∀ᶠ i in l, measured C.path.levels (j i) (r i) B)
    (hh:4 < B)(hη:0 < η)(hM:0 ≤ M):∀ᶠ i in l, ∀ x:I→ Lattice.Cover,
     WithinRoom (r i) M η (C.S.gridPoint (j i) ∘ x) 0 →
       Plot C k (b₁ i) (j i) x := by
    have hm := measured_rate hG (X:=C.path.levels) ht hj hr
    obtain ⟨hK,hU⟩:= brackets (C:=C) hM ht hm
    filter_upwards [hr,hK.grows.eventually_ge_atTop k,hm.pos,hU,hj.grows.eventually (shelf (X:=C.path.levels) hG hη hh)] with i he hi hy hA hx x hw
    have hX:=hA.1
    let s:= Lambda C.path.levels (j i)
    have hu:= lambda_gt C.path.levels (j i)
    have hz: 1 < s^B:= Real.one_lt_rpow (one_lt_two.trans hu) (by linarith only [hh]); let a:= C.S.a (j i)
    have hv:a < r i:= lt_of_lt_of_le (lt_mul_of_one_lt_right (C.S.a_pos _) hz) he.1
    have hP : r i ≤ (8*M+2)*r i:= le_mul_of_one_le_left hy.le (by linarith only [hM])
    refine ⟨fun a=> ?_, fun u v h=> lt_of_lt_of_le ?_ ((hw.spaced u v h)) ,hi,?_⟩ -- typo relation
    · have ha:= hw.span a; rw [sub_zero] at ha; exact ((show 8*‖(C.S.gridPoint (j i) ∘ x) a‖ ≤ 8*(M*r i) from mul_le_mul_of_nonneg_left ha (by norm_num)).trans_lt (show 8*(M*r i) < (8*M+2)*r i from by linarith only [hy])).trans_le hX
    · let L:= C.path.levels; have ha:= C.S.a_pos (j i)
      have hZ:2*a*((L.budget (j i)).B:ℝ)^2 < η*r i:= by
          calc _ = a*(2*((L.budget (j i)).B:ℝ)^2) := by ring
               _ < a*(η*s^B):=mul_lt_mul_of_pos_left hx ha
               _ = η*(a*s^B):=by ring
               _ ≤ _:=mul_le_mul_of_nonneg_left he.1 hη.le
      exact hZ
    exact (C.S.strictAnti.lt_iff_gt.mp (hv.trans_le (hP.trans hX))).le

end Aligned
end YM.RG05Readout
