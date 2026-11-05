import YM.TraceExtension.Quince.Harvest
import YM.Extra.SOURCE_HISTORIES.Aggregate

/-!
Apply `AtomStep` to a column, rebased so its current x *is* a basis
vector. Summation costs & actual push identities on the column. No
assumption of coherent choices even *within* calculation of this column.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Histories
open Lattice Wilson RG Source Function Filter Set MeasureTheory Bid Labels Motion
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {d : ℕ}
variable {F : Labels.Frame G d} (B : SectionData F) (H : History G) (N p m : ℕ) (A : Hol G)

namespace Surrey
private lemma scalar_price {W : Type*} {u : W → ℂ} {f : ℕ → W → ℂ} (h : Dominated f) (hv : ∃ c : ℝ, ∀ x, ‖u x‖ ≤ c) :
    Dominated fun i x => u x * f i x := by
  obtain ⟨b,hb,hr⟩ := h
  obtain ⟨c,hh⟩ := hv
  refine ⟨_,hb.mul_left c,fun i x => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (hh x) (hr ..) (norm_nonneg _) ((norm_nonneg _).trans (hh x))

variable {T : Heading F} {C η t : ℝ}

open InputColumn
structure Stepper (T:Heading F)(C η μ:ℝ):Prop where
    main (i : F.Index) (h : i ≠ 0) :
      let R := H.rep N p (m+1)
      let v := Size.axis F i
      PaidAtom B H N p m A ((primary 0 v).density 0 B R) (T.leads (H.S.block m) v)
       (η * F.coeffSize (F.core v)) (C * F.coeffSize (vowel F (H.S.block m) (F.core v)))
    regular (f : Config G (H.S.side (m+1) p) → ℂ) (b : Support (H.S.side (m+1) p)) (c : ℝ) :
      let R := H.rep N p (m+1)
      let u:= R.p.mass b c
      RegFit R 0 d A b f → R.p.supBounds 0 b f c → PaidAtom B H N p m A (salary R b f) 0 (η*u) (μ*u)
    forced (f : Config G (H.S.side (m+1) p) → ℂ) (i : ℕ) (c : ℝ) :
      let R := H.rep N p (m+1)
      let u:= R.p.mass (R.activities.forced i).support c/ Real.sqrt (H.levels.clock.forcedAllowance (m+1))
      SlotFit R 0 i f → 0 ≤ c → (∀ U, ‖f U‖ ≤ c) → PaidAtom B H N p m A (fare R i f) 0 (η*u) (μ*u)

variable {μ:ℝ}
/-- The costs after merge. Cone on the input is not even needed yet. -/
theorem individual (Q : Coefficient F (H.S.side (m+1) p)) (v : F.Coeff) (hr : H.Selected) (hM : m<N)
    (hp : Stepper B H N p m A T C η μ) (hμ:0≤μ) (hd : 0 ≤ η) (hi : Q.x=v)
    (h : Q.Format 0 A (H.rep N p (m+1)))
    (hw : Q.remBound 0 (H.rep N p (m+1)) (Real.sqrt (H.levels.clock.forcedAllowance (m+1))) t)
    (hPay : PaidAtom B H N p m A ((primary 0 v).density 0 B (H.rep N p (m+1)))
      (T.leads (H.S.block m) v) (η*F.coeffSize (F.core v)) (C * F.coeffSize (vowel F (H.S.block m) (F.core v)))) :
    let L := H.S.block m
    PaidAtom B H N p m A (Q.density 0 B (H.rep N p (m+1))) (T.leads L v)
      (η*(F.coeffSize (F.core v)+t)) (C*F.coeffSize (vowel F L (F.core v))+μ*t) := by
  intro L
  let R := H.rep N p (m+1)
  let y := Real.sqrt (H.levels.clock.forcedAllowance (m+1))
  let x := F.coeffSize (F.core v)
  let D := F.coeffSize (vowel F L (F.core v))
  let f := consist ((primary 0 v).density 0 B R) (fun i => salary R (Q.support i) (Q.regular i)) (fun i => fare R i (Q.forced i))
  have hk := (hr.represents N p (m+1) hM).good
  have h0 : 0 < y := Real.sqrt_pos.2 (forcedPos ..)
  have he := Coefficient.envelope B hk (primary_rem v h0) (primary_format (o:=0) (H:=A) v)
  have hE := Rep.envelope R hk
  have hR := (Rep.exponentEnv R hk).exp
  have hL := rem_dominated hw
  have hu : Dominated f := by
    refine dominated he.cost (scalar_price (Q.regular_series hw) ?_) (scalar_price (dress_abs hk hL) ?_)
    · obtain ⟨c,hc⟩ := hE.cost; exact ⟨c, fun i => (Complex.norm_real _).trans_le (hc i)⟩
    obtain ⟨c,hc⟩ := hR.cost; exact ⟨c, fun i => (Complex.norm_real _).trans_le (hc i)⟩
  have hf (i : Listing) : Measurable (f i) := by
    cases i with
    | inl j => exact he.meas
    | inr j =>
      cases j with
      | inl i => exact (Complex.continuous_ofReal.measurable.comp hE.meas).mul (masked_measurable _ _ _ (h.smooth i).borel)
      | inr i => exact (Complex.continuous_ofReal.measurable.comp hR.meas).mul ((h.borel i).mul (dressed_meas hk i))
  have hv : Q.density 0 B R = fun U => ∑' i, f i U := by
    funext U
    let a i := Q.maskedTerm R i U
    let b i := Q.forced i U * dressed R i U
    have hm : HasSum a (∑' i, a i) := ((Q.regular_series hw).summable U).hasSum
    have hn : HasSum b (∑' i, b i) := ((dress_abs hk hL).summable U).hasSum
    rw [(added (f:=fun i => f i U) (hm.mul_left (R.eval U:ℂ)) (hn.mul_left (Real.exp (R.exponent U):ℂ))).tsum_eq]
    change _ = (primary 0 v).density 0 B R U + _
    rw [primary_density,Coefficient.density,dress_eq hk hL]
    change (R.eval U:ℂ)*(part B 0 R U Q.x+∑' i,a i) + _ = _
    rw [show Q.x=v from hi]; unfold b; ring
  obtain ⟨r,s,ha,hb,hS,-,⟨a,hA,hA'⟩,b,hB,hB'⟩ := hw
  let u : Listing → F.Coeff := consist (T.leads L v) (fun _ => 0) (fun _ => 0)
  let g i := R.p.mass (Q.support i) (a i)
  let k i := (R.p.mass (R.activities.forced i).support (b i))/y
  let V := consist (η*x) (fun i => η*g i) (fun i => η*k i)
  let W := consist (C*D) (fun i => μ*g i) (fun i => μ*k i)
  have ht (j : Listing) : PaidAtom B H N p m A (f j) (u j) (V j) (W j) := by
    cases j with
    | inl j => exact hPay
    | inr j =>
      cases j with
      | inl j => exact hp.regular _ _ _ ⟨h.smooth j,h.origin j,h.identity_null j,h.projects j⟩ (hA' j)
      | inr j =>
        exact hp.forced _ _ _ ⟨h.invariant j,h.borel j,h.supported j,h.carried j,h.forcing j⟩ (hB' j).1 (hB' j).2
  have hi : HasSum u (T.leads L v) := by simpa [u,consist] using added (f:=u) hasSum_zero hasSum_zero
  have hy : Summable fun i => F.coeffSize (u i) := Summable.sum _ (hasSum_fintype _).summable (by
    apply Summable.sum; all_goals simp [u,consist,comp_def,Frame.coeffSize])
  have Hg : HasSum g (∑' i, g i) := hA.2.1.hasSum
  have Hk : HasSum k (∑' i, k i) := (hB.2.1.div_const y).hasSum
  let z := η * ∑' i, g i + η * ∑' i, k i
  have hV : HasSum V (η*x + z) := added (f:=V) (Hg.mul_left η) (Hk.mul_left η)
  let z' := μ * ∑' i, g i + μ * ∑' i,k i
  have hW : HasSum W (C*D + z') := added (f:=W) (Hg.mul_left μ) (Hk.mul_left μ)
  have hx : z ≤ η*t := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hS hd)
    have hz : ∑' i, k i ≤ s := by
      unfold k; rw [tsum_div_const]
      exact (div_le_iff₀ h0).mpr (le_trans hB.2.2 (by dsimp [y]; rw [mul_comm]))
    unfold z; rw [mul_add]; exact add_le_add (mul_le_mul_of_nonneg_left hA.2.2 hd) (mul_le_mul_of_nonneg_left hz hd)
  have hx' : z' ≤ μ*t := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hS hμ)
    have hz' : ∑' i, k i ≤ s := by
      unfold k; rw [tsum_div_const]
      exact (div_le_iff₀ h0).mpr (le_trans hB.2.2 (by dsimp [y]; rw [mul_comm]))
    unfold z'; rw [mul_add]; exact add_le_add (mul_le_mul_of_nonneg_left hA.2.2 hμ) (mul_le_mul_of_nonneg_left hz' hμ)
  have HH := atom_total B H N p m A hr hM.le ht hu hf hy hV.summable hW.summable
  rw [← hv, hi.tsum_eq,hV.tsum_eq,hW.tsum_eq] at HH
  apply atom_mono HH
  · rw [mul_add]; exact add_le_add_right hx _
  exact add_le_add_right hx' _


lemma gen_scale {v:F.Coeff} {g} (h:Integrable g (prior G _))(hp:PaidAtom B H N p m A g v C μ)(y:ℂ) : PaidAtom B H N p m A (y • g) (y • v) (‖y‖*C) (‖y‖*μ):=by
   have he:=H.levels.transition_mass m p (H.β N p (m+1)); obtain ⟨x,hx⟩:=hp; refine ⟨y • x,fun i=>?_⟩
   obtain ⟨ht,X,hP,hF,hQ,hV⟩:=hx i; let V:= stretch (scalar i y) X
   refine ⟨?_,V,?_,stretch_format _ hF,?_,?_⟩
   · rw [patch_smul,patch_smul,← smul_sub,Size.smul,norm_scalar]; exact mul_le_mul_of_nonneg_left ht (norm_nonneg _)
   · change scalar i y • X.x=_; rw [patch_smul,hP]
   · exact norm_scalar i y ▸ stretch_rem (scalar i y) hQ
   funext z; rw [show V.density 0 B _ z=_ from stretch_density .., hV]; unfold dance blast; rw[StepData.push_smul _ _ _ _ h]; simp only [Pi.smul_apply,smul_eq_mul,scalar_mul];ring
section paint
variable (h:H.Selected)(hm:m<N)(hT:Stepper B H N p m A T C η μ)
include h hm hT
lemma primaryPaid (v:F.Coeff):
    let L:=H.S.block m; let R:= H.rep N p (m+1)
    PaidAtom B H N p m A ((primary 0 v).density 0 B R) (T.leads L v) (η*F.coeffSize (F.core v)) (C* F.coeffSize (vowel F L (F.core v))) := by
    intro L R; let f(i:F.Index):= Size.axis F i; let V i:= v i • (primary 0 (f i)).density 0 B R
    have hV(i:F.Index):Envelope (V i):=by
        let Q:=primary (0:Site (H.S.side (m+1) p)) (f i); let P:=stretch (v i) Q; have hp: V i=P.density 0 B R:=funext fun j=> Eq.symm (stretch_density B R _ _ _ _)
        rw [hp]; exact Coefficient.envelope B (h.represents N p _ hm).good (stretch_rem _ (primary_rem _ zero_lt_one)) (stretch_format _ (primary_format (H:=A) _))
    let x i:= v i • T.leads L (f i); let a i:=‖v i‖*(η*F.coeffSize (F.core (f i))); let q i:=‖v i‖*(C*F.coeffSize (vowel F L (F.core (f i))))
    have hx(i):PaidAtom B H N p m A (V i) (x i) (a i) (q i):=by
       have hx(i): Integrable ((primary 0 (f i)).density 0 B R) (prior G _):=play_integrable H N h hm (primary_format (H:=A) _) (primary_rem _ zero_lt_one)
       apply gen_scale _ _ _ _ _ _ (hx i) _
       by_cases hh:i=0; · subst i; exact paid_one B H N p m A T C η h hm
       exact hT.main i hh
    classical
    have hz: Dominated V:= by choose u hu using fun i=> (hV i).cost; exact ⟨u,Summable.of_finite,hu⟩
    have H:= atom_total B H N p m A h hm.le hx hz (fun i=>(hV i).meas) (Summable.of_finite) Summable.of_finite Summable.of_finite
    have hv: (fun U=> ∑' i,V i U)= ((primary 0 v).density 0 B R):=by
        funext j; rw [tsum_fintype,primary_density]; unfold V; simp_rw [Pi.smul_apply, primary_density, smul_eq_mul]; conv_rhs=> rw [← Size.sum_axes F v]
        simp_rw [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]; refine Finset.sum_congr rfl fun i hi=>mul_left_comm ..
    have he: ∑' i,x i=T.leads L v:=by rw[tsum_fintype]; unfold x; simp_rw [← map_smul,← map_sum]; rw [show ∑ i:F.Index,v i • f i=v from Size.sum_axes F v]
    have hm(i:F.Index):F.core v i= if i=0 then 0 else v i:=by change Function.update v 0 _ i=_; by_cases h:i=0<;>simp[h]
    have ht: ∑' i,a i=η*F.coeffSize (F.core v):=by
        rw [tsum_fintype,Frame.coeffSize,Finset.mul_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; unfold a f; rw [hm i,Size.core_axis]; by_cases h:i=0; · simp[h,Labels.Frame.coeffSize]
        simp[h,Size.size_axis,mul_comm]
    have hu: ∑' i,q i=C*F.coeffSize (vowel F L (F.core v)):=by
        rw [tsum_fintype,Frame.coeffSize,Finset.mul_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; unfold q f; rw[Size.core_axis]; by_cases ht:i=0; · rw [if_pos ht,show vowel F L 0=0 from funext fun i=>by simp[vowel]]; simp [Labels.Frame.coeffSize,vowel,hm,ht]
        rw[if_neg ht, show vowel F L (Size.axis F i)= _ from YM.Planned.PrimaryIntegral295.PPX.vowel_col L i,Size.smul]; change _ * (C*(_*F.coeffSize (Size.axis F i)))=_; rw[Size.size_axis]; simp only [vowel,hm,ht,if_false,norm_mul,mul_one]; ring
    rwa [hv,he,ht,hu] at H
lemma include_one {w:ℝ}(hd:0≤η)(hv:0≤μ)(Q:Coefficient F _)(hp:Q.Format 0 A (H.rep N p (m+1)))(hW:Q.remBound 0 (H.rep N p (m+1)) (Real.sqrt (H.levels.clock.forcedAllowance (m+1))) w):
    let v:=Q.x; let L:= H.S.block m
    ∃ P :Coefficient F _, P.Format 0 A (H.rep N p m)∧ P.remBound 0 (H.rep N p m) (Real.sqrt (H.levels.clock.forcedAllowance m)) (C*F.coeffSize (vowel F L (F.core v))+μ*w)∧ P.density 0 B (H.rep N p m)=blast H N p m d (Q.density 0 B (H.rep N p (m+1))) ∧ F.coeffSize (P.x-T.leads L v) ≤η*(F.coeffSize (F.core v)+w):=by
    intro v L; obtain ⟨x,hx⟩:= individual B H N p m A Q v h hm hT hv hd rfl hp hW (primaryPaid B H N p m A h hm hT v); obtain ⟨hb,V,hV,hp,hQ,H'⟩:=hx Motion.nil; rw [patch_id] at hV; rw [patch_id,patch_id] at hb; rw [dance_nil] at H'; exact ⟨V,hp,hQ,H',hV.symm ▸ hb⟩
end paint
end Surrey
end YM.Extra.Histories
