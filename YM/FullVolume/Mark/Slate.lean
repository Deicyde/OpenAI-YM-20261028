import YM.FullVolume.Mark.Latch
import YM.MergeProof.Sonata

set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Matric
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}(B:SectionData F) (H : History G) (N p m : ℕ) (A : Hol G)
open Extra.Histories.InputColumn
local notation "κ"=> Real.sqrt (H.levels.clock.forcedAllowance (m+1))
private lemma foam {ι W : Type*} {u : W → ℂ} {f : ι → W → ℂ} (h : Dominated f) (hv : ∃ c : ℝ, ∀ x, ‖u x‖ ≤ c) :
    Dominated fun i x => u x * f i x := by
  obtain ⟨b,hb,hr⟩ := h; obtain ⟨c,hh⟩ := hv
  refine ⟨_,hb.mul_left c,fun i x => ?_⟩
  rw [norm_mul]; exact mul_le_mul (hh x) (hr ..) (norm_nonneg _) ((norm_nonneg _).trans (hh x))
variable {T : Extra.Histories.Heading F} {C η t w : ℝ}
local notation "Old"=> H.rep N p (m+1)
local notation "R"=> H.rep N p m
set_option quotPrecheck false
section
variable {n n': Side}{R':Rep G n}(F':Plate F n n')(K:Keeper R'.p R'.activities)
def tags (P:Coefficient F n)(i:F.Index): Listing → Pin F n' := consist (F'.main i) (fun j=> F'.tint j (P.regular j)) (fun j=>F'.ink j (stowK K P j))
def gather (P:Coefficient F n)(i:F.Index):Coefficient F n':=Extra.Histories.merge (code Listing) (tell ∘ tags F' K P i)
end
/-- Before shrink.Apply Coupon to already packed K addresses. Final wrappers EQ.
Keep the unit amplitude untouched (zero). -/
lemma design (F':Plate F (H.S.side (m+1) p) (H.S.side m p)) (Z : Keeper (H.rep N p (m+1)).p (H.rep N p (m+1)).activities)
    (P : Coefficient F (H.S.side (m+1) p))(X:Wing→Prop)(D:GaugeDoor Old R)(i:F.Index)
    (h:H.Selected)(hm:m<N)(hp:P.Format 0 A (H.rep N p (m+1)))(hP:P.remBound 0 (H.rep N p (m+1)) κ t)(hx:P.x=Size.axis F i)
    (hs:P.support=mapSeat)(hq: SoundDoor (H.levels.clock.op m p) D)(hz:0≤η)(hD:Plate.Prints B H N p m A F' T C η w D X)
    (hK: κ ≤ 1) (heX:∀ i, X (.gasKey (cart Z i))):
    let L := H.S.block m; let x:= P.x
    Span B H N p m A (gather F' Z P i) (P.exponentialEntry 0 B (Old)) (profile (Old).activities P.forced) (P.x 0) D X (P.density 0 B Old) (T.leads L x) (η*(F.coeffSize (F.core x)+t)) (C*F.coeffSize (vowel F L (F.core x))+η*t) (w+2*t) :=by
   intro L x
   let Q:= rack Z P; have hx':Q.x=x:=rfl; have htQ: Q.Format 0 A Old:=rack_format Z P hp; have hw: Q.remBound 0 Old κ t:= keeps Z P hP
   have hr: profile (Old).activities Q.forced=profile (Old).activities P.forced:= stows Z P
   have he: Q.exponentialEntry 0 B (Old)=P.exponentialEntry 0 B (Old):=rfl
   let J:=Extra.Histories.primary (0:Site (H.S.side (m+1) p)) x
   let f:= consist (J.density 0 B (Old)) (fun i => Extra.Histories.salary (Old) (Q.support i) (Q.regular i)) (fun i => Extra.Histories.fare (Old) i (Q.forced i))
   have hk := (h.represents N p (m+1) hm).good
   have h0 : 0 < κ := Real.sqrt_pos.2 (forcedPos ..)
   have hE := Rep.envelope Old hk
   have hR := (Rep.exponentEnv Old hk).exp
   have hL := rem_dominated hw
   have hy := Coefficient.envelope B hk (primary_rem (o:=0) x h0) (primary_format (o:=0) (H:=A) x); let U₀:= Old
   have hu : Dominated f := by
      refine InputColumn.dominated hy.cost (foam (Q.regular_series hw) ?_) (foam (dress_abs hk hL) ?_)
      · obtain ⟨c,hc⟩ := hE.cost; exact ⟨c, fun i => (Complex.norm_real _).trans_le (hc i)⟩
      obtain ⟨c,hc⟩ := hR.cost; exact ⟨c, fun i => (Complex.norm_real _).trans_le (hc i)⟩
   have hf (i : Listing) : Measurable (f i) := by
      rcases i with i|i|i; exact hy.meas
      exact (Complex.continuous_ofReal.measurable.comp hE.meas).mul (masked_measurable _ _ _ (htQ.smooth i).borel)
      exact (Complex.continuous_ofReal.measurable.comp hR.meas).mul ((htQ.borel i).mul (dressed_meas hk i))
   have hP': P.density 0 B Old=Q.density 0 B Old:= reentry he.symm hk (rem_dominated hP) hL hr.symm
   have hW : Q.density 0 B Old = fun U => ∑' i, f i U := by
      funext U; let a i := Q.maskedTerm Old i U; let b i := Q.forced i U * dressed Old i U
      have hn : HasSum a (∑' i, a i) := ((Q.regular_series hw).summable U).hasSum
      have ha : HasSum b (∑' i, b i) := ((dress_abs hk hL).summable U).hasSum
      rw [(added (f:=fun i => f i U) (hn.mul_left ((Old).eval U:ℂ)) (ha.mul_left (Real.exp ((Old).exponent U):ℂ))).tsum_eq]; change _ = (Extra.Histories.primary 0 x).density 0 B Old U + _
      rw [primary_density,Coefficient.density,dress_eq hk hL]; change ((Old).eval U:ℂ)*(part B 0 Old U Q.x+∑' i,a i) + _ = _; rw [hx']; unfold b; ring

   obtain ⟨l,r,ha,hb,hS,-,⟨a,hA,hA'⟩,b,hB,hB'⟩:=hw
   let g i:=(Old).p.mass (Q.support i) (a i); let k i:=((Old).p.mass ((Old).activities.forced i).support (b i))/κ
   let y:= F.coeffSize (F.core x); let d':= F.coeffSize (vowel F L (F.core x))
   let V:= consist (η*y) (fun i=> η*g i) (fun i=> η*k i); let W:= consist (C*d') (fun i=> η*g i) (fun i=> η*k i)
   let U': Listing→F.Coeff:= consist (T.leads L x) 0 0
   have Hk:SumBudget k r:=by
      refine ⟨fun i=>div_nonneg (hB.1 _) h0.le,hB.2.1.div_const _,?_⟩; unfold k; rw [tsum_div_const]; exact (div_le_iff₀ h0).2 (hB.2.2.trans_eq (mul_comm ..))
   let Hp := consist w (fun i=> 2*g i) (fun i=>2*k i); let O':Listing → Config G (H.S.side (m+1) p)→ℂ:=consist (J.exponentialEntry 0 B Old) (Q.maskedTerm Old) (fun _=>0); let E':= consist 0 (fun _=>0) (fun i=> exactGas U₀.activities i (Q.forced i)); let Y': Listing→ℂ:= consist (P.x 0) 0 0
   have hin(i':Listing): Span B H N p m A ((tell ∘ tags F' Z P i) i') (O' i') (E' i') (Y' i') D X (f i') (U' i') (V i') (W i') (Hp i'):=by
      rcases i' with i'|j|j
      · change Span B H N p m A (tell (F'.main i)) (J.exponentialEntry 0 B Old) 0 (P.x 0) D X (J.density 0 B Old) _ _ _ w
        have hx₀:x=Size.axis F i:=hx
        change Span _ _ _ _ _ _ _ _ _ _ _ _ _ (T.leads L x) (η*F.coeffSize (F.core x)) (C*F.coeffSize (vowel F L (F.core x))) w -- hx, x=L here
        unfold J; rw [hx,hx₀]; exact hD.main i
      · let U:= H.rep N p (m+1)
        have hp':U.p.supBounds 0 (mapSeat j) (P.regular j) (a j):=(congr_fun hs j) ▸ (hA' j)
        have hv':RegFit U 0 d A (mapSeat j) (P.regular j):=(congr_fun hs j) ▸ (show RegFit U 0 d A (P.support j) (P.regular j) from ⟨hp.smooth j,hp.origin j,hp.identity_null j,hp.projects j⟩)
        change Span _ _ _ _ _ _ _ (masked U.p.threshold (P.support j) (P.regular j)) _ _ _ _ (Extra.Histories.salary U (P.support j) (P.regular j)) _ (η*(U.p.mass (P.support j) _)) (η*(U.p.mass (P.support j) _)) (2*(U.p.mass (P.support j) _))
        rw [congr_fun hs j]; exact hD.regular j _ _ hv' hp'
      classical
      by_cases ht : Q.forced j=0
      · change Span B H N p m A (tell (F'.ink j (Q.forced j))) 0 (exactGas _ j (Q.forced j)) 0 D X (Extra.Histories.fare _ j (Q.forced j)) 0 _ _ _
        rw [ht]; rw [show exactGas (Old).activities j 0=0 by simp [exactGas]]; rw [show Extra.Histories.fare Old j 0=0 from funext fun U=> by simp [Extra.Histories.fare],hD.blank]; exact spanNone B H N p m A X D (mul_nonneg hz (Hk.1 j)) (mul_nonneg zero_le_two (Hk.1 j))
      have hψ:X (.gasKey j):=by
         have hr:j∈ Set.range (cart Z):= not_not.mp (fun hp'=>ht (pit Z P hp')); obtain ⟨p,rfl⟩:=hr; exact heX _
      exact Span.weaken (hD.forced j _ (b j) ht hψ ⟨htQ.invariant j, htQ.borel j,htQ.supported j,htQ.carried j,htQ.forcing j⟩ (hB' j).1 (hB' j).2) le_rfl le_rfl (mul_le_mul_of_nonneg_left (le_div_self (hB.1 _) h0 hK) zero_le_two)
   let z':=(∑' i,g i)+(∑' i,k i); have hy':z'≤t:=(add_le_add hA.2.2 Hk.2.2).trans hS
   have hV:HasSum V (η*y+η*z'):=by unfold z';rw [mul_add]; exact added (hA.2.1.hasSum.mul_left _) (Hk.2.1.hasSum.mul_left _)
   have hW':HasSum W (C*d'+η*z'):=by unfold z';rw [mul_add]; exact added (hA.2.1.hasSum.mul_left _) (Hk.2.1.hasSum.mul_left _)
   have hQ:HasSum Hp (w+2*z'):=by unfold z';rw [mul_add]; exact added (hA.2.1.hasSum.mul_left _) (Hk.2.1.hasSum.mul_left _)
   have huP : HasSum U' (T.leads L x):=by simpa only [U',consist,add_zero, Sum.elim_inl] using added (f:=U') hasSum_zero hasSum_zero
   have hP₀: Summable (fun i=> F.coeffSize (U' i)):= by apply summable_of_ne_finset_zero (s:={Sum.inl ()}); rintro (⟨⟩|i|i) hi; simp at hi; all_goals simp [U',Labels.Frame.coeffSize,consist]
   have hδ : HasSum Y' (P.x 0):=by simpa only [Y',consist,add_zero, Sum.elim_inl] using added (f:=Y') hasSum_zero hasSum_zero
   have he' (U): HasSum (fun j=> O' j U) (P.exponentialEntry 0 B Old U):=by
      have hJ j:J.maskedTerm Old j U=0:=congr_fun (map_zero (Push.Local.maskLinear _ _)) _
      have Hx(i:Coefficient F (H.S.side (m+1) p)):i.exponentialEntry 0 B Old U= part B 0 Old U (Coefficient.x i)+∑' j,i.maskedTerm Old j U:=rfl
      rw [← he,Hx,hx']; convert added (f:=fun j=> O' j U) ((Q.regular_series (keeps Z P hP)).summable U|>.hasSum) (hasSum_zero) using 1; change _= J.exponentialEntry _ _ _ U+(_+0);rw [Hx]; simp_rw [hJ,tsum_zero,add_zero];rfl -- hw consumed use
   have hq' j U: HasSum (fun i=> E' i j U) (profile (Old).activities P.forced j U):=by
      rw [← hr]; convert added (f:=fun i=>E' i j U) hasSum_zero (profiled (Old).activities _ hL U j) using 1; change _=(0:ℂ)+(0+_); rw [zero_add,zero_add]
   have h' := wind B H N p m A D hq h hm.le hin he' hq' hδ hu hf hP₀ hV.summable hW'.summable hQ.summable
   rw [← hW,← hP',hV.tsum_eq, hW'.tsum_eq,hQ.tsum_eq,huP.tsum_eq] at h'; apply Span.weaken h' (by nth_rw 2 [mul_add]; exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hy' hz)) (add_le_add le_rfl (mul_le_mul_of_nonneg_left hy' hz)) (add_le_add le_rfl (mul_le_mul_of_nonneg_left hy' zero_le_two))
end YM.MergeProof.Matric
