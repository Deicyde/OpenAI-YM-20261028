import YM.UVExtension.Lacing.Merge
/-! strengthening of Gust era sockets. Follows actual expressions explicitly. `δ=0`
 genuine path.N r origins. Uses observer.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Lacing
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus
open Eyelet MergeProof
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}(B:SectionData F) (H : History G) (N p m : ℕ) (A : Hol G)
open Extra.Histories.InputColumn
local notation "κ"=> Real.sqrt (H.levels.clock.forcedAllowance (m+1))
local notation "Λ"=> Real.sqrt (H.levels.clock.forcedAllowance m)
variable {T : Extra.Histories.Heading F} {C η t w : ℝ}
local notation "n"=> H.S.side m p
local notation "n'"=> H.S.side (m+1) p
local notation "Old"=> H.rep N p (m+1)
set_option quotPrecheck false
local notation "R"=> H.rep N p m
local notation "O" => Bucket F (R).p A n
set_option quotPrecheck false
private lemma foam {ι WW : Type*} {u : WW → ℂ} {f : ι → WW → ℂ} (h : Dominated f) (hv : ∃ c : ℝ, ∀ x, ‖u x‖ ≤ c) :
    Dominated fun i x => u x * f i x := by
  obtain ⟨b,hb,hr⟩ := h; obtain ⟨c,hh⟩ := hv
  refine ⟨_,hb.mul_left c,fun i x => ?_⟩
  rw [norm_mul]; exact mul_le_mul (hh x) (hr ..) (norm_nonneg _) ((norm_nonneg _).trans (hh x))
set_option synthInstance.maxHeartbeats 80000 in
set_option maxHeartbeats 800000 in
theorem burden (Z : Keeper (H.rep N p (m+1)).p (H.rep N p (m+1)).activities)
    (P : Coefficient F (H.S.side (m+1) p))(X:Set Wing)(D:GaugeDoor Old R)(L0:Lacing.Fence (F:=F) H N p m A) (i:Option F.Index)
    (h:Vintage.YM.RG.History.Selected H)(hm:m<N)(hp:P.Format 0 A (H.rep N p (m+1)))(hP:P.remBound 0 (H.rep N p (m+1)) κ t)(hx:P.x=Lacing.seed F i)
    (hz:0≤η)(hD:Manor B H N p m A Z D X L0 T C η w) (hK: κ ≤1):
    let L := H.S.block m; let x:= P.x
    Sends B H N p m A D X (P.exponentialEntry 0 B (Old)) (profile (Old).activities P.forced) (P.x 0) (P.density 0 B Old) (T.leads L x) (η*(F.coeffSize (F.core x)+t)) (C*F.coeffSize (vowel F L (F.core x))+η*t) (peat (F:=F) w i+2*t) (L0.rain (Eye P A Old κ).2 i) :=by
   intro L x
   have HP:Eligible P A Old κ:=⟨⟨Z⟩,hp,_,hP⟩
   let Q:= ageing P Z; have hx':Q.x=x:=rfl; have htQ: Q.Format 0 A Old:=dye P Z hp; have hw: Q.remBound 0 Old κ t:= priced P Z hp.origin hP
   have hr: profile (Old).activities Q.forced=profile (Old).activities P.forced:= stows Z P
   have he: Q.exponentialEntry 0 B (Old)=P.exponentialEntry 0 B (Old):=respect P Z hp.origin B
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
   let Hp := consist (peat (F:=F) w i) (fun i=> 2*g i) (fun i=>2*k i); let O':Listing → Config G (H.S.side (m+1) p)→ℂ:=consist (J.exponentialEntry 0 B Old) (Q.maskedTerm Old) (fun _=>0); let E':= consist 0 (fun _=>0) (fun i=> exactGas U₀.activities i (Q.forced i)); let Y': Listing→ℂ:= consist (P.x 0) 0 0
   let yg:= L0.income (Eye P A Old κ).2 i
   have hin(i':Listing): Sends B H N p m A D X (O' i') (E' i') (Y' i') (f i') (U' i') (V i') (W i') (Hp i') (yg i'):=by
      rcases i' with i'|j|j
      · change Sends _ _ _ _ _ _ _ _ ((Extra.Histories.primary 0 P.x).exponentialEntry 0 B Old) 0 (P.x 0) ((Extra.Histories.primary 0 P.x).density 0 B Old) (T.leads L P.x) (η*F.coeffSize (F.core P.x)) (C*F.coeffSize (vowel F L (F.core P.x))) (peat (F:=F) w i) (L0.vane i)
        -- dependent read technique
        erw [hx]; exact hD.pivot i
      · let he:= key n' j; let r:= HP.fernP he
        have hm : yg (Sum.inr (.inl j))= L0.glass he ((↑(Eyelet.fee (Old).p he.1.val):ℂ) • twig _ r):=by unfold yg;rw [HP.vistas];rfl
        rw [hm]; exact hD.glass he r (a j) (hA' j)
      by_cases Ho:j∈Set.range (L0.route); swap
      · let Y:= Q.forced j; change Sends B H N p m A _ _ 0 (exactGas _ j Y) 0 (Extra.Histories.fare _ j Y) 0 (η*k j) (η*k j) (2*k j) (yg _)
        have hr : Y=0:= pit Z P (hD.route ▸ Ho)
        rw [hr]; rw [show exactGas (Old).activities j 0=0 by simp [exactGas]]; rw [show Extra.Histories.fare Old j 0=0 from funext fun U=> by simp [Extra.Histories.fare]]; rw [show yg (.inr (.inr j))=0 from by unfold yg; rw [HP.vistas]; exact extend_apply' (fun u=> L0.wing u (HP.tollK u)) (0:ℕ→ Bucket F (R).p A n) _ Ho]
        exact leisure B _ _ _ _ _ X D (mul_nonneg hz (Hk.1 j)) (mul_nonneg zero_le_two (Hk.1 j))
      obtain ⟨u,rfl⟩:=Ho; let j:=L0.route u; have he:j=cart Z u:=congr_arg (fun f:StockTag n'↪ℕ=> f u) hD.route
      let Zu:= HP.sapP u; have hy: Q.forced j=Zu.val:=he ▸ stowed Z P u
      have hHp : (Old).p.mass u.val.1 (b j)= (Old).p.mass ((Old).activities.forced j).support (b j):=by
          apply congr_arg (fun x=> (Old).p.mass x (b j)); rw [he]; exact (Z.support (u,0)).symm
      have Q':=hD.wing u Zu (b j) (hB' j|>.1) (hy ▸ (hB' j).2)
      have hh:yg (.inr (.inr j))=L0.wing u (HP.tollK u):= by unfold yg; rw [HP.vistas]; exact L0.route.injective.extend_apply (fun t=>L0.wing t (HP.tollK t)) 0 _ -- may need explicit
      change Sends _ _ _ _ _ _ _ _ 0 (exactGas _ j (Q.forced j)) 0 (Extra.Histories.fare _ j (Q.forced j)) 0 _ _ (2*k j) _; rw [hy,hh]
      rw [hHp] at Q'; exact rents _ _ _ _ _ _ D X _ Q' le_rfl le_rfl (mul_le_mul_of_nonneg_left (le_div_self (hB.1 j) h0 hK) zero_le_two)
   let z':=(∑' i,g i)+(∑' i,k i); have hy':z'≤t:=(add_le_add hA.2.2 Hk.2.2).trans hS
   have hV:HasSum V (η*y+η*z'):=by unfold z';rw [mul_add]; exact added (hA.2.1.hasSum.mul_left _) (Hk.2.1.hasSum.mul_left _)
   have hW':HasSum W (C*d'+η*z'):=by unfold z';rw [mul_add]; exact added (hA.2.1.hasSum.mul_left _) (Hk.2.1.hasSum.mul_left _)
   have hQ:HasSum Hp (peat (F:=F) w i+2*z'):=by unfold z';rw [mul_add]; exact added (hA.2.1.hasSum.mul_left _) (Hk.2.1.hasSum.mul_left _)
   have huP : HasSum U' (T.leads L x):=by simpa only [U',consist,add_zero, Sum.elim_inl] using added (f:=U') hasSum_zero hasSum_zero
   have hP₀: Summable (fun i=> F.coeffSize (U' i)):= by apply summable_of_ne_finset_zero (s:={Sum.inl ()}); rintro (⟨⟩|i|i) hi; simp at hi; all_goals simp [U',Labels.Frame.coeffSize,consist]
   have hδ : HasSum Y' (P.x 0):=by simpa only [Y',consist,add_zero, Sum.elim_inl] using added (f:=Y') hasSum_zero hasSum_zero
   have he' (U): HasSum (fun j=> O' j U) (P.exponentialEntry 0 B Old U):=by
      have hJ j:J.maskedTerm Old j U=0:=congr_fun (map_zero (Push.Local.maskLinear _ _)) _
      have Hx(i:Coefficient F (H.S.side (m+1) p)):i.exponentialEntry 0 B Old U= part B 0 Old U (Coefficient.x i)+∑' j,i.maskedTerm Old j U:=rfl
      rw [← he,Hx,hx']; convert added (f:=fun j=> O' j U) ((Q.regular_series (priced P Z hp.origin hP)).summable U|>.hasSum) (hasSum_zero) using 1; change _= J.exponentialEntry _ _ _ U+(_+0);rw [Hx]; simp_rw [hJ,tsum_zero,add_zero];rfl -- hw consumed use
   have hq' j U: HasSum (fun i=> E' i j U) (profile (Old).activities P.forced j U):=by
      rw [← hr]; convert added (f:=fun i=>E' i j U) hasSum_zero (profiled (Old).activities _ hL U j) using 1; change _=(0:ℂ)+(0+_); rw [zero_add,zero_add]
   have h' := vouchers B H N p m A D hD.good h hm.le hD.coins (L0.income (Eye P A Old κ).2 i) hin he' hq' hδ hu hf hP₀ hV.summable hW'.summable hQ.summable
   rw [← hW,← hP',hV.tsum_eq, hW'.tsum_eq,hQ.tsum_eq,huP.tsum_eq] at h'; exact rents B H N p m A D X _ h' (by rw [mul_add η (F.coeffSize (F.core P.x)) t]; exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hy' hz)) (add_le_add le_rfl (mul_le_mul_of_nonneg_left hy' hz)) (add_le_add le_rfl (mul_le_mul_of_nonneg_left hy' zero_le_two))
end YM.UVExtension.Lacing
#print axioms YM.UVExtension.Lacing.burden
