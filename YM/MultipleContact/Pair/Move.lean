import YM.MultipleContact.Pair.Anchor
import YM.MultipleContact.Pair.Arrow

/-! Taylor-transport the fusion output on the physical filtration to the pair centroid. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.MultipleContact.Two
open Function Set Filter Metric Table Power Spec Extraction
open scoped Topology BigOperators ContDiff Filter Classical
variable {G:Gauge}{L:Register G}{T:Table L}
section Transport
variable {V:Type*}[NormedAddCommGroup V] {L:Register G}{T:Table L}{S:Table L}{P:DiffPlan S}{k w n:ℕ}(D:∀ k,Detector S k)
local notation "u₀" => fun y:E4=> -half y

def shifted (y:E4)(z:Points n):=Points.across (half y) z
lemma shifted_price {f:FamilyData V L}{p:ℝ}(he:AtPrice f p):AtPrice (fun e y z=>f e y (shifted y z)) p:=by
    intro e K hK hr; obtain ⟨r,hr₀,h⟩:=Room.reach hr hK
    let g(x:E4×Points e.n):=shifted x.1 x.2; let D:=closedBall (0:E4) (r/2); let K':=g '' (D×ˢ K)
    have hg:Continuous g:=by unfold g shifted Points.across points; refine (PiLp.continuous_toLp _ _).comp (continuous_pi fun i=>?_); exact (by fun_prop : Continuous (fun x:E4×Points e.n=>x.2 i)).add (half_continuous.comp continuous_fst)
    have h' : Room K':=by
       rintro z ⟨⟨y,z⟩,hz,rfl⟩
       have hf:=Set.mem_prod.mp hz
       have hv: ‖half y‖ ≤ r/2:= (half_norm y).trans (by simpa only [D,mem_closedBall,dist_zero_right] using hf.1)
       have hy:-half y∈ball 0 r:= by simpa only [mem_ball,dist_zero_right,norm_neg] using (hv.trans_lt (half_lt_self hr₀))
       rw [show Points.cons 0 (g (y,z)) = Points.across (half y) (Points.cons (-half y) z) from by ext1 i; exact Fin.cases (neg_add_cancel (half y)).symm (fun _=>rfl) i]
       exact Points.across_in _ (h _ hy z hf.2)
    exact (he e K' ((isCompact_closedBall (0:E4) (r/2)|>.prod hK).image hg) h').reindex K (fun z y=>shifted y z) ((norm_eventually (r/2) (half_pos hr₀)).mono fun y hy z hz=>⟨(y,z),(Set.mem_prod.mpr ⟨mem_closedBall.mpr ((dist_zero_right ..).le.trans hy.2.le),hz⟩), rfl⟩)

variable (T)(A B:S.Tag) (q:Fin n→L.Token)
lemma from_anchored (H:T.Homogeneous){y:E4}{z:Points n}(hy: away y z∈conf _):pairValue T A B q y z=anchoredValue T A B q y (shifted y z):=by
  have he:anchored y (shifted y z) =Points.across (half y) (away y z):= by
    rw [anchor_as_cons]; ext1 i
    refine Fin.cases ?_ (fun j=>Fin.cases ?_ (fun _=> rfl) j) i
    · simp [away,positions,Points.cons]
    change 0=_; simp [away,positions,Points.cons]
  rw [pairValue,anchoredValue,he]
  exact (translate T H _ _ hy _).symm


lemma from_site (H:T.Homogeneous)(w:ℕ)(v:S.Field w){y:E4}{z:Points n}(h:Safe (-half y) z): siteValue T q w v (-half y) z = siteValue T q w v 0 (shifted y z):=by
  have he: Points.cons 0 (shifted y z)=Points.across (half y) (Points.cons (-half y) z):=by ext1 j;exact Fin.cases (neg_add_cancel (half y)).symm (fun _=>rfl) j
  exact Eq.trans (translate T H _ _ h _).symm (congr_arg (fun x=>fixedValue T _ x) he.symm)

lemma often_pair {K:Set (Points n)}(hK:IsCompact K)(hr:Room K):∀ᶠ y in deleted E4,∀z∈K, away y z∈conf _ ∧ Safe (-half y) z:=by
    obtain ⟨r,hR,h'⟩:=hr.reach hK
    filter_upwards [norm_eventually (E:=E4) r hR] with y ⟨h₀,h₁⟩ z hz
    have he:‖half y‖<r:=(half_norm y).trans_lt h₁
    let hp (u:E4)(he:‖u‖<r):=h' u (mem_ball.mpr ((dist_zero_right ..).le.trans_lt he)) z hz
    exact ⟨away_clear (norm_pos_iff.mp h₀) (hp _ he) (hp _ (by simpa only [norm_neg] using he)),hp _ (by simpa only [norm_neg] using he)⟩

variable {Q : Splitting P}
private lemma promoted (H:P.Inclusions S) (h:w≤k) (v:S.Field w) {r:E4}{z:Points n}(hz:Safe r z): siteValue S q k (P.rise h v) r z=siteValue S q w v r z:= H.kernels h v hz _
-- sum of exact-grade label parts.
lemma recombines (Q:Splitting P)(h:P.Inclusions S)(h':S.Symmetric){z:Points n}{r:E4}(hr:Safe r z)(v:S.Field k):siteValue S q k v r z=∑ i:Fin (k+1),siteValue S q i.val (Q.part i k v) r z:=by
    rw [show siteValue S q k v r z=Work.A01.frontRead (S.classTokens∘q) (Points.cons r z) k v from (Work.A01.front_eval ..).symm]; nth_rw 1 [← Q.recombine h' h k v];rw [map_sum]; apply Finset.sum_congr rfl; intro i _; rw [Work.A01.front_eval]; exact promoted q h _ _ hr

lemma sized_branch (hS:S.Hierarchy)(h:P.Inclusions S)(Q:Splitting P)(hw:w≤k){g:FamilyData ℂ L}{a:ℝ}
          (h0:w=0→AtPrice g a)
          (hpos:0 < w → AtPrice (fun e y z=>missAt (w-1) (D (w-1)) g e z y) a):LocalBound (fun y=>Q.part w k (pull k (D k) g y)) a:=by
    by_cases he:w=0
    · exact (pull_price k (D k) (h0 he)).linear_const (Q.part w k)
    let f:=missAt (w-1) (D (w-1)) g; let u(y):= P.rise (by omega :w-1 ≤ k) (pull (w-1) (D (w-1)) g y)
    have hh : AtPrice (fun e y z=>g e y z-siteValue S e.letter k (u y) 0 z) a:=by intro e K hK hr; exact (hpos (by omega) e K hK hr).congr (Eventually.of_forall fun y z hz=> congr_arg (g e y z- ·) ((promoted e.letter h _ _ (hr z hz)).symm))
    refine ((miss_site k (D k) hS hh).linear_const (Q.part w k)).congr (Eventually.of_forall fun y z _ =>?_)
    rw [map_sub,Q.part_rise hS.laws.toSymmetric h,Q.beyondZero (by omega : w-1<w),LinearMap.zero_apply,sub_zero]

-- rpow-bounded remainder through m-th Taylor derivatives, for |u|≤ |y| regardless of twist.
lemma ray_estimate (hS:S.Smooth)(hP:P.Derivatives S){v:E4→S.Field w}{p:ℝ}(h:LocalBound v p)(m:ℕ)(f:E4→E4)(hf:∀y,‖f y‖ ≤ ‖y‖):
    AtPrice (fun e y z=> siteValue S e.letter w (v y) (f y) z - ∑i:Fin (m+1), (↑(i.val.factorial:ℕ):ℝ)⁻¹ • siteValue S e.letter (w+i) (arrow P w (f y) i (v y)) 0 z) (p+(m+1)):=by
    intro e K hK hr
    obtain ⟨r,hr₀,h'⟩:=hr.reach hK
    let C:=closedBall (0:E4) (r/2)
    let U:=C ×ˢ K; have hU:IsCompact U:= (isCompact_closedBall ..).prod hK
    have hu(p)(hp:p∈U):Safe p.1 p.2:= h' _ (closedBall_subset_ball (half_lt_self hr₀) ((Set.mem_prod.mp hp).1)) p.2 (Set.mem_prod.mp hp).2
    obtain ⟨a,ha,he⟩:=arrow_bound P w (m+1)
    obtain ⟨b,hb,hG'⟩:=site_bound_at hS e.letter (w+(m+1)) U hU hu
    apply (h.all K).op (q:=((m+1:ℕ):ℝ)) (mul_nonneg hb ha) (C:=b*a) (b:=fun z y=> siteValue S e.letter w (v y) (f y) z - ∑ i:Fin (m+1), (↑(i.val.factorial:ℕ):ℝ)⁻¹ • siteValue S e.letter (w+i) (arrow P w (f y) i (v y)) 0 z) _ |>.weaken (show p+((m:ℝ)+1) ≤ p+((m+1:ℕ):ℝ) from by push_cast; linarith)
    filter_upwards [norm_eventually (E:=E4) (r/2) (half_pos hr₀)] with y hy z hz
    have hw(t:ℝ)(ht:t∈Icc (0:ℝ) 1): (t • f y,z)∈U:=by
        refine Set.mem_prod.mpr ⟨?_,hz⟩; change t • f y∈closedBall (0:E4) _; rw [mem_closedBall,dist_zero_right,norm_smul, Real.norm_eq_abs,abs_of_nonneg ht.1]; exact (mul_le_of_le_one_left (norm_nonneg (f y)) ht.2).trans ((hf _).trans hy.2.le)
    refine taylorMix P e.letter w m z (v y) (f y) hP hS (fun t ht=>hu _ (hw t ht)) _ (fun t ht=> (hG' _ (hw t ht) _).trans ((mul_le_mul_of_nonneg_left (he ..) hb).trans ?_))
    rw [Real.rpow_natCast]; exact (le_of_eq (by ring : b*(a*‖v y‖*‖f y‖^(m+1))=b*a*‖v y‖*‖f y‖^(m+1))).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg (f y)) (hf y) (m+1)) (by positivity))

-- Promote a finite Taylor polynomial of observations to physical level k exactly.
private abbrev sumOk (w:Fin (k+1))(i:Fin (k-w.val+1)) : w.val+i.val ≤ k:= by omega
private def movedField (Q:Splitting P)(u:E4)(v:S.Field k):S.Field k:=∑ w:Fin (k+1),∑i:Fin (k-w.val+1), P.rise (sumOk w i) ((↑(i.val.factorial:ℕ):ℂ)⁻¹ • arrow P w.val u i.val (Q.part w.val k v))
private lemma realize_field (Q:Splitting P)(h:P.Inclusions S){r:E4}{z:Points n}(hr:Safe r z)(u:E4)(v:S.Field k):siteValue S q k (movedField Q u v) r z=∑ w:Fin (k+1), ∑i:Fin (k-w.val+1), (↑(i.val.factorial:ℕ):ℝ)⁻¹ • siteValue S q (w+i.val) (arrow P w u i (Q.part w k v)) r z:=by
    have hh(x):siteValue S q k x r z=Work.A01.frontRead (S.classTokens ∘ q) (Points.cons r z) k x:=(Work.A01.front_eval ..).symm
    rw [hh,movedField,map_sum]
    refine Finset.sum_congr rfl (fun w _=>by
       rw [map_sum]
       refine Finset.sum_congr rfl fun i _=>?_
       rw [← hh,promoted q h _ _ hr, Complex.real_smul]
       simp_rw [siteValue,fixedValue,← Work.A01.front_eval]
       rw [map_smul]; push_cast; rfl)


omit T A B q
-- main algebra with a shifted pair candidate
lemma moved_estimate (hS:S.Hierarchy)(h:P.Inclusions S)(hm:P.Derivatives S)(Q:Splitting P){g:FamilyData ℂ L}{v:E4→S.Field k}{f:E4→E4}{a:ℝ}(hK:AtPrice (fun e y z=>g e y z-siteValue S e.letter k (v y) (f y) z) a)
       (h0:∀w:Fin (k+1), LocalBound (fun y=>Q.part w k (v y)) (a+w-1-k))
       (hf:∀y,‖f y‖ ≤ ‖y‖):AtPrice (fun e y z=>missAt k (D k) g e z y) a:=by
    let s (y):=movedField Q (f y) (v y)
    have hv(w:Fin (k+1)):=ray_estimate hS.smooth hm (h0 w) (k-w.val) f hf
    let err (e:Exterior L)(w:Fin (k+1))(z:Points e.n)(y:E4):= siteValue S e.letter (w:ℕ) ((Q.part w k) (v y)) (f y) z - ∑i:Fin (k-w.val+1), (↑(i.val.factorial:ℕ):ℝ)⁻¹ • siteValue S e.letter (w.val+i.val) (arrow P w.val (f y) i.val (Q.part w.val k (v y))) 0 z
    have h'ou(e)(w:Fin (k+1)): ∀K,IsCompact K→Room K→Asympt K (err e w) a:= fun K hK hr=> (hv w e K hK hr).weaken (by push_cast [Nat.cast_sub (R:=ℝ) (by omega : w.val≤k)]; linarith)
    apply detect k (D k) hS (s:=s) (g:=g) (p:=a)
    intro e K ht hr
    obtain ⟨r,hr₀,hz⟩:=hr.reach ht
    have hh : ∀ᶠ y in deleted E4,∀z∈K, (∑ i,err e i z y)=siteValue S e.letter k (v y) (f y) z - siteValue S e.letter k (s y) 0 z:=by
         filter_upwards [norm_eventually (E:=E4) r hr₀] with y hy z ht
         have hw:=hz (f y) (mem_ball.mpr ((dist_zero_right ..).le.trans_lt ((hf y).trans_lt hy.2))) z ht
         simp only [err,Finset.sum_sub_distrib];rw [← recombines e.letter Q h hS.laws.toSymmetric hw,← realize_field e.letter Q h (hr _ ht)]
    have hq:Asympt K (fun z y=>siteValue S e.letter k (v y) (f y) z - siteValue S e.letter k (s y) 0 z) a:= (Asympt.finite_sum Finset.univ (err e) (K:=K) (p:=a) (fun i hi=>h'ou e i K ht hr)).congr hh
    exact ((hK e K ht hr).add hq).congr (Eventually.of_forall fun i z _=>sub_add_sub_cancel ..)
end Transport
variable {C:Family G}{S:Table C.book}{F:Order}{n k:ℕ}{P:DiffPlan S}
variable (H:Data C F S P)(A B:S.Tag)
def kernelPair (T:Table C.book) : FamilyData ℂ C.book:=fun e y z=>pairValue T A B e.letter y z
include H
lemma pair_price (ε:ℝ)(hε:0<ε):AtPrice (kernelPair A B S) (-(massDeg A B:ℝ)-ε):=by
    intro e K hK hr; refine ((shifted_price (anchor_price H A B ε hε)) e K hK hr).congr ((often_pair hK hr).mono fun i hi z hz=>(from_anchored S A B e.letter H.seed.kernel.translations (hi z hz).1).symm)
lemma center_miss (k:ℕ) (Q:Splitting P)(D:∀k,Detector S k):AtPrice (fun e y z=>missAt k (D k) (kernelPair A B S) e z y) ((k:ℝ)-massDeg A B+gain):=by
   let v:=pull k (D k) (kernelAnchor A B); let f(y:E4):=-half y
   let p:=(k:ℝ)-massDeg A B+gain
   have hf(y):‖f y‖≤‖y‖:=(norm_neg (half y)).le.trans (half_norm y)
   apply moved_estimate D H.seed.kernel H.inclusion H.deriv Q (v:=v) _ _ hf
   · intro e K ht hr
     refine ((shifted_price (anchor_miss k H A B (D k))) e K ht hr).congr ((often_pair ht hr).mono fun i hi z hz=>?_)
     change _=pairValue S A B e.letter i z - siteValue S _ _ _ (f i) _
     rw [from_anchored S A B e.letter H.seed.kernel.translations (hi z hz).1, from_site S e.letter H.seed.kernel.translations _ _ (hi z hz).2];rfl
   intro w
   have he(w:ℕ)(hw:w≤ k):LocalBound (fun y=>Q.part w k (v y)) ((w:ℝ)-1-(massDeg A B:ℝ)+gain):=by
       apply sized_branch D H.seed.kernel H.inclusion Q hw
       · rintro rfl e K hK hr
         exact (anchor_price H A B (1/2) one_half_pos e K hK hr).weaken (by push_cast; unfold gain; linarith)
       intro hp e K hK hr
       exact (anchor_miss (w-1) H A B (D (w-1)) e K hK hr).weaken (by push_cast [Nat.cast_sub hp]; linarith)
   exact (he w.val (by omega)).weaken (by linarith)

end YM.MultipleContact.Two
