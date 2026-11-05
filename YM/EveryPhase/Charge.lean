import YM.EveryPhase.Court

/-! # Time-smeared Minkowski stress action -/
set_option autoImplicit false
noncomputable section
namespace YM.EveryPhase.Stress
open Function Set Filter MeasureTheory Metric Boundary Next.BOUNDARY Mink Complex Probe Table
open Next.BOUNDARY.Descent
open scoped Topology BigOperators

-- Use open ball (of course continuous equal-one extends to edge too).
-- Through times in tsupport f, the complement must be **strictly** spacelike
-- to the specified test supports (subset of X). Thus a sufficiently large ball.
structure Season (f : Probe ℝ) : Prop where
  real (t : ℝ) : ((f t).re:ℂ)=f t
  smoothTime : HasCompactSupport ⇑f
  unit : (∫ t, f t)=1

lemma Season.stands {f} (hf : Season f) : (tsupport f).Nonempty := by
  by_contra! h
  have he (x) : f x=0 := image_eq_zero_of_notMem_tsupport (by simp [h])
  have ht := hf.unit; simp_rw [he] at ht; simp at ht

lemma accepts : ∃ f : Probe ℝ, Season f := by
  let c := stall (X:=ℝ)
  let s := ∫ x : ℝ, c x
  have ht : 0<s := c.integral_pos
  let f := (s:ℂ)⁻¹ • tint c
  refine ⟨f, fun x => ?_,?_,?_⟩
  · simp [f]
  · have h : HasCompactSupport ⇑(tint c) := by
      rw [HasCompactSupport,tint_support]; exact isCompact_closedBall ..
    apply HasCompactSupport.smul_left h
  simp only [f,_root_.smul_apply, smul_eq_mul,tinted,integral_const_mul,integral_complex_ofReal]
  exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr ht.ne')

structure Reservation (X : Set E4) (f : Probe ℝ) (c : Probe Space3) : Prop where
  pocket : HasCompactSupport ⇑c
  across : ∃ x : Space3, ∃ d : ℝ, 0<d ∧ EqOn ⇑c (fun _ => 1) (ball x d) ∧
    ∀ s∈tsupport f, ∀ y∉ball x d, ∀ z∈X, position y s-z∈Mink.spacelike

lemma reservable (X : Set E4) (f : Probe ℝ) (h : IsCompact X) (hf : HasCompactSupport ⇑f) :
    ∃ c, Reservation X f c := by
  obtain ⟨A,hA⟩ := (h.image (rest_cont.norm)).bddAbove
  obtain ⟨B,hB⟩ := ((h.prod hf).image (show Continuous (fun p : E4 × ℝ => |p.2 - YM.time p.1|) from by fun_prop)).bddAbove
  let d := max (A+B) 0+1
  have hd : 0<d := by dsimp only [d]; linarith [le_max_right (A+B) 0]
  let c : ContDiffBump (0:Space3) := ⟨d,d+d,hd, by linarith⟩
  refine ⟨tint c, ?_, 0,d,hd,?_,?_⟩
  · rw [HasCompactSupport,tint_support]; exact isCompact_closedBall ..
  · intro z hz; simp [c.one_of_mem_closedBall (ball_subset_closedBall hz)]
  intro s hs y hy z hz
  rw [lateral]
  simp only [sub_eq_add_neg,clock_add,clock_neg,time_position,Mink.rest_add,Mink.rest_neg,spatial_position]; simp only [← sub_eq_add_neg]
  have he : A+B<d := (le_max_left ..).trans_lt (lt_add_of_pos_right _ zero_lt_one)
  have ht₁ : |s-YM.time z| ≤ B := hB ⟨(z,s),⟨hz,hs⟩,rfl⟩
  have ht₂ : ‖spatial z‖ ≤ A := hA ⟨z,hz,rfl⟩
  have ht₃ : d≤‖y‖ := by simpa using hy
  linarith [norm_sub_norm_le y (spatial z)]
lemma Reservation.admits {X : Set E4} {f : Probe ℝ} {g : Probe Space3} (h : Reservation X f g) (hf : Season f)
    (x : E4) (hx : x∈X) : Jury g f x := by
  obtain ⟨y,d,hd,he,ht⟩ := h.across
  have hk : spatial x∈ball y d := by
    by_contra hp; obtain ⟨w,hw⟩ := hf.stands
    have he := ht w hw (spatial x) hp x hx
    rw [lateral] at he; simp [sub_eq_add_neg] at he; linarith [abs_nonneg (w + -YM.time x)]
  refine ⟨he.eventuallyEq_of_mem (isOpen_ball.mem_nhds hk),?_⟩
  intro s hs i r hr
  have hp : r∉ball y d := by
    intro hz
    obtain ⟨a,ha,hA⟩ := mem_closure_iff.mp hr _ isOpen_ball hz
    have he := (he.eventuallyEq_of_mem (isOpen_ball.mem_nhds ha)).fderiv_eq (𝕜:=ℝ)
    apply hA
    rw [drift_at,he]; simp
  have hh := ht s hs r hp x hx; rw [lateral] at hh; simpa [sub_eq_add_neg] using hh

variable {G : Gauge} {L : Register G} {S U : Table L} {W : Surface S}
  {D : ∀ n, Blanket n} {Z : W.Aurora D} {P : DiffPlan S} {F : Waves S} {H : S.RealSpin} {Q : Wightman S}

def Charge (Q : Wightman S) (K : Killing) (T : S.Stress) (f : Probe ℝ) (g : Probe Space3) :=
    ∑ b : Axis, fieldM Q T timeAxis b (touch K b (pincushion g f))

/-- `v ∂ Φ_B` as distribution is sum `∂_a Φ_B` tested at `v^a m`.
No integration-by-parts on general field-word domains here: minus is
in the definition. Includes the derivative of the affine factor. -/
def action (Q : Wightman S) (K : Killing) (R : S.Rotation) (B : S.Tag) (m : Test4) :=
    Q.operators.field (S.pin B.1 (rankAction R B.1 K.V B.2)) m+
      ∑ i : Axis, Q.operators.field (S.pin B.1 B.2) (partialProbe i (touch K i m))

def adjAction {S : Table L} {Q : Wightman S} (K : Q.operators.domain →ₗ[ℂ] Q.operators.domain)
    (U : Q.operators.domain →ₗ[ℂ] Q.operators.domain) := I • (K.comp U-U.comp K)

lemma action_labels (K : Killing) (T : S.Stress) (B : S.Tag) (R : S.Rotation) (w : Prospect F Z U P H T)
    (ha : Gallery W Z) (hQ : FieldCore W R H Q) (m : Test4) :
    action Q K R B m=Q.operators.field (S.pin B.1 (rankAction R B.1 K.V B.2)) m+
      ∑ i : Axis, zeta i • Q.operators.field (S.pin (B.1+1) (P.deriv B.1 i B.2)) (touch K i m) := by
  unfold action; congr 1; apply Finset.sum_congr rfl; intro i _
  rw [derivative_domain P w.hu w.hs w.hi w.hd w.hF w.hZ ha.spectra hQ, eucl_partial,map_smul]
  have he : ∀ (V : Module.End ℂ Q.operators.domain), zeta i • wick i • V = V := fun V => by
    rw [smul_smul,zeta_wick,one_smul]
  rw [he]

-- sign: shell calculates [B,T_euclidean]; multiplier is ζ
lemma measure_identity (K : Killing) (T : S.Stress) (B : S.Tag) (R : S.Rotation) (w : Prospect F Z U P H T)
    (h : StressLaws U T P.deriv R.lie) (ha : Gallery W Z) (hQ : FieldCore W R H Q) (m : Test4) (hm : HasCompactSupport ⇑m)
    (g : Probe Space3) (hg : HasCompactSupport ⇑g) (hr : ∀ r, ((g r).re:ℂ)=g r)
    (f : Probe ℝ) (hf : Season f) (hh : ∀ x∈tsupport m, Jury g f x) :
    adjAction (Q:=Q) (Charge Q K T f g) (Q.operators.field (S.pin B.1 B.2) m)=action Q K R B m := by
  rw [action_labels K T B R w ha hQ]
  apply on_domain hQ
  intro u v
  have he := Schwartz_shells K T B R w h ha m hm g hg hr f hf.smoothTime hf.unit hh (Sentence.rev Q.J u) v
  let V := Q.operators
  let M := V.field (S.pin B.1 B.2) m
  let M' := V.field (S.pin B.1 (rankAction R B.1 K.V B.2)) m
  let a := V.vector u; let b := V.evaluates v
  let B' (i : Axis) := touch K i m
  let T' (i) := V.field (S.pin 4 (T timeAxis i)) (touch K i (pincushion g f))
  let L (i) := V.field (S.pin (B.1+1) (P.deriv B.1 i B.2)) (B' i)
  have ht : (∑ i : Axis,zeta i * inner ℂ a (M (T' i b)).val)-(∑ i : Axis,zeta i * inner ℂ a (T' i (M b)).val)=
      inner ℂ a (M' b).val+∑ i : Axis,zeta i * inner ℂ a (L i b).val := by
    have ht (t : S.Union) (s : Test4) (p : Sentence S) : inner ℂ a (V.field t s (V.evaluates p)).val=
        W.expect (Sentence.rev Q.J u ++ ((t,s)::p)) := V.general W hQ.meets Q.J hQ.adj _ ((t,s)::p)
    have ht₁ (i : Axis) := ht (S.pin B.1 B.2) m ((S.pin 4 (T timeAxis i),touch K i (pincushion g f))::v)
    have h₁ i : inner ℂ a (M (T' i b)).val=_ := ht₁ i
    have ht₂ (i : Axis) := ht (S.pin 4 (T timeAxis i)) (touch K i (pincushion g f)) ((S.pin B.1 B.2,m)::v)
    have h₂ i : inner ℂ a (T' i (M b)).val=_ := ht₂ i
    dsimp only [M',L,b,B'] at * -- may painful
    simp_rw [h₁,h₂, ht]; exact he
  have hg : Charge Q K T f g=∑ i : Axis, (I*zeta i) • T' i := by
    refine Finset.sum_congr rfl (fun i _ => ?_); rw [TM, show zeta timeAxis= -I by simp [zeta], neg_neg]
  change inner ℂ a ((adjAction (Q:=Q) (Charge Q K T f g) M) b).val = inner ℂ a ((M'+∑ i : Axis,zeta i • L i) b).val
  rw [hg,adjAction]; simp only [LinearMap.smul_apply,LinearMap.comp_apply,LinearMap.add_apply,LinearMap.sub_apply,
    LinearMap.sum_apply,map_sum,map_smul, Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul_of_tower, Submodule.coe_sub,
    inner_sub_right,inner_smul_right,inner_add_right,inner_sum]
  rw [← ht]; simp_rw [mul_sub,Finset.mul_sum,show ∀ c d : ℂ,I*(I*c*d)= -(c*d) from fun c d => by simp [mul_assoc,← mul_assoc I I]]
  simp; abel

/-- Testing functions are Schwartz with HasCompactSupport (C∞ with compact
support). Real f, integral one; any such height profile. Spatial cutoff can
also be complex. Test supports not including exterior vectors of the matrix
element between which we test. Only a local identity. -/
theorem local_action (K : Killing) (T : S.Stress) (B : S.Tag) (R : S.Rotation) (w : Prospect F Z U P H T)
    (h : StressLaws U T P.deriv R.lie) (ha : Gallery W Z) (hQ : FieldCore W R H Q)
    (m : Test4) {X : Set E4} (hX : IsCompact X) (hm : tsupport m ⊆ X)
    (f : Probe ℝ) (hf : Season f) (c : Probe Space3) (hc : Reservation X f c) :
    adjAction (Q:=Q) (Charge Q K T f c) (Q.operators.field (S.pin B.1 B.2) m) = action Q K R B m := by
  let g := fun r : Space3 => ((c r).re:ℂ)
  have hg : HasCompactSupport g := by
    change HasCompactSupport ((fun r : ℂ => (r.re:ℂ)) ∘ (⇑c)); exact hc.pocket.comp_left (by simp)
  let k := hg.toSchwartzMap (Complex.ofRealCLM.contDiff.comp (Complex.reCLM.contDiff.comp (c.smooth ⊤)))
  have Hk (x) : k x=g x := rfl
  have hp := hc.pocket; obtain ⟨x,d,hd,hc,hC⟩ := hc.across
  have hk (t) (ht : t∈ball x d) : k t=1 := by rw [Hk]; unfold g; rw [hc ht]; simp
  have hh : Reservation X f k := ⟨hg, x,d,hd,fun p ht => hk p ht,hC⟩
  have hb (a : Axis) : Fields.causal (touch K a (pincushion (c-k) f)) m := by
    let M := touch K a (pincushion (c-k) f)
    intro y hy z hz
    have hs : tsupport M ⊆ {p : E4 | spatial p ∉ ball x d} ∩ {p : E4| YM.time p∈tsupport f} := by
      apply closure_minimal _ (((isOpen_ball.preimage rest_cont).isClosed_compl).inter ((isClosed_tsupport f).preimage clock_cont))
      intro i hi; change M i≠0 at hi
      constructor
      · exact fun ht => hi (by simp [M,touch_at,pincushion_at,hk _ ht, hc ht])
      by_contra h; exact hi (by simp [M,touch_at,pincushion_at,image_eq_zero_of_notMem_tsupport h])
    have he := hC _ (hs hy).2 _ (hs hy).1 z (hm hz); simpa using he
  have he : Charge Q K T f c=Charge Q K T f k + Charge Q K T f (c-k) := by
    have hm : pincushion (c-k) f=pincushion c f-pincushion k f := by ext1 i; simp [pincushion_at,sub_mul]
    unfold Charge; simp only [hm,map_sub,Finset.sum_sub_distrib]; abel
  have hy := measure_identity K T B R w h ha hQ m (hX.of_isClosed_subset (isClosed_tsupport _) hm)
    k hg (fun i => by rw [Hk]; simp [g]) f hf (fun p ht => hh.admits hf p (hm ht))
  rw [← hy]; ext1 u
  let A := Q.operators.field (S.pin B.1 B.2) m
  have ht : Charge Q K T f (c-k) (A u) = A (Charge Q K T f (c-k) u) := by
    simp only [Charge,LinearMap.sum_apply,map_sum]
    exact Finset.sum_congr rfl fun i _ => hQ.localPairs _ _ _ _ (hb i) u
  change I • (Charge Q K T f c (A u)-A (Charge Q K T f c u)) = I • ((Charge Q K T f k (A u))-A (Charge Q K T f k u))
  rw [he]; simp only [LinearMap.add_apply,map_add,ht]; abel
end YM.EveryPhase.Stress
