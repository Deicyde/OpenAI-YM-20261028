import YM.Contacts.Layers.Signed

/-! # Uniform subpower estimates on layers

A useful compactness argument especially near collisions of many groups. Do not try to take a uniform
threshold for an OPE estimate along all multiparameter paths; some of them may even cost different
(finite) output horizons. Use *normalized logs of all radii*, artificially introducing another
log-cost as well so that compactification gives conclusions on any profile, without an exception for
scales away from the small-length regime. The final bounds are ordinary uniform bounds with finite
constants on the indicated configurations, not pathwise.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Layers
open Function Filter Set MeasureTheory Table Spec OPE
open scoped Topology BigOperators Classical ContDiff
variable {W E I : Type*} [Fintype I]

-- works for arbitrary filters, but usually checked along sequences
structure Ride {W I: Type*} (R : I → W→ℝ) (φ : Filter ℕ) (T : ℕ→ℝ) (f : ℕ→ W) : Prop where
  height : Tendsto T φ atTop
  entries : ∀ i, ∃ s ∈ Icc (0:ℝ) 1, RateIs φ T (R i ∘ f) (-s)
def surcharges (R : I → W →ℝ) (w : W) (ε : ℝ) := ∏ i : I,(R i w)^(-ε)
lemma compactify (R : I→ W →ℝ) {q : W→ℝ} {U : Set W} {E : Type*} [Norm E] (F : W→ E) {ε : ℝ} (he : 0 < ε)
    (hr : ∀ x∈ U,∀ i, R i x∈ Ioc (0:ℝ) 1)
    (h : ∀ (φ : Filter ℕ) [φ.NeBot] (T : ℕ→ℝ) (f : ℕ→ W),
       Ride R φ T f → (∀ j, f j ∈ U) → ∃ c, RateIs φ T (q ∘ f) c ∧ RateLE φ T (F ∘ f) c) :
    ∃ C > (0:ℝ), ∀ w∈ U, ‖F w‖ ≤ C * q w * surcharges R w ε := by
  by_contra! ha
  choose f hu H using fun i:ℕ=> ha (Real.exp (i:ℝ)) (Real.exp_pos _)
  let p i j:= -Real.log (R j (f i)); let S i:= ∑ j,p i j; let T (i:ℕ) := (i:ℝ)+ S i
  have hp j (i) : 0 ≤ p i j:= neg_nonneg.mpr (Real.log_nonpos (hr _ (hu i) j|>.1.le) (hr _ (hu i) j|>.2))
  have hm (i) : 0 ≤ S i:= Finset.sum_nonneg fun j _=>hp j i
  have ht(i:ℕ): (i:ℝ) ≤ T i:= le_add_of_nonneg_right (hm i)
  let Ω:= Ultrafilter.of (atTop:Filter ℕ); let φ : Filter ℕ:= Ω
  haveI hN: NeBot φ:= by change NeBot (Ω:Filter ℕ); infer_instance
  have hT: Tendsto T φ atTop:= (tendsto_atTop_mono ht tendsto_natCast_atTop_atTop).mono_left (Ultrafilter.of_le _)
  have hratio (f : ℕ→ℝ)(h0 : ∀ i, 0 ≤ f i) (hh : ∀ i, f i ≤ T i) : ∃ s∈ Icc (0:ℝ) 1,Tendsto (fun i=> f i/T i) φ (𝓝 s):= by
    let g i:=f i/T i
    have hG : ∀ᶠ i in φ, g i ∈ Icc (0:ℝ) 1:= by filter_upwards [hT.eventually_gt_atTop 0] with i hi using ⟨div_nonneg (h0 _) hi.le,(div_le_one hi).mpr (hh i)⟩
    apply isCompact_Icc.ultrafilter_le_nhds (Ω.map g) ?_; refine le_principal_iff.mpr ?_; exact hG
  choose s hs hx using fun i:I=> hratio (fun j=>p j i) (hp i) (fun j=> le_trans (Finset.single_le_sum (fun i _=>hp i j) (Finset.mem_univ i)) (le_add_of_nonneg_left (Nat.cast_nonneg j)))
  obtain ⟨k,hk,hK⟩:=hratio _ Nat.cast_nonneg ht
  have hw(i:I):RateIs φ T (R i ∘ f) (-(s i)):= ⟨Eventually.of_forall fun j=> (hr _ (hu j) i).1,
    (hx i|>.neg).congr' (Eventually.of_forall fun j=> by dsimp [p]; rw [neg_div,neg_neg])⟩
  obtain ⟨c,hv,hc⟩:= h φ T f ⟨hT,fun i=>⟨s i,hs i,hw i⟩⟩ hu
  have hS : Tendsto (fun i=> S i/T i) φ (𝓝 (∑ i,s i)):= by simp_rw [S, Finset.sum_div]; exact tendsto_finsetSum _ fun i _=>hx i
  have h1 : k+(∑ i,s i)=1:= tendsto_nhds_unique (hK.add hS) (tendsto_const_nhds.congr' (by
     filter_upwards [hT.eventually_gt_atTop 0] with i hi; exact (by rw [← add_div]; exact (div_self hi.ne').symm)))
  have hM : c< k+c+∑ i, -ε * -(s i):=by
    simp only [neg_mul_neg,← Finset.mul_sum]; have hX : 0 ≤(∑ i,s i):= Finset.sum_nonneg fun i _=> (hs i).1
    rcases hX.eq_or_lt with H|H; rw [← H,mul_zero]; linarith only [h1,H]; linarith only [hk.1,mul_pos he H]
  have hfee:= RateIs.prod (b:=fun i=> -ε * -(s i)) (S:=Finset.univ) (fun i _=> (hw i).rpow (-ε)) hT
  have hE:= ((RateIs.exp' hK |>.mul hv).mul hfee).outweigh hc hM hT
  obtain ⟨i,hi⟩:= hE.exists; exact (H i).not_ge hi

-- No positivity or regularity of the profile family needed beyond exact finite powers below.
-- `B` is the bill *without* any epsilon charge; use RateIs only on the torus of paths.
variable {φ : Filter ℕ} {T : ℕ→ℝ} {r : I→W→ℝ} {p q : W→ℝ} {x : ℕ → W}
structure Bill (r : I → W→ℝ) (U : Set W) (b : W→ℝ) : Prop where
   pos : ∀ x∈U,0 < b x
   exactRate : ∀ (φ : Filter ℕ) [φ.NeBot] (T : ℕ→ℝ) (x : ℕ→ W), Ride r φ T x → (∀ i,x i∈U) → ∃ c:ℝ, RateIs φ T (b ∘ x) c
namespace Bill
variable {U : Set W}
omit [Fintype I] in
lemma one : Bill r U (fun _=>1):= ⟨fun _ _=>one_pos,fun _ _ _ _ h _=> ⟨_,RateIs.const h.height one_pos⟩⟩
omit [Fintype I] in
lemma times (h : Bill r U p) (k : Bill r U q) : Bill r U (p*q) := by
  constructor; exact fun _ hx=> mul_pos (h.pos _ hx) (k.pos _ hx)
  intro φ _ T x h' hv; obtain ⟨s,hs⟩:=h.exactRate φ T x h' hv; obtain ⟨t,ht⟩:=k.exactRate φ T x h' hv; exact ⟨_,hs.mul ht⟩
omit [Fintype I] in
lemma radius (i : I) (h : ∀ x∈ U,0 < r i x) : Bill r U (r i) :=
  ⟨h,fun φ _ T x h' _=> by obtain ⟨k,hk,h⟩:= h'.entries i; exact ⟨-k,h⟩⟩
omit [Fintype I] in
lemma powers (a : ℝ) (h : Bill r U p) : Bill r U (fun w=> (p w)^a) := by
  refine ⟨fun w hw=>Real.rpow_pos_of_pos (h.pos w hw) a, fun φ _ T x h' hx=>?_⟩; obtain ⟨k,hk⟩:= h.exactRate φ T x h' hx; exact ⟨_,hk.rpow a⟩
end Bill
end YM.Contacts.Layers
