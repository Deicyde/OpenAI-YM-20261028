import YM.AnalyticNext.GRID_STOP_ATTENUATION.Alphabet.Edit


set_option warningAsError false

/-!
# E/forced rewrites on the calibrated output generally

Simultaneous mixed edit (esp. for lists of attaching factors from canonical
extraction, larger unmarked vacuum reserve visible and price by overlap, not
per book). Entries given on the actual Pack of P, not quotient ambiguities.
Geometry, price, infinite summation and delivery to our susceptibility gates
are separate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.GridStop.Harvest
open Filter Function MeasureTheory RG Marker Wilson Lattice Multi Multi.Couples Finset
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {I W : Type} [Fintype I] [DecidableEq I] [DecidableEq W] [Fintype W] (R : Census W)
variable {G : Gauge} {n : Side} (P : Rep G n)
variable (D : Hot R → Pulse G n)
variable (Y : I → Support n) (tag : I → W) (F : I → Config G n → ℂ) (U : Config G n)

/-- Multiple names may contribute to the SAME correction singleton. -/
def pigment (t : I) : Poly R := Poly.send (R.fire (tag t)) (F t U)
def palette : Atom n I → Poly R := Sum.elim (Alphabet.share P D U) (pigment R tag F U)
def fusion := till Y (flags P.p.threshold U) (palette R P D tag F U)

/-- E change targeted only at singles (others keep). -/
def newE (x : Hot R) := (D x).1 - ∑ t : I, if Hot.one R (tag t)=x then F t else 0
def new (x : Hot R) : Pulse G n := (newE R D tag F x, fun q U => (fusion R P D Y tag F U q).part x.val)

omit [DecidableEq I] [Fintype W] in
lemma silent (p : Pack n) {κ δ : ℝ} (h : P.activities.Valid P.p δ κ) :
    (fusion R P D Y tag F U p).part R.quiet = incumbent P U p := by
  let z := flags P.p.threshold U
  unfold fusion till
  let S : Recipe n I := {Sum.inl p}
  rw [Poly.part_sum,sum_eq_single S]
  · unfold earning; have hs := alone Y p
    have hu : (ground Y S ∩ z=tags S) ↔ p.zone ∩ z = p.flagsAt := by rw [← merged_zone Y hs,←merged_tags Y hs,
      show fused Y S=p from fused_one Y p]
    split
    · rw [prod_singleton]; exact Alphabet.share_quiet ..
    rename_i hf; rw [Poly.part_nil]
    by_contra hx; exact hf (hu.mpr ((incumbent_legible P p h.forced).inventory _ (Ne.symm hx)))
  · intro S' hs he; obtain ⟨h,hq⟩ := mem_filter.mp hs
    have hx := Finset.nonempty_iff_ne_empty.mpr (show S'.toRight ≠ ∅ from fun e => he (purchase Y h hq e))
    obtain ⟨i,hi⟩ := hx
    unfold earning; split
    · rw [quiet_of_prod]; apply prod_eq_zero (mem_toRight.mp hi)
      change (Poly.send _ _).part _=_; simp [Ne.symm (R.fire_hot _)]
    rfl
  exact fun e => False.elim (e (mem_filter.mpr ⟨alone Y p,fused_one Y p⟩))

omit [DecidableEq I] [Fintype W] in
lemma regroups (p : Pack n) {κ δ : ℝ} (h : P.activities.Valid P.p δ κ) :
    Alphabet.share P (new R P D Y tag F) U p=fusion R P D Y tag F U p := by
  ext x
  by_cases ht : x.val.Nonempty
  · change (Alphabet.share P _ U p).part (⟨x,ht⟩ : Hot R).val = _
    rw [Alphabet.share_at]; rfl
  rw [show x=R.quiet from Subtype.ext (Finset.not_nonempty_iff_eq_empty.mp ht), Alphabet.share_quiet,silent _ _ _ _ _ _ U _ h]

omit [DecidableEq I] [Fintype W] in
lemma treats : Multi.lit R (fun t => (new R P D Y tag F t).1 U)=Multi.lit R (fun t => (D t).1 U) - ∑ i,pigment R tag F U i := by
  ext x
  by_cases h : x.val.Nonempty
  · let y : Hot R := ⟨x,h⟩
    change (Multi.lit R _).part y.val=(Multi.lit R _).part y.val - (∑ i,pigment R tag F U i).part y.val
    rw [Poly.part_sum,Multi.part_lit,Multi.part_lit]
    apply congrArg (fun v : ℂ => (D y).1 U - v)
    rw [sum_apply U univ (fun t => if Hot.one R (tag t) = y then F t else 0)]
    exact sum_congr rfl fun i _=> by
      unfold pigment; rw [Poly.part_send]; split
      · rename_i hf; rw [← hf]; exact (if_pos (show (Hot.one R (tag i)).val = R.fire _ from rfl)).symm
      rename_i he; rw [if_neg (show y.val≠ R.fire (tag i) from fun h => he (Subtype.ext h.symm))]; rfl
  rw [show x=R.quiet from Subtype.ext (Finset.not_nonempty_iff_eq_empty.mp h)]
  change (Multi.lit R _).part R.quiet=(Multi.lit R _).part R.quiet - (∑ i,pigment R tag F U i).part _
  simp [part_lit_quiet,Poly.part_sum,pigment,fun w : W => Ne.symm (R.fire_hot w)]

omit [Fintype I] [DecidableEq I] [Fintype W] in
lemma pigment_square (t : I) : pigment R tag F U t * pigment R tag F U t=0 := send_noProd
    (fun he => by
      obtain ⟨z,hz⟩:= he
      exact Finset.disjoint_left.mp hz.1 (mem_singleton_self _) (mem_singleton_self (tag t))) (F t U) (F t U)
omit [Fintype I] [DecidableEq I] [Fintype W] in
lemma pigment_silent (t : I) : (pigment R tag F U t).part R.quiet=0 := by simp only [pigment,Poly.part_send,
    if_neg (Ne.symm (R.fire_hot _))]

omit [Fintype I] in
private lemma meter (x : Poly R) (hx : x.part R.quiet=0) (s : Finset I) :
    let f := pigment R tag F U
    (x- ∑ i∈s,f i).pass * ∏ i∈s,(1+f i) = x.pass := by
  intro f
  induction s using Finset.induction_on with
  | empty => rw [sum_empty,sub_zero,prod_empty,mul_one]
  | @insert i s he ih =>
    let z := pigment R tag F U i
    rw [sum_insert he,prod_insert he,add_comm (f i) _,← sub_sub,sub_eq_add_neg (x- _) (f i),append_pass _ (-f i)]
    · rw [← mul_assoc _ (1+f i) _,mul_assoc _ (1+ -f i) _]
      have h := pigment_square R tag F U i
      rw [show (1+ -f i)*(1+f i)=1 from calc
        _ = 1-z*z := by ring
        _ = 1 := by rw [h,sub_zero],mul_one]
      exact ih
    · change x.part R.quiet-(∑ i∈s,f i).part _=_
      rw [Poly.part_sum, hx,Finset.sum_eq_zero (fun i _ => pigment_silent ..),sub_zero]
    · change -(f i).part R.quiet=_; simp only [f,pigment_silent,neg_zero]
    rw [neg_mul_neg]; exact pigment_square ..

omit [DecidableEq I] in
theorem crops {δ κ : ℝ} (h : P.activities.Valid P.p δ κ) (he : ∀ i,Weight P.p (Y i) (F i)) :
    many P R (new R P D Y tag F)=many P R D := by
  classical
  funext U
  unfold many composeAt
  rw [treats]
  let K := flags P.p.threshold U
  let A := Multi.lit R fun t => (D t).1 U
  let f := pigment R tag F U
  refine congrArg₂ _ rfl ?_; change (A-∑ i,f i).pass*(∑ p∈Pack.clears K,∏ i∈p,Alphabet.share P (new R P D Y tag F) U i) = _
  simp_rw [regroups R P D Y tag F U _ h]; unfold fusion
  have H := together Y (palette R P D tag F U) K (fun i ht => (he i).needs U (fun h => ht (by simp [palette,pigment,h])))
  rw [H,mul_comm _ (∏ _ : I,_) ,← mul_assoc]
  rw [show (A-∑ i,f i).pass * ∏ i : I,(1+ (palette R P D tag F U) (Sum.inr i)) = _ from meter R tag F U A (Multi.part_lit_quiet _) univ]
  rfl
end YM.AnalyticNext.GridStop.Harvest
