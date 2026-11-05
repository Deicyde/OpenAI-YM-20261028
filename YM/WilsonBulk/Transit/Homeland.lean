import YM.WilsonBulk.Transit.Rests

/-!
# Raw-body unchanged contraction estimate for all rank legs

Here symmetric on all slots; specialized marked fields may use the
head-only portion with weaker assumptions later. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet
open Function Filter Finset Lattice Laurent Pert.Bulk Bloch RG
open Push.AbsoluteSums Work.F08
open scoped Topology ENNReal BigOperators Classical
variable {α β : Type} {σ θ p q M : ℝ} {d n : ℕ} {L : Side} {P : Text α (n+1)}
variable {F H : Legs ℝ (n+1)} {T : Legs (Duct (Market α) (Market β)) (n+1)}
section heads
variable (h : Within (lawn α) θ M P) (ht : ∀ i, AuditLine (T i) (spotCost L σ) (n+1) (F i) (H i))
    (hp : 0 ≤ σ) (hθ : 0≤θ)
-- head held fixed aggregate
include h ht hθ
lemma corridor (x : Market α) (y : Legs (Market β) n) :
    Summable fun v=> P (hitch x v)*lot (crop T) v y := by
  have hv : Summable (fun v => P (hitch x v)) := by
     have hb:= within_total h hθ 0 x; refine (hb.comp_injective (show Injective (hitch x (n:=n)) from fun a b e=> by simpa using congr_arg crop e)).congr (fun a=> ?_); simp
  apply Summable.of_norm_bounded (hv.norm.mul_right (∏ i: Fin n, F i.succ)); intro v
  rw [norm_mul]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  unfold lot; rw [norm_prod]; exact prod_le_prod (fun i _=> norm_nonneg _) (fun i _=> (ht i.succ).entry ..)
omit h ht hθ

def hometown (T : Legs (Duct (Market α) (Market β)) (n+1)) (P : Text α (n+1)) (x : Market α) (y : Legs (Market β) n) := ∑' v,P (hitch x v)*lot (crop T) v y
include h ht hθ hp
omit hθ in
lemma fare_home (hs : σ/L.val≤θ) (x : Market β) (y : Legs (Market β) n) : tele T P (hitch x y)= ∑' v,T 0 v x * hometown T P v y := by
  unfold tele; rw [← (hitchEquiv _ _).tsum_eq _]
  refine Eq.trans ((Equiv.summable_iff (hitchEquiv _ _)).mpr (carrier (delta_shape hp hs) ht h hp (hitch x y))).tsum_prod ?_
  change ∑' v : Market α,∑' u:Legs (Market α) n,metal T P (hitch x y) (hitch v u) = _
  simp_rw [metal_head,tsum_mul_left]; rfl
omit hp in
lemma territory (L' : Finset (Legs (Market β) n)) (x : Market α) (e : Legs (Market β) n → ℝ) :
    let g := fun v : Legs (Market α) n => P (hitch x v)*(∑ y∈L',lot (crop T) v y * e y)
    Summable g ∧ ∑ y ∈ L',hometown T P x y * e y = ∑' v,g v := by
  intro g
  have hh (y : Legs (Market β) n) := (corridor h ht hθ x y).mul_right (e y)
  have he v : g v= ∑ y∈L', P (hitch x v)*lot (crop T) v y*e y:= by unfold g; rw [mul_sum]; simp_rw [← mul_assoc]
  refine ⟨(summable_sum (fun i (_:i∈L')=> hh i)).congr (fun v=> (he v).symm),?_⟩
  rw [tsum_congr he, Summable.tsum_finsetSum (fun x (_:x∈L')=>hh x)]; refine sum_congr rfl fun y _=> ?_; unfold hometown; rw [tsum_mul_right]
end heads

section budget
variable [Fintype α]
def resort (θ : ℝ) (M : ℝ) (F : Legs ℝ n) (L : Side) (d : ℕ) (α : Type) [Fintype α] := (Fintype.card (Legs α n):ℝ)*(moss L F θ d*M)
lemma globe_bound (h : TicketNull d P) (he : Within (lawn α) θ M P)
   (ht : ∀ i, AuditLine (T i) (spotCost L σ) (n+1) (F i) (H i)) (hv : ∀ i:Fin n, WalkIn L σ (T i.succ) d (F i.succ))
   (hs : 0≤σ) (hθ : 0<θ) (hL : σ/L.val≤θ/2) (x : Market α) :
   SumBudget (fun y=> Real.exp (globe L σ x y)*‖hometown T P x y‖) (resort θ M (crop F) L d α) := by
  apply budget_dual (fun _=> (Real.exp_pos _).le); intro s g hp
  let w := fun v : Legs (Market α) n=> P (hitch x v)*(∑ y∈s,lot (crop T) v y*g y)
  obtain ⟨hf,hf'⟩:= territory he ht hθ.le s x g; rw [hf']; change ‖∑' v, w v‖ ≤ _
  let e := around x.1 (α:=α) (n:=n)
  rw [← e.tsum_eq _]; change ‖∑' v, (w ∘ e) v‖ ≤ _
  rw [((e.summable_iff.mpr (show Summable w from hf)).tsum_prod),tsum_fintype]; unfold resort; apply (norm_sum_le ..).trans
  apply LE.le.trans (sum_le_sum ?_: ∑ i : Legs α n, ‖_‖ ≤ ∑ _ : Legs α n,moss L (crop F) θ d*M) _
  · intros t _
    let f := tester (crop T) x t s g
    change ‖∑' u: Slip n, draft P x t u*f u‖ ≤ _
    have hh := draft_past (T:=crop T) he (F:=crop F) hv hs (X:=x) (p:=g) (s:=s) hp hθ hL t
    have ha : HasSum (fun u=> draft P x t u * Taylor.lineRead u (Taylor.abridge d f)) 0 := h.removes x t f
    have heq a : f a=Taylor.rest d f a+Taylor.lineRead a (Taylor.abridge d f) := by unfold Taylor.rest; ring
    rw [tsum_congr (g:=fun a=> draft P x t a*Taylor.rest d f a + draft P x t a * Taylor.lineRead a (Taylor.abridge d f)) (fun a=>?_)]
    · rw [Summable.tsum_add (hh.2.1.of_norm) ha.summable]; rw [show (∑' a,draft P x t a * Taylor.lineRead a (Taylor.abridge d f))=0 from ha.tsum_eq, add_zero]; exact (norm_tsum_le_tsum_norm hh.2.1).trans hh.2.2
    rw [← mul_add,← heq]
  simp [nsmul_eq_mul]

lemma billed_tele (h : TicketNull d P) (he : Within (lawn α) θ M P)
   (ht : ∀ i, AuditLine (T i) (spotCost L σ) (n+1) (F i) (H i)) (hv : ∀ i:Fin n, WalkIn L σ (T i.succ) d (F i.succ))
   (hs : 0≤σ) (hθ : 0<θ) (hL : σ/L.val≤θ/2) (y : Market β) :
   rent (lawn β) σ (tele T P) 0 y ≤ ENNReal.ofReal (H 0 * resort θ M (crop F) L d α) := by
  rw [rent_head, ENNReal.ofReal_mul (ht 0).floor]
  have hx := mul_le_mul_left ((ht 0).col y) (ENNReal.ofReal (resort θ M (crop F) L d α))
  simp_rw [fare_home (P:=P) he ht hs (hL.trans (by linarith))]
  apply (ENNReal.tsum_le_tsum fun z=> bill_tsum ..).trans
  refine le_trans ?_ hx; rw [← ENNReal.tsum_mul_right, ENNReal.tsum_comm]
  refine ENNReal.tsum_le_tsum fun w=> ?_
  have h0 := globe_bound h he ht hv hs hθ hL w
  have ht' := (globe_pay (budget_nonneg h0)).1 (show SumBudget (fun z=> Real.exp (globe L σ w z)*|hometown T P w z|) _ from h0)
  refine LE.le.trans ?_ (mul_le_mul_right ht' (bill (T 0 w y) ((n+1:ℕ)*spotCost L σ w y)))
  rw [← ENNReal.tsum_mul_left]; refine ENNReal.tsum_le_tsum (fun z=>bill_mul _ _ _ _ _ ?_)

  refine le_trans (expense_sep (L:=L) w y z σ hs) ?_
  unfold globe; push_cast; apply add_le_add_left; unfold spotCost; have ht := mul_nonneg hs (delta_nonneg L w.1 y.1); linarith

lemma travel_budget (h : TicketNull d P) (hR : Regular P) (he : Within (lawn α) θ M P)
   {G : Duct (Market α) (Market β)} (ht : AuditLine G (spotCost L σ) (n+1) p q) (hv : WalkIn L σ G d p)
   (hs : 0≤σ) (hθ : 0 < θ) (hL : σ/L.val≤θ/2) :
    Within (lawn β) σ (q*((Fintype.card α:ℝ)^n*(momentWeight (θ/2) d*p^n/(L.val:ℝ)^d*M))) (travel G P) := by
  have ha := ht.floor; have hu:= ht.height; have hd:= momentWeight_nonneg (half_pos hθ).le d; have hh:=he.1
  refine ⟨by positivity,fun i x=>?_⟩; rw [(travel_regular _ hR).pay_one i 0];
  apply LE.le.trans (billed_tele (T:=fun _=>G) h he (fun _=>ht) (fun _=> hv) hs hθ hL _) (Eq.le ?_); simp [crop,resort,moss,Legs]
end budget
end YM.WilsonBulk.Sheet
