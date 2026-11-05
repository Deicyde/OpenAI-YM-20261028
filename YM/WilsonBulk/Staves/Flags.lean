import YM.WilsonBulk.Bunting.Regime

/-!
# Hypercubic symmetry on ACTUAL cover positions (not folded midpoint norm)

For any supportive rank template passing Regime, every rank separately has simple pointwise signed covariance, INCLUDING reversal base shift on reflected links. No spin-assumption about the frame or T. Recover by passing from finite-LHS identity on rank kernels. No uniform issue epochs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Parapet
open Lattice Laurent Function Filter Bloch RG Atelier Precision Exterior Wilson Pert.Bulk Sheet Hallmark Algebra
open scoped Topology Classical BigOperators ENNReal ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {α β : Type} {p q σ : ℝ} {c d : Side} {u r n e : ℕ}
-- if same linear input ticket; no rank mixing.
lemma truthful [Fintype α] (u : Matrix α α ℝ) (I : Record α) (hI : Document I)
    (h : submit (exposure (quill u (A:=ℝ))) (volumeTape I)=volumeTape I) : lecture (fun i j=> u i j) I=I := by
  have hh:= hI.lectured (A:=fun i j=> u i j); rw [exposure_quill_apply u] at h; apply monopoly hh.cap hh.coherent hI.cap hI.coherent; rw [lecture_tape]; exact h
-- pick origins

abbrev Mark (G : Gauge) := Market (Cloth G)
abbrev orient {α : Type} (i : α × Cloth G) := axisEquiv.symm i.2.1
abbrev flagFee (s : Signed) (i : Axis) : ℝ := if s.flip i then -1 else 1

def drift (s : Signed) (i : Axis) : Cover:= if s.flip i then -step (s.perm i) else 0
def banners (s : Signed) (p : Mark G) : Mark G := (s.act p.1 + drift s (orient p),(coord (s.perm (orient p)),p.2.2))
def ferry (i : Site c × Cloth G) : Edge (Site c) := (i.1,orient i)
def starColors (s : Signed) (b : Site c) (i : Pennant G c) : Pennant G c := let u:= Wilson.sendEdge s b (ferry i); (u.1,coord u.2,i.2.2)
lemma ferry_at (s : Signed) (b : Site c) (i : Pennant G c) : ferry (starColors s b i)=Wilson.sendEdge s b (ferry i) := Prod.ext rfl (axisEquiv.symm_apply_apply _)
lemma stiff (s : Signed) (b : Site c) : Injective (starColors (G:=G) s b) := by
  intro x y h; have hx : ferry x=ferry y := sendEdge_injective s b (by rw [← ferry_at,← ferry_at,h]); exact Prod.ext (by have hz:=congr_arg Prod.fst hx; exact hz) (Prod.ext (axisEquiv.symm.injective (congr_arg Prod.snd hx)) (by have hi:=congr_arg (fun i:Pennant G c=>i.2.2) h; exact hi))
lemma flags_move (s : Signed) (i : Mark G) : small c _ (banners s i)=starColors s (0:Site c) (small c (Cloth G) i) := by
  unfold starColors small banners ferry orient; cases he : s.flip (axisEquiv.symm i.2.1) <;> simp [drift,he, Wilson.sendEdge, Step.used, Step.rotate, posDir, affine, sub_eq_add_neg,wrap_signed]
def hallmark (s : Signed) (b : Site c) : Matrix (Pennant G c) (Pennant G c) ℝ := Matrix.of fun i j=> if starColors s b i=j then flagFee s (orient i) else 0
lemma swivel_chart (s : Signed) (b : Site c) : quill (hallmark s b) (A:=ℝ)=swivel (G:=G) s b := by
  ext1 x; ext1 i; unfold quill hallmark; simp only [Matrix.of_apply,ite_mul,zero_mul,smul_eq_mul]; rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]; rw [← ite_mul]; rfl

-- read sparse signed reorientation on rank pages.
lemma star_rank (s : Signed) (b : Site c) (i : Legs (Pennant G c) n) (P : Page (Pennant G c) n) :
    let Qx:= fun i j => hallmark (G:=G) s b i j
    Sheet.travel Qx P (starColors s b ∘ i)= (∏ j:Fin n, flagFee s (orient (i j))) * P i:= by
  intro Qx; unfold Sheet.travel tele; rw [tsum_eq_single i]; swap
  · intro j hj; unfold metal lot; apply mul_eq_zero_of_left; obtain ⟨k,hk⟩:= Function.ne_iff.mp hj; apply Finset.prod_eq_zero (Finset.mem_univ k); exact if_neg ((stiff s b).ne hk)
  unfold metal lot; congr 1; exact Finset.prod_congr rfl fun j _=> if_pos rfl -- inspect!
lemma march (s : Signed) (b : Site c) {I : Record (Pennant G c)} (hp : Document I) (h : Spins s b (volumeTape I) (volumeTape I)) (u e : ℕ) (i : Legs (Pennant G c) e) : I u e (starColors s b ∘ i)= (∏ j:Fin e,flagFee s (orient (i j))) * I u e i := by
  unfold Spins at h; rw [← swivel_chart] at h; exact (congr_fun (congr_fun (congr_fun (truthful (hallmark s b) I hp h).symm u) e) (starColors s b ∘ i)).trans (star_rank s b i _)
variable {D : ℕ→Side}
lemma Public.introduction (A : Text α n) (H : Public A) [Fintype α] (hD : Tendsto (fun i => (D i).val) atTop atTop) (u : Legs (Market α) n) (hn : n≠0) : Tendsto (fun i=>coupon (D i) _ A (small (D i) _ ∘ u)) atTop (𝓝 (A u)) := by
  obtain ⟨p,B,h,hp⟩:= H.money; exact printed_limit hD (Eventually.of_forall fun i=> hp) h (Eventually.of_forall fun _=>coupon_reads _ H.style) tendsto_const_nhds hn u
lemma Whisper.equivariant {I : Library G} (h : Whisper I) (s : Signed) (i : Legs (Mark G) n) (e : ℕ) : I e n (banners s ∘ i)=(∏ j:Fin n, flagFee s (orient (i j))) * I e n i := by
  cases n; · simp [Subsingleton.elim (banners s ∘ i) i]
  rename_i n; let D:=cascade (1:Side); let x:= I e (n+1); have ht := cascade_up (c:=(1:Side))
  refine tendsto_nhds_unique_of_eventuallyEq (Public.introduction x (h.palm _ _) ht (banners s ∘ i) (by omega)) ((Public.introduction x (h.palm _ _) ht i (by omega)).const_mul _) (Eventually.of_forall fun j=> ?_)
  let E:=small (D j) (Cloth G); change coupon (D j) (n+1) x (E ∘ (banners s ∘ i))=_
  rw [show E∘ (banners s ∘ i)=starColors s (0:Site (D j)) ∘ (E ∘ i) from funext fun l=> flags_move s (i l)]
  exact march s 0 (h.palm.at_issue (D j) h.style) ((h.guns _).spins s 0) e _ (E∘ i)
end YM.WilsonBulk.Parapet
