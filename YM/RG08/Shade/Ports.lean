import YM.RG08.Germ.Foliage
import YM.RG08.Quire.Cond
import YM.RG08.Scores.PageFees
/-!
# Rooted kernels stay on actual cells. All passive lifts literal
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Shade
open Function Filter Set Lattice Wilson Exterior Bloch Next.Free Work.F08 RG Laurent Precision Finset
open Quire Stationary Scores Scores.Pages Matrix Push.AbsoluteSums
open Planned.PrimaryIntegral295.Place
open scoped Topology ContDiff Classical
variable {E H α β : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup H] [NormedSpace ℝ H] {D r : ℕ} {L m f : Side} {G : Gauge} {i : Site L} {c : Site m} {R w η σ A B : ℝ}
private def rate (L : Side) := ((L.val):ℝ)⁻¹
def spinner (x : Site L) := ((L.val:ℝ))⁻¹ • seat (Lattice.lift x)
lemma nesting (p : Site L) (h : Odd L.val) (he : 1/2 ≤ R) : Stays (spinner p) (L.val:ℝ)⁻¹ R := by
  let d := rate L
  have hP : 0<(L.val:ℝ) := by positivity
  have hd : 0<d := inv_pos.mpr hP
  have hQ : d ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast L.property)
  have hx k : ‖spinner p k‖≤ (1-d)/2 := by
    change ‖d • seat (Lattice.lift p) k‖≤ _; rw [norm_smul,Real.norm_of_nonneg hd.le]
    have hv := Ratio.unambiguous h p k; have ht := (lift_centers p k).1
    have he : 2 * ((Lattice.lift p k).natAbs:ℝ) ≤ L.val - 1 := by
      apply le_sub_iff_add_le.mpr; exact_mod_cast (show 2*(Lattice.lift p k).natAbs+1 ≤ L.val by omega)
    rw [seat_apply, ← norm_natAbs,Real.norm_natCast]; have hw : d * L.val=1 := inv_mul_cancel₀ hP.ne'; nlinarith only [hw, mul_le_mul_of_nonneg_left he hd.le]
  have hh : MapsTo (fun x:E4=> spinner p+d•x) (examinable R) (examinable R) := by
    intro x h k
    change ‖spinner p k+d • x k‖ ≤ _; apply (norm_add_le ..).trans
    rw [norm_smul,Real.norm_of_nonneg hd.le]
    apply (add_le_add (hx k) (mul_le_mul_of_nonneg_left (h k) hd.le)).trans
    nlinarith only [mul_le_mul_of_nonneg_left he (sub_nonneg.mpr hQ)]
  refine ⟨hd.le,hQ,fun i=>(hx i).trans ((div_le_div_of_nonneg_right (sub_le_self _ hd.le) (by norm_num)).trans he),hh⟩
-- test φ(p/L+x/L)
def readdress (x : Voice D R) (p : Site L) := if hp:Odd L.val ∧ 1/2≤R then x.comp (scroll _ _ _ (nesting p hp.1 hp.2)) else 0
lemma read_scores (h : Odd L.val) (he : 1/2≤R) (p : Site L) (x : Voice D R) : ‖readdress x p‖≤‖x‖ ∧ ∀ g,
    readdress x p (sheet D R g) = x (sheet D R (roll (spinner p) ((L.val:ℝ))⁻¹ g)) := by
  have hv : readdress x p=x.comp (scroll (spinner p) _ _ (nesting p h he)) := dif_pos ⟨h,he⟩
  rw [hv]; constructor; swap; · intro g; rw [ContinuousLinearMap.comp_apply, (scroll_leaf ..).2]
  exact (ContinuousLinearMap.opNorm_comp_le ..).trans (by grw [(scroll_leaf ..).1]; simp)

variable {V W : Rooted E α r} {Q Q' : Fin r → Row α β}
-- readdress field; actual carry through `(Ratio.splitSites)`.
def shiftP (p : Site L) (V : Rooted E α r) := tub V (carpet p)
lemma shift_print (p : Site L) (h : Lit V w A) (hh : 0≤η) (hp : η≤L.val*w) :
    Lit (shiftP p V) η (Real.exp (4*η)^r*A) := by
  refine Ink.pour _ (budget_mono (budget_scale (show 0≤Real.exp (4*η)^r from by positivity) h) (fun i=>mul_nonneg (ling_pos _ _).le (norm_nonneg _)) (fun i=>(mul_le_mul_of_nonneg_right (carry_ling p i hh hp) (norm_nonneg _)).trans_eq (mul_assoc ..)) : Ink (ling η ∘ carpet p) V _) (ling_one hh)
lemma shifted (p : Site L) (h : Pens V) : Pens (shiftP p V) := h.pours _

variable [Fintype α] [Fintype β]
-- No op needs pickup points beyond actual mathematical stem.
def rhyme (V : Rooted E α r) (Q : Fin r → Row α β) := tub (sires V (flicker Q)) fieldsAt
def spring (V : Rooted E α r) (Q : Row α β) := sew (rhyme V (fun _=>Q))
private lemma rhyme_cost {p : Fin r → ℝ} (h : Lit V w A) (hw : 0≤w) (hp : 0 ≤ p)
    (hh : ∀ i,(Q i).strip w (p i)) : Ink (ling w ∘ fieldsAt) (sires V (flicker Q)) (((Fintype.card β:ℝ)^r * ∏ i,p i)*A) := by -- use grow_cost on norms
  have hv := grow_cost (fun x=> ‖V x‖) Q (show Glow (fun x=> ‖V x‖) w A by simpa [Glow, Quire.Lit,Charge,Quire.Ink] using h) hw hp hh
  unfold Quire.Ink; unfold Charge at hv; simp_rw [sires,norm_smul,mul_comm ‖flicker Q _‖]; simp_rw [leads,norm_mul,norm_norm] at hv; exact hv
lemma rhyme_receipt {p : Fin r→ℝ} (h : Lit V w A) (hw : 0≤w) (hp : 0 ≤ p) (hh : ∀ i,(Q i).strip w (p i)) :
    Lit (rhyme V Q) w (((Fintype.card β:ℝ)^r * ∏ i,p i)*A) := Ink.pour _ (rhyme_cost h hw hp hh) (ling_one hw)
lemma spring_receipt {Q : Row α β} (h : Lit V w A) (hw : 0≤w) (hv : 0≤B) (hh : Q.strip w B) : Lit (spring V Q) w (((Fintype.card β:ℝ)^r*B^r)*A) := by
  simpa only [spring,prod_const,card_univ,Fintype.card_fin] using stitching (rhyme_receipt h hw (show (0:Fin r → ℝ)≤ fun _=> B from fun _=> hv) (Q:=fun _=>Q) (fun _=>hh))
private lemma rhyme_fk (h : Pens V) (hp : ∀ i, Whole (Q i)) : Pens (sires V (flicker Q)) := by
  choose w A hw hA using hp; let p (i : Fin r) := max 0 (A i)
  have hV : Lit V 0 (∑' i, ‖V i‖) := by rw [Quire.Lit,show ling (α:=α) (r:=r) 0=1 from funext fun i=>by simp [ling]]; exact h.priced
  exact (rhyme_cost hV le_rfl (show 0 ≤ p from fun i=> le_max_left ..) (fun i=>strip_mono (hA i) (hw i).le (le_max_right ..))).pens (fun i=> ling_one le_rfl _)
lemma spring_tidy {Q : Row α β} (h : Pens V) (hv : Whole Q) : Tidy (spring V Q) := Tidy.sewn ((rhyme_fk (Q:=fun _=>Q) h fun _=>hv).pours _)
lemma rhyme_sub (h : Pens V) (hp : Pens W) (hq : ∀ i, Whole (Q i)) : rhyme (V-W) Q=rhyme V Q-rhyme W Q := by
  unfold rhyme; rw [show sires (V-W) (flicker Q)=sires V (flicker Q)-sires W (flicker Q) from funext fun i=>smul_sub ..,Pens.tub_sub fieldsAt (rhyme_fk h hq) (rhyme_fk hp hq)]
lemma rhyme_variation (h : Pens V) (hk : ∀ i, Whole (Q i)) (he : ∀ i, Whole (Q' i))(p : Fin r)(hv : ∀ i,i≠p→Q i=Q' i) : rhyme V (update Q p (Q p-Q' p))=rhyme V Q-rhyme V Q' := by
  unfold rhyme; rw [←Pens.tub_sub fieldsAt (rhyme_fk h hk) (rhyme_fk h he)]; congr 1; funext i
  unfold sires; simp only [Pi.sub_apply]; rw [←sub_smul]; congr 1
  unfold flicker; rw [← Finset.mul_prod_erase _ _ (mem_univ p),← Finset.mul_prod_erase _ (fun j=> Q j _ _ _) (mem_univ p),← Finset.mul_prod_erase _ (fun j=> Q' j _ _ _) (mem_univ p)]; rw [update_self]; simp only [Pi.sub_apply]; rw [sub_mul]; congr 1 <;> (congr 1; apply prod_congr rfl; intro j hj; first| rw [update_of_ne (mem_erase.mp hj).1]; done| rw [update_of_ne (mem_erase.mp hj).1,hv _ (mem_erase.mp hj).1])
lemma spring_sub {Q : Row α β} (h : Pens V) (hv : Pens W) (hp : Whole Q) : spring (V-W) Q=spring V Q-spring W Q := by unfold spring; rw [rhyme_sub h hv (fun _=>hp), sew_sub]
lemma spring_zero {Q : Row α β} (hp : Whole Q) : spring (0:Rooted E α r) Q=0 := by simpa only [sub_self] using spring_sub (Pens.zero _ _ : Pens (0:Rooted E α r)) (Pens.zero _ _) hp
lemma spring_echo {Q : Row α β} (e : E→L[ℝ] H) (h : Pens V) (ht : Whole Q) : e ∘ spring V Q=spring (e ∘ V) Q := by
  unfold spring rhyme; rw [sew_map, Pens.echo_pool _ (rhyme_fk h fun i : Fin r=>ht)]; congr 2; exact funext fun i=> map_smul ..

lemma shifts (x : Rooted ℝ α r) (g : Ratio m f) (p : Site g.count) (i : Site m) (V : Fin r→ PAC (Co g.count α) m) (h : Pens x) :
    stitch (shiftP p x) m i V=stitch x f (g.assemble (i,p)) (carriesG g ∘ V) := by
  unfold shiftP; rw [st_tub _ _ h,stitch_apply h.of_norm]; refine tsum_congr fun b=>?_; congr 1; refine prod_congr rfl fun j _=> ?_
  simp only [Function.comp_apply,carriesG,silks,split_co,moves_parent,moves_residue,carpet, ← g.unpack]; simp
lemma rhyme_tell (x : Rooted ℝ α r) (h : Pens x) (ht : ∀ i, Whole (Q i)) (z : Site m) (V : Fin r→PAC β m) :
    stitch (rhyme x Q) m z V=stitch x m z (fun i=> (Q i).acts m*ᵥ V i) := by
  unfold rhyme; rw [st_tub _ _ (rhyme_fk h ht), stitch_apply h.of_norm]
  have he := sum_bounded (rhyme_fk (Q:=Q) h ht).of_norm (g:=fun i=>rosary V z (fieldsAt i)) (fun i=>rosary_bill V z (fieldsAt i)); rw [he.tsum_prod]; apply tsum_congr; intro i
  choose w A hw hA using ht
  unfold rosary silks; dsimp only; simp_rw [row_expand (hA _) (hw _|>.le)]
  rw [← tsum_fin_prod _ (fun j=>row_money (hA j) (hw j|>.le) _ _ _), ←tsum_mul_left]; apply tsum_congr; intro j
  unfold sires flicker; rw [smul_eq_mul,mul_comm _ (x i),mul_assoc, Finset.prod_mul_distrib]; congr 2; refine prod_congr rfl fun k _=>?_ ; simp only [fieldsAt,map_add,add_assoc]
lemma spring_tell {Q : Row α β} (x : Rooted ℝ α r) (h : Pens x) (ht : Whole Q) (z : Site m) (V : PAC β m) :
    rootSong (spring x Q) m z V=rootSong x m z (Q.acts m *ᵥ V) := by unfold spring; rw [sew_diagonal (f:=rhyme x (fun _=>Q)) ((rhyme_fk h fun i : Fin r=>ht).pours _ : Pens (rhyme x _))]; exact rhyme_tell x h (fun i=>ht) z (fun _=>V)
end YM.RG08.Shade
