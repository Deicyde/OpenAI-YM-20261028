import YM.RG08.Quire.Pins
import YM.RG08.Peals.Rain
/-!
# Marked contractions; absolute mass in Banach costs
Attach from any actual marked root, with exact normalization T and covariance.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Quire
open RG Laurent Lattice Wilson Bloch Next.Free Work.F08 Push.AbsoluteSums Finset Function Filter
open UVExt.Paths Stationary
open scoped Topology ContDiff Classical BigOperators
variable {E F α ι : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {p : Option Side} {r s : ℕ} {w η A B C : ℝ}
variable {K H : Row α α} {f g : Rooted E α (r+2)}

def knot (p : Option Side) (f : Rooted E α (r+2)) (K : Row α α) (b : Beads α (r+2)) := tuneS K p b • f b
def jib (p : Option Side) (K : Row α α) (f : Rooted E α (r+2)) : Rooted E α r := sew (batting r • tub (knot p f K) stems)
lemma knot_budget (h : Lit f w A) (hv : 0≤w) (hk : K.strip η B) (hp : 0≤η) (he : 0≤B) (p) : Ink (ling w ∘ stems) (knot p f K) (B*A) := by
  apply budget_mono (budget_scale he h) (fun i=>mul_nonneg (ling_pos _ _).le (norm_nonneg _)); intro i
  simp only [knot,norm_smul]
  have hh (i:Beads α (r+2)) : (girth (stems i):ℝ) ≤ girth i := by exact_mod_cast (stems_le (stem1 i)).trans (stems_le i)
  have ht : ‖tuneS K p i‖≤B := stroke_known _ hk hp _ _ _
  simp only [ling]; grw [Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hh i) hv),ht]; exact le_of_eq (mul_left_comm ..)
lemma knot_prices (h : Pens f) (hk : Whole K) (p) : Pens (knot p f K) := by
  obtain ⟨σ,C,hp,H⟩:= hk
  have he : Lit f 0 (∑' i, ‖f i‖) := by rw [Lit,show ling (α:=α) (r:=r+2) 0=1 from funext fun i=>by simp [ling]]; exact h.priced
  exact (knot_budget he le_rfl (strip_mono H le_rfl (le_max_left C 0)) hp.le (le_max_right ..) p).pens (fun i=>ling_one le_rfl _)
lemma jib_tidy (h : Pens f) (hk : Whole K) (p) : Tidy (jib p K f) := Tidy.sewn (Pens.scale ((knot_prices h hk p).pours _) _)
lemma jib_print (h : Lit f w A) (hv : 0≤w) (hk : K.strip η B) (hp : 0≤η) (he : 0≤B) (p) : Lit (jib p K f) w (‖batting r‖*(B*A)) := stitching (Ink.scale ((knot_budget h hv hk hp he p).pour stems (ling_one hv)) _)
lemma jib_less (p) (h : Pens f) (hg : Pens g) (hv : Whole K) : jib p K (f-g)=jib p K f-jib p K g := by unfold jib; rw [show knot p (f-g) K=knot p f K-knot p g K from funext fun i=>smul_sub .., Pens.tub_sub stems (knot_prices h hv _) (knot_prices hg hv _),smul_sub,sew_sub]
lemma jib_kern (p) (h : Pens f) (he : Whole K) (hv : Whole H) : jib p (K-H) f=jib p K f-jib p H f := by unfold jib; rw [show knot p f (K-H)=knot p f K-knot p f H from funext fun i=> by unfold knot; rw [tuneS_minus _ _ he hv]; exact sub_smul ..,Pens.tub_sub stems (knot_prices h he _) (knot_prices h hv _),smul_sub,sew_sub]
lemma jib_blank (p) (h : Whole K) : jib p K (0:Rooted E α (r+2))=0 := by simpa only [sub_self] using jib_less p (Pens.zero _ _ : Pens (0:Rooted E α (r+2))) (Pens.zero _ _) h
lemma cast_sew (e : E→L[ℝ] F) (a : ℝ) (f : Rooted E α r) : e ∘ sew (a • f)=sew (a • (e ∘ f)) := by rw [sew_map, show e ∘ (a • f)=a • (e ∘ f) from funext fun i=>map_smul ..]
lemma jib_stays (e : E→L[ℝ] F) (p) (h : Pens f) (he : Whole K) : e ∘ jib p K f=jib p K (e ∘ f) := by unfold jib; rw [cast_sew,Pens.echo_pool _ (knot_prices h he _), show e ∘ knot p f K=knot p (e ∘ f) K from funext fun i=>map_smul ..]

-- from x₁ (not from x_mark) to the first contracted leg of V; retain all original costs.
variable {u v : Rooted E α (r+1)} {V W : Shale α (s+1)}
def stemLayer (u : Rooted E α (r+1)) (V : Shale α (s+1)) (b : Coves α r s) := V b.2 • u b.1
def coral (i : Coves α r s × Cover) := tide (i.1,(i.1.1 0).1+i.2)
def tie (u : Rooted E α (r+1)) (V : Shale α (s+1)) (K : Row α α) := tub (sires (stemLayer u V) (wakes K)) coral
def clasp (K : Row α α) (u : Rooted E α (r+1)) (V : Shale α (s+1)) := sew (syl r s • tie u V K)
lemma seized (x : Coves α r s × Cover) : girth (coral x)≤(s+1)*girth x.1.1+girth x.1.2 + s*size x.2 := by
  apply (tune_girth (x.1,(x.1.1 0).1+x.2)).trans; dsimp only; grw [size_add,show size (x.1.1 0).1≤girth x.1.1 from single_le_sum (f:=fun i=> size (x.1.1 i).1) (fun _ _=>Nat.zero_le _) (mem_univ 0)]; exact le_of_eq (by ring)
lemma coral_fee (hg : 0 ≤ w) (h : Lit u (((s+1:ℕ):ℝ)*w) A) (ht : Glow V w B) (hk : K.strip ((s:ℝ)*w) C) (hc : 0≤C) : Ink (ling w ∘ coral) (sires (stemLayer u V) (wakes K)) (C*(A*B)) := by
  apply Ink.sires_cost (h.prods ht) _ _ hc
  intro i; rw [mul_comm C]
  apply budget_mono (budget_scale (mul_nonneg (ling_pos _ _).le (ling_pos _ _).le) (hk (i.1 0).2 (i.2 0).2)) (fun i=>mul_nonneg (ling_pos _ _).le (norm_nonneg _)); intro a
  simp only [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); simp only [ling]
  rw [← Real.exp_add,← Real.exp_add]; apply Real.exp_monotone
  have he : (girth (coral (i,a)):ℝ) ≤ ((s+1:ℕ):ℝ)*(girth i.1:ℝ)+(girth i.2:ℝ)+(s:ℝ)*size a := by exact_mod_cast seized (i,a)
  nlinarith only [mul_le_mul_of_nonneg_left he hg]
lemma coral_pens (h : Pens u) (he : Summable V) (hk : Whole K) : Pens (sires (stemLayer u V) (wakes K)) := by
  obtain ⟨σ,C,hp,H⟩:= hk
  have he : Glow V 0 (∑' i, ‖V i‖) := by
    rw [Glow,show ling (α:=α) (r:=s+1) 0=1 from funext fun i=>by simp [ling]]; exact (pens_for.mpr he).priced
  have hh : Lit u ((↑(s+1:ℕ):ℝ)*0) (∑' i, ‖u i‖) := by rw [Lit,mul_zero,show ling (α:=α) (r:=r+1) 0=1 from funext fun i=>by simp [ling]]; exact h.priced
  exact (coral_fee (le_refl (0:ℝ)) hh he (strip_mono H (by rw [mul_zero]; exact hp.le) (le_max_left C 0)) (le_max_right ..)).pens (fun i=>ling_one le_rfl _)
lemma tie_pens (h : Pens u) (hp : Summable V) (hk : Whole K) : Pens (tie u V K) := (coral_pens h hp hk).pours _
lemma clasp_tidy (h : Pens u) (hp : Summable V) (hk : Whole K) : Tidy (clasp K u V) := Tidy.sewn ((tie_pens h hp hk).scale _)
lemma clasp_cost (hg : 0 ≤ w) (h : Lit u (((s+1:ℕ):ℝ)*w) A) (ht : Glow V w B) (hk : K.strip ((s:ℝ)*w) C) (hc : 0≤C) : Lit (clasp K u V) w (‖syl r s‖*(C*(A*B))) := stitching ((Ink.pour _ (coral_fee hg h ht hk hc) (ling_one hg)).scale _)
lemma clasp_balance (h : Pens u) (hv : Pens v) (hp : Summable V) (hk : Whole K) : clasp K (u-v) V=clasp K u V-clasp K v V := by unfold clasp; rw [show tie (u-v) V K=tie u V K-tie v V K from ?_,smul_sub,sew_sub]; unfold tie; rw [←Pens.tub_sub coral (coral_pens h hp hk) (coral_pens hv hp hk)]; congr 1; funext i; simp only [sires,stemLayer,Pi.sub_apply,smul_sub]
lemma clasp_income (h : Pens u) (he : Summable V) (hv : Summable W) (hk : Whole K) : clasp K u (V-W)=clasp K u V-clasp K u W := by unfold clasp; rw [show tie u (V-W) K=tie u V K-tie u W K from ?_,smul_sub,sew_sub]; unfold tie; rw [←Pens.tub_sub coral (coral_pens h he hk) (coral_pens h hv hk)]; congr 1; funext i; simp only [sires,stemLayer,Pi.sub_apply,smul_sub,sub_smul]
lemma clasp_debit (h : Pens u) (he : Summable V) (hk : Whole K) (hp : Whole H) : clasp (K-H) u V=clasp K u V-clasp H u V := by unfold clasp; rw [show tie u V (K-H)=tie u V K-tie u V H from ?_,smul_sub,sew_sub]; unfold tie; rw [←Pens.tub_sub coral (coral_pens h he hk) (coral_pens h he hp)]; congr 1; funext i; exact sub_smul ..
lemma clasp_stays (e : E→L[ℝ] F) (h : Pens u) (he : Summable V) (hk : Whole K) : e ∘ clasp K u V=clasp K (e ∘ u) V := by unfold clasp tie; rw [cast_sew,Pens.echo_pool _ (coral_pens h he hk), show e ∘ sires (stemLayer u V) (wakes K)=sires (stemLayer (e ∘ u) V) (wakes K) from funext fun i=>by simp only [Function.comp_apply,sires,stemLayer,_root_.map_smul]]
lemma clasp_zero (e : Summable V) (hk : Whole K) : clasp K (0:Rooted E α (r+1)) V=0 := by simpa only [sub_self] using clasp_balance (Pens.zero _ _ : Pens (0:Rooted E α (r+1))) (Pens.zero _ _) e hk
lemma clasp_stop (h : Pens u) (hk : Whole K) : clasp K u (0:Shale α (s+1))=0 := by simpa only [sub_self] using clasp_income h (show Summable (0:Shale α (s+1)) from summable_zero) (show Summable (0:Shale α (s+1)) from summable_zero) hk
end YM.RG08.Quire
