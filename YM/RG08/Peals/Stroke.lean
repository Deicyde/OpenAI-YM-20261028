import YM.RG08.Peals.Lap

/-! # Two legs, contraction kernel

E normalized log wells represent one action per translation, exponential
moment pre; each `chirp` includes the factor r!/(r-2)!/2. Used both in
finite-period and in direct cover operations (no windings in `none`). -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open RG Laurent Lattice Wilson Exterior Precision Bloch Next.Free Push.AbsoluteSums Finset Function Filter
open Stationary Analysis UVExt.Paths Matrix
open scoped Topology ContDiff
variable {α I : Type} {σ θ A B C : ℝ} {r n : ℕ} {m : Side}

lemma Dfade {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (v : E) (f : Tensor.T E ℝ (n+1)) (h : Tensor.Sym f) :
    D v (Tensor.diagonal f) = (↑(n+1:ℕ):ℝ) • Tensor.diagonal (f.curryLeft v) := by
  funext z; rw [Analysis.D,Tensor.differential_diagonal f h]; simp only [Pi.smul_apply,Nat.cast_smul_eq_nsmul]; rfl
lemma Dhush {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (v : E) (f : Tensor.T E ℝ 0) : D v (Tensor.diagonal f)=0 := by
  rw [show Tensor.diagonal f=(fun _=> Tensor.diagonal f 0) from funext fun _=> congr_arg f (Subsingleton.elim ..)]; funext x; simp [D]
lemma DDfade [Fintype α] (v u : α → ℝ) (f : Tensor.T (α → ℝ) ℝ (n+2)) (h : Tensor.Sym f) (x : α → ℝ) :
    D u (D v (Tensor.diagonal f)) x=(↑(n+2:ℕ):ℝ)*(↑(n+1:ℕ):ℝ)*f (Fin.cons v (Fin.cons u (fun _:Fin n=>x))) := by
  rw [Dfade v f h,DscaleL _ _ (Tensor.diag_smooth _ ω),Dfade u _ (Tensor.freeze_sym f h v)]
  rw [mul_assoc]; rfl

def stem1 (j : Beads α (r+1)) : Beads α r := Fin.tail j
def stroke (M : Row α α) (p : Option Side) (z v : Cover×α) :=
    p.elim (M z.2 v.2 (v.1-z.1)) (fun m=> M.acts m (0,z.2) (wrap m (v.1-z.1),v.2))
lemma stroke_late (M : Row α α) (h : M.safe) (m : I → Side) {l : Filter I} (hl : Tendsto (fun i => (m i).val) l atTop)
    (a b : Cover×α) : Tendsto (fun i=>stroke M (.some (m i)) a b) l (𝓝 (stroke M none a b)) := entry_limit m hl _ h ..
lemma stroke_minus {M N : Row α α} (h : Whole M) (e : Whole N) (p a b) :
    stroke (M-N) p a b=stroke M p a b-stroke N p a b := by
  cases p; rfl
  exact congr_fun (congr_fun (h.less e _) _) _
lemma stroke_known (M : Row α α) (h : M.strip σ A) (hp : 0≤σ) (z v) (p) : ‖stroke M p z v‖ ≤ A := by
  have he := Width.unweighted (h z.2 v.2) hp
  cases p with
  | none => exact budget_single he _
  | some m =>
    apply le_trans (norm_tsum_le_tsum_norm ?_) ?_
    · exact ((Work.F08.summable_sift (f:=M z.2 v.2) (he.2.1.of_norm) 0 (wrap m (v.1-z.1))).norm)
    exact budget_mono he (fun _=> norm_nonneg _) (fun i => by split <;> simp) |>.2.2
lemma stroke_trans (M : Row α α) (z v) (m : Side) (x : Site m) :
    stroke M (some m) z v=M.acts m (x+wrap m z.1,z.2) (x+wrap m v.1,v.2) := by
  apply tsum_congr; intro i; simp only [map_sub,zero_add,sub_eq_iff_eq_add,add_assoc,add_right_inj, add_comm ((wrap m) i)]

variable {F H : Shale α (r+2)} {M N : Row α α}

def tuneS (M : Row α α) (p : Option Side) (j : Beads α (r+2)) := stroke M p (j 0) (j (Fin.succ (0:Fin _)))
abbrev stems (j : Beads α (r+2)) : Beads α r := stem1 (stem1 j)
def rumba (M : Row α α) (p : Option Side) (F : Shale α (r+2)) := pool (F * tuneS M p) stems
def batting (n : ℕ) := (1/2:ℝ)*(n+2)*(n+1)
def chirp (M : Row α α) (p : Option Side) (F : Shale α (r+2)) := batting r • score (rumba M p F)
lemma stems_le (p : Beads α (r+1)) : girth (stem1 p) ≤ girth p := by
  unfold girth; rw [Fin.sum_univ_succ (n:=r)]; exact Nat.le_add_left ..
theorem rumba_price (h : M.strip σ A) (hp : 0≤σ) (hx : Glow F θ C) (ht : 0 ≤ θ) (p) (ha : 0 ≤ A) :
    Glow (rumba M p F) θ (A*C) := by
  apply Charge.poolage stems (ling_one ht)
  apply budget_mono (budget_scale ha hx) (fun i => mul_nonneg (ling_pos _ _).le (norm_nonneg _)); intro i
  rw [Pi.mul_apply,norm_mul]
  have he : (girth (stems i):ℝ)≤girth i := by exact_mod_cast (stems_le (stem1 i)).trans (stems_le i)
  apply le_trans (mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left he ht))
    (mul_le_mul_of_nonneg_left (stroke_known M h hp (i 0) (i (Fin.succ (0:Fin (r+1)))) p) (norm_nonneg _)) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (Real.exp_pos _).le) (le_of_eq ?_)
  unfold ling; ring
lemma tuneS_minus (M N : Row α α) (h : Whole M) (e : Whole N) (p) :
    (tuneS (r:=r) (M-N) p)=tuneS M p-tuneS N p := funext fun _ => stroke_minus h e ..

variable [Fintype α]
theorem chirp_price (h : M.strip σ A) (hp : 0≤σ) (hx : Glow F ((r+1:ℕ)*θ) C) (ht : 0 ≤ θ) (p) (ha : 0 ≤ A) :
    Glow (chirp M p F) θ (‖batting r‖*(A*C)) ∧ Tunable (chirp M p F) := by
  have hs := rumba_price h hp hx (by positivity) p ha
  exact ⟨(score_price hs ht).scale _,(score_tunable (hs.summable (ling_one (by positivity)))).scale _⟩
omit [Fintype α] in
lemma spinS {M : Row α α} (p) (h : Summable F) (e : Whole M) : Summable (F*tuneS M p) := by
  obtain ⟨s,D,hv,H⟩ := e
  exact sum_bounded h (fun x : Beads α (r+2)=> show ‖tuneS M p x‖ ≤ D from stroke_known M H hv.le ..)
omit [Fintype α] in
lemma rumba_summable (p) (h : Summable F) (e : Whole M) : Summable (rumba M p F) :=
  ((spinS p h e).hasSum.tsum_fiberwise stems).summable
omit [Fintype α] in
lemma rumba_less (hf : Summable F) (hp : Summable H) (he : Whole M) (p) :
    rumba M p (F-H)=rumba M p F-rumba M p H := by
  unfold rumba; rw [_root_.sub_mul,pool_minus _ (spinS p hf he) (spinS p hp he)]
omit [Fintype α] in
lemma rumba_alt (hf : Summable F) (he : Whole M) (hg : Whole N) (p) : rumba (M-N) p F=rumba M p F-rumba N p F := by
  unfold rumba; rw [tuneS_minus _ _ he hg, _root_.mul_sub,pool_minus _ (spinS p hf he) (spinS p hf hg)]
lemma chirp_minus (p) (h : Summable F) (hh : Summable H) (e : Whole M) :
    chirp M p (F-H)=chirp M p F-chirp M p H := by
  unfold chirp; rw [rumba_less h hh e,score_sub (rumba_summable p h e) (rumba_summable p hh e),smul_sub]
lemma chirp_note (p) (h : Summable F) (e : Whole M) (g : Whole N) :
    chirp (M-N) p F=chirp M p F-chirp N p F := by
  unfold chirp; rw [rumba_alt h e g, score_sub (rumba_summable p h e) (rumba_summable p h g),smul_sub]
@[simp] lemma chirp_empty (M : Row α α) (p) (h : Whole M) : chirp M p (0:Shale α (r+2))=0 := by
  have hx : Summable (0:Shale α (r+2)) := summable_zero
  simpa only [sub_self] using chirp_minus p hx hx h
end YM.RG08
