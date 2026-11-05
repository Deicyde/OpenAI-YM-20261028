import YM.RG08.Peals.Tiring

/-! # Rooted two-vertex joining estimates

With center addresses at the first contracted slots, charge preserves all
other slot positions; `s` output slots on shifted leg. No additional translation
counts even for full normalization.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open RG Laurent Lattice Wilson Exterior Precision Bloch Next.Free Push.AbsoluteSums Finset Function Filter
open Stationary Analysis UVExt.Paths Matrix
open scoped Topology ContDiff
variable {α : Type} {σ θ A B C : ℝ} {r s : ℕ} {m : Side} {M : Row α α}
variable {F E : Shale α (r+1)} {K H : Shale α (s+1)}

abbrev Coves (α : Type) (r s : ℕ) := Beads α (r+1) × Beads α (s+1)
def layerT (F : Shale α (r+1)) (K : Shale α (s+1)) (i : Coves α r s) : ℝ := F i.1*K i.2
def wakes (M : Row α α) (i : Coves α r s × Cover) : ℝ := M (i.1.1 0).2 (i.1.2 0).2 i.2

def shiftedBy (z : Cover) (b : Beads α s) (j : Fin s) : Cover × α := ((b j).1+z,(b j).2)
def tide (i : Coves α r s × Cover) : Beads α (r+s) := Fin.append (stem1 i.1.1) (shiftedBy i.2 (stem1 i.1.2))

def skiff (F : Shale α (r+1)) (K : Shale α (s+1)) (M : Row α α) : Shale α (r+s) :=
    pool (leads (layerT F K) (wakes M)) tide
abbrev syl (r s : ℕ) := ((↑(r+1):ℝ)*(↑(s+1):ℝ))
def medley (M : Row α α) (F : Shale α (r+1)) (K : Shale α (s+1)) := syl r s • score (skiff F K M)

lemma tune_girth (b : Coves α r s × Cover) : girth (tide b) ≤ girth b.1.1 + girth b.1.2 + s*size b.2 := by
  have hv : girth (shiftedBy b.2 (stem1 b.1.2)) ≤ girth b.1.2 + s*size b.2 := by
    apply le_trans (sum_le_sum (s:=univ) (f:=fun j:Fin s => size ((stem1 b.1.2 j).1+b.2)) fun j _=> size_add ..)
    simp only [sum_add_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,add_le_add_iff_right]
    exact stems_le ..
  unfold tide girth; rw [Fin.sum_univ_add]; simp only [Fin.append_left,Fin.append_right]; rw [add_assoc]; exact add_le_add (stems_le _) hv

theorem voyager (h : 0 ≤ σ) (hf : Glow F σ A) (hg : Glow K σ B) (hh : M.strip (s*σ) C) (hp : 0≤C) :
    Charge (fun i=> ling σ (tide i)) (leads (layerT F K) (wakes M)) (C*(A*B)) := by
  apply leads_cost hp (hf.cross hg)
  intro i
  have he := hh (i.1 0).2 (i.2 0).2
  rw [mul_comm _ (ling _ _*_)]; apply budget_mono (budget_scale (mul_nonneg (ling_pos _ _).le (ling_pos _ _).le) he) (fun _=> mul_nonneg (ling_pos _ _).le (norm_nonneg _))
  intro a
  simp only [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  unfold ling; rw [← Real.exp_add,← Real.exp_add]; apply Real.exp_monotone
  have he : (girth (tide (i,a)):ℝ) ≤ girth i.1+(girth i.2:ℝ)+(s:ℝ)*size a := by exact_mod_cast tune_girth (i,a)
  nlinarith only [mul_le_mul_of_nonneg_left he h]

theorem skiff_price (h : 0 ≤ σ) (hf : Glow F σ A) (hg : Glow K σ B) (hh : M.strip (s*σ) C) (hp : 0≤C) : Glow (skiff F K M) σ (C*(A*B)) :=
  Charge.poolage tide (ling_one h) (voyager h hf hg hh hp)

variable [Fintype α]

theorem medley_price (h : 0 ≤ σ) (hf : Glow F ((r+s+1:ℕ)*σ) A) (hg : Glow K ((r+s+1:ℕ)*σ) B) (hh : M.strip (s*((r+s+1:ℕ)*σ)) C) (hp : 0≤C) :
    Glow (medley M F K) σ (‖syl r s‖*(C*(A*B))) ∧ Tunable (medley M F K) := by
  have hx := skiff_price (by positivity : 0 ≤ ((r+s+1:ℕ):ℝ)*σ) hf hg hh hp
  exact ⟨(score_price hx h).scale _,(score_tunable (hx.summable (ling_one (by positivity)))).scale _⟩
omit [Fintype α] in
lemma voyage_exists (h : Whole M) (hf : Summable F) (he : Summable K) : Summable (leads (layerT F K) (wakes M)) := by
  have hv : Glow F 0 _ := (show Glow F 0 (∑' i, ‖F i‖) by unfold Glow Charge ling; simp only [zero_mul,Real.exp_zero,one_mul]; exact ⟨fun i=> norm_nonneg _,hf.norm,le_rfl⟩)
  have hg : Glow K 0 _ := (show Glow K 0 (∑' i, ‖K i‖) by unfold Glow Charge ling; simp only [zero_mul,Real.exp_zero,one_mul]; exact ⟨fun i=> norm_nonneg _,he.norm,le_rfl⟩)
  obtain ⟨w,A,hp,H⟩ := h
  exact (voyager (le_refl (0:ℝ)) hv hg (Work.F08.strip_mono H (by rw [mul_zero]; exact hp.le) (le_max_left A 0)) (le_max_right ..)).summable (fun i=> ling_one le_rfl (tide i))
omit [Fintype α] in
lemma skiff_exists (h : Whole M) (hf : Summable F) (he : Summable K) : Summable (skiff F K M) := ((voyage_exists h hf he).hasSum.tsum_fiberwise tide).summable
lemma medley_tunable (h : Whole M) (hf : Summable F) (he : Summable K) : Tunable (medley M F K) := (score_tunable (skiff_exists h hf he)).scale _
lemma medley_single (h : Whole M) (hf : Summable F) (hg : Summable E) (hp : Summable K) :
    medley M (F-E) K=medley M F K-medley M E K := by
  have hx : skiff (F-E) K M=skiff F K M-skiff E K M := by
    unfold skiff; rw [show layerT (F-E) K=layerT F K-layerT E K from funext fun i => sub_mul ..,leads_minus,pool_minus _ (voyage_exists h hf hp) (voyage_exists h hg hp)]
  unfold medley; rw [hx,score_sub (skiff_exists h hf hp) (skiff_exists h hg hp),smul_sub]
lemma medley_dual (h : Whole M) (hf : Summable F) (hg : Summable K) (hp : Summable H) :
    medley M F (K-H)=medley M F K-medley M F H := by
  have hx : skiff F (K-H) M=skiff F K M-skiff F H M := by
    unfold skiff; rw [show layerT F (K-H)=layerT F K-layerT F H from funext fun i => _root_.mul_sub ..,leads_minus,pool_minus _ (voyage_exists h hf hg) (voyage_exists h hf hp)]
  unfold medley; rw [hx,score_sub (skiff_exists h hf hg) (skiff_exists h hf hp),smul_sub]
lemma medley_flow {N : Row α α} (h : Whole M) (e : Whole N) (hf : Summable F) (hg : Summable K) :
    medley (M-N) F K=medley M F K-medley N F K := by
  have hx : skiff F K (M-N)=skiff F K M-skiff F K N := by
    unfold skiff; rw [show wakes (r:=r) (s:=s) (M-N)=wakes M-wakes N from rfl,leads_diff,pool_minus _ (voyage_exists h hf hg) (voyage_exists e hf hg)]
  unfold medley; rw [hx,score_sub (skiff_exists h hf hg) (skiff_exists e hf hg),smul_sub]
lemma medley_start (h : Whole M) (e : Summable K) : medley M (0:Shale α (r+1)) K=0 := by
  have he : Summable (0:Shale α (r+1)) := summable_zero
  simpa only [sub_self] using medley_single h he he e
lemma medley_end (h : Whole M) (e : Summable F) : medley M F (0:Shale α (s+1))=0 := by
  have he : Summable (0:Shale α (s+1)) := summable_zero
  simpa only [sub_self] using medley_dual h e he he
end YM.RG08
