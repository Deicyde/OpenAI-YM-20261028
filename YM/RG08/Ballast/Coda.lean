import YM.RG08.Ballast.Tune

/-! # Uniqueness and thermodynamic determinations on actual lines -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open RG Laurent Lattice Wilson Bloch Next.Free Push.AbsoluteSums Finset Function Filter
open UVExt.Paths Stationary
open scoped Topology ContDiff Classical
variable {α β ι : Type} {r : ℕ} {w w' C A B : ℝ} {m : Side}
variable [Fintype α] {F H : Shale α r}

-- alpha angle/base included always. positivity result at all r>0.
omit [Fintype α] in
lemma chord_single (v : Fin r→Co m α) (x : Beads α r) (z : Site m) :
    rosary (m:=m) (fun k => Pi.single (v k) 1) z x=if silks z x=v then 1 else 0 := by
  classical
  split
  · rename_i h; rw [← h]; simp [rosary]
  rename_i h
  obtain ⟨i,hi⟩ := Function.ne_iff.mp h
  exact prod_eq_zero (mem_univ i) (Pi.single_eq_of_ne hi _)

lemma central_only {F : Shale α (r+1)} (h : Summable F) (hp : ordered F) (b) (hc : CenterDot b) (m : Side) :
    recital F m (fun k => Pi.single (silks (0:Site m) b k) 1)=∑' j, if silks (0:Site m) j=silks (0:Site m) b then F j else 0 := by
  rw [recital_eval _ h,sum_eq_single 0]
  · simp_rw [chord_single]; apply tsum_congr; intro x; split <;> simp
  · intro z _ hz; refine Eq.trans ?_ (show (∑' _j : Beads α (r+1), (0:ℝ))=0 from tsum_zero); apply tsum_congr; intro j
    rw [chord_single]; split
    next he =>
      rw [mul_one]; by_contra hv
      have hr : (j 0).1=0 := hp j hv
      have hy := congr_arg Prod.fst (congr_fun he 0); simp only [silks,hr,show (b 0).1=0 from hc,map_zero,add_zero] at hy
      exact hz hy
    next he => simp
  simp

lemma tuned_note_limit {F : Shale α (r+1)} (h : Summable F) (hp : ordered F) (b) (hc : CenterDot b)
    {v : Filter ι} (m : ι→Side) (hm : Tendsto (fun i => (m i).val) v atTop) : Tendsto (fun i =>
      recital F (m i) (fun k => Pi.single (silks (0:Site (m i)) b k) 1)) v (𝓝 (F b)) := by
  let s (i) (j : Beads α (r+1)) := if silks (0:Site (m i)) j=silks (0:Site (m i)) b then F j else 0
  let f (j : Beads α (r+1)) := if j=b then F j else 0
  simp_rw [central_only h hp b hc]
  have hu (j) : Tendsto (fun i => s i j) v (𝓝 (f j)) := by
    by_cases he : j=b
    · rw [he]; simp only [s,f,↓reduceIte]; exact tendsto_const_nhds
    obtain ⟨k,hk⟩ := Function.ne_iff.mp he
    refine EventuallyEq.tendsto ?_
    filter_upwards [eventually_unfold m hm (j k).1,eventually_unfold m hm (b k).1] with i hv hw
    dsimp only [f,s]; rw [if_neg he,if_neg]; intro ht
    apply hk
    have he := congr_fun ht k
    have hp : wrap (m i) (j k).1=wrap (m i) (b k).1 := add_left_cancel (congr_arg Prod.fst he)
    exact Prod.ext ((hv.symm.trans (congr_arg lift hp)).trans hw) (by change (silks (0:Site (m i)) j k).2=(silks (0:Site (m i)) b k).2; exact congr_arg Prod.snd he)
  have hb (i j) : ‖s i j‖ ≤ ‖F j‖ := by unfold s; split <;> simp
  have he := tendsto_tsum_of_dominated_convergence h.norm hu (.of_forall hb)
  rw [show ∑' j,f j=F b by simp [f]] at he; exact he

lemma solo (f : Shale α 0) (m : Side) (i : Fin 0 → PAC α m) (b : Beads α 0) :
    recital f m i=(Fintype.card (Site m) : ℝ)*f b := by
  rw [recital_eval _ (Summable.of_finite (f:=f))]; simp only [rosary,Finset.prod_empty,univ_eq_empty, mul_one]
  rw [tsum_eq_single b (fun i hi=> (hi (Subsingleton.elim ..)).elim)]; simp

-- exact stencil, all slots symmetrized
lemma unique_words (h : Tunable F) (v : Tunable H) {l : Filter ι} [l.NeBot] (m : ι→Side)
    (hm : Tendsto (fun i => (m i).val) l atTop) (he : ∀ᶠ i in l, stanza F (m i)=stanza H (m i)) : F=H := by
  have hu : ∀ᶠ i in l, recital F (m i)=recital H (m i) := he.mono fun i he => Tensor.ext_diag _ _ (h.2.2 (m i)) (v.2.2 (m i)) he
  cases r with
  | zero =>
    obtain ⟨i,hi⟩ := hu.exists
    funext b
    apply mul_left_cancel₀ (show (Fintype.card (Site (m i)):ℝ)≠0 by positivity)
    rw [← solo F (m i) 0 b,hi,solo H _ _ b]
  | succ r =>
    funext b
    by_cases hp : CenterDot b
    · exact tendsto_nhds_unique_of_eventuallyEq (tuned_note_limit h.1 h.2.1 b hp m hm) (tuned_note_limit v.1 v.2.1 b hp m hm) (hu.mono fun _ hx=> DFunLike.congr_fun hx _)
    rw [not_ne_iff.mp (mt (h.2.1 b) hp),not_ne_iff.mp (mt (v.2.1 b) hp)]

lemma Tunable.unique (h : Tunable F) (g : Tunable H) (hQ : ∀ m, stanza F m=stanza H m) : F=H :=
  unique_words h g (fun n : ℕ => (⟨n+1,Nat.succ_pos _⟩:Side)) (tendsto_add_atTop_nat _) (.of_forall fun _ => hQ _)
lemma Tunable.score_eq (h : Tunable F) : score F=F := (score_tunable h.1).unique h (stanza_score h.1)
lemma score_sub (h : Summable F) (v : Summable H) : score (F-H)=score F-score H := by
  have hp : Summable (F-H) := h.sub v
  exact (score_tunable hp).unique ((score_tunable h).sub (score_tunable v)) fun m => by rw [stanza_score hp, stanza_sub h v,stanza_sub (score_summable h) (score_summable v),stanza_score h,stanza_score v]
lemma reword_price (h : Tunable F) (hV : Glow H ((r+1:ℕ)*w) A) (hw : 0≤w) (hg : ∀ m,stanza F m=stanza H m) : Glow F w A := by
  have he : Summable H := hV.summable (ling_one (by positivity))
  rw [h.unique (score_tunable he) (fun m => (hg m).trans (stanza_score he m).symm)]
  exact score_price hV hw
end YM.RG08
