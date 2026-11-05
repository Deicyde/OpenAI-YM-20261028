import YM.RG08.Needle.Task
/-!
# Raw transfer linear algebra incl sector reading shifts
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Needle
open RG Laurent Lattice Wilson Bloch Exterior Precision Push.AbsoluteSums Finset Function Filter Matrix Work.F08 Next.Free
open UVExt.Paths Stationary Planned.PrimaryIntegral295 Shade Quire Source Source.Drops Labels Scores Scores.Pages Tall Vale Reflect Staffer Loom PertExtension.Series.Radial PertExtension.Series.Tested
open scoped Topology ContDiff Classical BigOperators Matrix.Norms.Frobenius
variable {E H I α β:Type}[NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E]{G:Gauge}{L c f p: Side}
variable {V U: Screed E α}{A:Canticle α}{K:Row α α}{n r s t u v m D:ℕ}
variable {R W:Rooted E α r}
lemma grant_sm {V:Rooted E α n}(r:ℕ)(t:ℝ): grant r (t•V)=t•grant r V := by
  by_cases h:r=n; subst n; rw [grant_self,grant_self]
  simp [grant,h]
lemma grant_plus {V W:Rooted E α n}(r:ℕ) : grant r (V+W)=grant r V+grant r W := by
  by_cases h:r=n; subst n; rw [grant_self,grant_self,grant_self]
  simp [grant,h]
lemma tub_scale {V : α→E}(h:Pens V)(t:ℝ)(Y:α→β) : tub (t•V) Y=t•tub V Y := by funext i; let e:=t • ContinuousLinearMap.id ℝ E; exact (congr_fun (Pens.echo_pool Y h e) i).symm
lemma spring_a [Fintype α][Fintype β]{Q:Row α β}(h:Pens R)(t:ℝ)(hp:Whole Q): spring (t•R) Q=t•spring R Q := by
  let e := t • ContinuousLinearMap.id ℝ E; change spring (e ∘ R) Q=e ∘ spring R Q; exact (spring_echo _ h hp).symm
lemma spring_plus [Fintype α][Fintype β]{Q:Row α β}(h:Pens R)(hw:Pens W)(hp:Whole Q): spring (R+W) Q=spring R Q+spring W Q := sub_eq_iff_eq_add.mp (Eq.symm (by simpa using! spring_sub (h.plus hw) hw hp))
lemma jib_more {U V:Rooted E α (r+2)}(h:Pens U)(he:Pens V)(hp: Whole K): jib none K (U+V)=jib none K U+jib none K V := sub_eq_iff_eq_add.mp (Eq.symm (by simpa using! jib_less none (h.plus he) he hp))
lemma jib_wt {U:Rooted E α (r+2)} (h:Pens U)(v:ℝ)(hp:Whole K): jib none K (v•U)= v • jib none K U := Eq.symm (jib_stays (v • ContinuousLinearMap.id ℝ E) none h hp)
lemma clasp_more {V W:Rooted E α (r+1)}{A:Shale α (s+1)}(h:Pens V)(he:Pens W)(hp:Whole K)(ht:Summable A):clasp K (V+W) A=clasp K V A+clasp K W A:= sub_eq_iff_eq_add.mp (Eq.symm (by simpa using! clasp_balance (h.plus he) he ht hp))
lemma clasp_wt {V:Rooted E α (r+1)}{A:Shale α (s+1)}(h:Pens V)(hp:Whole K)(ht:Summable A)(v:ℝ): clasp K (v•V) A=v • clasp K V A := Eq.symm (clasp_stays (v • ContinuousLinearMap.id ℝ E) h ht hp)
variable [Fintype α]
set_option maxHeartbeats 400000 in
lemma muted (hp:Whole K)(h:∀ i j,Tunable (A i j))(he:∀ i j,Tidy (U i j))(hv:∀ i j,Tidy (V i j)) : murmur none K A (U+V) n u=murmur none K A U n u + murmur none K A V n u := by
  induction n using Nat.caseStrongRecOn generalizing u with
  | zero=> funext r; rw [Pi.add_apply,murmur,murmur,murmur]; rfl
  | ind i ih=>
    let f n:=murmur none K A U n; let g n:=murmur none K A V n; let X n u:=Refrain K A none n u
    have hf n u r : Pens (f n u r) := (quiet_tidily hp h he ..).pens -- Lean .. all implicit
    have hg n u r : Pens (g n u r):= (quiet_tidily hp h hv ..).pens
    have hW n u r : Summable (X n u r):= (refrains_tune hp h ..).1
    funext r
    have hh : ∑ b∈wheel i,∑ a∈wheel u,Quire.hymn K (murmur none K A (U+V) b.1 a.1) (X b.2 a.2) r=
         (∑ b∈wheel i,∑ a∈wheel u,Quire.hymn K (f b.1 a.1) (X b.2 a.2) r)+(∑ b∈wheel i,∑ a∈wheel u,Quire.hymn K (g b.1 a.1) (X b.2 a.2) r) := by
      rw [← sum_add_distrib]; apply Finset.sum_congr rfl; intro b hb; rw [←sum_add_distrib]; apply Finset.sum_congr rfl; intro a ha
      rw [ih _ (by have he:=mem_antidiagonal.mp hb; omega)]
      unfold Quire.hymn; rw [←sum_add_distrib]; apply Finset.sum_congr rfl; intro j _; change grant r (clasp K ((f b.1 a.1) (j.1+1)+(g b.1 a.1) (j.1+1)) ((X b.2 a.2) (j.2+1))) = _; rw [clasp_more (hf ..) (hg ..) hp (hW ..),grant_plus]
    rw [Pi.add_apply,murmur_step, hh, congr_fun (ih i le_rfl) (r+2),Pi.add_apply,jib_more (hf i u _) (hg i u _) hp,murmur_step,murmur_step]; unfold f g X at *; simp only [smul_add]; abel
lemma munified (hp:Whole K)(h:∀ i j,Tunable (A i j))(he:∀ i j,Tidy (U i j))(v:ℝ): murmur none K A (v•U) n u r=v • murmur none K A U n u r := Eq.symm (murmur_map (v • ContinuousLinearMap.id ℝ E) hp h he)
lemma hymn_blank {U: Spine E α} (hk:U=0){S:Verse α}(ht:∀ i,Tunable (S i))(h:Whole K): Quire.hymn K U S r=0 := by
  rw [hk]; unfold Quire.hymn; exact sum_eq_zero fun b _=> by change grant r (clasp K (0:Rooted E α (b.1+1)) (S (b.2+1)))=_; rw [clasp_zero (ht _).1 h,grant_zero]
lemma hymn_empty {i r:ℕ} (ht : ∀ i j,Tunable (A i j))(hk:Decked A)(hp:Whole K)(U: Spine E α)(he:∀ i,Pens (U i)) : Quire.hymn K U (Refrain K A none i 0) r=0 := by
  unfold Quire.hymn; apply sum_eq_zero; intro i _; rw [show Refrain _ _ _ _ 0 (i.2+1)=0 from not_ne_iff.mp (mt (treble_reel hp ht hk) (fun H=> by obtain ⟨⟨hr,-⟩,-⟩:=H; omega)),clasp_stop (he _) hp,grant_zero]
lemma muted_m (hp:Whole K)(h:∀ i j,Tunable (A i j))(he:∀ i j,Tidy (U i j))(m:ℕ): murmur none K A (fem m U) n=fem m (murmur none K A U n) := by
  induction n using Nat.caseStrongRecOn with
  | zero=>funext k r; rw [murmur,show murmur none K A U 0=U from funext fun i=>funext fun r=>by rw [murmur]]
  | ind i ih=>
    funext k r
    rw [murmur_step]
    rw [ih i le_rfl]; by_cases ht:m≤k
    · rw [footing ht, footing ht,murmur_step]; congr 2; refine Finset.sum_congr rfl fun b hb=> ?_; rw [ih b.1 (by have he:=mem_antidiagonal.mp hb; omega)]
      let f := murmur none K A U b.1; let x:= Refrain K A none b.2
      let g (a:ℕ×ℕ):=Quire.hymn K (fem m f a.1) (x a.2) r
      let S:=(wheel k).filter fun j=>m≤ j.1
      rw [← sum_subset (s₁:=S) (f:=g) (filter_subset ..)]
      · apply sum_nbij' (fun i=> (i.1-m,i.2)) (fun i=> (i.1+m,i.2))
        · intro i hi; simp only [S,wheel,mem_filter,mem_antidiagonal] at hi ⊢; omega
        · intro i hi; simp only [S,wheel,mem_filter,mem_antidiagonal] at hi ⊢; omega
        · intro i hi; rcases i with ⟨i,j⟩; change (_,_)=(i,j); congr 1; simp only [S,wheel,mem_filter] at hi; exact Nat.sub_add_cancel hi.2
        · rintro ⟨a,b⟩ _; change (_,_)=(a,b); congr 1; exact Nat.add_sub_cancel ..
        intro i hi; unfold g; rw [show fem m f i.1=f (i.1-m) from funext fun a=>footing (mem_filter.mp hi).2]
      intro j hj hn; apply hymn_blank _ (fun k=> refrains_tune hp h ..) hp
      funext x; unfold fem; rw [if_neg]; rfl
      intro he; exact hn (mem_filter.mpr ⟨hj,he⟩)
    unfold fem; rw [if_neg ht,if_neg ht,jib_blank _ hp,Finset.sum_eq_zero,zero_add,smul_zero]
    intro b hb; apply sum_eq_zero; intro a ha; change Quire.hymn K (murmur none K A (fem m U) b.1 a.1) _ r=0; rw [ih b.1 (by have he:=mem_antidiagonal.mp hb; omega)]; apply hymn_blank _ (fun _=>refrains_tune hp h ..) hp
    funext i; unfold fem; rw [if_neg]; rfl
    have ht:=mem_antidiagonal.mp ha; omega
lemma washed_a (hp:Whole K)(h:∀ i j,Tunable (A i j))(he:∀ i j,Tidy (U i j))(v:ℝ)(τ:ℕ): washed τ none K A (v • U)= v • washed τ none K A U := by
  funext i j; simp only [washed,fun n e r=>munified (n:=n) (u:=e) (r:=r) hp h he v,Pi.smul_apply,Finset.smul_sum]
lemma washed_plus (hp:Whole K)(h:∀ i j,Tunable (A i j))(he:∀ i j,Tidy (U i j))(hv: ∀ i j,Tidy (V i j))(τ:ℕ):washed τ none K A (U+V)=washed τ none K A U+washed τ none K A V:= by funext i j; simp only [washed,fun n u=>muted (n:=n) (u:=u) hp h he hv,Pi.add_apply,sum_add_distrib]
lemma washed_epoch (hp:Whole K)(h:∀ i j,Tunable (A i j))(he:∀ i j,Tidy (U i j))(hg:Decked A) (hU:Fits u U) (hv:u≤v) : washed v none K A U=washed u none K A U:= by
  funext i j; symm; refine sum_subset (range_mono (Nat.add_le_add_right (show windows u i≤ windows v i from Nat.add_le_add_right hv _) 1)) ?_; intro x hx he'; refine not_ne_iff.mp (mt (murmur_degree hp h hg he hU) ?_); unfold windows at he'; have hh := mt (@Finset.mem_range (u+3*i+1) x|>.2) he'; omega
lemma wash_fem (hp:Whole K)(h:∀ i j,Tunable (A i j))(he:∀ i j,Tidy (U i j))(hg: Decked A)(hU:Fits u U)(hv : u ≤ v+m) : washed v none K A (fem m U)= fem m (washed u none K A U) := by
  funext j r; unfold washed; simp_rw [fun n=> muted_m (n:=n) hp h he m]; by_cases ht:m≤j
  · simp_rw [footing ht]; symm; apply sum_subset (range_mono (by unfold windows; omega)); intro x hx hg'; apply not_ne_iff.mp; apply mt (murmur_degree hp h hg he hU); intro hF; simp only [Finset.mem_range] at hg'; unfold windows at *; omega
  unfold fem; simp [ht]
end YM.RG08.Needle
