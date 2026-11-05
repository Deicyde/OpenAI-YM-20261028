import YM.RG08.Wallet.Wind

/-! # Fixed-order earnings and fixed-step limit exchanges -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open RG Laurent Lattice Wilson Bloch Next.Free Push.AbsoluteSums Finset Function Filter
open Stationary Analysis UVExt.Paths Matrix
open scoped Topology ContDiff Classical
variable {α : Type} {M : Row α α} {n r e s : ℕ} {m : ℕ→ Side} {w A : ℝ}
variable [Fintype α]
variable {U : ℕ → Shale α r}
private lemma shrinking (n : ℕ) {w : ℝ} (hw : 0<w) : ∃ s, 0 < s ∧ (n:ℝ)*s≤w := by
  by_cases h : n=0; · exact ⟨w,hw,by rw [h,Nat.cast_zero,zero_mul]; exact hw.le⟩
  have hp : 0 < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h
  exact ⟨w/n,div_pos hw hp,by rw [mul_div_cancel₀ w hp.ne']⟩ -- orientation check
omit [Fintype α] in
lemma Vanished.scored (h : Vanished U) : Vanished (fun i=> score (U i)) := by
  obtain ⟨w,δ,hp,hδ,H⟩:=h; obtain ⟨v,hv,h⟩:= shrinking (r+1) hp
  exact ⟨v,δ,hv,hδ,fun i=> score_price (glow_less (H i) h le_rfl) hv.le⟩
lemma Glows.chirpW {F : Shale α (r+2)} (h : Glows F) (e : Whole M) (p) : Glows (chirp M p F) := by
  obtain ⟨w,C,hp,H⟩:=h; obtain ⟨v,hv,h⟩:= shrinking (r+1) hp
  obtain ⟨s,A,hq,Hm⟩:=e; exact ⟨_,_,hv,(chirp_price (Work.F08.strip_mono Hm le_rfl (le_max_left A 0)) hq.le (glow_less H h le_rfl) hv.le p (le_max_right ..)).1⟩
lemma Mending.dropped {V : ℕ→Shale α (r+2)} {F : Shale α (r+2)} (h : Mending V F) (hv : Whole M) (hp : Tendsto (fun i=>(m i).val) atTop atTop) :
    Mending (fun i=> chirp M (some (m i)) (V i)) (chirp M none F) := by
  let X i := chirp M (some (m i)) (V i-F); let Y i := chirp M (some (m i)) F-chirp M none F
  have hu : Vanished X := by
    obtain ⟨s,δ,hs,hδ,H⟩:= h.2; obtain ⟨w,A,hp,hf⟩:= hv
    obtain ⟨z,hz,hZ⟩:= shrinking (r+1) hs
    refine ⟨z,fun i=> ‖batting r‖*(max A 0*δ i),hz,by simpa using (hδ.const_mul (max A 0)).const_mul ‖batting r‖,fun i=>?_⟩
    apply (chirp_price _ hp.le (glow_less (H i) hZ le_rfl) hz.le _ (le_max_right ..)).1
    exact Work.F08.strip_mono hf le_rfl (le_max_left ..)
  have hh : Vanished Y := by
    let f i := score (rumba M (some (m i)) F-rumba M none F)
    have hx : Vanished f := (YM.RG08.dropped h.1 hv hp).scored
    rw [show Y=batting r • f from funext fun i=> by
      have he := h.1.summable; unfold Y chirp f; rw [Pi.smul_apply,score_sub (rumba_summable _ he hv) (rumba_summable _ he hv),smul_sub]]
    exact hx.scale _
  refine ⟨h.1.chirpW hv _,?_⟩
  have he i : chirp M (some (m i)) (V i)-chirp M none F=X i+Y i := by
    rw [show X i=_ from chirp_minus (some (m i)) (h.ever i).summable h.1.summable hv]; unfold Y; abel
  simp only [he]; exact hu.plus hh
omit [Fintype α] in
lemma Mending.bounds {F : Shale α r} (h : Mending U F) : ∃ w C, 0<w ∧ ∀ i,Glow (U i) w C := by
  obtain ⟨⟨w,D,hp,H⟩,z,δ,hv,hδ,Hδ⟩:=h
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hδ.eventually (gt_mem_nhds (show (0:ℝ) < 1 from zero_lt_one)))
  obtain ⟨u,hu⟩ := ((range N).image δ).finite_toSet.bddAbove
  let c:=max 1 u
  have hc i : δ i ≤ c := by by_cases h : N≤ i
                            · exact (hN i h|>.le.trans (le_max_left ..))
                            exact (hu (mem_image_of_mem δ (mem_range.mpr (Nat.lt_of_not_ge h)))).trans (le_max_right ..)
  refine ⟨min w z,c+D,lt_min hp hv,fun i=> ?_⟩
  nth_rw 1 [← sub_add_cancel (U i) F]; apply Charge.add (glow_less (Hδ i) (min_le_right ..) (hc i)) (glow_less H (min_le_left ..) le_rfl) (fun i=> (ling_pos _ _).le)

private lemma wide_side {w v u : ℝ} (h : 0<w) (he : 0<v) (hx : 0<u) (r s) :
    ∃ y, 0 < y ∧ (↑(r+s+1:ℕ):ℝ)*y ≤ w ∧ (↑(r+s+1:ℕ):ℝ)*y ≤ v ∧ (s:ℝ)*((↑(r+s+1:ℕ):ℝ)*y) ≤ u := by
  obtain ⟨U,hU,hu⟩:= shrinking s hx
  obtain ⟨z,hz,hF⟩:= shrinking (r+s+1) (lt_min hU (lt_min h he))
  have hv := hF.trans (min_le_right ..)
  exact ⟨z,hz,hv.trans (min_le_left ..),hv.trans (min_le_right ..),(mul_le_mul_of_nonneg_left (hF.trans (min_le_left ..)) (Nat.cast_nonneg _)).trans hu⟩
lemma Glows.medleyL {F : Shale α (r+1)} {T : Shale α (s+1)} (h : Glows F) (e : Whole M) (hx : Glows T) : Glows (medley M F T) := by
  obtain ⟨w,A,hp,H⟩:=h; obtain ⟨v,B,hq,Hv⟩:=hx; obtain ⟨z,C,hz,HZ⟩:=e; obtain ⟨x,hx,h,hQ,hF⟩:=wide_side hp hq hz r s
  exact ⟨_,_,hx,(medley_price hx.le (glow_less H h le_rfl) (glow_less Hv hQ le_rfl) (Work.F08.strip_mono HZ hF (le_max_left C 0)) (le_max_right ..)).1⟩
lemma Mending.medleyL {V : ℕ→Shale α (r+1)} {F : Shale α (r+1)} {W : ℕ→Shale α (s+1)} {T : Shale α (s+1)}
    (h : Mending V F) (e : Whole M) (hp : Mending W T) : Mending (fun i=>medley M (V i) (W i)) (medley M F T) := by
  refine ⟨h.1.medleyL e hp.1,?_⟩
  let X i := medley M (V i-F) (W i); let Y i := medley M F (W i-T)
  have hu : Vanished X := by
    obtain ⟨w,δ,hz,hδ,H⟩:=h.2; obtain ⟨v,C,hv,Hv⟩:= hp.bounds; obtain ⟨s',A,hs,h⟩:=e
    obtain ⟨p,hp,hh,hq,he⟩:=wide_side hz hv hs r s
    refine ⟨p,fun i=> ‖syl r s‖*(max A 0*(δ i*C)),hp,by simpa using ((hδ.mul_const C).const_mul (max A 0)).const_mul ‖syl r s‖, fun i=>?_⟩
    exact (medley_price hp.le (glow_less (H i) hh le_rfl) (glow_less (Hv i) hq le_rfl) (Work.F08.strip_mono h he (le_max_left A 0)) (le_max_right ..)).1
  have hv : Vanished Y := by
    obtain ⟨w,δ,hz,hδ,H⟩:=hp.2; obtain ⟨v,C,hv,Hv⟩:= h.1; obtain ⟨s',A,hs,h⟩:=e
    obtain ⟨p,hp,hh,hq,he⟩:=wide_side hv hz hs r s
    refine ⟨p,fun i=> ‖syl r s‖*(max A 0*(C*δ i)),hp,by simpa using ((hδ.const_mul C).const_mul (max A 0)).const_mul ‖syl r s‖, fun i=>?_⟩
    exact (medley_price hp.le (glow_less Hv hh le_rfl) (glow_less (H i) hq le_rfl) (Work.F08.strip_mono h he (le_max_left A 0)) (le_max_right ..)).1
  have he i : medley M (V i) (W i)-medley M F T=X i+Y i := by
    unfold X Y; rw [medley_single e (h.ever i).summable h.1.summable (hp.ever i).summable,medley_dual e h.1.summable (hp.ever i).summable hp.1.summable]; abel
  simp only [he]; exact hu.plus hv
omit [Fintype α] in
lemma Mending.prolongL {F : Shale α r} (h : Mending U F) : Mending (fun i=> prolong s (U i)) (prolong s F) := by
  by_cases he : s=r; · subst s; simp only [prolong_self]; exact h
  unfold prolong; simp only [Ne.symm he, ↓reduceDIte]; exact Mending.one 0 Glows.zero
lemma Mending.both {X : ℕ → Canticle α} {F : Canticle α} (h : ∀ i j,Mending (fun v=>X v i j) (F i j)) (e : Whole M) (hp : Tendsto (fun i=>(m i).val) atTop atTop) (n j r):
    Mending (fun i=> Refrain M (X i) (some (m i)) n j r) (Refrain M F none n j r) := by
  induction n using Nat.caseStrongRecOn generalizing j r with
  | zero => simp only [Refrain]; exact h j r
  | ind n ih =>
    let R i := Refrain M (X i) (some (m i))
    let G := Refrain M F none
    have hu (b a:ℕ×ℕ) (he : b∈wheel n) : Mending (fun i=>symphony M (R i b.1 a.1) (R i b.2 a.2) r) (symphony M (G b.1 a.1) (G b.2 a.2) r) := by
      have ht := mem_antidiagonal.mp he; exact Mending.sums _ fun t _=> ((ih b.1 (by omega) _ _).medleyL e (ih b.2 (by omega) _ _)).prolongL
    simp_rw [Refrain_step]
    let V (b a : ℕ×ℕ) i := symphony M (R i b.1 a.1) (R i b.2 a.2) r; let T (b a : ℕ×ℕ) := symphony M (G b.1 a.1) (G b.2 a.2) r
    have hr := Mending.sums (U:=fun b i=> ∑ t∈wheel j,V b t i) (F:=fun b=>∑ a∈wheel j,T b a) (wheel n) (fun b he=> Mending.sums (wheel j) (U:=V b) (fun a _=> hu b a he))
    exact (((ih n le_rfl _ _).dropped e hp).plus (hr.scale (1/2:ℝ))).scale _
theorem peals_late {X : ℕ→Canticle α} {F : Canticle α} (h : ∀ i j,Mending (fun v=>X v i j) (F i j)) (e : Whole M) (hp : Tendsto (fun i=>(m i).val) atTop atTop) (t u r): Mending (fun i=> upswell M (X i) (some (m i)) t u r) (upswell M F none t u r) := Mending.sums (U:=fun j i=> t^j • Refrain M (X i) (some (m i)) j u r) (range _) (fun i _=> (Mending.both h e hp i u r).scale _)
end YM.RG08
