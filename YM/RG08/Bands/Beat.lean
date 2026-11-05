import YM.RG08.Bands.Lake
/-!
# Field operator on heat polymers, z-period fee envelopes
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.RG08.Bands
open Filter Analysis Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect Work.F08 Push.AbsoluteSums Matrix
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Staffer PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Town
open scoped BigOperators Topology Real ContDiff Matrix.Norms.Frobenius
variable {I α:Type}{m c:Side}{e t τ n r k:ℕ}
variable [Fintype α][DecidableEq α] {p:Option Side}{u:Spine ℝ α}{S:Canticle α}{K:Row α α}{U:HeatS α} -- fix
section strokes
def peels (p:Option Side)(K:Row α α)(U:HeatS α) : HeatS α:= fun i k v=> jib p K (U i k (v+2))
def choirR (p:Option Side)(K:Row α α)(S:Canticle α)(U:HeatS α) : HeatS α:= fun i k=> ∑ b∈wheel i,∑ a∈wheel k, Quire.hymn K (U b.1 a.1) (Refrain K S p b.2 a.2)
def pumpP (p:Option Side)(K:Row α α)(S:Canticle α)(U:HeatS α): HeatS α := peels p K U+choirR p K S U
def ticks (U:HeatS α) : HeatS α := fun i j=> (↑(i+1:ℕ):ℝ) • U (i+1) j
lemma reeling_peels (h:Reels τ U)(hp:Whole K): Reels τ (peels p K U) := fun i=> swung fun j=> ⟨fun k=>jib_tidy ((h i).tide j _|>.pens) hp p,fun r hr=>by unfold peels; rw [(h i|>.thin j).budget (r+2) (by omega),jib_blank _ hp]⟩
lemma ret_seconds (hp:Whole K)(hg:Gets S) (h:Loomed n u) : Loomed (n+t) (Quire.hymn K u (Refrain K S p r t)):= by
    refine ⟨hymn_tidy hp (fun i=> (h.tide i).pens) (fun i=> (refrains_tune hp (fun i j=> (hg.2 i j).1) p r t i).1),fun i hi=>?_⟩
    refine sum_eq_zero (s:=wheel i) ?_; intro j hj; have hx:= mem_antidiagonal.mp hj
    by_cases hz:n < j.1+1; · rw [h.budget _ hz,clasp_zero ((refrains_tune hp (fun i j=>hg.2 i j|>.1) p ..).1) hp,grant_zero]
    have ht : t+2<j.2+1:= by omega
    rw [show Refrain K S p r t (j.2+1)=0 from (not_ne_iff.mp (mt (treble_reel hp (fun i j=> hg.2 i j|>.1) hg.1) (fun ⟨⟨hx,k,hk⟩,h⟩=> by omega))),clasp_stop (h.tide _|>.pens) hp,grant_zero]
lemma reeling_choir (hp:Whole K)(hg:Gets S)(h:Reels τ U) : Reels τ (choirR p K S U):= by
    refine fun i=> swung (fun k=> Loomed.sum (fun b hb=> Loomed.sum (fun a ha=>?_)))
    refine Loomed.rise (ret_seconds hp hg (p:=p) ((h b.1).thin a.1)) ?_; have H:=mem_antidiagonal.mp ha; omega
lemma reels_tick (h:Reels τ U): Reels τ (ticks U):= fun i=> swung fun j=> Loomed.sc ((h (i+1)).thin j) _
private lemma low_zero (o:Site c)(A:Rooted ℝ α 0): lap (K.acts c) (rootSong A c o)=0:= by funext x; unfold lap rootSong; simp_rw [Dhush]; simp [Analysis.D]
private lemma low_one (o:Site c)(A:Rooted ℝ α 1): lap (K.acts c) (rootSong A c o)=0:= by
  have hx: Tensor.Sym (stitch A c o):=fun v s=> by rw [show v ∘ s=v from funext fun _=> congr_arg v (Subsingleton.elim ..)]
  funext x; unfold lap rootSong; simp_rw [Dfade _ _ (n:=0) hx]; norm_num [Dhush]
private lemma spare (p:Site c)(hp:Whole K) (h:Loomed (n+2) u) : lap (K.acts c) (large p (n+2) u)=large p n (fun i=>jib (some c) K (u (i+2))) := by
    unfold large; rw [lap_sum (h:=fun i _=> root_smooth p (u i)),sum_range_succ',sum_range_succ',low_zero, low_one,add_zero,add_zero]; apply sum_congr rfl; intro i _; exact root_lap (h.tide _) hp c p
lemma peelsD (h:Reels τ U)(hp:Whole K)(z:Site c): glee τ z (peels (some c) K U)=landP (K.acts c) (glee τ z U):= by
    ext1 i; ext1 j; exact (congr_arg (lap (K.acts c)) (larger_s (k:=τ+j+2) ((h i).thin j) (by omega) z)|>.trans (spare z hp (((h i).thin j).rise (Nat.le_add_right (τ+j) 2)))).symm
private lemma zeroR (p:Site c)(f:Psalm (Co c α))(V:Shale α 0): arch (K.acts c) f (stanza V c)=0 := by funext x; unfold arch stanza; simp_rw [Dhush]; simp
lemma reeling_read (p:Site c)(hp:Whole K)(hg:Gets S) (h:Loomed n u): large p (n+t) (Quire.hymn K u (Refrain K S (some c) r t))=arch (K.acts c) (large p n u) (Beats K S c r t):= by
    let W:=Refrain K S (some c) r t; have he k:= refrains_tune hp (fun i j=> (hg.2 i j).1) (some c) r t k
    have hz k (hh:t+2 < k): W k=0:= not_ne_iff.mp (mt (treble_reel hp (fun i j=> hg.2 i j|>.1) hg.1) (fun ⟨⟨he,k,hk⟩,ht⟩=> by omega))
    let X:= K.acts c
    change large p (n+t) (Quire.hymn K u W)=arch X _ (grand (t+2) W c); rw [larger_s h (k:=n+1) (by omega),larger_s (ret_seconds (r:=r) (t:=t) hp hg h) (k:=n+(t+1)) (by omega)] -- let W mismatch
    unfold large grand; rw [arch_first (h:=fun k _=>root_smooth p (u k))]; simp_rw [arch_second (h:=fun (i:ℕ) (_:i∈range (t+2+1))=> stanza_smooth (W i) c)]
    rw [sum_range_succ' (f:=fun i=> ∑ j∈range (t+2+1), arch X (rootSong (u i) c p) (stanza (W j) c)), sum_eq_zero (fun k (_:k∈range (t+2+1))=> hush₁ (K:=K) ..), add_zero]
    simp_rw [sum_range_succ' (n:=t+2),show ∀ i,arch X (rootSong (u (i+1)) c p) (stanza (W 0) c)=0 from fun _=> zeroR (K:=K) p _ _,add_zero]
    rw [triangle_sum (fun i j=> arch X (rootSong (u (i+1)) c p) (stanza (W (j+1)) c)) n (t+1)]; swap
    · intro i j hh; constructor; · by_contra he; exact hh (by rw [h.budget _ (by omega),root_zero,arch_stop])
      by_contra he; exact hh (by rw [hz _ (by omega),stanza_zero,arch_wait])
    refine sum_congr rfl ?_; intro i hi; unfold Quire.hymn; rw [root_sum p (wheel i) (h:=fun v _=> (Tidied i (clasp_tidy ((h.tide _).pens) (show Summable (W (v.2+1)) from (he _).1) hp)).pens)]
    refine sum_congr rfl ?_; intro v hv; rw [← mem_antidiagonal.mp hv,grant_self]; exact (clasp_love (h.tide _) (he _) hp ..).symm
lemma choirD (h:Reels τ U)(hp:Whole K)(hg:Gets S)(z: Site c): glee τ z (choirR (some c) K S U)=rim (K.acts c) (glee τ z U) (Beats K S c):= by
    funext i j
    let W (u v:ℕ×ℕ):= Quire.hymn K (U u.1 v.1) (Refrain K S (some c) u.2 v.2)
    have hx (a b:ℕ×ℕ)(hp':b∈wheel j): Loomed (τ+j) (W a b):= (ret_seconds hp hg (p:=some c) ((h a.1).thin b.1)).rise (by have ht:=mem_antidiagonal.mp hp'; omega)
    unfold rim glee; refine Eq.trans (spool_group (k:=τ+j) (F:=fun i=> ∑ b∈wheel j,W i b) (wheel i) (fun b _=> Loomed.sum (hx b)) z) (sum_congr rfl fun b hb=>?_)
    rw [spool_group _ (hx b)]; refine sum_congr rfl ?_; intro a ha; rw [show τ+j = τ+a.1+a.2 by have he:= mem_antidiagonal.mp ha; omega]; exact reeling_read z hp hg ((h b.1).thin a.1)
lemma tallyD (h:Reels τ U)(p:Site c): glee τ p (ticks U)=countT (glee τ p U):= by
    ext1 i; ext1 j; rw [countT,← Nat.cast_smul_eq_nsmul ℝ]; simp only [glee,ticks,large,Pi.smul_apply,Finset.smul_sum]; exact sum_congr rfl fun b _=> root_scale p ((h _).tide ..|>.pens) _
end strokes
end YM.RG08.Bands
