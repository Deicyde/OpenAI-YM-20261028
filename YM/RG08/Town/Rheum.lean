import YM.RG08.Town.Arras
/-!
# No-rank and stable families. Anchor at arbitrary `p`.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.RG08.Town
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect Work.F08 Push.AbsoluteSums Matrix
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Staffer PertExtension.Series.Radial PertExtension.Series.Tested
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {I α β:Type}{m c f L:Side}{i n r k e D h τ j:ℕ}{x:Cover}{η A R σ:ℝ}{G:Gauge}
section grade
variable {P:StripU G L}{U:Tale G}{v v':Rooted ℝ (Loc G 1) r}
def pebble (U:Tale G) : Tale G:= fun i j=>if j=0 then U i j else 0
def polishS (U:Tale G):= U-pebble U
lemma polS_pos (h:r≠0) (U:Tale G) : polishS U i r=U i r:= by simp only [polishS,pebble,h,↓reduceIte,sub_zero, Pi.sub_apply]
lemma polish_dark (U:Tale G)(i:ℕ): polishS U i 0=0:= by unfold polishS pebble; simp
lemma pews {X:Rooted ℝ (Loc G 1) 0}(h:Tidy X) (b:Site c)(z:Site f) (x:Link G c)(y:Link G f): rootSong X c b x=rootSong X f z y:= by
   unfold rootSong Tensor.diagonal; rw [stitch_apply h.pens.of_norm,stitch_apply h.pens.of_norm]; simp only [rosary,Finset.univ_eq_empty,Fintype.card_fin,Nat.cast_zero] -- fix
   simp
lemma pebble_stone (h: Stone τ U): Stone τ (pebble U) := by
  constructor
  · intro i j; unfold pebble; split; exact h.tidy i j; exact Tidy.zero ..
  · intro i j he; by_cases he':j=0; subst j; exact Nat.zero_le _
    exact (he (if_neg he')).elim
  intro m i a b ha hb hx k; dsimp only
  refine Fit.supply (Eventually.of_forall (fun t=>?_)) _
  unfold arco year large; refine sum_congr rfl ?_; intro j hj; simp only [Finset.sum_apply,Finset.sum_apply]; refine congr_arg (t^j*·) (sum_congr rfl ?_); intro u hu; unfold pebble
  split; next h'=> subst u; exact pews (h.tidy j 0) ..
  rw [root_zero]; rfl
lemma jewel_stone (h:Stone τ U): Stone τ (polishS U):= h.less (pebble_stone h)
lemma lone_lap {G:Type}[Fintype G]{E: Canticle G}{Q:Row G G} {V:Screed ℝ G} (he: Whole Q)(hD:∀ i j,Tunable (E i j))(h:∀ i r, r≠0→ V i r=0) (i r): murmur none Q E V (n+1) i r=0:= by
   suffices ∀ a k i r,k=a+1→ murmur none Q E V k i r=0 from this n (n+1) i r rfl
   intro a; induction a using Nat.strong_induction_on with
   | h n IH=>
     intro k i r hk; subst k
     have hp (j m:ℕ)(hh:j ≤ n)(l)(hl:0<l): murmur none Q E V j m l=0:= by
       cases j with
       | zero=>rw [murmur,h _ _ (by omega)]
       | succ j=>exact IH j (by omega) (j+1) m _ rfl
     rw [murmur_step,hp n i le_rfl (r+2) (by omega),jib_blank none he, sum_eq_zero,zero_add,smul_zero]
     intro p hp'; apply Finset.sum_eq_zero; intro j hj; apply Finset.sum_eq_zero; intro m hm
     rw [hp p.1 j.1 (by have he:=mem_antidiagonal.mp hp'; omega) (m.1+1) (by omega),clasp_zero ((refrains_tune he hD ..).1) he,grant_zero]
lemma slateS (Q:Cross L (Loc G 1) (Loc G 1))(p:Site L)(v:Rooted ℝ (Loc G 1) 0)(h:Tidy v)(he:Whole Q): spring (lotS p v) (scan Q)=v:= by
   apply Tidy.uniquely (spring_tidy (lot_tidy h.pens p).pens (scan_whole he)) h; intro n; funext x; let g:Ratio n (n*L):= ⟨L,rfl⟩
   rw [spring_tell _ (lot_tidy h.pens p).pens (scan_whole he),lot_period g p h.pens]; exact pews h ..
lemma vault_party (p:Site L)(h:Stone τ U)(hp: Fair P): inscribed τ P p (pebble U)= Tall.hill P.scale (pebble U):= by
   let K:= veiled P.cv; let V:= reachP p (pebble U)
   have h0 i j (hj: j≠0): V i j=0:= by unfold V reachP pebble; rw [if_neg hj,lot_zero]
   have he: washed τ none K P.song V=V := by
     ext1 i; ext1 j; unfold washed; rw [Finset.sum_eq_single 0,murmur]; intro p ht he; obtain ⟨v,rfl⟩:=Nat.exists_eq_succ_of_ne_zero he; exact lone_lap (veiled_whole hp.cm) hp.tune h0 i j
     simp
   unfold inscribed; congr 1; funext i j
   change spring (washed τ none K P.song V i j) _=_; rw [he]; by_cases hh:j=0
   · subst j; exact slateS _ _ _ ((pebble_stone h).tidy i 0) hp.ct
   rw [h0 i j hh,spring_zero (scan_whole hp.ct),pebble,if_neg hh]
lemma puzzleS (p:Site L)(h:Stone τ U)(he:Fair P)(hk:r≠0) : inscribed τ P p (polishS U) i r=inscribed τ P p U i r:= by
   let X:=polishS U; let Q:=pebble U; have hM:=inscription_add p (jewel_stone h) (pebble_stone h) he; rw [vault_party p h he,show polishS U+pebble U=U from sub_add_cancel ..] at hM
   rw [hM,Pi.add_apply,Pi.add_apply,show Tall.hill P.scale Q i r=0 from ?_,add_zero]; unfold Q Tall.hill pebble; simp [hk]

def holdP (p:Site L)(Q:Cross L (Loc G 1) (Loc G 1))(v:Rooted ℝ (Loc G 1) r):= spring (lotS p v) (scan Q)
def rampP (τ:ℕ)(P:StripU G L)(p: Site L)(U:Tale G)(i j:ℕ):= originS τ P p U none i j-holdP p P.tree (U i j)
def coreT (τ:ℕ)(P:StripU G L)(p: Site L)(U:Tale G)(i j:ℕ):= inscribed τ P p U i j-holdP p P.tree (U i j)
lemma holdsP (p:Site L)(h: Stone τ U)(hp:Fair P) (i j:ℕ):
    rampP τ P p U i j=spring (∑ k∈range (windows τ i),murmur none (veiled P.cv) P.song (reachP p U) (k+1) i j) (scan P.tree):= by
  let X k:= murmur none (veiled P.cv) P.song (reachP p U) (k+1) i j
  have hX k:Tidy (X k):= quiet_tidily (veiled_whole hp.cm) hp.tune (reaches h.cap h.tidy _|>.2) ..
  unfold rampP originS holdP washed; rw [Finset.sum_range_succ', spring_plus (Tidy.additions (fun k (_:k ∈ range (windows τ i))=> hX k)|>.pens) (show Pens (murmur none _ _ _ 0 i j) by rw [murmur]; exact (reaches h.cap h.tidy p).2 i j|>.pens) (scan_whole hp.ct),murmur,reachP]; rw [add_sub_cancel_right]
lemma core_read (p:Site L)(U:Tale G)(hp: Fair P)(i j:ℕ): coreT τ P p U i j=rampP τ P p U i j + ∑ a ∈ range i, glaze P.scale j a (i-a) • originS τ P p U none a j := by
    rw [coreT,inscribed,ridge _ hp.once]; unfold rampP; abel
section
variable {Q K:Cross L (Loc G 1) (Loc G 1)}{Z:Cross L (Candles G) (Loc G 1)}
lemma belly_hold (p:Site L)(hp: Tidy v)(hQ: Whole Q): holdP p Q v=belly p Q v:= by
   apply Tidy.uniquely (spring_tidy (lot_tidy hp.pens p).pens (scan_whole hQ)) (belly_mood p hQ hp); intro m; funext x; let g:Ratio m (m*L):=⟨L,rfl⟩; rw [ spring_tell _ (lot_tidy hp.pens p).pens (scan_whole hQ),lot_period g p hp.pens, scan_at g,lodge_f]; exact Eq.symm (belly_period g p hQ hp _ (fun _=>x))
lemma drapery (p:Site L)(h:Stone τ U)(hX: Speaks Q Z K)(hp: Whole Q)(hK:Whole K)(ht:Whole Z)(s:ℕ):
    holdP p K (Loom.strand τ s U r)=holdP p Q (Loom.strand τ s U r) - ∑ i∈range r,belly p Z (crock (Loom.strand τ s U i) r):= by
  let R:=Loom.strand τ s U
  have he i:Tidy (R i):= strand_tid h.tidy
  let W i:= belly p Z (crock (R i) r); have hW i: Tidy (W i):= belly_mood p ht (crock_tid (he i).pens _)
  have hm:Tidy (∑ i∈range r,W i):= Tidy.additions (fun i _=>hW i)
  rw [belly_hold p (he r) hK,belly_hold p (he r) hp]; apply Tidy.uniquely (belly_mood p hK (he r)) ((belly_mood p hp (he r)).less hm); intro m; funext v
  let g: Ratio m (m*L):=⟨L,rfl⟩; let b:Site m:=0; let x:= installed g Z*ᵥv
  obtain ⟨hV,hA⟩:= hX m v
  have hu (i:ℕ) : rootSong (W i) m b v=rootSong (crock (R i) r) (m*L) (g.assemble (b,p)) x:= belly_period g p ht (crock_tid (he i).pens _) _ (fun _=>v)
  have hP : rootSong (belly p Q (R r)-∑ i∈range r,W i) m b=rootSong (belly p Q (R r)) m b-∑ i∈range r,rootSong (W i) m b := by rw [← root_sum b (range r) W (fun i _=>(hW i).pens)]; unfold rootSong; rw [st_sub (belly_mood p hp (he r)|>.pens.of_norm) hm.pens.of_norm]; rfl
  
  change _=rootSong (belly p Q (R r) - ∑ i∈range r,W i) m b v; rw [hP,Pi.sub_apply,Finset.sum_apply]; simp_rw [hu]
  let F P:= rootSong (belly p P (R r)) m b v
  have hh (P) (hP:Whole P) : F P=rootSong (R r) (m*L) (g.assemble (b,p)) (installed g P*ᵥv):= belly_period g p hP (he r) b (fun _=>v)
  change F K= F Q - _; rw [hh K hK,hh Q hp,←hV,←hA]; exact lights h.tidy (h.shore _ _) x s r
end
lemma stone_off (p:Site L)(h:Tidy v)(k:Tidy v')(Q:Cross L (Loc G 1) (Loc G 1))(hz: Whole Q) : holdP p Q (v-v')=holdP p Q v-holdP p Q v' := by unfold holdP lotS shiftP; rw [Pens.tub_sub _ h.pens k.pens,spring_sub (h.pens.pours _) (k.pens.pours _) skylight_ok]; exact spring_sub (lot_tidy h.pens p|>.pens) (lot_tidy k.pens p|>.pens) (scan_whole hz) -- let unfold okay?
end grade
end YM.RG08.Town
