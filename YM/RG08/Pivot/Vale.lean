import YM.RG08.Pivot.Tells

set_option autoImplicit false
noncomputable section
namespace YM.RG08.Pivot
open Function Filter Lattice Wilson RG Exterior Precision Next.Free
open Laurent Bloch Matrix Work.F08 Tree FreeResolvent Stationary
open UVExt.Paths Drift Scores Loom Shade Quire Tall Vale Analysis Reflect Finset
open scoped Topology BigOperators
variable {G:Gauge} {R:ℝ}{P:Patch} {D n j t d r :ℕ} {K: KernelChoices} {H:Cross P.L (TypeFace 1) (TypeFace 1)}
variable {V:Train P.J} {W:Train j} {X:Repeated P.L} {U : BoardU D R G} {F: Air G} (q:ChartRatio G)(i:G.ColorIndex)
private lemma embark {c f:Side} (g: Ratio c f) (x:Site c) (H:Cross g.count (Loc G 1) (Loc G 1)) {Y:EnvelopeU D R G r} (hv:1/2≤R) (hp:Odd g.count.val) (hz:Tidy Y)(h:Whole H) (t:ℕ)(φ:Exam D):
    recitalP (aboard t H Y) x φ=∑ p : Site g.count, increase g.count t • twistV (installed g H) (recitalP Y (g.assemble (x,p)) (haloPull p φ)) := by
  have ha p:= halo_tid (w:=p) hp hv hz h
  unfold aboard
  have hL : (g.count.val:ℝ)^t*(Fintype.card (Site g.count):ℝ)⁻¹=increase g.count t:= (div_eq_mul_inv ..).symm
  rw [hL]; let b:=increase g.count t; let V:=∑ i:Site g.count, Vale.halo i Y H; let u:= plug φ R
  unfold recitalP
  rw [show u∘(b•V)=b • (u∘V) from funext fun i=> map_smul u b (V i), st_scale b (((Tidy.additions (s:=univ) (fun i _=> ha i)).pens.shaped u).of_norm)]
  unfold u; rw [graft, st_sums _ (fun i _=> ((ha i).pens.shaped (plug φ R)).of_norm), Finset.smul_sum]; unfold b
  refine sum_congr rfl fun i _=>congr_arg ((increase g.count t) • ·) ?_
  let v:= plug (haloPull i φ) R
  apply Tensor.ext_diag _ _ ((Tidy.map (plug φ R) (ha i)).sym x) (turns_sym _ ((Tidy.map v hz).sym (g.assemble (x,i))))
  funext u; exact halo_pay g x i H Y hz φ h hp hv u

private lemma hurled_aboard {L:Side} (Q:Cross L (Loc G 1) (Loc G 1)) {W : ℕ→ EnvelopeU D R G r} {V:EnvelopeU D R G r}
    (ht:1/2≤R) (hl:Odd L.val)(hv:Whole Q)(hW:∀ i,Tidy (W i))(h:Tidy V)(he: Hurled W V)(n:ℕ):
    Hurled (fun i=> aboard n Q (W i)) (aboard n Q V) := by
  -- use Halo budget same Ω 0

  refine ⟨(sailing (m:=n) hl ht h hv).pens,?_⟩
  simp_rw [← Needle.aboard_sub hl ht hv (hW _) h]
  obtain ⟨a,ha,hP⟩:=he.moment.thus
  choose B hB hb using fun p:Site L=> run_node hv p
  let v:=(L.val:ℝ)^n*(Fintype.card (Site L):ℝ)⁻¹
  let A:=∑ p,B p^r
  refine ⟨fun i=>‖v‖*(A*a i),by simpa using! (ha.const_mul A).const_mul ‖v‖,fun i=>?_⟩
  unfold aboard; apply Ink.scale; unfold A; rw [sum_mul]; apply Ink.additions _ (fun i=> (ling_pos _ _).le)
  intro p _
  rw [show (ling (α:=Loc G 1) (r:=r) 0)=brocade (fun _=>1) from funext fun i=>by simp [ling,brocade]]
  apply halo_ear hl ht (w:=fun _=>1) (fun _=>le_rfl) (fun _=>le_rfl) p (hB p) _
  · convert hP i using 1; ext i; simp [ling,brocade]
  intro i; simp only [mul_one]; exact hb p i

-- series equality with the FULL G from finer curvature jets
lemma olog_masts (hv:1/2≤R)(hp:P.Branches K G)(hn:4 ≤ j)(hg : Gets F)(hs: Marvel n U)(hU:∀ i,Polished (U 0 i)) (ht:Whole H)
    (hz:∀ c f (h:f.val=c.val*P.L.val), Inputs (linked P K c f h) (installed (linked P K c f h).ratio H) ((pink K.penalty V).acts f) ((pink K.penalty W).acts c)) :
    let D:=plaza G K.penalty W none; let M:=plaza G K.penalty V none
    let Y:= filament P K V q i X F none U n d
    frisk D (Y 0) n r=aboard d (painted G H) (frisk M (U 0) n r) := by
  let Y (p):= filament P K V q i X F p U n d
  let S p:= plaza G K.penalty V p; let T p:= plaza G K.penalty W p
  let U₀ p:= frisk (S p) (U 0) n r
  let U' p:= frisk (T p) (Y p 0) n r
  intro D M y
  have hm : Whole (painted G H):= by
    obtain ⟨w,K,hs,H⟩:=ht; exact ⟨_,_,hs,paint_budget H⟩
  have he:= period_flights (h:=d) (σ:=q) (w:=V) (i:=i) (W:=X) hp hv hs.hem hs.cap hg
  obtain ⟨_,_,A⟩:= portion G K.penalty_pos P.order_cut; obtain ⟨_,_,B⟩:=portion G K.penalty_pos hn
  have hx p (C : ℝ) (h:Plaque (S p) C): Tidy (U₀ p) := Tidy.additions fun i _=> song_front h (hs.hem 0) i r
  have hy p (C : ℝ) (h:Plaque (T p) C): Tidy (U' p) := Tidy.additions fun i _=> song_front h (fun k=> ((he.1 p).2 0 k)) i r
  apply Needle.envelope_ext
  intro φ; let s:= plug φ R
  apply Tidy.uniquely (Tidy.map s (hy none _ ((B W).1))) (Tidy.map s (show Tidy (aboard d (painted G H) (U₀ none)) from Tidy.scale (Tidy.additions fun i _=> halo_tid P.odd_side hv (hx none _ (A V).1) hm) _))
  intro c; funext v
  let m i:=even_side i*c; let f i:=m i*P.L; let l (i:ℕ): Ratio (even_side i) (m i):=⟨c,rfl⟩
  have hV : Tendsto (fun i=>(m i).val) atTop atTop:= tendsto_atTop_mono (fun i=> Nat.le_mul_of_pos_right (even_side i).val c.property) evenings_grow
  have hF : Tendsto (fun i=> (f i).val) atTop atTop:= tendsto_atTop_mono (fun i=>Nat.le_mul_of_pos_right (m i).val P.L.property) hV
  have hΨ i: Even (m i).val:= (evenings i).mul_right _; have hh i: Even (f i).val:= (hΨ i).mul_right _
  have hX:=fare_walk ((B W).1) (dormer G K.penalty_pos hn W m hV hΨ) (fun i=>(B W).2 _ (hΨ i)) (he.2 m hV 0) n r
  have hK: Hurled (fun i=> U₀ (some (f i))) (U₀ none):= fare_walk ((A V).1) (dormer G K.penalty_pos P.order_cut V f hF hh) (fun i=>(A V).2 _ (hh i)) (fun i=> Hurled.fixed (hs.hem 0 i).pens) n r
  have hY:= hurled_aboard _ hv P.odd_side hm (fun i=>hx _ _ ((A V).2 _ (hh i))) (hx _ _ (A V).1) hK d
  let E:= ContinuousMultilinearMap.apply ℝ _ ℝ (fun _:Fin r=> v)
  refine tendsto_nhds_unique_of_eventuallyEq (E.continuous.continuousAt.tendsto.comp (pens_tuft (hX.maps s) c 0))
    (E.continuous.continuousAt.tendsto.comp (pens_tuft (hY.maps s) c 0)) (Eventually.of_forall (fun j=>?_))
  let o : Site (m j):= (l j).assemble (0,0); have hhP : (l j).residue o=(0:Site c):=(l j).assemble_res _
  let p:= (linked P K (m j) (f j) rfl); let H':= installed p.ratio H
  have hp':(l j).residue o=(0:Site c):=hhP
  have hh:=embark p.ratio o (painted G H) hv P.odd_side (hx _ _ ((A V).2 _ (hh j))) hm d φ
  let w: Fin r→ Link G c:=fun _=> v; let F'' := (aboard d (painted G H) (U₀ (some (f j))))
  calc _=recitalP (U' (some (m j))) o φ (tiltCopy (l j) G∘ w):= (by rw [rec_copy (l j) (hy _ _ ((B W).2 _ (hΨ j))).pens,hp']; rfl)
       _=recitalP F'' o φ (tiltCopy (l j) G ∘ w):= by
         apply DFunLike.congr_fun; unfold F''; rw [show recitalP (aboard d (painted G H) (U₀ (some (f j)))) o φ=_ from hh,paint_port]
         exact shoresup q i (c:=m j) (f:=f j) rfl hp hv hn (hΨ j) (hz _ _ rfl) hg hs hU o φ
       _=_:= by rw [rec_copy (l j) (hY.ever j),hp']; rfl
end YM.RG08.Pivot
