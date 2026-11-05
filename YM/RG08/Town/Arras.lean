import YM.RG08.Town.Inscript
/-!
# Reading mass of a scalar-normalized insertion from actual preimages of the *formal* columns.
Includes exactly the denominator used on local bulk. Still all independent and theta-free.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.RG08.Town
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect Work.F08 Push.AbsoluteSums Matrix
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run
open scoped BigOperators Topology Real ContDiff Classical
variable {I α β:Type}{m c f L:Side}{n r k e D h τ:ℕ}{x:Cover}{η A R:ℝ}{G:Gauge}
section linear
variable {U A:Tale G}{P:StripU G L}
lemma inscript0 (p:Site L)(he:Fair P): inscribed τ P p (0:Tale G)=0:= by
   have hx : originS τ P p (0:Tale G) none=0:= by
     have hw: washed τ none (veiled P.cv) P.song (0:Screed ℝ (Park G L))=0 := by simpa using! washed_a (U:=0) (veiled_whole he.cm) he.tune (fun i j=> Tidy.zero ℝ (Park G L) j) 0 τ
     ext1 i; ext1 j; unfold originS; rw [show reachP p (0:Tale G)=(0:Screed ℝ (Park G L)) from (funext fun i=>funext fun j=> lot_zero _),hw]; exact spring_zero (scan_whole he.ct)
   unfold inscribed; rw [hx]; simpa only [zero_smul] using hill_weight P.scale (0:Tale G) 0
lemma inscription_add (p:Site L)(hp: Stone τ U)(hv:Stone τ A)(he:Fair P): inscribed τ P p (U+A)=inscribed τ P p U+inscribed τ P p A:= by
   let F U:= washed τ none (veiled P.cv) P.song (reachP p U)
   have hz: F (U+A)= F U+F A:= by
      have hh: reachP p (U+A)= reachP p U+ reachP p A := funext fun i=>funext fun j=>by unfold reachP lotS shiftP; simp only [Pi.add_apply]; rw [Pens.tub_plus _ (hp.tidy i j).pens (hv.tidy i j).pens]; exact spring_plus ((hp.tidy i j).pens.pours _) ((hv.tidy i j).pens.pours _) skylight_ok
      unfold F; rw [hh,washed_plus (veiled_whole he.cm) he.tune (reaches hp.cap hp.tidy p|>.2) (reaches hv.cap hv.tidy p|>.2)]
   have hM (U:Tale G)(h:Stone τ U) i j: Pens (F U i j):= (washed_duty (veiled_whole he.cm) he.tune he.lived (reaches h.cap h.tidy p|>.2) (reaches h.cap h.tidy p|>.1)).2 i j|>.pens
   unfold inscribed; rw [← hill_add]; refine congr_arg (Tall.hill P.scale) (funext fun i=>funext fun j=>?_)
   change spring (F (U+A) i j) _= _; rw [hz, Pi.add_apply,Pi.add_apply]; exact spring_plus (hM U hp i j) (hM A hv i j) (scan_whole he.ct)
lemma inscription_sc (p:Site L)(g:ℝ)(h:Stone τ U)(he:Fair P): inscribed τ P p (g•U)=g • inscribed τ P p U:= by
   let F U:= washed τ none (veiled P.cv) P.song (reachP p U)
   have hx:= reaches h.cap h.tidy p
   have hb:F (g • U)=g • F U:= by unfold F; rw [show reachP p (g • U)= g • reachP p U from ?_,washed_a (veiled_whole he.cm) he.tune hx.2]; funext i j; unfold reachP lotS shiftP; simp only [Pi.smul_apply]; rw [tub_scale (h.tidy i j).pens,spring_a ((h.tidy i j).pens.pours _) _ skylight_ok]
   unfold inscribed; rw [← hill_weight]; refine congr_arg _ (funext fun i=>funext fun j=>?_); change spring (F (g•U) i j) _=_; rw [hb,Pi.smul_apply,Pi.smul_apply]; exact spring_a ((washed_duty (veiled_whole he.cm) he.tune he.lived hx.2 hx.1).2 i j|>.pens) g (scan_whole he.ct)
lemma inscript_list (s:Finset I)(p:Site L)(A:I→Tale G)(h:∀ i∈s,Stone τ (A i))(he:Fair P): inscribed τ P p (∑ i∈s,A i)=∑ i∈s,inscribed τ P p (A i):= by
   induction s using Finset.induction_on with
   | empty=> simp [inscript0 _ he]
   | insert i s hi ih=> rw [sum_insert hi, sum_insert hi, inscription_add p (h i (mem_insert_self ..)) (Stone.group s _ (fun j hj=>h j (mem_insert_of_mem hj))) he, ih fun j hj=>h j (mem_insert_of_mem hj)]
private lemma washing_s [Fintype α]{V:I→Screed ℝ α}(s:Finset I) (hp:∀ i∈s,∀ j k, Tidy (V i j k)) {K:Row α α}(he:Whole K){B:Canticle α}(hB:∀ i j,Tunable (B i j)) : washed τ none K B (∑ i∈s,V i)=∑ i∈s,washed τ none K B (V i) := by
   induction s using Finset.induction_on with
   | empty=> simp only [sum_empty]; simpa using! washed_a (U:=0) he hB (fun i j=> Tidy.zero ℝ _ j) 0 τ
   | insert j s hx ih=>
      have hk i hi h k:= hp i (mem_insert_of_mem hi) h k; rw [sum_insert hx,sum_insert hx,washed_plus he hB (hp j (mem_insert_self ..)) (fun i j=>?_ ),ih hk]; rw [Finset.sum_apply, Finset.sum_apply]; exact Tidy.additions fun _ h'=>hk _ h' _ _
private lemma spring_s [Fintype α][Fintype β]{V:I→ Shale α r}(s:Finset I)(hp :∀ i∈s,Pens (V i)){K:Row α β}(he:Whole K): spring (∑ i∈s,V i) K=∑ i∈s,spring (V i) K := by
   induction s using Finset.induction_on with
   | empty=> simp [spring_zero he]
   | insert i s hx ih=> rw [sum_insert hx,sum_insert hx,spring_plus (hp i (mem_insert_self ..)) (Pens.additions (fun i h'=>hp i (mem_insert_of_mem h'))) he,ih (fun i h'=>hp i (mem_insert_of_mem h'))]
private lemma hill_s [Fintype α]{V:I→Screed ℝ α}(S:PowerSeries ℝ)(s:Finset I): Tall.hill S (∑ i∈s,V i)=∑ i∈s,Tall.hill S (V i):= by
   induction s using Finset.induction_on with
   | empty=> simp only [sum_empty]; simpa only [zero_smul] using hill_weight S (0:Screed ℝ α) 0
   | insert i s hi ih=> rw [sum_insert hi, sum_insert hi, hill_add, ih]
lemma anthem {V: BoardU D R G}(φ:Exam D)(h:1/2 ≤ R)(he:Fair P)(hv:Marvel τ V)(d:ℕ): ringU φ (push P τ d V)=(↑L.val^d/(Fintype.card (Site L):ℝ)) • ∑ p:Site L, inscribed τ P p (ringU (Pages.roll (spinner p) (L.val:ℝ)⁻¹ φ) V) := by
  let U p:=ringU (Pages.roll (spinner (p:Site L)) (L.val:ℝ)⁻¹ φ) V; let W p:= reachP p (U p)
  have hu p:=Stone.graph hv (Pages.roll (spinner (p:Site L)) (L.val:ℝ)⁻¹ φ)
  let Z:= cream d V L; let F (B:Screed ℝ (Park G L)):= washed τ none (veiled P.cv) P.song B
  let q:= (↑L.val:ℝ)^d/(Fintype.card (Site L):ℝ); have hX:= veiled_whole he.cm
  have hW p:= reaches (p:=p) (hu p).cap (hu p).tidy; have hD:= creamy d L hv.cap (fun i j=>(hv.hem i j).pens) h he.odds
  have hh i j:Tidy ((∑ i:Site L,W i) i j):= by rw [Finset.sum_apply,Finset.sum_apply]; exact Tidy.additions fun p _=> (hW p).2 i j
  have ht:(fun i r=>plug φ R ∘ (cream d V L i r))=q • ∑ p:Site L,W p := by
     funext i r; rw [Pi.smul_apply,Pi.smul_apply,Finset.sum_apply,Finset.sum_apply,Finset.smul_sum]; unfold cream; rw [graft]; refine sum_congr rfl ?_; intro p _; rw [show plug φ R ∘ reelF p d V i r=q • (plug φ R ∘ raysF p (V i r)) from funext fun b=> _root_.map_smul (plug φ R) q (raysF p (V i r) b),marks_read (hv.hem i r).pens h he.odds]; rfl
  let A:=filop P.cv P.tree P.song none τ d V
  have hk : ringU φ A= q • ∑ p:Site L, originS τ P p (U p) none := by
     funext i r; unfold ringU A filop
     rw [spring_echo _ ((washed_duty (s:=none) hX he.tune he.lived hD.2 hD.1).2 i r).pens (scan_whole he.ct), wash_map _ hX he.tune hD.2, ht, washed_a hX he.tune hh, washing_s _ (fun p _=> (hW p).2) hX he.tune]
     have hh p: Pens (F (W p) i r):= ((washed_duty (s:=none) hX he.tune he.lived (hW p|>.2) (hW p|>.1)).2 i r).pens
     let p (K:Shale (Park G L) r):= spring K (scan P.tree); simp only [Pi.smul_apply,Finset.sum_apply]; change p (q • ∑ j:Site L,F (W j) i r)=_; rw [show p _ = q • ∑ j:Site L,p (F (W j) i r) from (spring_a (Pens.additions fun j (_:j∈(univ:Finset (Site L)))=> hh j) q (scan_whole he.ct)).trans (congr_arg (q • ·) (spring_s _ (fun p _=>hh p) (scan_whole he.ct)))]; rfl
  change ringU φ (Tall.hill P.scale A)= _
  rw [show ringU φ (Tall.hill P.scale A)=Tall.hill P.scale (ringU φ A) from funext fun i=>funext fun r=> Tall.summons .., hk, hill_weight, hill_s]; rfl
end linear
open PertExtension.GaussianScore Tree
-- matches idealized *finite-regulator* full conditional, no finite common price asserted
lemma transfer_at (P:Patch)(K:KernelChoices)(w: Train P.J)(hd:f.val=c.val*P.L.val)(O: Matrix (Body 1 f) (Body 1 c) ℝ)(o:Site c) (M:FreeResolvent.FaceRow)(hX:Inputs (linked P K c f hd) O ((pink K.penalty w).acts f) (M.acts c)) (ν:G.ColorIndex)(D': ChartRatio G)(X:Repeated P.L)(A:Air G)(hA:Gets A)(hp:P.Branches K G)(C:PowerSeries ℝ) (U:Tale G)(hU:Stone τ U)(p:Site P.L) :
    let S:= linked P K c f hd
    let B:= awakening ν P D' K.penalty A
    let F:= X.forest S.ratio; let Q:StripU G P.L:=⟨conditionalCov G X K w,coarseMean G X K w,B,C⟩
    ∀ v:Link G c,let W:= lodgeP G S.ratio (riseM S G F O*ᵥ v) v
    let L:= leaned (forest_precision G K w c f hd hp F) (snow G F) (chargeS S F G) W
    let H:= expEra (surge S G A ν D')
    let V i (y:Alley G S.ratio):= large (S.ratio.assemble (o,p)) (τ+i) (U i) (fineL G S.ratio y)
    let Y e:= large o (τ+e) (originS τ Q p U (some c) e)
    ∀ j, L (billow V H j)= ∑ i∈wheel j,Y i.1 v*L (H i.2) := by
  intro S B F Q v W L H V Y j
  have hk:Whole Q.cv:=(conditional_truth G X K w hp).1; have he:Whole Q.tree:= (hk.prod ((probe_recites G P K).1.flipped)).weight _
  have hW:=Gets_awake P D' K ν hA; have hY:= reaches hU.cap hU.tidy p
  let q:=scan Q.tree; let u:=washed τ (some c) (veiled Q.cv) Q.song (reachP p U)
  have ht:= consumes (V:=reachP p U) (forest_precision G K w c f hd hp F) (snow G F) (veiled_whole hk) (chargeS S F G) (people P K X w hp hd) hW hY.2 hY.1 o W j
  have hm: V=(fun i=> large o (τ+i) (reachP p U i)):= funext fun i=>funext fun y=> by unfold V; unfold large; rw [Finset.sum_apply,Finset.sum_apply]; exact sum_congr rfl fun j hj=> Eq.symm (lot_period S.ratio p (hU.tidy i j|>.pens) ..)
  have hz i: large o (τ+i) (u i) W=Y i v:= by
     have hp : q.acts c *ᵥ v=W:= tree_lodge G K hd hp v hX; unfold Y large; rw [Finset.sum_apply,Finset.sum_apply]; refine sum_congr rfl ?_; intro j hj; change _=rootSong (spring (u i j) q) c o v; rw [spring_tell _ ((washed_duty (s:=some c) (veiled_whole hk) (fun i k=>hW.2 i k|>.1) hW.1 hY.2 hY.1).2 i j).pens (scan_whole he),hp]
  rw [hm]; exact Eq.trans ht (sum_congr rfl fun i _=> congr_arg (· * L (H _)) (hz i.1))
lemma transfer_cover {V:Tale G}{P:StripU G L} (p:Site L)(he:Fair P)(h:Stone τ V)(m:ℕ→Side)(hm:Tendsto (fun i=> (m i).val) atTop atTop) : Hurled (fun i=> originS τ P p V (some (m i)) e r) (originS τ P p V none e r):= (WashHurled (U:=fun _=>reachP p V) m (fun i j=> Hurled.fixed (reaches h.cap h.tidy p|>.2 i j|>.pens)) (S:=P.song) ⟨he.lived,fun i j=>⟨he.tune i j,he.bought i j⟩⟩ (veiled_whole he.cm) hm).spring (scan_whole he.ct) -- Gets has summable?
end YM.RG08.Town
