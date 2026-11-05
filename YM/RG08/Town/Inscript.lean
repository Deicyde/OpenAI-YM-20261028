import YM.RG08.Town.Piazza
/-!
# Fully normalized conditional transfer of arbitrary unmasked evaluated source

Cover quantities in unwrapped displacement basis. Translate anchor at will
(exact). Ward, no order-gradient assumptions.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.RG08.Town
open Matrix Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run
open scoped BigOperators Topology Real ContDiff Classical
variable {I:Type}{m c f L:Side}{n r k e D h τ:ℕ}{B Y x:Cover}{η A R:ℝ}{G:Gauge}
section scalar
abbrev Tale (G:Gauge):= Screed ℝ (Loc G 1)
structure Stone (τ:ℕ)(U:Tale G):Prop where
   tidy : ∀ i j, Tidy (U i j)
   cap : Fits τ U
   shore : ∀ m:Side,∀ i:Site m, Shore i τ U
variable {U V: Tale G}{P:BoardU D R G}
def ringU (φ:Exam D)(P:BoardU D R G): Tale G:= fun i j=> plug φ R ∘ P i j
lemma Stone.graph (hp:Marvel τ P) (φ:Exam D): Stone τ (ringU φ P):= ⟨fun i j=> Tidy.map _ (hp.hem i j), Fits.echo hp.cap φ, fun i j=> hp.wardrobe _ _ _⟩
lemma Stone.transport (h:Stone τ U)(x:Cover) : Stone τ (season x U) := by
   refine ⟨fun i j=>tidy_roam (h.tidy i j) x, roam_cap h.cap,?_⟩; intro m p f g hf hg hx i
   have hp : (fun i=> large p (τ+i) (season x U i))=(fun i=>large (p+wrap m x) (τ+i) (U i)) := by funext i; unfold large season; simp_rw [fun i r=> roam_song (r:=r) (h.tidy i r).pens p (x:=x)] -- U
   simp only [hp]; exact h.shore m _ f g hf hg hx i
lemma Stone.zero : Stone τ (0:Tale G):= ⟨fun i j=> Tidy.zero ..,cap_none,fun m i=>vocalized (fun k=> ⟨0,fun j=> Cargo.blank i _ _ _⟩)⟩
lemma Stone.weight (h:Stone τ U)(b:ℝ): Stone τ (b • U):= ⟨fun i j=>(h.tidy i j).scale b,cap_scale h.cap b,fun m i=>vocalized (fun k=>by obtain ⟨V,H⟩:=Shore.vessel (h.shore _ i) h.tidy k; exact ⟨b • V, fun j=>Cargo.weight (H j) h.tidy b⟩)⟩
lemma Stone.more (h:Stone τ U)(hp:Stone τ V): Stone τ (U+V):= ⟨fun i j=>(h.tidy i j).plus (hp.tidy i j),cap_plus h.cap hp.cap, fun m p=> Tall.Shore.pair (h.shore _ p) (hp.shore _ p) h.tidy hp.tidy⟩
lemma Stone.less (h:Stone τ U)(hp:Stone τ V): Stone τ (U-V) := by rw [sub_eq_add_neg,← neg_one_smul ℝ]; exact h.more (hp.weight _)
lemma Stone.group (s:Finset I) (F:I→Tale G)(h:∀ i∈s,Stone τ (F i)): Stone τ (∑ i∈s,F i):= by
  induction s using Finset.induction_on with
  | empty=>rw [sum_empty]; exact Stone.zero
  | insert i s hi ih=> rw [sum_insert hi]; exact (h i (mem_insert_self ..)).more (ih fun i hi=>h i (mem_insert_of_mem hi))
end scalar

section step
variable {U:Tale G} {v:Shale (Loc G 1) r}{p:Site L}{P:StripU G L}{g:Option Side}
def lotS (p:Site L)(v:Rooted ℝ (Loc G 1) r):= spring (shiftP p v) (skylight _ (Loc G 1))
def reachP (p:Site L)(U:Tale G):= fun i r=> lotS p (U i r)
def originS (τ:ℕ)(P:StripU G L)(p:Site L)(U:Tale G) (g:Option Side): Tale G := fun i j=> spring (washed τ g (veiled P.cv) P.song (reachP p U) i j) (scan P.tree)
def inscribed (τ:ℕ)(P:StripU G L)(p:Site L)(U:Tale G):= Tall.hill P.scale (originS τ P p U none)
lemma lot_tidy (h:Pens v)(p:Site L): Tidy (lotS p v):= spring_tidy (shifted p h) skylight_ok
@[simp] lemma lot_zero (p:Site L): lotS p (0:Shale (Loc G 1) r)=0 := by
   unfold lotS shiftP; rw [show tub (0:Shale (Loc G 1) r) _=0 from funext fun i=>tsum_zero]; exact spring_zero skylight_ok
lemma reaches (h:Fits τ U)(he:∀ i j, Tidy (U i j))(p:Site L): Fits τ (reachP p U)∧∀ i j,Tidy (reachP p U i j):=⟨fun i j hx=>h i j fun hp=> hx (by rw [reachP,hp,lot_zero]),fun i j=>lot_tidy (he i j).pens p⟩
lemma origin_kind (he:Fits τ U)(hp:∀ i j,Tidy (U i j))(hx:Fair P): Fits τ (originS τ P p U g) ∧ ∀ i j,Tidy (originS τ P p U g i j):= by
   obtain ⟨h,k⟩:= reaches he hp p; obtain ⟨hz,H⟩:= washed_duty (veiled_whole hx.cm) hx.tune hx.lived k h (s:=g); have hh:= scan_whole hx.ct
   exact ⟨fun i j hP=>hz i j fun he=> hP (by rw [originS,he,spring_zero hh]),fun i j=>spring_tidy (H i j).pens hh⟩
-- root witness at ANY offset from coarse arbitrary origin i
lemma lot_period (g:Ratio c f)(p:Site g.count)(h:Pens v)(W:Alley G g)(x:Site c) : rootSong (lotS p v) c x W=rootSong v f (g.assemble (x,p)) (fineL G g W) := by
   unfold lotS; rw [spring_tell _ (shifted p h) skylight_ok,rootSong,Tensor.diagonal, shifts v g p x _ h]
   change stitch _ f _ _=stitch _ f _ _; congr 1; funext i j; change ((skylight _ (Loc G 1)).acts c *ᵥ W) (splitCo g _ j)=_; rw [skylight_in]; rfl
lemma lot_history (h:Pens v){p q:Site L} (he:Lattice.lift q+x=L.val•Y+Lattice.lift p) : lotS q (roam x v)=roam Y (lotS p v):= by
   apply Tidy.uniquely (lot_tidy (pens_roam h x) q) (tidy_roam (lot_tidy h p) _)
   intro m; let S:Ratio m (m*L):=⟨L,rfl⟩; funext i
   rw [roam_song (lot_tidy h p).pens,lot_period S q (pens_roam h _), lot_period S p h,roam_song h]
   have hx : S.embed 0=0:= map_zero S.root
   refine congr_arg (fun z=>rootSong v (m*L) z (fineL G S i)) ?_; simp only [Ratio.assemble,hx,zero_add,S.embed_wrap]; rw [← map_add,←map_add]; exact congr_arg (wrap (m*L)) he
lemma sailed (h: Stone τ U)(hk:Fair P){p q:Site L}(he: Lattice.lift q + x=L.val•Y+Lattice.lift p): originS τ P q (season x U) g=season Y (originS τ P p U g) := by
   have hz:reachP q (season x U)=season Y (reachP p U):= funext fun i=> funext fun j=> lot_history (h.tidy i j|>.pens) he
   funext i j; unfold originS; rw [hz,← washes (A₀:=reachP p U) τ (fun i j=>lot_tidy (h.tidy i j).pens p) (veiled_whole hk.cm) hk.tune]; exact Eq.symm (spring_space (washed_duty (veiled_whole hk.cm) hk.tune hk.lived (reaches h.cap h.tidy _|>.2) (reaches h.cap h.tidy _|>.1) |>.2 i j|>.pens) (scan_whole hk.ct))
lemma order_moves (h: Stone τ U)(hk:Fair P){p q:Site L}(he:Lattice.lift q+x=L.val•Y+Lattice.lift p): inscribed τ P q (season x U)=season Y (inscribed τ P p U):= by unfold inscribed; rw [sailed h hk he,hill_places]

lemma marks_read {U:EnvelopeU D R G r}(h: Pens U)(hr:1/2≤R)(he:Odd L.val)(φ:Exam D)(p:Site L): plug φ R ∘ raysF p U= lotS p (plug (Pages.roll (spinner p) (L.val:ℝ)⁻¹ φ) R ∘ U) := by
   apply Tidy.uniquely (Tidy.map _ (rays_tidied h hr he p)) (lot_tidy (h.shaped _) p); intro m; let g:Ratio m (m*L):=⟨L,rfl⟩; funext v; rw [rays_present g p v 0 h hr he φ,lot_period g p (h.shaped _) v 0]
private lemma award (d:ℕ)(p:Site L) : ∃ φ:Exam D, ∀ q:Site L, φ.val (spinner q)= if q=p then ((Fintype.card (Site L):ℝ) / (L.val:ℝ)^d) else 0 := by
   have hf: Injective (spinner (L:=L)):= by
     intro i j h; unfold spinner at h; have hk:=smul_right_injective E4 (show ((L.val:ℝ))⁻¹≠0 by positivity) h
     have hx : Lattice.lift i=Lattice.lift j:= by
       ext1 v; exact Int.cast_injective (α:=ℝ) (congr_arg (fun x:E4=> x v) hk)
     exact (wrap_lift i).symm.trans ((congr_arg (wrap L) hx).trans (wrap_lift j))
   let f (i:Site L)(x:E4):= ‖x-spinner i‖^2/(‖spinner p-spinner i‖^2)
   let A:= (univ:Finset (Site L)).erase p; let W:ℝ:=Fintype.card (Site L)/(L.val:ℝ)^d
   refine ⟨⟨fun x=> W*∏ i∈A,f i x, show ContDiff ℝ D _ from contDiff_const.mul (contDiff_prod (fun i _=> ?_))⟩,fun q=>?_⟩ -- maybe `.prod`
   · unfold f; exact (((contDiff_id.sub contDiff_const).norm_sq ℝ).div_const ..)
   change W* _=_; split
   next h=>
    subst q; rw [prod_eq_one ?_,mul_one]
    intro b hb; exact div_self (pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hf.ne (mem_erase.mp hb).1.symm))))
   next h=> rw [Finset.prod_eq_zero (f:=fun i=> f i (spinner q)) (mem_erase.mpr ⟨h,mem_univ _⟩) (by simp [f]),mul_zero]
-- test point only (auxiliary native center), trick to inherit proven full Ward
private def speck (D:ℕ): Sheet D := ⟨⟨0,by omega⟩,fun _=>0⟩
private def latest (v:Screed ℝ (Loc G 1))(p:τ ≤ h)(D:ℕ) : BoardU D 1 G := fun i j b=> v i j b • Scores.utter D 1 ⟨0,fun _=>by simp⟩ (speck D)
private lemma latest_val (U:Tale G)(p:τ≤h)(φ:Exam D): ringU φ (latest U p D)=φ.val 0 • U := by
   funext i j b; unfold ringU latest
   let A:= Scores.utter D 1 ⟨0,fun _=>by simp⟩ (speck D)
   have he: A (sheet D 1 φ)=φ.val 0 := by unfold A; rw [Scores.whisper]; change iteratedFDeriv ℝ 0 φ.val 0 (basis ∘ (fun i:Fin 0=> (0:Axis)))=_; simp
   change _=φ.val 0 * _; simp only [Function.comp_apply,_root_.map_smul]; change U i j b * (A (sheet D 1 φ)) = φ.val 0 * U i j b; rw [he, mul_comm]
private lemma last_m (hU:Stone τ U)(p:τ≤h)(D:ℕ) : Marvel τ (latest U p D) := by
   refine ⟨fun i j hj=>hU.cap i j fun hz=> hj (funext fun b=>by rw [latest,hz,Pi.zero_apply,zero_smul]; rfl),fun i j=> ?_,fun i φ k=>?_⟩
   · let A:= Scores.utter D 1 ⟨0,fun _=>by simp⟩ (speck D); exact Tidy.map ((ContinuousLinearMap.id ℝ ℝ).smulRight A) (hU.tidy i j)
   change Shore k τ (ringU φ (latest U p D)); rw [latest_val]; exact (hU.weight _).shore i k
lemma verbatim (p:Site L)(hd:Odd L.val)(hx:Stone τ U): ∃ (V : BoardU 1 1 G) (φ:Exam 1), Marvel τ V ∧ (fun i j=> plug φ 1 ∘ cream τ V L i j)=reachP p U := by
  let V:= latest U (le_refl τ) 1; have h:=last_m hx (le_refl τ) 1
  obtain ⟨φ,hφ⟩:= award (D:=1) τ p
  let B:=cream τ V L
  refine ⟨V,φ,h,?_⟩; change (fun i j=>plug φ 1 ∘ B i j)=_
  funext i j
  unfold B cream; rw [graft]
  let Y:= (↑(L.val):ℝ)^τ /(Fintype.card (Site L):ℝ)
  let Z (q:Site L):=Pages.roll (spinner q) (L.val:ℝ)⁻¹ φ
  have hz(q:Site L): plug φ 1 ∘ reelF q τ V i j = Y • ((φ.val (spinner q)) • lotS q (U i j)):= by
     rw [show plug φ 1 ∘ reelF q τ V i j= Y• (plug φ 1 ∘ raysF q (V i j)) from funext fun b=> _root_.map_smul (plug φ 1) Y (raysF q (V i j) b), marks_read (h.hem ..|>.pens) (by norm_num) hd]
     rw [show plug (Z q) 1∘ V i j = (Z q).val 0 • U i j from congr_fun (congr_fun (latest_val _ (le_refl τ) (Z q)) i) j]; unfold lotS shiftP; rw [tub_scale (hx.tidy i j|>.pens),spring_a ((hx.tidy i j).pens.pours _) _ skylight_ok]
     congr 2; simp only [Z,Pages.roll, smul_zero,add_zero]
  simp_rw [hz]; rw [sum_eq_single_of_mem p (mem_univ _),hφ p,if_pos rfl,smul_smul, show Y*_=1 from (by unfold Y; field_simp),one_smul]; rfl
  intro b _ hb; rw [hφ b,if_neg hb,zero_smul,smul_zero]
lemma projected_note (p:Site L)(hd:Odd L.val)(hc:Whole P.cv)(hP:Whole P.tree)(ht: Gets P.song) {V:BoardU D R G} (h:Marvel τ V)(HR:1/2≤R) (φ:Exam D)(he:(fun i j=>plug φ R ∘ cream τ V L i j)=reachP p U)(g:Option Side) :
    ringU φ (filop P.cv P.tree P.song g τ τ V)=originS τ P p U g := by
  have hB:= creamy τ L h.cap (fun i j=>(h.hem i j).pens) HR hd
  have hz:= washed_duty (s:=g) (veiled_whole hc) (fun i j=> (ht.2 i j).1) ht.1 hB.2 hB.1
  funext i j; unfold ringU originS filop; rw [spring_echo _ (hz.2 i j).pens (scan_whole hP),wash_map _ (veiled_whole hc) (fun i j=>(ht.2 i j).1) hB.2,he]
lemma inscribe_law (p:Site L)(he: Fair P)(hx:Stone τ U) : Stone τ (inscribed τ P p U) := by
  obtain ⟨V,φ,h,hv⟩:= verbatim p he.odds hx
  have hh:= crest_u (d:=τ) he (by norm_num) h; have hr:=Stone.graph hh φ
  let A:=filop P.cv P.tree P.song none τ τ V
  suffices ringU φ (Tall.hill P.scale A)= inscribed τ P p U by rw [← this]; exact hr
  unfold inscribed; rw [← projected_note p he.odds he.cm he.ct ⟨he.lived,fun i j=>⟨he.tune i j,he.bought i j⟩⟩ h (by norm_num) φ hv none]; funext i j; exact Tall.summons ..
end step
end YM.RG08.Town
