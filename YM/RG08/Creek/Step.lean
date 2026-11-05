import YM.RG08.Creek.Array
/-! # Bulk markers exponential update, including identity with normalized scalar receipts through all orders. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Creek
open Function Finset Filter RG Lattice Laurent Quire Vale Bloch Next.Free Stationary Shade Wax Town Bands Plot Needle Tall Scores
open scoped Topology ContDiff BigOperators Real Classical Matrix
variable {I α β W: Type} [Fintype I][DecidableEq I][Fintype α][DecidableEq α][Fintype β][DecidableEq β]{G:Gauge}{a:I→ℕ}{v:I→ℝ}{r τ D:ℕ}{R:ℝ}{L:Side}{x: Places I}{b:I→Sight D R}
structure Styled {T:Finset I}(t:ℕ)(U:Screed (Poise T D R) α):Prop where -- T binder
   tidy: ∀ i j,Tidy (U i j)
   cap: Fits t U
abbrev Layouts (I:Type)(G:Gauge)(D:ℕ)(R:ℝ):= Places I→ Mill I (Loc G 1) D R
structure Sense (a:I→ℕ)(F:Layouts I G D R) :Prop where
   style : ∀ x t, Styled (vanes a t) (F x t)
   stone : ∀ x y t, Stone (vanes a t) (access y (F x) t)
   void : ∀ x,F x ∅=0
   only : ∀ t, Only t (fun x=> F x t)

section surgery
variable {T:Finset I}{F:Layouts I G D R}{p:Cover}{i:I}
-- addresses apply adjoint no choice, keep witnesses, widths propagated. At this stage use explicit p and real weights
private def pres (M: Scouts T D R →L[ℝ] Scouts T D R): Poise T D R→ₗ[ℝ] Poise T D R where
   toFun a:= a.comp M
   map_add' a b:= ContinuousLinearMap.ext fun _=>rfl
   map_smul' v a:= ContinuousLinearMap.ext fun _=>rfl
abbrev footT (L:Side)(x: Places I)(p:I→Site L): Places I:= fun i=> stemA L (x i) (p i)
-- within announced geometry
private def M₁ (p:I→Site L)(t:Finset I)(hp:Odd L.val ∧ 1/2≤R)(D:ℕ):= Wax.mottle t D (spinner ∘ p) (fun _=> (L.val:ℝ)⁻¹) (fun i=>nesting (p i) hp.1 hp.2)
def shuffle (p:I→Site L)(t:Finset I)(D:ℕ)(R:ℝ): Poise t D R→L[ℝ] Poise t D R:= if h: Odd L.val∧ 1/2≤R then (pres (M₁ p t h D)).mkContinuous 1 (fun x=> (ContinuousLinearMap.opNorm_comp_le x _).trans (by grw [show ‖M₁ p t h D‖ ≤ 1 from mote ..]; simp)) else 0
lemma shuffle_cost (p:I→Site L)(t:Finset I)(D:ℕ)(R:ℝ): ‖shuffle p t D R‖ ≤ 1:= by unfold shuffle; split; exact LinearMap.mkContinuous_norm_le _ zero_le_one _; exact (show ‖(0:Poise t D R→L[ℝ] Poise t D R)‖≤1 from (norm_zero (E:=Poise t D R→L[ℝ] Poise t D R)).trans_le zero_le_one)
abbrev spar (p:I→Site L)(hp:Odd L.val)(hv:1/2≤R)(x:I→Sight D R):= fun i=> Pages.scroll (spinner (p i)) (L.val:ℝ)⁻¹ D (nesting (p i) hp hv) (x i)
lemma called_s (p:I→Site L)(t:Finset I)(hp:Odd L.val)(hv:1/2≤R) (b:I→Sight D R) (x:Poise t D R):
   shuffle p t D R x (speak t b)=x (speak t (spar p hp hv b)):= by unfold shuffle; rw [dif_pos ⟨hp,hv⟩]; exact congr_arg x (moto t D _ _ _ b)
lemma only_sh (h:Sense a F)(x:Places I)(b:I→ Sight D R)(he:Odd L.val)(hp:1/2≤R)(t:Finset I): scope t (fun p=>access (spar p he hp b) (F (footT L x p)) t):=by
   intro p q H; dsimp only
   unfold access; rw [show F (footT L x p) t=F (footT L x q) t from h.only t _ _ (fun i hi=> by unfold footT; rw [H i hi])] -- unfold access
   have ht : speak t (spar p he hp b)=speak t (spar q he hp b):= spoke_eq D fun i hi=> congr_arg (fun j=>Pages.scroll (spinner j) _ _ (nesting j he hp) (b i)) (H i hi)
   simp_rw [sampleK,ht]
lemma style_sc {U: Screed (Poise T D R) α}(h:Styled τ U)(s:ℝ): Styled τ (s • U):= ⟨fun i j=> (h.tidy i j).scale _, cap_scale h.cap _⟩
lemma style_sum {U:W→ Screed (Poise T D R) α}(s:Finset W)(h:∀ i∈s,Styled τ (U i)): Styled τ (∑ i∈s,U i):= by
   refine ⟨fun i j=>?_,?_⟩
   · rw [Finset.sum_apply,Finset.sum_apply]; exact Tidy.additions fun i hi=>(h i hi).tidy ..
   intro i j he; refine le_of_not_gt fun hp=>he ?_; rw [Finset.sum_apply,Finset.sum_apply]; exact sum_eq_zero fun k hk=> not_ne_iff.mp (mt ((h k hk).cap i j) (by omega))
-- ambient absolute Tales using season before; fine norm exactly readdressed. s input defined explicitly; commutative binders

def shop (p:I→Site L)(W:Layouts I G D R)(x:Places I)(v:I→ℝ)(t:Finset I): Screed (Poise t D R) (Loc G 1):= fun i j=> (∏ r∈t,v r) • (shuffle p t D R ∘ W (footT L x p) t i j)
def signet (L:Side)(W:Layouts I G D R)(x:Places I)(v:I→ℝ): Mill I (Loc G 1) D R:= fun t=> ∑ p:subroll t (Site L),shop (enter t p) W x v t
lemma shop_style (h:Sense a F)(p:I→Site L)(x: Places I)(v:I→ℝ)(t:Finset I): Styled (vanes a t) (shop p F x v t):= by
   have hp:=h.style (footT L x p) t
   refine style_sc ⟨fun i j=> Tidy.map _ (hp.tidy i j),fun i j he=> hp.cap i j fun hx=>he ?_⟩ _ -- annotate style
   ext; simp only [hx,comp_apply,Pi.zero_apply,map_zero]
lemma shop_sh (p:I→Site L)(x:Places I)(b:I→Sight D R)(F:Layouts I G D R)(v:I→ℝ)(t:Finset I)(he:Odd L.val)(hz:1/2≤R) :
    access b (shop p F x v) t=(∏ i∈t,v i) • access (spar p he hz b) (F (footT L x p)) t:= funext fun i=>funext fun j=> by rw [access,shop,samples_vany]; exact congr_arg (fun f: Rooted ℝ (Loc G 1) j=> _ • f) (funext fun i=> called_s p t he hz b _)
lemma sign_style (h: Sense a F)(x:Places I)(t:Finset I): Styled (vanes a t) (signet L F x v t):= style_sum _ fun i _=>shop_style h ..
abbrev preface (W:Layouts I G D R)(x:Places I)(p:I→Site L)(v:I→ℝ)(hp:Odd L.val)(he:1/2≤R)(b:I→Sight D R)(t: Finset I): Tale G := (∏ i∈t,v i) • access (spar p hp he b) (W (footT L x p)) t
lemma sign_s (hp:Odd L.val)(he:1/2≤R): access b (signet L F x v)=convent (Site L) I (fun p=>preface F x p v hp he b):= by
   funext t i j; unfold signet access convent; simp only [Finset.sum_apply]; rw [graft]; exact sum_congr rfl fun p _=> congr_fun (congr_fun (shop_sh (enter t p) x b F v t hp he) i) j
lemma sign_w (h: Sense a F)(hp:Odd L.val)(he:1/2≤R) : ∀ t, Stone (vanes a t) (access b (signet L F x v) t):=by
   intro t; rw [sign_s hp he]; exact Stone.group _ _ fun _ _=>(h.stone ..).weight _
end surgery
section leaves
variable {P:StripU G L}{F:Layouts I G D R}{T:Finset I}
-- Banner wiring. start and end cells use same normalization mesh and absolute COUNT.
abbrev vines (L:Side)(U:Rooted (Poise T D R) (Loc G 1) r) := spring (shiftP (0:Site L) U) (skylight _ (Loc G 1))
def chancel (L:Side)(K:Mill I (Loc G 1) D R): Mill I (Park G L) D R:= fun t i j=>vines (I:=I) (T:=t) L (K t i j)
lemma vines_ok (L:Side){U: Rooted (Poise T D R) (Loc G 1) r}(hp:Pens U): Tidy (vines (T:=T) L U):= spring_tidy (shifted _ hp) skylight_ok
lemma vines_0 (L:Side): vines L (0: Rooted (Poise T D R) (Loc G 1) r)=0:= by
  unfold vines shiftP; exact (congr_arg (spring · _) (show tub (0:Rooted (Poise T D R) (Loc G 1) r) (carpet (0:Site L) (α:= Loc G 1) (r:=r))=0 from funext fun i=>tsum_zero)).trans (spring_zero skylight_ok)
lemma vines_e (b:I→Sight D R)(L:Side){U:Rooted (Poise T D R) (Loc G 1) r}(he:Pens U) : sampleK T b ∘ vines L U = lotS (0:Site L) (sampleK T b ∘ U):=by unfold vines lotS; rw [spring_echo _ (shifted _ he) skylight_ok,shiftP,Pens.echo_pool _ he]; rfl
lemma chStyle {K:Mill I (Loc G 1) D R}(hp:Styled τ (K T)): Styled τ (chancel L K T):= ⟨fun i j=> vines_ok L (hp.tidy i j).pens,fun i j hx=> hp.cap i j fun hz=> hx (by unfold chancel; rw [hz,vines_0])⟩
lemma angel (L:Side)(K:Mill I (Loc G 1) D R)(hK:∀ i, Styled (vanes a i) (K i)) : access b (chancel L K)= reachP (0:Site L) ∘ access b K:= funext fun i=>funext fun j=>funext fun k=> vines_e b _ ((hK i).tidy _ _).pens
lemma ch_z {K:Mill I (Loc G 1) D R}(hz:K ∅=0): chancel L K ∅=0:=by funext i j; unfold chancel; rw [hz]; exact vines_0 _
lemma sign_l (h: Sense a F)(hp:Odd L.val)(he:1/2≤R): signet L F x v ∅=0 := by
   refine sum_eq_zero ?_; intro p _; funext i j y; simp only [shop,h.void,Pi.smul_apply,Pi.zero_apply,Function.comp_apply,map_zero,smul_zero]

def solar (P:StripU G L) (a:I→ℕ)(v:I→ℝ)(F:Layouts I G D R): Places I→ Mill I (Park G L) D R:= fun x=> noon (veiled P.cv) P.song a (chancel L (signet L F x v))
lemma fair_he (h:Fair P): Gets P.song:= ⟨h.lived,fun i j=>⟨h.tune i j,h.bought i j⟩⟩
lemma solar_p (h:Sense a F)(hp: Fair P)(hr:1/2≤R): Styled (vanes a T) (solar P a v F x T):= by
   let S (t : Finset I):= chancel L (signet L F x v) t; have ht (t): Styled (vanes a t) (S t):= chStyle (sign_style h x t); have hh:= fair_he hp; have hv (i:ℕ) : Styled (vanes a T) (orbitV none (veiled P.cv) P.song S T i):= ⟨orbit_t (veiled_whole hp.cm) hh (fun i=>(ht i).tidy) T i, orbit_cap (veiled_whole hp.cm) hh (fun i=>(ht i).tidy) (by linarith) (fun i=>(ht i).cap) T i⟩
   change Styled _ (noon _ _ _ S T); unfold noon; exact ⟨fun i j=> Tidy.additions fun n _=>(hv n).tidy i j,fun i j he=>le_of_not_gt (fun hp=>he (sum_eq_zero fun n _=>not_ne_iff.mp (mt ((hv n).cap i j) (by omega))))⟩
-- mean and reparam.
def mature (p:StripU G L)(F:Mill I (Park G L) D R) : Mill I (Loc G 1) D R:= fun T=> Tall.hill p.scale (fun i j=> spring (F T i j) (scan p.tree))
abbrev creekT (P:StripU G L)(a:I→ℕ)(v:I→ℝ)(F:Layouts I G D R): Layouts I G D R:= fun x=> mature P (solar P a v F x)
lemma crest_style (h:Sense a F)(hp:Fair P)(hr:1/2≤R) : Styled (vanes a T) (creekT P a v F x T):= by
   let S:=solar P a v F x; have hs:Styled (vanes a T) (S T):= solar_p h hp hr
   let g i j:= spring (S T i j) (scan P.tree); have he:= scan_whole hp.ct; have hh: Fits (vanes a T) g:= fun i j hv=> hs.cap _ _ fun hx=>hv (by unfold g; rw [hx,spring_zero he])
   exact ⟨(hill_rank P.scale hh (fun i j=>spring_tidy (hs.tidy _ _|>.pens) he)).2,(hill_rank P.scale hh fun i j=> spring_tidy (hs.tidy _ _|>.pens) he).1⟩
lemma mature_y {U:Mill I (Park G L) D R}(he:Fair P)(hp:∀ t i j,Pens (U t i j)) (x:I→Sight D R): access x (mature P U)= (Tall.hill P.scale ∘ hears (scan P.tree)) ∘ access x U:= by
   funext T i j; rw [access,mature,Tall.summons]; let p:=sampleK T x; have hx : (fun i j=>p ∘ spring (U T i j) (scan P.tree))= hears (scan P.tree) (access x U T):= funext fun i=>funext fun j=>spring_echo _ (hp T i j) (scan_whole he.ct); change Tall.hill P.scale _ _ _=Tall.hill P.scale _ _ _; exact congr_arg (fun f: Screed ℝ (Loc G 1)=>Tall.hill P.scale f i j) hx
lemma solar_z (h: Sense a F)(hp:Fair P)(hr:1/2≤R) : creekT P a v F x ∅=0:=by
    let S:=signet L F x v; let U:=chancel L S; have he t:= sign_style (v:=v) (L:=L) h x t; have hz:U ∅=0:= ch_z (sign_l h hp.odds hr); have hs:=orbit_sleep (A:=U) R (by linarith) (veiled_whole hp.cm) (fair_he hp) (fun i j k=> (chStyle (L:=L) (he i)).tidy _ _) hz
    have hx : solar P a v F x ∅=0:= by funext i j; unfold solar noon; change (∑ k∈ range (windows (vanes a ∅) i+1), Wax.orbitV none (veiled P.cv) P.song U ∅ k i j)=_; exact sum_eq_zero fun k _=> by rw [hs]; rfl
    unfold creekT mature; simp only [hx,Pi.zero_apply,spring_zero (scan_whole hp.ct)]; funext i j; simp [Tall.hill]
lemma banners_y (h:Sense a F)(hp:Fair P)(hr:1/2≤R)(hv:∀ m,(veiled P.cv|>.acts m)ᵀ=(veiled P.cv|>.acts m))(x:Places I)(b:I→Sight D R)(T:Finset I):
   Fabrics G (access b (creekT P a v F x)) T= inscribed (vanes a T) P 0 (Fabrics G (access b (signet L F x v)) T):=by
   unfold creekT; rw [mature_y hp (fun i j k=> (solar_p h hp hr|>.tidy _ _).pens)]; unfold solar; have he t:=sign_style (v:=v) (L:=L) h x t
   rw [noon_s b (veiled_whole hp.cm) (fair_he hp) (fun i j k=> (chStyle (L:=L) (he i)).tidy _ _) (by linarith),angel L _ he]; exact isbn hp hv (o:=0) (sign_w h hp.odds hr) (access_nil _ (sign_l h hp.odds hr)) T
end leaves
end YM.RG08.Creek
