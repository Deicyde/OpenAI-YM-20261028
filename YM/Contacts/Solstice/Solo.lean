import YM.Contacts.Solstice.Projection
/-!
# The full group and graded OPE of its contact

Score formulas often test with joint test masks, so the centroid projection
is being applied inside the (ambient) integral. Here spell out the one-group OPE with that
convention and show in particular how to use directly with any reader of the resulting
fields, retaining the field coordinates after integrating. Statements about OPE residual
against exteriors and the all-weights projected cost are for this same operator.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Solstice
open Function Filter Set Metric MeasureTheory Submodule Table Spec Normal MultipleContact MultipleContact.Script OPE Layers Ordered Harvest Route
open scoped Topology Classical BigOperators ContDiff InnerProductSpace MeasureTheory
variable {E W I J : Type}[NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E]
variable {G: Gauge}{C : Family G}{F : Extraction.Order}{S: Table C.book}{Z : Final C F S}
variable {k : ℕ}{g : Normal.Group k}{P:E→ₗᵢ[ℝ] Points k} {d : J→ℕ}
local notation "GN" => Normal.Group k
local notation "Z'" => Z.sector.derivatives
local notation "Q'" => Board (Normal.Group k) (Letter Z.sector.derivatives)
abbrev root (g : GN) := (⊤:Pieces g)
def clasp (g : GN) (h : g.Nonempty) : (root g).parts:= ⟨g,by rw [one_set _ rfl h]; exact Finset.mem_singleton_self g⟩
variable (r : Route P (root g) I W)
lemma root_sober (δ : ℝ) : Sober r δ:= by
   rcases Finset.eq_empty_or_nonempty g with h|h; swap; · exact sober_single r (q:=clasp g h) (one_set _ rfl h) δ
   intro i _ h'; have hx:= (root g).nonempty_of_mem_parts i.property; have he:= hx.mono ((root g).subset i.property); exact (he.ne_empty h).elim

variable (hg : g.Nonempty)
include hg
private lemma clasp_tag {A : Type} {f: GN→ Grammar A} : ∏ i∈ (root g).parts,tag i (f i) = tag g (f g):= by rw [one_set _ rfl hg,Finset.prod_singleton]
lemma tag_turn (Φ : Expression Z'→ₗ[ℂ] Expression Z')(f): turnOne (clasp g hg) Φ (tag g f) = tag g (Φ f):= by
   let F:= fun _ : GN=>f; have hh:= turns (clasp g hg) Φ F; rw [clasp_tag hg,clasp_tag hg] at hh; change turnOne _ Φ _ = tag g (Function.update F g (Φ f) g) at hh; rw [Function.update_self] at hh; exact hh
/-- polynomial supplied by the contact, before root readout at each point. -/
lemma tag_alone (f : Menu k) (Q : System E (Expression Z') k)(a:ℝ)(x:E)(p:SmoothTests E) : action x p (Q.election P a f (root g))=tag g (action x p (Q.vote P a g (f g))):= by
    change action x p (Ordered.product (root g).parts (fun i=> retag E (tag i) (Q.vote P a i (f i))))= _; rw [one_set _ rfl hg,Ordered.product_one, retags,action_reshape]; rfl

variable (M : Devices Z.sector.derivatives)(n : ℕ)
omit hg
def rootCoeff : Reader E W (S.Field n) k Z.sector.derivatives := fun w x=> (M.row (r.oculus w g x) n).comp eraseTags.toLinearMap
def rootProjection : Reader E W (S.Field n) k Z.sector.derivatives:= fun w x=> (M.project (r.oculus w g x) n).comp eraseTags.toLinearMap
-- exterior residual/correlations (projected/merge reading) through all phases; use Backdrop.*
include hg
lemma coefficient_loan (h : sees M (clasp g hg) n r)(H : Services C F S): Loan Z M r (jackpot r (clasp g hg) n) (rootCoeff r M n):= by
   have he(w:W)(x:E)(f:GN→ Expression Z.sector.derivatives) : rootCoeff r M n w x (∏ i∈ (root g).parts,tag i (f i))= M.row (r.oculus w g x) n (f g):= by rw [clasp_tag hg]; unfold rootCoeff; simp [erase_tags]
   refine ⟨⟨⟨fun w j _ _ hx=>?_⟩,?_⟩, jackpot_cost .., ?_⟩
   · unfold rootCoeff; rw [show r.oculus w g _=r.oculus w g _ from owned (clasp g hg) hx w] -- ambiguity
   · intro V _ v U w hU hv hv' e he'; apply ContinuousOn.congr ?_ (fun x hx=> he _ _ (fun i=> e i x)); let f(v':V):= r.oculus w g (v v'); apply M.row_continuous n (he' g (clasp g hg).property) ((r.oculus_continuous w _).comp_continuousOn hv)
     exact fun x hx=> (r.palette_fits (clasp g hg) w (v x)).trans (closedBall_subset_closedBall (le_trans (h _ (hv' hx)) (M.clearance_le n)))
   intro φ _ T w x c hp hC ht C e hf
   obtain ⟨t,h0,hv⟩:= hp.entries (r.register g); have heH : c=(n:ℝ)*(-t):= RateEqual hC (hv.rpow (n:ℝ))
   have hF:= hf g (clasp g hg).property t ⟨h0,hv⟩; have hA:= hF.outputs hp.height H (habitat0 (clasp g hg) ht hp.height hv) (r.along_paths (clasp g hg) w x) h0.1 h0.2 (seesReceipt M (clasp g hg) n h ht)
   apply RateLE.congr (RateLE.mono hA (?_)) (Eventually.of_forall fun i=> (he (w i) (x i) (fun j=> e j i)).symm); rw [one_set _ rfl hg,Finset.sum_singleton,heH]; linarith only

-- equalities for reading coefficient/projection on ANY loan-eligible registration
variable (θ : Backdrop S r d) (α : W → Viewers Z) [Fintype J]
variable {q : Fin k→ℕ} (T : W→ Cells S q)
local notation "Y" w => r.components M T w -- notation hygiene
variable (w : W)(p : SmoothTests E)(f : Menu k)
/-- one-root contact kernel feeding field expression. -/
def candle (x:E) := action x p ((r.components M T w).vote P (r.length w) g (f g))
lemma ordinary (x:E) : r.windings M (θ.polls M α) T f w p x= θ.finalReading M α w x (candle r M T w p f x):= by
   unfold windings scoreAt; rw [tag_alone hg]; unfold Backdrop.polls; simp [erase_tags,candle]
lemma patron (a : Bool) (x:E) : r.windings M (θ.controlled M (clasp g hg) n a α) T f w p x=θ.finalReading M α w x (felt M (r.oculus w g x) a n (candle r M T w p f x)):= by
   unfold windings scoreAt; rw [tag_alone hg]; change θ.finalReading M α w x (eraseTags (turnOne _ _ ((tag g) _)))= _; rw [tag_turn,erase_tags]; rfl
lemma caption (x : E) : r.windings M (rootCoeff r M n) T f w p x= M.row (r.oculus w g x) n (candle r M T w p f x):= by
   unfold windings scoreAt; rw [tag_alone hg]; change M.row _ _ (eraseTags ((tag g) _))=_; rw [erase_tags]; rfl
lemma rolled (x : E) : r.windings M (rootProjection r M n) T f w p x= M.project (r.oculus w g x) n (candle r M T w p f x) := by
   unfold windings scoreAt; rw [tag_alone hg]; change M.project _ _ (eraseTags ((tag g) _))=_; rw [erase_tags]; rfl
lemma uncork (x : E) : r.windings M (θ.polls M α) T f w p x= (∑ j:Fin (n+1),r.windings M (θ.controlled M (clasp g hg) j.val true α) T f w p x)+r.windings M (θ.controlled M (clasp g hg) n false α) T f w p x := by
   rw [ordinary r hg M θ α T w p f x]; simp_rw [patron]; rw [← map_sum, ← map_add]; congr 1
   change _= (∑ j:Fin (n+1), M.insertRow (r.oculus w g x) j (candle r M T w p f x)) + (candle r M T w p f x-M.replaceAt (r.oculus w g x) n (candle r M T w p f x)) -- parentheses bind sum?
   rw [M.replace_sum]; abel
lemma gradePart (x : E){v : ℕ} (hx:v≤n): M.splitting.part v n (r.windings M (rootProjection r M n) T f w p x)= r.windings M (rootCoeff r M v) T f w p x:= by rw [rolled r hg,caption r hg,M.select_grade _ hx]
lemma part_read_field (x : E) : r.windings M (θ.controlled M (clasp g hg) n true α) T f w p x= θ.finalReading M α w x (insertField M.basis (r.oculus w g x) n (r.windings M (rootCoeff r M n) T f w p x)):= by rw [patron,caption r hg]; rfl

variable [MeasureSpace E][BorelSpace E][(volume:Measure E).IsAddHaarMeasure]
variable [Fintype I]
-- constant x not support-only, operation independent of the whole normal block
omit [Fintype I] [MeasureSpace E] [BorelSpace E] [(volume:Measure E).IsAddHaarMeasure] in
lemma extent_always (hK : normalOn P g= ⊤) :
    (∀ x, r.oculus w g x = r.oculus w g 0) ∧ ∀ x, θ.finalReading M α w x= θ.finalReading M α w 0:=by
   have he (x:E) : x-0∈ normalOn P g:= by rw [hK]; exact Submodule.mem_top
   exact ⟨fun x=> r.oculus_still w g x 0 (he x) (Or.inl rfl),fun x=> θ.final_fixed M α w (clasp g hg) (he x)⟩
omit [Fintype I] [BorelSpace E] [(volume:Measure E).IsAddHaarMeasure] in
lemma steady_reader (u : E4)(h : Integrable (r.windings M (rootCoeff r M n) T f w p))(hs : ∀ x, r.oculus w g x=u)(hh : ∀ x, θ.finalReading M α w x= θ.finalReading M α w 0) :
    (∫ x,r.windings M (θ.controlled M (clasp g hg) n true α) T f w p x)= θ.finalReading M α w 0 (insertField M.basis u n (∫ x,r.windings M (rootCoeff r M n) T f w p x)):= by
   let L:=LinearMap.toContinuousLinearMap ((θ.finalReading M α w 0).comp (insertField M.basis u n))
   simp_rw [part_read_field r hg M n,hs]; -- hh via rw x even 0
   have he:= L.integral_comp_comm h; conv_lhs => arg 2; ext x; rw [hh x]
   exact he

variable {T θ} 
variable {δ : ℝ}(hT : Given T) (hs : sees M (clasp g hg) n r)(Hp : r.Authority M q)(hb : tsupport p.val ⊆ r.stage w)(H : Services C F S)
include hs hT Hp hb H
lemma coeffThrough (v : ℕ)(hv : v≤n) : Integrable (r.windings M (rootCoeff r M v) T f w p) :=
     readable f w p (coefficient_loan r hg M v (fun x _ hh=> le_trans (hs x hh) (M.antitone_clearance hv)) H) hT Hp H hb
lemma project_mem : Integrable (r.windings M (rootProjection r M n) T f w p):= by
    let L(j:Fin (n+1)):=LinearMap.toContinuousLinearMap (Z.sector.derivatives.rise (show j.val ≤ n from Nat.le_of_lt_succ j.isLt)); let F(x:E):=r.windings M (rootProjection r M n) T f w p x; let t (j:Fin (n+1))(x:E):=r.windings M (rootCoeff r M j) T f w p x
    change Integrable F; rw [show F=(fun x=>∑ j:Fin (n+1),L j (t j x)) from ?_]; exact integrable_finsetSum _ fun j _=> (L j).integrable_comp (coeffThrough r hg M n w p f hT hs Hp hb H j.val (Nat.le_of_lt_succ j.isLt))
    funext x; unfold F t; rw [rolled r hg]; simp_rw [caption r hg]; exact (M.project_through ..).symm
lemma weight_projects (v : ℕ)(hv:v≤n) :
    M.splitting.part v n (∫ x,r.windings M (rootProjection r M n) T f w p x) = ∫ x,r.windings M (rootCoeff r M v) T f w p x:= by simp_rw [← gradePart r hg M n T w p f _ hv]; exact ((LinearMap.toContinuousLinearMap (M.splitting.part v n)).integral_comp_comm (project_mem r hg M n w p f hT hs Hp hb H)).symm
variable (hx : θ.Eligible δ)
include hx
lemma product_split : (∫ x,r.windings M (θ.polls M α) T f w p x) =
    (∑ j:Fin (n+1),∫ x,r.windings M (θ.controlled M (clasp g hg) j true α) T f w p x)+∫ x,r.windings M (θ.controlled M (clasp g hg) n false α) T f w p x := by
    have he(j:Fin (n+1)):= readable f w p (Backdrop.at_front true hx (i:=clasp g hg) (α:=α) (n:=j.val) (fun x _ hh'=> (hs x hh').trans (M.antitone_clearance (Nat.le_of_lt_succ j.isLt))) H) hT Hp H hb; simp_rw [uncork r hg M n θ α T w p f]; rw [integral_add (integrable_finsetSum _ (fun j _=>he j)) (readable f w p (Backdrop.at_front false hx hs H) hT Hp H hb),integral_finsetSum _ (fun j _=> he j)]
end YM.Contacts.Solstice
