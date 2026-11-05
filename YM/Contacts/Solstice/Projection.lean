import YM.Contacts.Solstice.Strict
/-!
# Initial loans also reading root residuals and output fields

Not restricted to the inspecting scale of a root. Running contact subtraction at descendant
nodes has independent its own horizon; the initial output reading can operate through any
integer weight. This is the same detection working also on its punctured open function and all
finite horizons after forming clusters. Pay root clearance on original test support; inner
projections sending centroid allow the larger halo radii required there **even when the root
inspector has less clearance**. If requiring increasing horizons including interpolation, pay
initial clearance through them at each stage. This is verified later in schedules; here keep the
horizons fixed. Works on any character, also unselected.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Solstice
open Function Filter Set Metric MeasureTheory Submodule Table Spec Normal MultipleContact MultipleContact.Script OPE Layers Ordered Harvest Route
open scoped Topology Classical BigOperators ContDiff InnerProductSpace MeasureTheory
variable {E W I J : Type}[NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E]
variable {G: Gauge}{C : Family G}{F : Extraction.Order}{S: Table C.book}{Z : Final C F S}
variable {k : ℕ}{g : Normal.Group k}{Q : Pieces g}{P:E→ₗᵢ[ℝ] Points k} {d : J→ℕ} {r : Route P Q I W}
local notation "GN" => Normal.Group k
local notation "E!" => Expression Z.sector.derivatives
local notation "Q'" => Board (Normal.Group k) (Letter Z.sector.derivatives)
variable (M : Devices Z.sector.derivatives)(i : Q.parts)(n : ℕ)

def sees (r : Route P Q I W) := ∀ w,r.stage w ⊆ strip (normalOn P i.val) (M.clearance n)
lemma step_sees (h : r.ceiling ≤ M.clearance n) : sees M i n r:= fun w x hx=> (show ‖(normalOn P i.val).starProjection x‖≤ _ from r.clear w i.val i.property hx).trans h
-- one edit in a strict reader. acts on entire cluster polynomial in that tag.
def felt (M : Devices Z.sector.derivatives)(x : E4) (a : Bool) (n : ℕ) : E!→ₗ[ℂ] E! := if a then M.insertRow x n else M.residue x n
variable (a : Bool)
def turnOne (F : E!→ₗ[ℂ] E!) : Q'→ₗ[ℂ] Q' := appropriating {i.val} ((tag i.val).toLinearMap.comp F)
lemma turns (F : E!→ₗ[ℂ] E!)(x : GN→ E!) : turnOne i F (∏ j∈Q.parts,tag j (x j))= ∏ j∈Q.parts,tag j (Function.update x i.val (F (x i.val)) j):= by
   rw [welded_update, ← Finset.prod_erase_mul Q.parts (fun i=> tag i (x i)) i.property]; apply weld_untouched
   · let v := Q.parts.erase i.val; let z(j:GN):= tag j (x j); let D:Set GN:={i.val}; have ht(j : GN)(hj:j∈v) : fork D (z j)=outlet (z j):= fork_out D j (fun he=> (Finset.mem_erase.mp hj).1 (Set.mem_singleton_iff.mp he)) (x j); rw [map_prod,map_prod]; exact Finset.prod_congr rfl ht
   exact fork_in {i.val} i.val (Set.mem_singleton _) _
lemma seesReceipt {x : ℕ→E}{w:ℕ→ W}{φ:Filter ℕ}(hp : sees M i n r)(hx : ∀ k,x k∈ r.stage (w k)) : Fits M φ n (fun j=> r.oculus (w j) i.val (x j)) (r.avenue i.val w x):=by rintro p ⟨p,rfl⟩; exact Eventually.of_forall fun k=> (r.oculus_extent (w k) (x k) i p).trans (hp _ (hx k))
def evidence (a : Bool)(n : ℕ) := if a then n else n+1

def jackpot (r : Route P Q I W) (i : Q.parts)(n : ℕ)(w : W) := r.R i.val w ^ (n:ℝ)
lemma jackpot_cost (r : Route P Q I W) : Bill r.diameter univ (jackpot r i n):= Bill.powers (n:ℝ) (Bill.radius _ (fun _ _=> (r.valid ..).1))

lemma owned {x y : E} {j : Q.parts} (h : x-y∈ normalOn P j.val)(w) : r.oculus w i.val x=r.oculus w i.val y:= by
   by_cases he:j=i; subst j; exact r.oculus_still _ _ _ _ h (Or.inl rfl)
   exact r.oculus_still _ _ _ _ h (Or.inr (Q.disjoint j.property i.property (Subtype.val_injective.ne he)))
namespace Backdrop
variable (θ : Backdrop S r d) [Fintype J] (α : W→ Viewers Z)
def controlled : Reader E W ℂ k Z.sector.derivatives := fun w x=> (θ.polls M α w x).comp (turnOne i (felt M (r.oculus w i.val x) a n))
lemma control_read (w x t) : θ.controlled M i n a α w x (∏ j∈Q.parts,tag j (t j))= θ.finalReading M α w x (∏ j∈Q.parts, Function.update t i.val (felt M (r.oculus w i.val x) a n (t i.val)) j):= by unfold controlled; rw [LinearMap.comp_apply,turns, θ.voted]
lemma control_post : Fixed (θ.controlled M i n a α) Q P:= ⟨fun w j _ _ h=> by unfold controlled; rw [owned i h, (θ.anchored M α).keeps w j h]⟩

variable {M i θ n α} {δ : ℝ} (hδ : θ.Eligible δ)(hs : sees M i n r)
include hδ hs
lemma control_plot : Lit r (θ.controlled M i n a α):= by
   constructor; exact θ.control_post M i n a α; intro V _ v U w hU hV h t ht
   let L(x:V):=r.oculus w i.val (v x); let F(j:GN)(x:V):= Function.update (fun j=>t j x) i.val (felt M (L x) a n (t i.val x)) j; refine ContinuousOn.congr (θ.final_plot (M:=M) (α:=α) hδ w hV h (f:=F) ?_) (fun x hx=> θ.control_read M i n a α _ _ (fun i=> t i x)) -- `f:=...` implicit; dot?
   intro k hk; by_cases he:k=i.val; swap; · simpa only [F,Function.update_of_ne he] using ht k hk
   subst k; simp_rw [F,Function.update_self]
   have hc:=ht i.val i.property; have hl:ContinuousOn L U:= (r.oculus_continuous w i.val).comp_continuousOn hV; let V:= r.palette w i.val ∘ v; have hm(t: _)(hh : t ∈ U): V t⊆ closedBall (L t) (M.clearance n):= (r.palette_fits i w (v t)).trans (closedBall_subset_closedBall (hs _ (h hh)))
   cases a; exact M.residue_visible n hc hl hm (fun _ _=> r.centre ..); exact Displays.field (fun t _=> r.centre ..) hl (M.row_continuous n hc hl fun t ht=> (hm _ ht).trans (closedBall_subset_closedBall (M.clearance_le n)))
lemma at_front (A : Services C F S) : Loan Z M r (jackpot r i (evidence a n)) (θ.controlled M i n a α):= by
   refine ⟨control_plot a hδ hs,jackpot_cost ..,?_⟩; intro φ _ T w x c hp hc hx b e he; obtain ⟨v,h0,h⟩:= hp.entries (r.register i.val)
   have hR:= he i.val i.property v ⟨h0,h⟩; have hv : c= -v*(evidence a n:ℕ):= RateEqual hc ((h.rpow ((evidence a n:ℕ):ℝ)).swap (mul_comm ..)) -- shadow hv repair
   let L(k):= r.oculus (w k) i.val (x k); let f(k):= felt M (L k) a n (e i.val k); let E:= Function.update e i.val f; let B:= Function.update b i.val (b i.val+c)
   have hX(i'):∀h:i'∈Q.parts, Funds Z M φ T (r.avenue i' w x) 0 (B i') (E i'):= by
      intro h'; by_cases hh:i'=i.val; swap; · simp only [E,B, Function.update_of_ne hh]; exact layer_coarsen A M ⟨i',h'⟩ w x hx hp (he i' h')
      subst i'; have he':=habitat0 i hx hp.height h; simp only [B,E,Function.update_self]; let M':=seesReceipt M i n hs hx (φ:=φ)
      cases a with
      | false=>
        have hh:=hR.drop hp.height A he' (r.along_paths i w x) M' h0.1 h0.2 le_rfl; -- simplify
        apply Funds.mono hh ?_ (by rfl); rw [hv]; dsimp [evidence]; push_cast; linarith only
      | true=>
        refine Fine.funds (Fine.field hp.height (r.along_paths i w x) (p:=fun t=> M.row (L t) n (e i.val t)) ?_) zero_le_one; apply (hR.outputs hp.height A he' (r.along_paths i w x) h0.1 h0.2 M').mono; rw [hv]; unfold evidence; simp; linarith only -- binder?
   have hh:=θ.final_counts hδ hx hp.height A E B hX (α:=α); have hm : (Q.parts.sum B)=c+Q.parts.sum b:= by rw [← Finset.sum_erase_add _ _ i.property,← Finset.sum_erase_add Q.parts b i.property,(show (Q.parts.erase i.val).sum B=(Q.parts.erase i.val).sum b from Finset.sum_congr rfl fun j hj=> Function.update_of_ne (Finset.mem_erase.mp hj).1 ..),Function.update_self]; ring;
   apply RateLE.congr (hm ▸ hh) (Eventually.of_forall fun j=> Eq.symm (?_)); rw [θ.control_read]; refine congrArg (θ.finalReading M α (w j) (x j)) (Finset.prod_congr rfl fun k hk=>?_); by_cases he:k=i.val; subst k; simp [f,L,E]
   simp [Function.update_of_ne he,E]
end Backdrop
end YM.Contacts.Solstice
