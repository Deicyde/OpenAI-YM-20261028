import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mallow.Reseve
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Marlin.Pylon
/-! # Higher payment at second chamber.
Adapt VerifiedReset soft table using within-step footprint growth. -/
set_option autoImplicit false
noncomputable section
namespace YM.Merge.Spicy
open Function Filter Set Lattice Wilson RG Pressure Precision
open Push Push.AbsoluteSums
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Averaging Geo Residual Extra.Iteration
open WilsonStartup Progress.DirectedRecipe PhysicalNext.Repeat Mallow Marlin
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}{S:Clip}{T:Collection.Source G n}{X:Listing G n}{p q:BudgetPoint}{P:PathData G}
variable {a e w σ C Λ β α γ:ℝ} {k:ℕ→ℝ}
-- payable form
def summer (p:BudgetPoint)(S:Clip)(σ C:ℝ):= Footprint.payment 1 p.B 0 (σ/8) 1 (Fintype.card Signed * lowerSize S C) (p.supportExponent+2) lowCount
def fruit (G:Gauge) (p:BudgetPoint)(H:ℝ):= Footprint.payment 1 (4*p.B+2) 0 (1/2) (resetLoss G p) H (p.supportExponent+2) 81
def opens (G:Gauge)(p:BudgetPoint)(S:Clip)(σ C α H:ℝ):= fruit G p H + hitNeed p G α H*summer p S σ C
lemma spice (h:P.Bounds S σ C Λ)(hp : Width p S σ) : Ac.Hit (fun i:Seat n × Low=> i.1.spread (i.2.home P p 0)) p.B
    (fun i=> Real.exp ((i.2.length P:ℝ)/S.relaxation)*|i.2.mark P S|) (p.supportExponent+2) (summer p S σ C):=by
  let g (i : Low) := Real.exp ((i.length P:ℝ)/S.relaxation)* |i.mark P S|
  have hg i : 0 ≤ g i := mul_nonneg (Real.exp_pos _).le (abs_nonneg _)
  have hK := channel_anchored (n:=n) _ g hg (kept_debit G p P hp h)
  have he:= p.exponent_pos; have hB:0<(p.B:ℝ) := by exact_mod_cast p.B_pos
  have hz:= hp.1; have ht := hp.2.2; have hx:(p.supportExponent+2)/(p.B:ℝ) ≤ σ/2:= by
     have hv:(p.supportExponent+2)/(p.B:ℝ)≤ (p.supportExponent+1)/(p.B:ℝ) + (p.supportExponent+1)/(p.B:ℝ) := by rw [← add_div]; apply div_le_div_of_nonneg_right _ hB.le; linarith
     linarith only [hv,ht]
  unfold summer
  refine Footprint.assigned (id : Site n → Site n) 1 (fun Y : Support n => by simp) (fun i : Seat n × Low => i.1.2) (fun i => g i.2) (fun i => hg i.2) (fun i => i.2.length P) (fun i : Seat n × Low => i.1.spread (Low.home P i.2 p (0:Site n))) hK p.B 0 p.B (C:=1) (v:=lowCount) (a:=p.supportExponent+2) (ε:=σ/8) (v':=(p.B:ℝ)⁻¹) ?_ ?_
    zero_le_one (show Footprint.reserve (3*σ/4) (p.supportExponent+2) (p.B:ℝ)⁻¹ (σ/8) from ⟨by linarith,by linarith,by rw [← div_eq_mul_inv]; linarith⟩) (fun i => g i.2) (fun i => hg i.2) (fun _ => by simp)
  · rintro i y hy; obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hy
    simpa only [affine, separation_translate, Signed.act_zero,zero_add,id_eq] using! (spin_separation i.1.1 i.1.2 j (0:Site n)).trans_le (low_dist p P _ hj)
  intro i; rw [Seat.visit_count]
  apply le_of_mul_le_mul_left (a:=(p.B:ℝ)) ?_ hB; rw [mul_add,← mul_assoc,mul_inv_cancel₀ hB.ne',one_mul]; exact_mod_cast low_geometry p P i.2 (0:Site n)

lemma bigger (h : ∀ i,0≤ k i) (hk: Quotes.early p X.reg k a)(he:2≤p.B) :
    Ac.Hit (expand ∘ X.reg) p.B (fun i => resetLoss G p*k i) (p.supportExponent+2) (fruit G p a):= by
  have hz:=loss_pos G p; have hp:=p.exponent_pos
  exact Footprint.assigned id 1 (fun Y : Support n => by simp) _ _ h _ _ hk _ 0 _ (fun i x hx => enlarged_dist p _ x hx)
    (fun i => by rw [one_mul,add_comm]; exact_mod_cast enlarge p (X.reg i) he) hz.le ⟨by linarith,by norm_num,by unfold preExponent; linarith⟩
    _ (fun i => mul_nonneg hz.le (h i)) (by simp)
lemma june (g:G.Simple)(hn:20<n.val)(h : Collection.Local X p T a w)(he:P.Bounds S σ C Λ)(hp:Width p S σ)(hf:Decent S p):
    Vapor (Collection.shelves X P p) (Collection.branch X P S p T α) (raiser p) (opens G p S σ C α a):=by
  have hv:= Mallow.cools (α:=α) g h he hp hf hn
  refine ⟨hv.texts,hv.visits,hv.travels,hv.tails,?_⟩
  obtain ⟨k,ht,hx⟩:=h.cheap; let Δ:= Averaging.delta (X.read T)
  have hy : Ac.Hit (soft X P p) p.B (quoteL P p S α Δ k) (p.supportExponent+2) (opens G p S σ C α a):= by
     have hz:= spice (n:=n) he hp; have hh:= bigger (fun i=>(ht i).1) hx hf.radius
     have hL:0 ≤ summer p S σ C:= Cost.nonneg (hz 0)
     intro x; exact Cost.enlarge (Cost.sum (f:=fun i:LKey n=> if x∈(soft X P p i) then quoteL P p S α Δ k i * Real.exp ((p.supportExponent+2)*coverNumber p.B ((soft X P p) i)) else 0) (hh x) (Quotes.hit_scale (hitPower_pos p G α Δ) hz x)) (add_le_add_right (mul_le_mul_of_nonneg_right (hit_allow (delta_bound g h.projects)) hL) _)
  have hQ (i:ℕ) := Local.quote_soft (R:=P) (c:=S) g α Δ ht h.smooth (numbering _ i)
  refine ⟨_,⟨fun i=> (norm_nonneg _).trans (hQ i 1),?_⟩, hQ⟩
  rw [show (raiser p).supportExponent+1=p.supportExponent+2 from (by unfold raiser; dsimp only; ring)]; exact fun i=> Cost.equiv (numbering _) (hy i)
end YM.Merge.Spicy
