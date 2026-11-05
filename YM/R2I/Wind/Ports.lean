import YM.R2I.Wind.Gauge
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Evaluation
/-! # Reconnect with wind corrections. Keep all shelves and SHIFT by actual wind power.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Averaging.Wind
open Function Filter Set Lattice Wilson RG StressFlux Finset
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace Classical
open Ovens Ovens.Pipes Progress.DirectedRecipe Collection Quotes
open PhysicalNext.Repeat Lease Next.Scheduling RG.Supply Push.AbsoluteSums Extra.Iteration
open Payments Footprint
variable {G:Gauge}{n:Side}{P:BudgetPoint}{X:Listing G n}{V:Collection.Source G n}
abbrev Key (n:Side) := ℕ ⊕ Seat n
def bolts {u:Type} (f:ℕ→u) (g:Seat n → u) := Sum.elim f g ∘ numbering (Key n)
variable (τ:ℝ) (c:Pipes G n) (q:Tap G n) (A:Lease P n)
def port:Pipes G n where
  reg:= bolts c.reg A.placement
  kernel:= c.kernel
  softer:= bolts c.softer A.place
  sites i:= by unfold bolts Function.comp; cases numbering (Key n) i with
                | inl i=> exact c.sites i
                | inr i=> exact ⟨_,(A.placement i).anchor⟩
def load : Tap G n:= ⟨bolts q.regular (Lease.stem τ),q.forced,bolts q.logarithm (A.twig τ)⟩
set_option quotPrecheck false
local notation "c₀" => port c A
local notation "Y" => load τ q A
local notation "N" => numbering (Key n)
-- universe F
local notation "I" => Key n
variable {c} {q} (h:Fittings q c P)
include h
lemma sailsF : Payments.Fittings (load τ q A) (port c A) P:= by
  let V:= Sum.elim c.reg A.placement; let V':= Sum.elim c.softer A.place
  let o₀:= Sum.elim q.regular (Lease.stem τ); let τ':=Sum.elim q.logarithm (A.twig τ)
  have ht (i:I) : P.Regular (V i).support (o₀ i) ∧ (o₀ i) 1=0 ∧ (Nonwrapping (V i).support (V i).site → ∀ a b, IsAffineDirection (V i).site a → IsAffineDirection (V i).site b → logHessian (o₀ i) a b=0):= by
    rcases i with i|u
    · exact ⟨h.regular.smooth i,h.regular.at_flat i,h.regular.vanish i⟩
    exact ⟨A.stems_reg τ _, stems_one .., fun he=> (A.stems_wound u he).elim⟩
  have hv (i:I) : Trio.Tidy P (V' i) (τ' i) ∧ ∀ U : Config G n, τ' i U ≠ 0 → ¬ Healthy P.threshold (V' i) U := by
    rcases i with i|u
    · exact ⟨⟨h.looks i,h.reads i,h.steady i⟩, h.visits i⟩
    exact ⟨A.twigs_tidy .., fun U he hh=>he (A.twigs_zero τ u U hh)⟩ -- parse
  have hK := h.support
  refine ⟨⟨(fun i=>(ht (N i)).1), (fun i=>(ht (N i)).2.1), fun i=>(ht (N i)).2.2⟩, ⟨hK.sym,hK.symtest,hK.meas,hK.meas_test,hK.reads,hK.reads_test,hK.permit⟩,?_,fun i=>(hv (N i)).2,fun i=>(hv (N i)).1.invariant,fun i=>(hv (N i)).1.uses,fun i=>(hv (N i)).1.borel,?_⟩
  · intro s b; obtain ⟨e⟩:= h.moves s b; let p := Equiv.sumCongr e.ep (Seat.move s b); let m := ((N).trans p).trans (N).symm; have hN (i:ℕ): N (m i)=p (N i):= (N).apply_symm_apply _
    have he(i:I): (V (p i)).site = affine s b (V i).site ∧ (V (p i)).support=(V i).support.image (affine s b) ∧ o₀ (p i)= o₀ i ∘ pull s b:= by
       rcases i with i|u
       · exact ⟨e.reg_site i,e.reg_support i,funext (e.valuesE i)⟩
       refine ⟨rfl,u.spread_move s b _,?_⟩; unfold o₀; change Lease.rayH τ ∘ (Seat.move s b u).view=_; rw [Seat.view_move]; rfl
    refine ⟨⟨m,e.kp,fun i=> ?_,fun i=> ?_, e.forced_support, e.forced_inventory,e.forced_tests,fun i U=>?_,e.valuesK⟩⟩
    · change (V (N (m i))).site = _; rw [hN]; exact (he (N i)).1
    · change (V (N (m i))).support = _; rw [hN]; exact (he (N i)).2.1
    change o₀ (N (m i)) U=_; rw [hN]; exact congr_fun (he (N i)).2.2 U
  intro s b; obtain ⟨v,h₁,h₂⟩:= h.carries s b; let p := Equiv.sumCongr v (Seat.move s b); let m := ((N).trans p).trans (N).symm; have hN (i:ℕ): N (m i)=p (N i):= (N).apply_symm_apply _
  have he (i:I): V' (p i)=(V' i).image (affine s b) ∧ τ' (p i)=τ' i∘ pull s b:= by
    rcases i with i|u; · exact ⟨h₁ i,funext (fun U=> h₂ U i)⟩
    refine ⟨u.spread_move s b _,?_⟩; change A.patchK τ ∘ (Seat.move s b u).view=_; rw [Seat.view_move]; rfl
  refine ⟨m,fun i=>?_,fun U i=>?_⟩
  · change V' (N (m i))=_; rw [hN]; exact (he (N i)).1
  change τ' (N (m i)) U=_; rw [hN]; exact congr_fun (he (N i)).2 U
omit h
variable (s a b δ w χ κ:ℝ)
def spendX (m:ℝ)(P:BudgetPoint)(n:Side):= Fintype.card (Seat n)* (Real.exp ((P.supportExponent+1)*( (brake P.B n:ℝ)+81))*m)
def lilac (G:Gauge)(P:BudgetPoint)(t:ℝ):= t * tollG G P
set_option quotPrecheck false
local notation "ε" => (|τ| * P.threshold^2)
local notation "r" => (turnFee P*lilac G P (|τ| * P.threshold^2))
local notation "k" => lilac G P ε
-- ALL actual soft. Pre-Boom Hits with old sizes
lemma readyE {c:Pipes G n}{q:Tap G n}{x:ℝ}(h:(c.pours q).EBound P x):
     ((port c A).pours (load τ q A)).EBound P (x+spendX r P n):= by
   obtain ⟨v,hv,hq⟩:=h; let u : ℝ:= r
   let f':= Sum.elim v (fun _:Seat n=>u); let V:= Sum.elim c.reg A.placement; let o₀:= Sum.elim q.regular (Lease.stem (G:=G) τ)
   have he:0 ≤ u:= by unfold u lilac; have hh := tollG_nonneg (G:=G) (P:=P); have hi:=(turnFee_pos P); positivity
   have ht(i:I): P.supBounds (V i).site (V i).support (o₀ i) (f' i):= by
      rcases i with i|i; · exact hv i
      change P.supBounds _ _ _ u; refine sup_le (A.stems_norm (G:=G) τ i) (?_); unfold u lilac; apply le_of_eq; ring
   refine ⟨f' ∘ N,fun i=> ht (N i),fun o=>?_⟩
   refine Cost.equiv (N) (Cost.sum (f:=fun i:I=> if (V i).site=o then P.mass (V i).support (f' i) else 0) (hq o) ?_)
   let g:= Real.exp ((P.supportExponent+1)*((brake P.B n:ℝ)+81))*u; have hg : 0 ≤ g:= by unfold g; positivity
   apply Cost.mono (Cost.finite (α:=Seat n) g hg)
   · intro i; split; exact mul_nonneg (Real.exp_pos _).le he; exact le_rfl
   intro i; split; swap; · exact hg
   change Real.exp (P.supportExponent*coverNumber P.B (i.spread A.garden))*u ≤g; rw [Seat.visit_count]
   apply mul_le_mul_of_nonneg_right _ he; apply Real.exp_monotone; gcongr; · linarith [P.exponent_pos]
   · linarith
   exact_mod_cast A.size
-- combine soft Hit
lemma paysSoft {c:Pipes G n}{x:ℝ}{k':ℕ→ℝ}(h: Payments.softCost P c k' x) : softCost P (port c A) (bolts k' (fun _ : Seat n=> k)) (x+spendX k P n):= by
   let u' : ℝ:= k; have hp:0≤u':= by unfold u' lilac; exact mul_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _)) tollG_nonneg
   let q' := Sum.elim k' (Function.const (Seat n) u'); let g:= u' * Real.exp ((P.supportExponent+1)*((brake P.B n:ℝ)+81)); have hg:0≤g:= mul_nonneg hp (Real.exp_pos _).le
   refine ⟨fun i=>?_,fun x=>?_⟩
   · change 0≤q' (N i); cases N i with
     | inl i=> exact h.1 i
     | inr i=> exact hp
   unfold spendX; rw [mul_comm (Real.exp _)]; refine Cost.equiv (N) (Cost.sum (f:=fun i:I=> if x∈Sum.elim c.softer A.place i then q' i*Real.exp ((P.supportExponent+1)*coverNumber P.B (Sum.elim c.softer A.place i)) else 0) (h.2 x) ?_)
   apply Cost.mono (Cost.finite (α:=Seat n) g hg)
   · intro i; split; exact mul_nonneg hp (Real.exp_pos _).le; exact le_rfl
   intro i; split; swap; · exact hg
   change u'*Real.exp ((P.supportExponent+1)*coverNumber P.B (i.spread A.garden)) ≤ g; rw [Seat.visit_count]; apply mul_le_mul_of_nonneg_left _ hp; apply Real.exp_monotone; apply mul_le_mul_of_nonneg_left _ (add_nonneg P.exponent_pos.le zero_le_one); exact_mod_cast A.size
lemma pays_hit {u v : ℕ→ℝ}(h: rooted q u v) (A:Lease P n) : rooted (load τ q A) u (bolts v (fun _:Seat n=> k)) := by
   -- c unused, omit implicit input
   intro i U; let V : Key n→Pot G n:= Sum.elim q.logarithm (A.twig τ); let g' := (k); let v':=Sum.elim v (Function.const (Seat n) g'); refine ⟨(h i U).1,?_⟩
   change ‖V (N i) U‖≤ v' (N i); cases N i with
   | inl i=> exact (h i U).2
   | inr i=> exact (A.twigs_norm τ i U).trans_eq (by change _=lilac _ _ _; unfold lilac; ring)
section funds
variable (α Δ H a w:ℝ) {v : ℕ → ℝ} (he:H≤a)
        {R : PathData G}{b:Clip}{σ C Λ δ':ℝ}
local notation "L" => shelves X R P
local notation "Z" => Collection.fill X R b P V α Δ
local notation "Π" => port (L) A
local notation "M" => load τ (Z) A
local notation "W" => regularNeed G P b σ C α a
local notation "Vw" => softNeed G P b σ C α a
--- budget loosen needed separately. caller with δ'</!
open WilsonStartup Residual Lattice.Corona Geo Ovens
variable (g:G.Simple)(hR: R.Bounds b σ C Λ)(hC: Decent b P)(hσ: Width P b σ)(hn:20<n.val)
    (hp:P.threshold^2* |Δ| ≤ a)
    (hL: Collection.Local X P V H w)
set_option quotPrecheck false
local notation "S₁" => resetFee G P*(a-H)
local notation "T₁" => softReset G P (a-H)
-- param indices; don't pass δ bound on t. quote_budget' cheap supply
lemma soft_add : softReset G P (a-H) = softReset G P a-softReset G P H:= by unfold softReset Footprint.payment degreeIncome; ring
include hp hR hC hσ
private lemma fundsY (hu:∀ i,P.supBounds (X.reg i).site (X.reg i).support (V.logRead i) (v i)) (hV: Quotes.early P X.reg v H) : anchored P (incoming X R P) (quoteE R P b α Δ v) (W - S₁) ∧
 Ac.Hit (soft X R P) P.B (quoteL R P b α Δ v) (P.supportExponent+1) (Vw - T₁):= by
  have hB := Cost.nonneg hR.three
  have ⟨he,hk⟩ := enlarging G X.reg hC.radius (fun i => (hu i).1) hV
  obtain ⟨hx,hb,hl⟩ := rows (n:=n) G R b P hR hσ
  obtain ⟨hL,hH,hD⟩ := budget_pos P G b hR.width hB
  have ht := turnFee_pos P
  have hg := P.threshold_pos
  refine ⟨fun o => Cost.enlarge (Cost.sum (he o) (Cost.sum
    (anchored_scale («r»:=turnFee P*(|Δ| * P.threshold^2)) (by positivity) hx o)
    (anchored_scale («r»:=turnFee P*(|α+Δ| * P.threshold^3)) (by positivity) hb o))) ?_, fun x => ?_⟩
  · unfold regularNeed; linarith only [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp hL) ht.le,
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (fresh_allow hp (α:=α)) hH) ht.le]
  refine Cost.enlarge (Cost.sum (hk x) ((hit_scale (hitPower_pos P G α Δ) hl) x)) ?_
  unfold softNeed; rw [soft_add]; linarith only [mul_le_mul_of_nonneg_right (hit_allow (G:=G) hp (α:=α)) hD]
include hn hL g
lemma extend {γ:ℝ}(hz:spendX r P n ≤ S₁)(ht:spendX k P n≤ T₁)
  (hF: Fees G P b σ C α a w δ' γ): Ingredients Π M P δ' γ:= by
   have he:= hL.fittings g hR hC hn α Δ
   obtain ⟨k',hk,hG⟩:= hL.expensive
   obtain ⟨v,hv,hV⟩:= hL.cheap; obtain ⟨h'',hr⟩:= fundsY (C:=C) α Δ H a hR hC hσ hp hv hV
   let v':= quoteL R P b α Δ v ∘ numbering (LKey n)
   have hT(i:ℕ)(U):‖(Z).logarithm i U‖≤v' i:=Local.quote_soft (R:=R) (c:=b) g α Δ hv hL.smooth (numbering _ i) _
   obtain ⟨m,κ,hm,hX⟩:= hF.hard
   let v₀:= bolts v' (fun _:Seat n=> k)
   have hv'' : Payments.softCost P Π v₀ (Vw - T₁+spendX k P n):= paysSoft τ A ⟨fun i=>(norm_nonneg _).trans (hT i 1),fun x=>Cost.equiv (numbering _) (hr x)⟩
   apply tender (q:=v₀) (p:=k') (sailsF τ A he) _ ⟨fun i=>(hk i).1, hG⟩ ⟨hv''.1,fun i=>Cost.enlarge (hv''.2 i) (by linarith only [hm,ht])⟩ (pays_hit τ (q:=Z) (fun i U=> ⟨(hk i).2 U,hT i U⟩) A) hX
   obtain ⟨u,hu,h⟩:= readyE τ A (show ((L).pours (Z)).EBound P (W-S₁) from ⟨_,fun i=>Local.quote_regular g hR hC α Δ hv hL.smooth (numbering _ i), fun x=>Cost.equiv (numbering _) (h'' x)⟩)
   exact ⟨u,hu,fun x=> Cost.enlarge (h x) (by linarith [hF.regular])⟩
end funds
end YM.AnalyticBridge.VerifiedReset.Averaging.Wind
#print axioms YM.AnalyticBridge.VerifiedReset.Averaging.Wind.extend
