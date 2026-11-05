import YM.WilsonBulk.Recast.Render
import YM.WilsonBulk.Tickets.Issue

/-! # Kinetic re-expression: canonical β old * Ω(g_old), any Ω computed from unmasked
 kernel ALL powers and their models in rescaled log (no exception for `bar` in Calendar).
 Emit vacuum cohesion statements. Exact authority for arbitrary later actions and horizons,
 step ordering data. Distinct formal scheme and gauge. Cost arithmetic continuation elsewhere.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Parapet
open Lattice Laurent Function Filter Bloch Matrix LinearMap Precision Exterior Wilson Pert.Bulk Sheet Atelier Finset
open Recall PowerSeries
open scoped Topology Classical BigOperators ENNReal ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {B Q : Bed} {I J : Library G} {α β : Type} {c : Side} {e d : ℕ} {p r : Word}

variable (k : G.ColorIndex)
-- full kinetic one surface. input normalized in ISlamp rule incl unit at p; don't impose gauge by it.
def revenue (I : Library G) : Word := PowerSeries.mk fun i=> subdue k (I i 2)
abbrev missed (I : Library G) := polling (revenue k I)
lemma earnings (I : Library G) (i) : coeff i (revenue k I)=subdue k (I i 2) := coeff_mk ..
lemma revenue_color (h : Whisper I) (hs : G.Simple) (j : G.ColorIndex) : revenue k I=revenue j I := by ext1 i; rw [earnings,earnings]; unfold subdue; rw [color_price h hs j k k _ _ _ i, if_pos rfl]
lemma revenue_anchor (hI : Crest I B) (h : subdue k (summit G B 0 2)=1) : constantCoeff (revenue k I)=1 := by rw [← PowerSeries.coeff_zero_eq_constantCoeff, earnings,hI,h]
lemma revenue_parity (h : Document I) : Pall (revenue k I) := by intro i hi; rw [earnings,h.parity i 2 (by omega),subdue_zero]

-- `revenue` linear on public ranks
lemma subdue_many (s : Finset β) (V : β→ Text (Cloth G) 2) (h : ∀ i∈s, Public (V i)) : subdue k (∑ i∈s,V i)=∑ i∈s,subdue k (V i) := by
  induction s using Finset.induction with
  | empty=> simp
  | insert i s he ih=> have hf : ∀ i∈s,Public (V i):=fun _ h'=>h _ (mem_insert_of_mem h'); rw [sum_insert he,sum_insert he,subdue_plus (Public.gather _ hf) (h i (mem_insert_self ..)), ih hf]
lemma revenue_shift (h : Pamphlet I) (g r : Word) : revenue k (reorder g r I)=(r^2)*bar g (revenue k I) := by
  ext1 i; rw [earnings,bar_terms,reorder,subdue_many k _ _ (fun i _=>(h i _).scale _)]; simp only [earnings, pencil,subdue_pay]
lemma chosen_shift (h : Pamphlet I) (he : constantCoeff (revenue k I)=1) :
    revenue k (reorder (missed k I) (recover (missed k I)) I)=1:= by rw [revenue_shift k h, ← (poll_rule he).2,← mul_pow, missed, rec_one (poll_rule he).1,one_pow]
-- receipt ledger and downstream use

def resetI (I : Library G) := reorder (missed k I) (recover (missed k I)) I
structure Healthy (V : Library G) (B : Bed) : Prop where
  report : Whisper V
  crests : Crest V B
  shared : revenue k V=1
lemma Healthy.after {V : Library G} (hp : Whisper V) (ht : Crest V Q) (hz : subdue k (summit G Q 0 2)=1) : Healthy k (resetI k V) Q := by -- M unbound unnecessary
  let g:= missed k V; let v:=recover g
  have HH:= hp.palm; have hc := revenue_anchor k ht hz; have h0 : constantCoeff g=1:= (poll_rule hc).1; have hG:= crown h0
  have hv : Pall g:= (revenue_parity k hp.style).polling; have hV:= hv.recovery h0
  refine ⟨⟨Document.at_first hp.style hv hV,Cashless.shelter hp.cash,Pamphlet.authorized HH,fun i=>?_⟩, (anchor_literal h0 hG).trans ht, chosen_shift k HH hc⟩
  change Regime (volumeTape (issue i (reorder g v V)))
  rw [Pamphlet.issue_reorders HH i, reorder_tape (HH.at_issue i hp.style).cap]; exact authority i (by rw [mul_comm]; exact rec_one h0) (hp.guns i)
lemma Healthy.null {I J : Library G} (h : Healthy k I B) (w : Healthy k J Q) (hs : G.Simple) : BodyNull (I-J) := by
  apply BodyNull.fuse h.report w.report k hs; intro i; rw [← earnings, ← earnings,h.shared,w.shared]
lemma shelf (P : RG.Patch) (K : RG.KernelChoices) (M : ChartRatio G) (T : Model P K) (h : Passage M B Q T) (V : Library G) (hi : Whisper V) (he : Crest V B) (hp : subdue k (summit G Q 0 2)=1) :
    Healthy k (resetI k (pressureI M T B Q V)) Q := Healthy.after k (whispers_post h hi he) (funext fun i=> press_lead _ _ _ _ V hi.style i) hp
lemma starts {A : RG.Levels G} {H : Horizon A} {F : MapPrices} (hf : H.Suffices F) (x : ℕ) : Healthy k (upstream G) (H.H x x) := by
  have ht:= voyage_crest hf x; refine ⟨initial_whisper x hf, ht,?_⟩; ext1 j; cases j with
  | zero=> rw [earnings,ht, price_at_horizon hf le_rfl]; simp
  | succ j=> rw [earnings]; rw [top_price k (j+1) (by omega), coeff_one,if_neg (by omega)]
end YM.WilsonBulk.Parapet
