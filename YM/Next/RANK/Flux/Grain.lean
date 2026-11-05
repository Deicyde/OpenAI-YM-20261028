import YM.Next.RANK.Flux.Rain
import YM.Next.RANK.Flux.Striker

/-!
# Static rent merges at one-kernel output

First-level cost receipts at odd palettes BEFORE any contour estimate. Numbers
carry opaque post-L walls; upcoming monotone delay lemmas separately. Hits core
uncolored $γ$ even for compulsory flag of ANY species. True norm on marked H
and topology still kept. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Flux
open Marker Glyph Exponential Finset Lattice Ac Relation Value Corona RG Wilson MeasureTheory
open scoped BigOperators Classical

variable {V ι κ α β : Type*} {G : Gauge} {n : Side} [DecidableEq V] [Fintype V] {ζ : V→ Site n} {t e a b y : ℝ}
variable (S : ι→ Plug G ζ t) (F : κ → Lining G ζ t) (Q : BudgetPoint)

section
variable [Fintype ι] [Fintype κ] (f : ι ⊕κ→ℝ)

structure Risible (M : ℕ) (d : ℝ) : Prop where
  day : 0 ≤ d
  grain : ((M+M+1:ℕ):ℝ)^4*d ≤ 1

lemma marches {ι : Type*} [Fintype ι] {Q : BudgetPoint} (X : ι→Support n) (b : ι→ℝ) {d a e : ℝ} (h : ∀ i,0 ≤ b i) (he : Hits X b Q a d) (hv : e≤a) : Hits X b Q e d:= by
  intro i; apply le_trans _ (he i); apply Finset.sum_le_sum; intro j hP; unfold alarm; have :=h j; gcongr
omit [Fintype κ] in
lemma sum_subtype' {A : ι → Prop} [DecidablePred A] (f : ι→ℝ) (g : ι→Support n) (R : ι→Prop) (p : ℝ) :
    strike (g ∘ Subtype.val (p:=A)) (f ∘ Subtype.val) Q (R ∘ Subtype.val) p = strike g f Q (fun i => A i ∧ R i) p:= subtype_strike ..
lemma hits_filter (Y : ι→ Support n) (v : ι→ℝ) (s : ι→ Prop) [DecidablePred s] (h : ∀ i,0 ≤ v i) (he : Hits Y v Q e a) :
    Hits (Y ∘ Subtype.val (p:=s)) (v ∘ Subtype.val) Q e a:= fun i=> by
  apply le_trans _ (he i); let g j:= i∈Y j
  change strike _ _ _ (g ∘ Subtype.val) _ ≤ _; rw [sum_subtype']; exact supple Y v Q _ _ _ (fun j h=> h.2) h
lemma plus_hits (v : ι→ℝ) (g : κ→ℝ) {d e x y} (S : ι→ Plug G ζ t)
    (hs : Hits (fun i=> (S i).extent) v Q d x) (hp : Hits (fun i=> (raised (F i)).extent) g Q d y) (he : x+y≤e) : Hits (dish S F) (Sum.elim v g) Q d e:= by
  have hh : dish S F=Sum.elim (fun i=> (S i).extent) (fun i=> (raised (F i)).extent):= by ext i; cases i with | inl i=>rw [dishfest];rfl|inr i=>rfl
  rw [hh]; intro i; rw [drill]; exact (add_le_add (hs i) (hp i)).trans he

variable (hf : ∀ i,0 ≤ f i)
include hf
lemma reaches (h : Hits (dish S F) f Q (e+1) y) (hr : Risible Q.B y) (hv : 0≤ e) :
    let R:= panel S F; let m:= panda S F f
    Hits (feet (sunny R)) (fun i : Bright R=>m i.val) Q e (Real.exp y-1) ∧
      Hits (fun i=>Plug.extent (Plug.raid (evening R i))) (fun i : Dimmed R=>m i.val) Q e (Real.exp y-1):= by
  intro R m; let D:=dish S F
  have H: Hits (lamps S F) m Q e (Real.exp y-1):= pad S F f Q hf h hr.grain hv hr.day
  have he := hits_filter Q (lamps S F) m (fun i=>¬ (R i).landed) (panda_pos S F f · hf) H; have hz:= hits_filter Q (lamps S F) m (fun i=>(R i).landed) (panda_pos S F f · hf) H
  have ht: feet (sunny R)=lamps S F ∘ Subtype.val:= by
    ext1 p; have hx:=congr_arg Plug.extent (bright_valid R p); exact hx.symm.trans (pan_extent ..)
  have hp:(fun i=> Plug.extent (Plug.raid (evening R i)))=lamps S F∘Subtype.val:= by
    ext1 p; rw [← dim_valid R p]; exact pan_extent ..
  rw [ht,hp]; exact ⟨he,hz⟩

lemma candles (β : ℝ) (hF : flat F) (h : Hits (dish S F) f Q (e+1) y) (hr : Risible Q.B y) (hv : 0≤e)
    (H : ∀ i,strike (dish S F) f Q (fun j=> ∃ p : ι,j = .inl p ∧ ¬(S p).landed ∧ i∈(S p).fires.val) (e+1) ≤ β) :
    let p:=panel S F; ∀ i, strike (feet (sunny p)) (fun t => panda S F f t.val) Q (fun j=> i∈(sunny p j).fires.val) e ≤ β:= by
  intro p i; apply le_trans _ (H i)
  let K : ι⊕κ→Prop:=fun j=> ∃ p : ι,j = .inl p ∧ ¬ (S p).landed∧ i∈ (S p).fires.val; let A j:= i∈(sunny p j).fires.val
  have he j:A j→ ∃ t∈j.val.val,K t:= by
    intro hx; have he:= congr_arg Plug.fires (bright_valid p j); change (p _).fires=(sunny _ j).fires at he
    have hh : i∈(shining S F j.val).val:= by
      rw [← pan_mark]; change i∈(p _).fires.val; rw [he]; exact hx
    obtain ⟨l|l,hj,hZ⟩:=mem_biUnion.mp hh
    · refine ⟨_,hj,l,rfl,cool S F _ ?_ (mem_toLeft.mpr hj),?_⟩; intro hz;exact j.property (show (panel S F j.val).inventory.Nonempty from (pan_vital S F j.val).symm ▸ hz)
      change i∈ (CoverReads.ofPlug _).fires.val at hZ; rwa [p_coverFire] at hZ
    change i∈(raised (F l)).fires.val at hZ; rw [hF] at hZ;exact False.elim (notMem_empty _ hZ)
  exact report1 F S _ f (panda_pos S F f · hf) _ K _ e he (fun i L hl=> pad_root S F f Q hf h hr.grain hv hr.day L i hl)

end

section
variable (X : ι→ SourceAt G ζ) [DecidableEq ι] [Fintype ι] (p : ι→ℝ) {Q}
lemma touches_here (h : ∀ i,0 ≤ p i) (H : Hits (feet X) p Q (e+1) y) (hv : 0 ≤ e) (hr : Risible Q.B y) : Hits (feet (Bond X)) (hlog X p) Q e y:= fun i=> by
  apply le_trans _ (H i); apply expire X p Q _ h H hr.grain hr.day hv; exact fun _=> mem_biUnion.mp
end
end YM.Next.Rank.Flux
