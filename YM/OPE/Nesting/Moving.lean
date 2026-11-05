import YM.OPE.Nesting.Transactions

/-! Changing finite exterior port labels along their bounded rotation systems
or transforming all colors by reality. These are multilinear (actual `moment`
maps) even when the neighbor test points move. Comparisons invoke agreement
of class readings under reindexing only on configurations with clearance. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Nesting
open Orbits Orbits.Reader Function Filter Extraction Set Table Tree Measures Menu Atom
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{B:Register G}{S:Table B}{L I J:Type}

def chars {e:J→ℕ}(w:Labels S e)(i:J):S.Tag:=⟨e i,w i⟩

namespace Atom
variable [Fintype J]
def flipPanel (A:Atom S L)(Tv:L→Table B) (e:J→ℕ) (y:L→J→E4)(i:L):MultilinearMap ℂ (fun j=> S.Field (e j)) ℂ := (A.amp i) • sectionLabels (d:=Sum.elim e (degrees A.tags)) (voices A.tags) (moment (Tv i) (beside (y i) (A.place i)))

lemma panel_apply (A:Atom S L)(Tv:L→Table B) {e:J→ℕ}{y:L→J→E4} {i:L}(ht:(Tv i).Hierarchy)(hf:Injective (beside (A.place i) (y i)))(w:Labels S e): A.flipPanel Tv e y i w = A.sample Tv y (chars w) i :=by
    unfold sample duet
    have hz:= sectionLabels_apply (voices A.tags) (moment (Tv i) (beside (y i) (A.place i))) w
    refine Eq.trans (show _ = A.amp i * whole (Tv i) (y i) w (A.place i) (voices A.tags) from congr_arg (A.amp i*·) hz) ?_
    exact congr_arg (A.amp i * ·) (whole_flip (voices A.tags) w _ (y i) (hT:=ht) hf)
end Atom
namespace Menu
variable [Fintype J] (P:Menu S L) (Tv:L→Table B)(e:J→ℕ)(y:L→J→E4)(i:L)
def panel := ∑ j:P.Draw,(P.pick j).flipPanel Tv e y i
lemma panel_apply (ht:(Tv i).Hierarchy)(hf:∀ c:P.Draw, Injective (beside ((P.pick c).place i) (y i)))(w:Labels S e): P.panel Tv e y i w=P.atView Tv y (chars w) i:=by rw [panel,MultilinearMap.sum_apply]; apply Finset.sum_congr rfl (fun j _=> (P.pick j).panel_apply Tv ht (hf _) w)
end Menu
section Price
variable {l:Filter L}{T:L→ℝ}{u b W γ:ℝ} {z:L→I→E4} {A A':Menu S L}
variable [Fintype J](Tv:L→Table B)(hTv: ∀ i,(Tv i).Hierarchy)(e:J→ℕ){y:L→J→E4}(hx:Intervals l T u z y) (he:Kept l T b y)(hu:u≤b)

include hx he hu hTv
lemma Menu.view_eq (h:Eligible l T z b A)(w:L→Labels S e): (fun l=>A.panel Tv e y l (w l)) =ᶠ[l] (fun i=> A.atView Tv y (chars (w i)) i):=(eventually_all.mpr fun p=>h.roomAcross p hx he hu).mono (fun i hi=> Menu.panel_apply A Tv _ y i (hTv i) hi _)

lemma move_cost (h:∀ w:J→S.Tag,weightOf w≤W → RateLE l T (fun s=> A.atView Tv y w s - A'.atView Tv y w s) γ)
    (hA:Tendsto T l atTop)(hp:weight e ≤ W)(hh:Eligible l T z b A)(hh':Eligible l T z b A') (w:L→Labels S e)(hw:∀ j:J, RateLE l T (fun i=> w i j) 0) : RateLE l T (fun i=>A.atView Tv y (chars (w i)) i - A'.atView Tv y (chars (w i)) i) γ:=by
        let f (i:L):= (A.panel Tv e y i)-(A'.panel Tv e y i)
        have hr(w:L→Labels S e): (fun i=>f i (w i)) =ᶠ[l] (fun i=> A.atView Tv y (chars (w i)) i - A'.atView Tv y (chars (w i)) i):=(Menu.view_eq (A:=A) Tv hTv e hx he hu hh w).sub (Menu.view_eq (A:=A') Tv hTv e hx he hu hh' w)
        have hs(v:Labels S e):RateLE l T (fun i=> f i v) γ:= (h (chars v) hp).congr (hr fun _=>v).symm
        simpa only [Finset.sum_const_zero,add_zero] using (contract hA f hs w _ hw).congr (hr w)
end Price

namespace Atom
variable (ρ:S.RealSpin)
def tint (v:S.Tag):S.Tag:=⟨v.1,S.conj ρ v.1 v.2⟩
lemma twoTint (v:S.Tag):tint ρ (tint ρ v)=v:= (congr_arg _ (S.reflect_star ρ v.1 v.2))
def shadowed (A:Atom S L):Atom S L:={A with tags:=tint ρ ∘ A.tags, amp:=fun i=> (starRingEnd ℂ) (A.amp i)}

variable (A:Atom S L) (Y:Table B)(s:L) [Fintype J]
lemma bar_duet {y:L→J→E4}{w:J→S.Tag}(ht:Y.Hierarchy)(hr:Y.respects S)(hi:Injective (beside (A.place s) (y s))): star (duet Y (A.place s) A.tags (y s) w)= duet Y (A.place s) (tint ρ ∘ A.tags) (y s) (tint ρ ∘ w):=by
     rw [duet_moment,duet_moment,← bar_observes ρ ht hr hi]
     rw [show splice (tint ρ ∘ A.tags) (tint ρ ∘ w)=tint ρ ∘ splice A.tags w from funext fun j=>by cases j <;> rfl]; rfl
lemma sample_star {y:L→J→E4}{w:J→S.Tag}(Y:L→Table B)(ht:(Y s).Hierarchy)(hr:(Y s).respects S)(hi:Injective (beside (A.place s) (y s))): (starRingEnd ℂ) (A.sample Y y (tint ρ ∘ w) s) = (A.shadowed ρ).sample Y y w s:=by
     unfold sample; rw [map_mul]
     apply congr_arg ((starRingEnd ℂ) (A.amp s)*·) (by change star _= _; rw [bar_duet ρ A (Y s) s ht hr hi,show tint ρ ∘ (tint ρ ∘ w)=w from funext (fun i=> Atom.twoTint ρ _)]; rfl) -- maybe orientation arg order due variable
end Atom
namespace Menu
variable (ρ:S.RealSpin) (P:Menu S L)
def shadowed : Menu S L:= {P with pick:=Atom.shadowed ρ ∘ P.pick}
lemma shadowed_ok {l:Filter L}{T:L→ℝ}{b:ℝ} {z:L→I→E4}(h:Eligible l T z b P): Eligible l T z b (P.shadowed ρ):=by
    intro c; change P.Draw at c; obtain ⟨hf,hk,ζ,hζ⟩:=h c; refine ⟨hf,hk, ζ,hζ.transfer <| Eventually.of_forall fun i=>?_⟩; exact (norm_star _).le

variable [Fintype J] (Y:L→Table B)(y:L→J→E4)(w:J→S.Tag)(s:L)(ht:(Y s).Hierarchy)(hr:(Y s).respects S)(hi:∀ c:P.Draw, Injective (beside ((P.pick c).place s) (y s)))
include ht hr hi
lemma shadowed_view:(P.shadowed ρ).atView Y y w s = (starRingEnd ℂ) (P.atView Y y (tint ρ ∘ w) s):=by
    unfold atView; rw [map_sum]; change (∑ c:P.Draw,((P.pick c).shadowed ρ).sample Y y w s)=_; exact Finset.sum_congr rfl (fun c _=>(Atom.sample_star ρ _ s Y ht hr (hi c)).symm) -- arg order
end Menu

namespace Atom
variable {G:Gauge}{B:Register G}{S:Table B}{l:Filter L}{T:L→ℝ}{b u γ W:ℝ} {z:L→I→E4}{A A':Menu S L}(ρ:S.RealSpin) [Fintype J](y:L→J→E4)(w:J→S.Tag)(p:weightOf w≤W)(q:Intervals l T u z y)(he:Kept l T b y)(hu:u≤b)(hh:Eligible l T z b A)(hh':Eligible l T z b A')
    (Y:L→Table B)(ht:∀ s,(Y s).Hierarchy)(hr:∀ s,(Y s).respects S)
include p q he hu hh hh' ht hr
lemma same_shadow (h:RateLE l T (fun i=> A.atView Y y (tint ρ ∘ w) i-A'.atView Y y (tint ρ ∘ w) i) γ):RateLE l T (fun i=>(A.shadowed ρ).atView Y y w i-(A'.shadowed ρ).atView Y y w i) γ := by
    refine h.transfer ?_
    filter_upwards [eventually_all.mpr fun c=>hh.roomAcross c q he hu,eventually_all.mpr fun c=>hh'.roomAcross c q he hu] with i hi hi'
    change ‖(A.shadowed ρ).atView ..-(A'.shadowed ρ).atView ..‖≤‖_‖
    rw [Menu.shadowed_view ρ A _ _ _ _ (ht _) (hr _) hi,Menu.shadowed_view ρ A' _ _ _ _ (ht _) (hr _) hi', ← map_sub]; exact (norm_star _).le
end Atom
variable {C:Family G}{F:Order}{S:Table C.book}(U:Spec.Final C F S)

lemma agree_shadow {l:Filter L}{T:L→ℝ}{b u γ W:ℝ} {z:L→I→E4}{A A':Menu S L}(ρ:S.RealSpin)(h:Agrees U l T z u b W γ A A')(hh:Eligible l T z b A)(hh':Eligible l T z b A')(hu:u≤b):Agrees U l T z u b W γ (A.shadowed ρ) (A'.shadowed ρ) :=by
    intro J _ w y s p q he; exact Atom.same_shadow ρ y w p q he hu hh hh' (spectator U ∘ s) (fun i=> spectate ..) (fun i=>spectate_respects U (s i)) <| h _ _ _ (by exact p) q he
end YM.OPE.Nesting
