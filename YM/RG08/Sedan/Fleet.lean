import YM.RG08.Sedan.Mill

/-! # Base and crown at output. Shape & calibration, get without Grimoire guesses. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Sedan
open Filter Function Matrix MeasureTheory Finset Lattice Exterior Wilson RG Precision Stationary Work.F05 Tree Carrel Prism Tack Camera Gallery
open Forms Rudder Anchor Isles Laurent Pert.Bulk Packets Mount Glyph Room Bloch Quarry Aggregate Steam Spar Symmetry Roost
open scoped Classical Matrix ContDiff Topology BigOperators InnerProductSpace PowerSeries ENNReal Matrix.Norms.Frobenius
variable {c:Side}{G:Gauge}{P:Patch}{K:KernelChoices}{I J:Type}{n:ℕ}

abbrev Wheel (G:Gauge) := Rudder.Raw G.ColorIndex 2
structure Seed (B:Bed)(T:Wheel G):Prop where
 honor:Honor G 2 T
 cast:picture G.ColorIndex 2 T=(1/2:ℝ) • Cast.root G B
 main:Loop.Core T (1/2)

-- lift controller; announce each v with schedule. rank indexed r=0.. (two slots at r=0).
structure Yard (G:Gauge) where
 need : ℕ→ℕ→ℝ
 tall e r:0<need e r
 coats:ℕ→ℕ→ℝ
 cash : ℕ→ℕ→ℝ
 tag (e r):Rigged (n:=r+1) (Symmetry.dressed G (Mount.rank r)) (need e r) (coats e r) (cash e r)

def paving (w:ℕ→ℕ→ℝ)(h:∀ e r,0<w e r):Yard G where
 need:=w
 tall:=h
 coats e r:= (warehouse (n:=r+1) (w e r) (h ..) (by omega) (Symmetry.dressed G (Mount.rank r)) (Symmetry.respects G (Mount.rank r))).choose
 cash e r:= (warehouse (n:=r+1) (w e r) (h ..) (by omega) (Symmetry.dressed G (Mount.rank r)) (Symmetry.respects G (Mount.rank r))).choose_spec.choose
 tag e r:= (warehouse (n:=r+1) (w e r) (h ..) (by omega) (Symmetry.dressed G (Mount.rank r)) (Symmetry.respects G (Mount.rank r))).choose_spec.choose_spec

def initial (H:Yard G)(B:Bed): Wheel G := Cast.starter G B (H.coats 0 0)
lemma attained (H:Yard G)(B:Bed)(hG:G.Simple){v:Clip}{τ u C:ℝ}(hp:B.metric.strip (H.need 0 0) C)(hb:∀ n,Floor B v n τ u)(h:∀ n, Bid.Sworn B n G)(hi:H.need 0 0≤1)(hc:0≤C):
 Seed B (initial H B) ∧ Held (carpet _) (H.coats 0 0) (H.cash 0 0 * Cast.funds G C) (initial H B):=by
 obtain ⟨he,hp',hm,hU⟩:=Cast.seats B hG hp hb h (H.tall 0 0) hi hc (H.tag 0 0)
 have ht0:= (H.tag 0 0).1;have hp0:= (H.tag 0 0).2.2.1
 exact ⟨⟨⟨he,_,_,ht0,mul_nonneg hp0 (by unfold Cast.funds Cast.tax;have :=Flat.sumToken_pos; positivity),hp'⟩,hm,hU⟩,hp'⟩

def lonely (T:Wheel G):Castle G:= fun r e=> if h:r=0 then if e=0 then h ▸ T else 0 else 0
private lemma compress_scale (G:Gauge)(T:Wheel G)(x:ℝ): compress 1 (x • T)=x • compress 1 T:=rfl
lemma simple_zero(B:Bed){T:Wheel G}(hT:Seed B T): demand (lonely T) 0= - bare (alum G B) 0:=by
 obtain ⟨⟨H,s,p,hS,hP,hE⟩,ht,hU⟩:=hT
 funext n
 by_cases he:n=2
 · subst n
   have hg: Prism.polar (alum G B) = (- (1/2:ℝ)) • Cast.spur G (Flat.output B):=rfl
   unfold demand Mount.flight; simp only [zero_add, range_one,sum_singleton,le_refl,Nat.sub_self,Mount.rank];
   rw [show lonely T 0 0=T from rfl, Carrel.complete_top (G:=G) T (stick 0) H hE hP hS,ht,compress_scale,Cast.root,Cast.beam,show compress 1 (Anchor.extend 1 (Cast.spur G (Flat.output B)))=Cast.spur G (Flat.output B) from funext (fun i=>Anchor.extend_top ..)]
   rw [Pi.neg_apply,Prism.bare,dif_pos rfl,if_pos rfl];change _ = - Prism.polar (alum G B); rw [hg,neg_smul,neg_neg]; simp
 unfold demand Mount.flight;simp only [zero_add,range_one,sum_singleton,Nat.sub_self,Mount.rank]; rw [if_neg (by simp [Ne.symm he]),Pi.neg_apply,Prism.bare,dif_neg he,neg_zero]
lemma loneliness {T:Wheel G}(hT:Honor G 2 T):Sedan.Fair (lonely T):=by
 refine ⟨?_,?_⟩ <;> intro r e <;> by_cases h:r=0 <;> by_cases he:e=0
 · exact fun H=> False.elim (H (by simp [Live,h,he]))
 · intro _; unfold lonely; rw [dif_pos h,if_neg he]
 · intro _;exact dif_neg h
 · intro _;exact dif_neg h
 · subst h; subst he; exact hT
 · unfold lonely;rw [dif_pos h,if_neg he];exact Honor.nil
 · unfold lonely;rw [dif_neg h]; exact Honor.nil
 unfold lonely;rw [dif_neg h]; exact Honor.nil
lemma sober (B:Bed){T:Wheel G}(ht:Seed B T): Grimoire (bare (alum G B)):=by
 have hh: Mount.Stable (lonely T):= (loneliness ht.honor).rails
 have h:= Grimoire.demand (lonely T) hh
 have he(i)(hi:i≠0):bare (alum G B) i=0:=by ext n x; simp [Prism.bare, hi]
 have hz : bare (alum G B) 0= - demand (lonely T) 0:=neg_eq_iff_eq_neg.mp (simple_zero B ht).symm -- orientation
 refine ⟨?_,?_,?_⟩ <;> intro i n <;> rcases i with _|i
 · intro H; exact h.ceiling _ _ (fun hh=>H (by rw [hz,Pi.neg_apply,hh,neg_zero]))
 · rw [he _ (by omega)]; simp
 · rw [hz]; exact h.negative.solvent _ _
 · rw [he _ (by omega)];exact ⟨fun _ _=>rfl,Forms.Sym.zero⟩
 · rw [hz];exact h.negative.billed _ _
 rw [he _ (by omega)];exact ⟨1,0,zero_lt_one,le_rfl,zero_held⟩

lemma consulate (h:P.Branches K G){C:Castle G}{T:Wheel G}{A B:Bed}{Z:ChartRatio G}(ht:Seed B T)(he:Foyer P K A B C Z):
 Grimoire (-(vault G P K h C Z A B)) ∧ AcademyL (-vault G P K h C Z A B) ∧ -vault G P K h C Z A B 0=demand (lonely T) 0:=by
 obtain ⟨_,_,hx,hM,hF⟩:=he.gold
 obtain ⟨hN,hX⟩:=fortune h Z A he.stash hF hx hM
 refine ⟨((sober B ht).add hN).negative,(prayers h A B he).neg,?_⟩
 unfold Prism.vault;rw [Pi.add_apply,hX,add_zero, simple_zero B ht]
end YM.RG08.Sedan
