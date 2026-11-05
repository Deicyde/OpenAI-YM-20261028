import YM.RG08.Sedan.Fleet

/-! # Output curvature cartridge, schedule-oriented choice, fallback elsewhere.
 Geometry thresholds v only (cost arbitrary), so UV stability doesn't depend on a
 smallness decision. Earlier requests or other packs may use narrower schema, apparently
 different harvest shown equal on coupled outputs. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Sedan
open Filter Function Matrix MeasureTheory Finset Lattice Exterior Wilson RG Precision Stationary Work.F05 Tree Carrel Prism Tack Camera Gallery
open Forms Rudder Anchor Isles Laurent Pert.Bulk Packets Mount Glyph Room Bloch Quarry Aggregate Steam Spar Symmetry Roost
open scoped Classical Matrix ContDiff Topology BigOperators InnerProductSpace PowerSeries ENNReal Matrix.Norms.Frobenius
variable {G:Gauge}{n e p r q:ℕ}(H:Yard G)
abbrev Gird (G:Gauge) (r:ℕ):= Rudder.Raw G.ColorIndex (Mount.rank r)
def Passable (F:Gird G r)(x:ℝ):Prop := ∃ p:ℝ, Held (carpet _) x p F
/- `wood` on frames that fail planned support, get some weaker positive width if possible. -/
def room (F:Gird G r):ℝ:= if h:∃ x:ℝ,0<x∧Passable F x then h.choose else 1
private def foo (x:ℝ):Yard G:=Sedan.paving (G:=G) (fun _ _=> if 0<x then x else 1) (fun _ _=>by split <;> first | assumption| exact zero_lt_one)

def grant (e:ℕ)(F:Gird G r) : Gird G r:=
 if Passable F (H.need e r) then relift (n:=r+1) (Symmetry.dressed G (Mount.rank r)) (H.coats e r) F else relift (n:=r+1) (Symmetry.dressed G (Mount.rank r)) ((foo (G:=G) (room F)).coats e r) F
lemma grant_open (e:ℕ)(F:Gird G r){t:ℝ}(h:Held (carpet _) (H.need e r) t F): grant H e F=relift (n:=r+1) (Symmetry.dressed G (Mount.rank r)) (H.coats e r) F:=if_pos (show Passable F _ from ⟨_,h⟩)
lemma gift (e:ℕ)(F:Gird G r)(hf:Cloak (Symmetry.dressed G (Mount.rank r)) 1 F)(hc:Closing F)(hp:∃ x,0<x ∧ Passable F x):
 let U:=grant H e F; Honor G (Mount.rank r) U ∧ picture G.ColorIndex (Mount.rank r) U=F:=by
 intro U
 have he (W:Yard G)(hS:Passable F (W.need e r)):
    let V:=relift (n:=r+1) (Symmetry.dressed G (Mount.rank r)) (W.coats e r) F; Honor G (Mount.rank r) V ∧ picture G.ColorIndex (Mount.rank r) V=F:=by
    obtain ⟨p,h⟩:=hS
    obtain ⟨hx,h',hp,hV⟩:=W.tag e r
    let s:=max p 0; have hv:s≥0:=le_max_right ..
    obtain ⟨hE,hQ,hT,_⟩:=hV F s ⟨hf,hc,hv,h.mono le_rfl (le_max_left ..) (fun _=>le_rfl)⟩
    exact ⟨⟨hE,_,_,hx,mul_nonneg hp hv,hQ⟩,hT.symm⟩
 unfold U grant
 split
 next h=>exact he H h
 next _=>
   have hv:0<room F ∧ Passable F (room F):=by unfold room;rw [dif_pos hp]; exact hp.choose_spec
   apply he (foo (room F));unfold foo Sedan.paving;dsimp only;rw [if_pos hv.1];exact hv.2

-- exact demand replace protocols

def overlooks (A:Castle G)(p:ℕ):Prop:= ∀ e r,p ≤ e → A r e=0
lemma flight_start (F:Gird G r)(e:ℕ)(s:ℕ):Mount.flight r e F e s=if he:Mount.rank r=s then Steam.move he (completed F (stick r) (Mount.rank r)) else 0:=by unfold Mount.flight;rw [Nat.sub_self,zero_add];split_ifs with h hh <;> first| rfl| (subst hh; rfl)|grind
lemma flight_nil (k e j n:ℕ): Mount.flight (G:=G) k j 0 e n=0:=by
 unfold Mount.flight;split_ifs with h
 swap; rfl
 rcases n with _|a; · obtain ⟨hx,h⟩:=h;unfold Mount.rank at h; omega
 exact completed_null ..

lemma demand_mates (A C:Castle G)(ht:∀ i r,i ≤ e → r ≤ i → A r i=C r i): demand A e=demand C e:=by
 ext k t;unfold demand; simp only [Finset.sum_apply];refine Finset.sum_congr rfl fun i hi=>Finset.sum_congr rfl fun r hr=>?_ ; rw [ht _ _ (by simpa using hi) (by simpa using hr)]

lemma addition (A D:Castle G)(H:overlooks D e)(he:∀ j a,j<e → a ≤ j →A a j=D a j):
 demand A e (Mount.rank n)=demand D e (Mount.rank n)+if n ≤ e then completed (A n e) (stick n) (Mount.rank n) else 0:=by
 unfold demand;conv_rhs=>lhs;rw [Finset.sum_range_succ]
 rw [Finset.sum_range_succ]
 rw [Finset.sum_eq_zero (s:=range (e+1)) (f:=fun r=>Mount.flight r e (D r e) e (Mount.rank n)) (fun _ _=>by rw [H _ _ le_rfl,flight_nil]),add_zero];apply congrArg₂ (fun x y:Flake _ (Market (Loc G 1))=>x+y)
 · apply sum_congr rfl;intro j hj;apply sum_congr rfl;intro a ha;rw [he _ _ (by simpa using hj) (by simpa using ha)]
 split_ifs with h
 · rw [Finset.sum_eq_single_of_mem n (by simpa) (fun i _ hi=>?_),flight_start,dif_pos rfl]
   · rfl
   · rw [flight_start,dif_neg (by intro hv; apply hi; unfold Mount.rank at hv;omega)]
 apply Finset.sum_eq_zero;intro i hi;rw [flight_start,dif_neg (by simp only [mem_range] at hi; unfold Mount.rank;omega)]
lemma addition_one (A D:Castle G)(_H:overlooks D e)(he:∀ j a,j<e→ a ≤ j →A a j=D a j):demand A e 1=demand D e 1:=by
 unfold demand;conv_rhs=>rw [Finset.sum_range_succ]
 rw [Finset.sum_range_succ];apply congrArg₂ (fun x y:Flake _ (Market (Loc G 1))=>x+y)
 · apply sum_congr rfl; intro i hi;apply sum_congr rfl;intro r hr;rw [he _ _ (by simpa using hi) (by simpa using hr)]
 apply Finset.sum_congr rfl;intro i hi;simp only [flight_start,dif_neg (by unfold Mount.rank;omega:Mount.rank i≠1)]
end YM.RG08.Sedan
