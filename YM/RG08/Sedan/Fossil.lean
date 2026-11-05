import YM.RG08.Sedan.Lane

/-! # First unmatched repetition all arities. Expanded corner paths paid ONCE, every frame
 accounted. Alignment rates in later files. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Sedan
open Filter Function Matrix MeasureTheory Finset Lattice Exterior Wilson RG Precision Stationary Work.F05 Tree Carrel Prism Tack Camera Gallery
open Forms Rudder Anchor Isles Laurent Pert.Bulk Packets Mount Glyph Room Bloch Quarry Aggregate Steam Spar Symmetry Roost
open scoped Classical Matrix ContDiff Topology BigOperators InnerProductSpace PowerSeries ENNReal Matrix.Norms.Frobenius
variable {G:Gauge}{n e p r q:ℕ}(H:Yard G)
abbrev Scroll (G:Gauge):=Steam.Grain (Market (Loc G 1))
variable (V:Scroll G)(A:Castle G)
def carry (e:ℕ)(r:ℕ):Gird G r:=grant H e (Anchor.extend 1 ((V-demand A) e (Mount.rank r)))
def patcher (e:ℕ):Castle G:=fun r j=> if e=j then if Live r j then carry H V A e r else 0 else A r j
lemma patched (e:ℕ)(h:e ≠ p):patcher H V A e r p=A r p:=if_neg h

def Closed (V:Scroll G)(A:Castle G)(e:ℕ):Prop :=∀ k<e,∀ n,0<n→ (V-demand A) k n=0

variable {V A}
lemma approval (h:AcademyL V)(hs:Grimoire V)(hA:Fair A)(ho:Closed V A e)(he:r ≤ e):
 Honor G (Mount.rank r) (carry H V A e r) ∧ completed (carry H V A e r) (Mount.stick r) (Mount.rank r)=(V-demand A) e (Mount.rank r):=by
 let U:=V-demand A;let n:=Mount.rank r
 have hh:= hs.sub (Grimoire.demand A hA.rails)
 obtain ⟨u,p,hu,hp,hZ⟩:=hh.billed e n
 obtain ⟨hD,hU,hV⟩:= Roost.frontier U e (h.sub (masters hA.rails)) (fun k hk n hn=> ho k hk n (Nat.pos_iff_ne_zero.mpr hn)) (k:=n) (by unfold n Mount.rank; omega) (hh.solvent e n).2 (hh.solvent e n).1 hZ
 obtain ⟨hT,hK⟩:= gift H (r:=r) e _ hD hU ⟨u,hu,p,hV⟩
 refine ⟨hT,?_⟩
 obtain ⟨hc,v,b,hv,hb,hM⟩:=hT
 rw [carry,complete_top _ _ hc hM hb hv,hK]; funext i;exact extend_top ..
lemma single (h:AcademyL V)(hg:G.Simple)(hs:Grimoire V)(hA:Fair A)(ho:Closed V A e):
 (V-demand A) e 1=0:=by
 let U:=V-demand A;have hh:=hs.sub (Grimoire.demand A hA.rails)
 obtain ⟨u,p,hu,hp,hE⟩:=hh.billed e 1
 obtain ⟨hD,-,-⟩:=Roost.frontier U e (h.sub (masters hA.rails)) (fun k hk n hn=>ho k hk n (Nat.pos_of_ne_zero hn)) (k:=1) (by omega) (hh.solvent e 1 |>.2) (hh.solvent e 1 |>.1) hE
 have hT:= Gallery.single_wear _ hg hD.hair
 ext i;rw [← Anchor.extend_top ((V-demand A) e 1) i,hT];rfl

lemma leg (h:AcademyL V)(hg:G.Simple)(hs:Grimoire V)(hA:Fair A)(ho:Closed V A e)(hE:overlooks A e):
 let T:=patcher H V A e;Closed V T (e+1) ∧ Fair T ∧ overlooks T (e+1):=by
 intro T
 have hi(k)(p:ℕ)(hk:k < e):T p k=A p k:=patched H _ _ e (by omega)
 have hf : Fair T:=by
    constructor
    · intro r i hh; unfold T patcher; rw [if_neg hh];by_cases hl:e=i <;> simp [hl,hA.rests r i hh]
    intro r i
    unfold T patcher;split
    next he=>
       subst i; by_cases hL:Live r e
       · rw [if_pos hL];exact (approval H h hs hA ho hL.1).1
       · rw [if_neg hL];exact Honor.nil
    exact hA.honor r i
 have hx:=hs.sub (Grimoire.demand T hf.rails)
 refine ⟨?_,hf,?_⟩
 · intro k hk i hP
   by_cases he:k=e
   · subst k;rcases i with _|(_|r)
     · omega
     · change V e 1-demand T e 1=_;rw [addition_one T A hE (fun j a h _=>hi j a h)]; exact Sedan.single h hg hs hA ho
     by_contra hr; obtain ⟨hp,m,hm⟩:=hx.ceiling _ _ hr;have hL:Live r e:=⟨by omega,by unfold Even;exact ⟨m-1,by omega⟩⟩
     apply hr; change V e (Mount.rank r)-demand T e (Mount.rank r)=0
     rw [addition T A hE fun j a h _=>hi j a h,if_pos hL.1,show T r e=carry H V A e r from by unfold T patcher; rw [if_pos rfl,if_pos hL], (approval H h hs hA ho hL.1).2]; change _ - (demand A e _ +(V e _-demand A e _))=0;abel
   change V k i-demand T k i=0
   rw [demand_mates T A (fun j a hj _=>hi _ _ (by omega))]; exact ho k (by omega) i hP
 intro i r hi;rw [show T r i=A r i from patched H _ _ _ (by omega)]; exact hE i r (by omega)

variable (V)(T:Wheel G)
/-- k harvests through k, e increasing. -/
def carriage : ℕ→Castle G
| 0=>lonely T
| k+1=>patcher H V (carriage k) (k+1)
def sorted : Castle G:=fun r e=> Sedan.carriage H V T e r e

lemma toward (hg:G.Simple)(hs:Grimoire V)(h:AcademyL V)(hT:Honor G 2 T)(he:V 0=demand (lonely T) 0)(k:ℕ):
 Closed V (carriage H V T k) (k+1) ∧ Fair (carriage H V T k) ∧ overlooks (carriage H V T k) (k+1):=by
 induction k with
 | zero=>
    refine ⟨fun i hi j _ => ?_,loneliness hT,?_⟩
    · rw [show i=0 by omega, Pi.sub_apply,he,Sedan.carriage,sub_self]; rfl
    intro e r he;unfold Sedan.carriage lonely; split
    next hh=> rw [if_neg (by omega:e≠0)]
    next hh=>rfl
 | succ k ih=> exact Sedan.leg H h hg hs ih.2.1 ih.1 ih.2.2
lemma matching (r:ℕ){k e:ℕ}(h:e ≤ k):carriage H V T k r e=sorted H V T r e:=by
 induction k,h using Nat.le_induction with
 | base=>rfl
 | succ i hi ih=>rw [carriage,patched,ih];omega
lemma well_sorted (hg:G.Simple)(hs:Grimoire V)(h:AcademyL V)(hT:Honor G 2 T)(he:V 0=demand (lonely T) 0):
    Fair (sorted H V T) ∧ sorted H V T 0 0=T ∧ ∀ e n,0<n→demand (sorted H V T) e n= V e n:=by
 have hp:= toward H V T hg hs h hT he
 refine ⟨⟨fun r e h=> (hp e).2.1.rests r e h,fun r e=>(hp e).2.1.honor r e⟩,rfl,fun e n hn=>?_⟩
 rw [← demand_mates (carriage H V T e) _ (fun _ _ hj _=>matching H V T _ hj)]
 exact (sub_eq_zero.mp ((hp e).1 e (by omega) n hn : V e n-demand (carriage H V T e) e n=0)).symm

/-- Aperture explicit and independent-primitive law, scalar excluded. -/
theorem harvest (P:Patch)(K:KernelChoices)(A B:Bed)(C:Castle G)(Z:ChartRatio G)(h:P.Branches K G)(F:Foyer P K A B C Z)(T:Wheel G)(hT:Seed B T)(hg:G.Simple):
 let V:=-(Prism.vault G P K h C Z A B);let R:=sorted H V T; Fair R ∧ R 0 0=T ∧ ∀ e n,0<n→demand R e n= V e n:=by
 intro V R;obtain ⟨h1,h2,h3⟩:= consulate h hT F -- implicit A/B?
 exact well_sorted H V T hg h1 h2 hT.honor h3
end YM.RG08.Sedan
