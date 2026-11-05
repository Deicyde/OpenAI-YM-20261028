import YM.RG08.Mason.Edge
import YM.RG08.Supplies.Actual

/-! # Pre widths and length gates, order parallel. Ask widths before L!
 All arithmetic pre, eta_j and compiled functional. Entry cutoff horizon e ≤ J coarse, holding
 estimates at narrow OWN widths ν_{J_i}. -/
noncomputable section
namespace YM.RG08.Yamen
open Lattice Laurent Pert.Bulk Forms Room Carrel Steam Isles Rows Rate Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry Prism Quarry Roost Packets Ducat Mason Supplies
open scoped Classical Matrix BigOperators PowerSeries Topology
set_option autoImplicit false
variable (G:Gauge)(P X:MapPrices)(K:KernelChoices)
/-- thumbnail diagonal adjusts fitting J, J+1 neighbor. positive before L. -/
def trod (j:ℕ):=min (min (min 1 (P.α j)) (P.α (j+1))) (min (Supplies.Strip G P X K j) (Supplies.Strip G P X K (j+1)))
lemma trod_life (j):0<trod G P X K j:=lt_min (lt_min (lt_min (by norm_num) (P.alpha_pos _)) (P.alpha_pos _)) (lt_min (positive_strip _) (positive_strip _))
lemma trod_below (j):trod G P X K j ≤ 1:=min_le_left .. |>.trans ((min_le_left ..).trans (min_le_left ..))
-- individual width for arity e+2 (p supplied before exactly this)
private def granted (r:ℕ)(p:ℝ):= if h:0<p then (Spar.warehouse (I := G.ColorIndex) (n := r+1) p h (by omega) (Symmetry.dressed G (RG08.Mount.rank r)) (Symmetry.respects G _)).choose else 1
lemma granted_pos (r:ℕ){p:ℝ}(h:0<p):0<granted G r p:=by unfold granted; rw [dif_pos h]; exact (Spar.warehouse (I := G.ColorIndex) (n := r+1) p h (by omega) (Symmetry.dressed G (RG08.Mount.rank r)) (Symmetry.respects G _)).choose_spec.choose_spec.1

private def picker (f:ℕ→ℝ):ℕ→ℝ
| 0=>f 0
| j+1=>min (picker f j) (f (j+1))
private lemma pick_life (f:ℕ→ℝ)(h:∀ i,0<f i)(e):0<picker f e:=by induction e with
 | zero=>exact h 0
 | succ i hi=>exact lt_min hi (h (i+1))
private lemma pick_upper (f:ℕ→ℝ){e p:ℕ}(hp:p ≤ e):picker f e ≤ f p:=by induction e with
 | zero=>
          obtain rfl:p=0:=by omega
          apply le_rfl
 | succ i hi=> by_cases h:p ≤ i
               · exact (min_le_left ..).trans (hi h)
               have he:p=i+1:=by omega
               subst p; exact min_le_right ..

def rise (j:ℕ)(e:ℕ):ℝ:= trod G P X K j / (8*((e:ℝ)+1))
def promise (p:ℕ)(w:ℝ):=granted G p w/(p+2:ℕ)/32
-- maintain antitone property and capacity vs same-degree ranks via rise. 0 simply use trod.
def honesty (j:ℕ):ℕ→ℝ
 | 0=>rise G P X K j 0
 | n+1=> let w:=honesty j n; min (min (rise G P X K j (n+1)) w) (picker (fun p=>promise G p w) n)
lemma honesty_pos (j n):0<honesty G P X K j n:=by
 have hr(i):0<rise G P X K j i:=div_pos (trod_life ..) (by positivity)
 induction n with
 | zero=>exact hr 0
 | succ n hn=>
   exact lt_min (lt_min (hr (n+1)) hn) (pick_life _ (fun i=>by unfold promise;have he:=granted_pos G i hn;positivity) _)
lemma honesty_rise (j e):honesty G P X K j e ≤ rise G P X K j e:=by cases e;exact le_rfl; exact (min_le_left ..).trans (min_le_left ..)
lemma honesty_small (j e): honesty G P X K j e ≤ trod G P X K j:= (honesty_rise ..).trans (div_le_self (trod_life ..).le (by linarith [Nat.cast_nonneg (α:=ℝ) e]))

def atlas (j:ℕ):Yard G:= Sedan.paving (fun n _=> honesty G P X K j n) (fun n _=>honesty_pos _ _ _ _ _ n)
lemma registered (j e r:ℕ):(Yamen.atlas G P X K j).coats e r = granted G r (honesty G P X K j e):=by unfold Yamen.atlas Sedan.paving granted; rw [dif_pos (honesty_pos ..)]
lemma compulsory (j:ℕ){n e:ℕ}(h:e<n)(p:ℕ)(hp:p ≤ e): honesty G P X K j n ≤ ((Yamen.atlas G P X K j).coats e p)/(RG08.Mount.rank p:ℕ)/32:=by
 induction n with
 | zero=>omega
 | succ n hi=>
   by_cases he:e=n
   · subst he;rw [registered];exact (min_le_right ..).trans (pick_upper _ hp)
   exact ((min_le_left ..).trans (min_le_right ..)).trans (hi (by omega))

-- grade radii meet all adjacent arms if L sufficiently large pre. floor width ω & cost.
def brim (j i:ℕ) := min 1 (min (P.α j) (P.α i))
abbrev gleam (j i:ℕ):= allotment P j i
-- B bound for both T,T' before L varies with j period. depends only on Ω clipped.
def basis (j:ℕ):= (Yamen.atlas G P X K j).cash 0 0 * Cast.funds G (max 0 (P.Ω j))
lemma basis_nn (j:ℕ):0 ≤ basis G P X K j:=by
 unfold basis Cast.funds Cast.tax
 have h:=((Yamen.atlas G P X K j).tag 0 0).2.2.1;have he :0 ≤ max 0 (P.Ω j):= le_max_left ..;have hx:=Flat.sumToken_pos; positivity
variable {G P X K}
lemma stepN {a:Levels G}(i:ℕ) : a.clock.J (i+1)=a.clock.J i ∨ a.clock.J (i+1)=a.clock.J i+1:=by have ht:=a.fits.mono (show i ≤ i+1 by omega);have he:=a.fits.stepSlow i;omega
lemma brim_credit {i j:ℕ}(h:j=i∨j=i+1):trod G P X K i ≤ brim P j i:=by
 unfold brim trod; refine le_min (trod_below ..) (le_min ?_ ?_) <;> cases h <;> rename_i he <;> try rw (config:={occs:=.all}) [he] -- occurrence i+ maybe rw fails goals w/o j
 all_goals grind
lemma warmth {i j:ℕ}(h:j=i∨j=i+1):trod G P X K i ≤ Supplies.Strip G P X K j:=by cases h with | inl h=> rw [h];exact (min_le_right ..).trans (min_le_left ..)
                                                                                                      | inr h=>rw [h];exact (min_le_right ..).trans (min_le_right ..)
lemma curvature (i:ℕ){r e:ℕ}(h:r ≤ e): 4*honesty G P X K i e ≤ trod G P X K i ∧ ((r+1:ℕ):ℝ)*(4*honesty G P X K i e) ≤ trod G P X K i:=by
 have ht:= honesty_rise G P X K i e; have hf:= honesty_pos G P X K i e
 unfold rise at ht; have he:= (le_div_iff₀ (by positivity)).mp ht
 have hz:( (r:ℝ)+1) ≤ (e:ℝ)+1:=by exact_mod_cast Nat.succ_le_succ h
 push_cast; constructor <;> nlinarith only [he,hz,Nat.cast_nonneg (α:=ℝ) r,hf]
end YM.RG08.Yamen
