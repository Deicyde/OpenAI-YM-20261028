import YM.RG08.Prism.Frost
import YM.RG08.Atlas.Plume
import YM.RG08.Gallery.Call

/-!
# Transfer to bulk positively ranked tape through support. No assertions at regulator scalar r=0.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Prism
open Function Matrix Lattice Exterior Stationary RG Laurent Fold Glyph Room Camera Steam Finset Bloch Mount Drum Forms
open Rows Pert.Bulk Packets Isles
open Precision RG Wilson Tack Tree Filter Gallery MvPolynomial
open scoped Classical Matrix ContDiff Topology BigOperators InnerProductSpace PowerSeries ENNReal
variable {I J U:Type}[Fintype I][Fintype J][Fintype U]

def under (L:Matrix U U ℝ): Grain U:=fun e n => if hz:n=2 then if e=0 then fun x=>(-1/2:ℝ)*L (x ⟨0,by omega⟩) (x ⟨1,by omega⟩) else 0 else 0
lemma ledger_K (L:Matrix U U ℝ): Glyph.stock (under L)=liftInn (Fold.shelter L MvPolynomial.X):=by
 ext e:1;rw [Glyph.stock,PowerSeries.coeff_mk,liftInn,PowerSeries.coeff_C]
 split_ifs with he
 · subst e
   unfold Glyph.showV under; rw [sum_eq_single_of_mem 2 (by decide) (fun i hi ih=>by rw [dif_neg ih,parley_zero]),dif_pos rfl, if_pos rfl]
   unfold Glyph.parley Fold.shelter word
   rw [← (Fin.consEquiv (fun _:Fin 2=>U)).sum_comp,Fintype.sum_prod_type,Finset.smul_sum];apply Finset.sum_congr rfl;intro i _
   rw [←(Equiv.funUnique (Fin 1) U).symm.sum_comp, Finset.smul_sum];apply Finset.sum_congr rfl;intro j _; simp_rw [Fin.prod_univ_two,smul_smul];rfl
 unfold showV under; apply Finset.sum_eq_zero; intro n _;simp_rw [if_neg he];split <;> exact parley_zero

def polar (A:Kernel U U)(x:Tape 2 (Market U)):ℝ:= -(1/2:ℝ)*(A (x 0) (x 1))
def bare (A:Kernel U U):Grain (Market U):=fun e n=>if hi:n=2 then if e=0 then Steam.move hi.symm (polar A) else 0 else 0
lemma bivered (U:Grain I)(T:Grain I):Glyph.stock (U+T)=Glyph.stock U+Glyph.stock T:=by ext e:1;rw [map_add,Glyph.stock,PowerSeries.coeff_mk,Glyph.stock,PowerSeries.coeff_mk,Glyph.stock,PowerSeries.coeff_mk];unfold showV; rw [← sum_add_distrib];exact Finset.sum_congr rfl (fun n _=>parley_add ..)

variable (G:Gauge)(P:Patch)(K:KernelChoices)(h:P.Branches K G)(C:Castle G)(B:ChartRatio G)(A A':Bed)(n:Side)

def mill :Grain (Market (Loc G 1)):= Steam.allG (Prism.ice P K A) (inlet h C B) (Prism.rains P K A)
def maiden :Grain (Lines G n 1):=Steam.allG (winterGreen P K A n) (unveil (inlet h C B) n) (springGreen P K A n)
def alum :Kernel (Loc G 1) (Loc G 1):= Cell.color G (Flat.output A')
lemma mill_rate (hc:Mount.Stable C){σ p:ℝ}(ht:Cell.Warm G K P A σ p)(hp:0<σ)(hn:σ ≤ 1): Grafted (fun i=>maiden G P K h C B A (chain i)) (mill G P K h C B A):=by
 obtain ⟨hi,hy⟩:=Prism.ready_roads P K A ht hp hn
 have hh:= Isles.tagged hi hp
 have he:=Isles.tagged hy hp
 let X:=inlet h C B;have hE:=inlet_eligible h B hc
 intro e u hu t
 have hS k:slaw X k:=by
   by_cases C0:0<k
   · have hd:=((castle_room P C hc k).add (bell_room h k)).neg.add (dusk_room P B k)
     intro n; convert hd n using 1;rw [show X k n=ghost h C B k n by unfold X inlet;rw [if_pos C0]]; rfl
   intro n;refine ⟨1,0,zero_lt_one,le_rfl,?_⟩;unfold X inlet; rw [if_neg C0];exact zero_held
 obtain ⟨α,hA,hV⟩:=hedgeline X e hE (legal_inlet h B hc) hS
 let θ:=min σ α; have hT:0<θ:=lt_min hp hA
 have hw:Isles.seats θ (fun i=> unveil (hedge e X) (chain i)) (hedge e X):=fun j k=>by obtain ⟨B,H⟩:=hV j k;exact ⟨B,H.mono hT (min_le_right ..) le_rfl⟩
 obtain ⟨b0,H⟩:=cooling hw ((hh.mono hT (min_le_left ..) le_rfl).line) (he.mono hT (min_le_left ..) le_rfl) e u
 have hv:= H.light hu t
 simp_rw [←hedge_unveil,all_hedge _ _ u e le_rfl] at hv
 have hj (i:ℕ) : allG (winterGreen P K A (chain i) (G:=G)) (hedge e (unveil X (chain i))) (springGreen P K A (chain i) (G:=G)) e u=maiden G P K h C B A (chain i) e u:=all_hedge _ _ _ _ le_rfl
 -- erw by taking pointwise functions
 change Tendsto (fun i=> (maiden G P K h C B A (chain i)) e u ((carpetRoad (Loc G 1)).visit i ∘ t)) _ _
 convert hv using 2
 exact congrFun (hj _).symm _
 rfl

lemma certified {σ p:ℝ}(he: A'.metric.strip σ p)(hh:0<σ)(ht:σ ≤ 1)(hp:0 ≤ p):Tagged σ (Flat.sumToken*(Fintype.card Faces*p)) (alum G A') (fun n=>patron G (Precision.K (A'.metric.acts n))):=by -- names from Cast; tag color requires ColorIndex n.
 obtain ⟨hy,hm⟩:= Flat.output_cost he hp hh.le ht
 refine Cell.color_tagged G (⟨⟨?_,?_,hy,?col⟩,hm⟩)
 · exact mul_nonneg Flat.sumToken_pos (mul_nonneg (Nat.cast_nonneg _) hp)
 · exact Cell.output_city A'
 case col=> exact Cell.col_of_row (Cell.output_city A') hy

lemma graft_under (g:Kernel U U)(T:∀ P:Side,Matrix (Co P U) (Co P U) ℝ){σ p:ℝ}(hh: Tagged σ p g T)(he:0 < σ): Grafted (fun i=>under (T (chain i))) (bare g):=by
 have ht:= Isles.tagged hh he
 intro i j hj A
 by_cases hz:j=2
 · subst j;by_cases he:i=0
   · subst i;simp only [under,bare,Steam.move,neg_div];exact ((ht.light (A 0) (A 1)).const_mul (-(1/2:ℝ)))
   simp [under,bare,he]
 simp [under,bare,hz]
def vault (A':Bed): Grain (Market (Loc G 1)):=bare (alum G A')+mill G P K h C B A
def tray (A':Bed)(n:Side): Grain (Lines G n 1):=under (patron G (Precision.K (A'.metric.acts n)))+maiden G P K h C B A n
lemma graft_vault (hc:Mount.Stable C){σ p τ u:ℝ}(ht:Cell.Warm G K P A σ p)(hp:0 < σ)(hn:σ ≤ 1)(he: A'.metric.strip τ u)(hE:0 < τ)(hU:τ ≤ 1)(hB:0 ≤ u):Grafted (fun i=> tray G P K h C B A A' (chain i)) (vault G P K h C B A A'):=by
 intro i k hh x; exact ((graft_under _ _ (certified G A' he hE hU hB) hE) i k hh x).add (mill_rate G P K h C B A hc ht hp hn i k hh x)
lemma deployed {σ p:ℝ}(ht:Cell.Warm G K P A σ p):Glyph.stock (tray G P K h C B A A' n)=Prism.col (grace G (Line.habitat P K n) (Line.green _) A A') (fir (Line.habitat P K n)) (unveil (inlet h C B) n):=by
 rw [tray,bivered,ledger_K,Prism.col];unfold maiden;rw [← ready_mean P K A A' n ht,←ready_phases P K A A' n ht];rfl
end YM.RG08.Prism
