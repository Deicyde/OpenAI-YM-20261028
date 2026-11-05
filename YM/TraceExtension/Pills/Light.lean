import YM.TraceExtension.Pills.Knick
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pills
open Function Filter Matrix Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Lamp
open Filch Turret Shepherd AnalyticBridge VerifiedReset Drupes Extra.Iteration SectorAffine Fen Kits
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n:Side}{I : Type}
abbrev Flop := Fin 2→ PlaqAxes
variable (L:Finset I)(P:I→Wo G) (h:∀ i∈L,(P i).Invariant)
def strum (a:Flop)(b:Cards G) :=∑ i∈ L,charge (P i) a b
def thud(a:Flop) (x:Axis)(b:Cards G):= ∑ i∈L,charge (P i) a b*delta (P i) x
def tint (a:Flop)(p:Cover)(c: Cards G→ℝ): Wo G:=⟨![Extra.Iteration.slot 0 (a 0),Extra.Iteration.slot p (a 1)],c⟩
lemma tint_k (a:Flop)(p:Cover)(c: Cards G→ℝ): delta (tint a p c)=p ∧ (fun k=>((tint a p c).leg k).plaq)=a:=⟨by simp [delta,tint],by funext k;fin_cases k<;>simp[tint]⟩
abbrev Colour := Flop × Option Axis
def ink : Colour→Wo G := fun i=>match i.2 with
 | none=> tint i.1 0 (-strum L P i.1 + ∑ x:Axis, thud L P i.1 x)
 | some x=>tint i.1 (step x) (-thud L P i.1 x)
def shade:= (P ⊕ᵥ ink L P)
def swat (L:Finset I):= L.disjSum (univ:Finset Colour)
lemma paint_ch (a q:Flop)(p:Cover)(c b): charge (tint a p c) q (b:Cards G)= if a=q then c b else 0:=by rw[charge,(tint_k ..).2]; rfl
private lemma note_h (i:Flop)(a:Option Axis) (b v) : charge (ink L P (b,a)) i v = if b=i then match a with|none=> -(strum L P b v)+(∑ x:Axis,thud L P b x v)|some x=>-thud L P b x v else 0:=by
    unfold ink; cases a <;> dsimp only <;> rw [paint_ch] <;> split_ifs <;> try rfl
private lemma tools (i:Flop)(a:Option Axis): delta (ink L P (i,a))=match a with|none=>0|some x=>step x:=by cases a <;> exact (tint_k ..).1
lemma valid : hush (swat L) (shade L P):=by
    intro a v
    constructor
    · change (∑ i∈swat L,charge _ _ _)=0; rw [swat,sum_disjSum]
      change strum L P a v+(∑ i:Colour, charge _ _ _)=_
      rw [Fintype.sum_prod_type,sum_eq_single a]; rotate_left
      · intro x _ hp; simp [shade,note_h,hp]
      · simp
      simp only[shade,Sum.elim_inr,note_h,if_true,eq_self]; rw [Fintype.sum_option]; simp only[sum_neg_distrib]; abel
    intro x; rw[swat,sum_disjSum]; change thud L P a x v+(∑ i:Colour,charge (ink L P i) a v * (delta (ink L P i) x:ℝ))=_
    rw [Fintype.sum_prod_type,sum_eq_single a]; rotate_left
    · intro x _ he; simp [note_h,he]
    · simp
    rw [Fintype.sum_option]; simp only [note_h,tools,if_true]; simp[step_apply,mul_ite]
-- invariance of successive label. arbitrary coefficients at finite roots.
private def clo(G:Gauge):Submodule ℝ (Cards G→ℝ) where
    carrier:= setOf fun F=>∀ u:G.El,∀ X:Fin 2→ G.Color, ∑ b:Cards G,F b * (∏ k,(G.adjoint u (X k)) (b k)) = ∑ b:Cards G,F b*(∏ k,X k (b k))
    zero_mem':=by simp
    add_mem':=by
        intro F H hp hv u X; simp only[Pi.add_apply, add_mul,Finset.sum_add_distrib]; exact congr_arg₂ _ (hp u X) (hv u X)
    smul_mem':=by intro c F h u X; simp only[Pi.smul_apply,smul_eq_mul,mul_assoc,← Finset.mul_sum,h u X]
include h
lemma pristine (c:Colour): (ink L P c).Invariant:=by
    rcases c with ⟨c,a⟩
    have hv(i)(hi:i∈L) : charge (P i) c ∈ clo G:=by
        by_cases hx:(fun k=> ((P i).leg k).plaq)=c
        · rw[show charge (P i) c=(P i).coeff from funext fun _=> if_pos hx]; exact h i hi
        rw [show charge (P i) c=0 from funext fun _=> if_neg hx]; exact (clo G).zero_mem
    have hh (x:Axis): thud L P c x ∈ clo G:=by
        rw[show thud L P c x=(∑ i∈L, (↑(delta (P i) x):ℝ) • charge (P i) c) from funext (fun i=>by unfold thud; rw[Finset.sum_apply]; exact sum_congr rfl fun _ _=>mul_comm ..)]
        exact (clo G).sum_mem fun i hi=> (clo G).smul_mem _ (hv _ hi)
    cases a with
    | none=>
        change -strum L P c +∑ x:Axis,thud L P c x∈clo G; refine (clo G).add_mem ((clo G).neg_mem ?_) ((clo G).sum_mem (fun i _=>hh i)); rw [show strum L P c=∑ i∈ L,charge (P i) c from funext fun x=>(Finset.sum_apply ..).symm]; exact (clo G).sum_mem hv
    | some x=> exact (clo G).neg_mem (hh x)
omit h
lemma ink_length(c:Colour): (ink L P c).length ≤ 10:=by
    have hp(a:Flop)(b:Cover)(v:Cards G→ℝ): (tint a b v).length= 8+ size b:=by simp [Atom.length,tint,Laurent.size,Fin.sum_univ_two]; omega
    rcases c with ⟨q,v⟩; unfold ink; cases v
    · simp [hp,Laurent.size]
    rename_i x; simp[hp, show Laurent.size (step x) =1 from step_size (posDir x)]
end YM.Trace.Pills
