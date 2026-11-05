import YM.UVExtension.Eyelet.Bows
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Eyelet
open Function Filter MeasureTheory Set Lattice Wilson RG Source Extra.Histories Labels
open Planned.GuardedAtom Guard Push Local MergeProof Next.Foundations Concert BoundedContinuousFunction
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n:Side}{d :ℕ} {F:Frame G d} {H: Hol G} {p: BudgetPoint}{R:Rep G n} {ι:Type}
variable {E Y:Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
section layer
variable {U: Type}{f:U→Type}[∀ i,NormedAddCommGroup (f i)][∀ i, NormedSpace ℂ (f i)]
omit [NormedSpace ℂ E] in
lemma sumL {F:ι→ E}{a:ι→ℝ} (hp:Summable a)(hc:∀ i,‖F i‖≤a i): ‖∑' i,F i‖≤∑' i,a i:=by
   have hV: Summable fun i=>‖F i‖:= hp.of_nonneg_of_le (fun _=> norm_nonneg _) hc; exact (norm_tsum_le_tsum_norm hV).trans (hV.tsum_le_tsum hc hp)
variable {A:Type}[CompleteSpace E]
def NormSum {ι:Type}(f:ι→E)(a:E):Prop:=Summable (fun i=> ‖f i‖) ∧ HasSum f a
omit [NormedSpace ℂ E] in
lemma insured (L:U→ Type)[∀ i,NormedAddCommGroup (L i)] (F: (i:U)→ (L i)→ E) (f:↥(lp L 1)) {u:ℝ} (h:∀ i,‖F i (f i)‖ ≤ u * ‖f i‖) : NormSum (fun i=> F i (f i)) (∑' i,F i (f i))∧ ‖∑' i,F i (f i)‖≤ u*‖f‖:= by
    have hp:= (castL f).mul_left u
    have he := hp.summable.of_norm_bounded h; have hv:=hp.summable.of_nonneg_of_le (fun i=> norm_nonneg _) h
    exact ⟨⟨hv,he.hasSum⟩,(norm_tsum_le_tsum_norm hv).trans ((hv.tsum_le_tsum h hp.summable).trans_eq hp.tsum_eq)⟩
end layer

abbrev TagI := Eyelet.Slot n
abbrev supE (p:BudgetPoint) (i:Eyelet.Slot n) := Concert.Tap p G 0 i.1.val

def flash (H:Hol G)(d:ℕ)(p:BudgetPoint)(i:Eyelet.Slot n) (k:supE (G:=G) p i) : (Gondola d H i.1 p)→L[ℂ] ℂ:= (evalCLM ℂ k).comp (boxes (tin d H i.1 p)).subtypeL

def burn (G:Gauge)(p:BudgetPoint)(n:Side)(i:StockTag n) (U: Lab G n) : (Stream G p i)→L[ℂ] ℂ:= (evalCLM ℂ U).comp (boxes (sink (G:=G) p i)).subtypeL

lemma flashes (H:Hol G)(p:BudgetPoint)(i:Eyelet.Slot n) (k:supE (G:=G) p i) {x:Birth H i.1 p d}: flash H d p i k (twig _ x)= k.read x.val:=rfl
lemma sizzles (i:StockTag n) {x:Bolt (G:=G) p i} (U:Lab G n) : burn G p n i U (twig _ x)=x.val U.tag:=rfl

lemma Gondola.ext {p:BudgetPoint} (i:Eyelet.Slot n)(x y:Gondola d H i.1 p) (h:∀ k:supE (G:=G) p i, flash H d p i k x=flash H d p i k y): x=y:= Subtype.ext (DFunLike.ext _ _ h)
lemma Stream.ext {p:BudgetPoint} (i:StockTag n)(x y:Stream G p i)(h:∀ U, burn G p n i ⟨U⟩ x=burn G p n i ⟨U⟩ y): x=y:= Subtype.ext (DFunLike.ext _ _ (fun ⟨x⟩=>h x))
variable (H d p)

def gaze (i:Eyelet.Slot n) (k:supE (G:=G) p i) : Roc d H n p→L[ℂ] ℂ:= (flash H d p i k).comp (lp.evalCLM ℂ _ 1 i)

def tire (i:StockTag n)(U:Lab G n): Coil G n p→L[ℂ] ℂ:= (burn G p n i U).comp (lp.evalCLM ℂ _ 1 i)
lemma Roc.ext (x y:Roc d H n p) (h:∀ i t,gaze (d:=d) H p i t x=gaze (d:=d) H p i t y): x=y:= lp.ext (funext fun i=> Gondola.ext i (x i) (y i) (h i))
lemma Coil.ext (x y: Coil G n p) (h:∀ i t,tire p i ⟨t⟩ x=tire p i ⟨t⟩ y): x=y:= lp.ext (funext fun i=> Stream.ext i (x i) (y i) (h i))
variable {H d p}

namespace Eligible
variable {Q:Coefficient F n} {v:ℝ}(h:Eligible Q H R v)
lemma take (i:Eyelet.Slot n)(z:supE (G:=G) R.p i) : gaze d H R.p i z h.tollE=(fee R.p i.1.val:ℂ)*z.read (graft Q i):=rfl
lemma make (i:StockTag n)(U:Lab G n) : tire R.p i U h.tollK=((fee R.p i.val.1/v:ℝ):ℂ)*profile R.activities Q.forced i.val U.tag:=rfl
lemma blankC {x:F.Coeff}(h: Eligible (primary (F:=F) 0 x) H R v) : h.tollE=0 ∧ h.tollK=0 := by -- primary name
  refine ⟨Roc.ext _ _ _ _ _ fun i t=>?_,Coil.ext _ _ _ fun i t=>?_⟩
  · rw [take,map_zero]; rw [show graft (primary (F:=F) 0 x) i = 0 from ?_]; rw [Tap.read,show (0:Config G n→ℂ)=(fun _=>0) from rfl,Work.G07.left_const]; split <;>simp
    unfold graft; split <;> rfl
  rw [make,map_zero]; simp [profile,cram,Extra.Histories.primary]
end Eligible
end YM.UVExtension.Eyelet
