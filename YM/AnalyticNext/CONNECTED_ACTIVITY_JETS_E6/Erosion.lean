import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Scroll
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Stigma


/-!
# Unmasked equations local, even away from toggle domain

Apply to price from nearby gauges: formula agrees on stencil,
without needing true `ρ` there. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Frond
open Filter Function Lattice RG Pressure Pressure.Tube Pressure.Stores Work.E03 Work.F03 Exterior Wilson Push Push.AbsoluteSums Finset
open Precision Shell Channel Next.Fluctuations Bloch Laurent SliceRows Mask Coat SliceRows.DataKernel Scroll   LocalRows
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical InnerProductSpace
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S}
variable {V V' Q Q' : Config G c} {U U' : Config G f} {x : ℝ} {P : Teller G}
variable (h : Room P S T x)

private lemma clearsV {ι : Type} (F : Config G c → ι → Twin c→ Pay G) (o : ι→Site c)
    (h : Rule (till x) F o (fun i=>i.1.1)) (p : Room P S T x)
    (i : ι) (he : AgreeNear id (o i) (radiusB x/4) V V') :
    zip (F V) (T.Xn (till x) V) i=zip (F V') (T.Xn (till x) V') i := by
  unfold zip; apply sum_congr rfl; intro j _
  rw [h.stencil i V V' (he.shrink (by rw [separation_self]; have hj:=p.sight; omega)) j]; by_cases hb : F V' i j=0
  · simp only [hb,_root_.zero_apply]
  suffices hh : T.Xn (till x) V j=T.Xn (till x) V' j by rw [hh]
  exact plotted_near id (sep_step (c:=c)) V V' T.low T.down _ _ j S.patch.L.property (he.shrink
    (by have hz:=h.reach V' i j hb; change separation (o i) j.1.1 +_ ≤_; have he:=p.sight; omega))

include h
lemma shoreVisa (p : Rod c f) (he : AgreeNear id (focus S p) (radiusB x/4) V V') :
    visual T (till x) V p=visual T (till x) V' p := by
  rcases p with i|i
  · exact clearsV _ _ (crosses _ T P h.accepted) h i he
  exact clearsV _ _ (sameLevel _ _ S.patch.L.property T.R.mn (Row.rights _ _ h.accepted.crosses.1 P.width.le)
    pole mesh) h i he

omit h in
private lemma clearsD {ι : Type} [Fintype ι] (F : Config G c → ι → Twin c→ Pay G) (o : ι→Site c)
    {a b : ι → G.Color} (h : Rule (till x) F o (fun i=>i.1.1)) (p : Room P S T x) (i : Twin c)
    (he : AgreeNear id i.1.1 (radiusB x/4) V V') (hp : ∀ j,separation i.1.1 (o j) ≤ till x→ a j=b j) :
    unzip (F V) a i=unzip (F V') b i := by
  unfold unzip; apply sum_congr rfl; intro j _; by_cases hg : separation i.1.1 (o j) ≤ till x
  · rw [hp j hg,h.stencil j V V' (he.shrink (by have ht:=p.sight; omega))]
  have hx (V : Config G c): F V j i=0 := by by_contra hh; rw [separation_comm] at hg; exact hg <| h.reach V j i hh
  rw [hx _,hx _,map_zero]; simp

private lemma shoresT (i : Cell c) (he : AgreeNear id i.1 (radiusB x/2) V V')
    (hu : AgreeNear S.ratio.parent i.1 (radiusB x/2) U U') (hp : AgreeNear id i.1 (radiusB x/2) Q Q') :
    let R:=till x
    stormC T V i=stormC T V' i ∧ stormL T R U Q V i=stormL T R U' Q' V' i ∧ stormD T R V i=stormD T R V' i := by
  intro R; have hx := h.sight
  let a (u : Twin c) := u.1.1
  have hv : Rule R (T.Φ R) (fun i=> S.ratio.parent i.1.1) a := crosses R T P h.accepted
  have hz : Rule R (T.Φ' R) Prod.fst a := sameLevel _ _ S.patch.L.property T.R.mn (Row.rights _ _ h.accepted.crosses.1 P.width.le) pole mesh
  have hy : Rule R (T.N R) Prod.fst a := sameLevel _ _ S.patch.L.property T.R.o (Row.rights _ _ h.accepted.crosses.2.1 P.width.le) id mesh
  have hF : faceValue V i=faceValue V' i := facesight id (sep_step (c:=c)) V V' _ (he.shrink (by change separation i.1 i.1+4≤_; rw [separation_self]; omega))
  have hE x' (hp : separation i.1 x'≤R) : AgreeNear id x' (radiusB x/4) V V' := he.shrink (by unfold R at hp; omega)
  have ha : AgreeNear id i.1 (radiusB x/4) V V' := hE i.1 (by simp)
  have hh j : T.Xn R V (i,j)=T.Xn R V' (i,j) := plotted_near id (sep_step (c:=c)) V V' T.low T.down R _ (i,j) S.patch.L.property
    (ha.shrink (by change separation i.1 i.1+ (R+4)≤_; rw [separation_self]; unfold R; omega))
  refine ⟨by unfold stormC; rw [hF],?_,?_⟩
  · unfold stormL; apply sum_congr rfl; intro j _
    rw [hh j, clearsD _ _ hv h (i,j) (b:=T.Xf R U') ha ?_, clearsD _ _ hz h (i,j) (b:=Tube.Z S Q' V') ha ?_]
    swap
    · intro b h;  exact plotted_near _ (parent_step S) U U' T.high T.up R 1 b le_rfl (hu.shrink (by
          unfold R; change separation i.1 (S.ratio.parent b.1.1) ≤ R at h; unfold R at h; omega))
    intro b h; have hc : separation i.1 (id b.1) ≤ radiusB x/2 := by change separation i.1 b.1 ≤ _; change separation i.1 b.1≤R at h; unfold R at h; omega
    unfold Tube.Z; rw [hp b hc, he b hc]
  unfold stormD; apply sum_congr rfl; intro j _
  rw [hh j, clearsD _ _ hv h (i,j) ha (a:=canopyF T R V) (b:=canopyF T R V') (fun j hj=> clearsV _ _ hv h j (hE _ hj)),
    clearsD _ _ hz h (i,j) ha (a:=canopyI T R V) (b:=canopyI T R V') (fun j hj=> clearsV _ _ hz h j (hE _ hj)),
    clearsD _ _ hy h (i,j) ha (a:=canopyN T R V) (b:=canopyN T R V') (fun j hj=> clearsV _ _ hy h j (hE _ hj))]

lemma rivers (p : Spot c f) (q q' : S.Choices) (he : AgreeNear id (lead S p) (radiusB x/2) V V')
    (hu : AgreeNear S.ratio.parent (lead S p) (radiusB x/2) U U') (hp : AgreeNear id (lead S p) (radiusB x/2)
      (S.prediction U q) (S.prediction U' q')) (v : Bool) : loft T x U q V v p=loft T x U' q' V' v p := by
  let o:= lead S p; let R:=till x; have hv := h.sight
  have hx (i:Rod c f) (hi : focus S i=o) : effective T R U (S.prediction U q) V i=effective T R U' (S.prediction U' q') V' i := by
    have hg : separation (lead S p) (focus S i)=0 := hi ▸ separation_self _
    exact congrArg₂ (· - ·) (costsy h i (he.shrink (by omega)) (hp.shrink (by omega)) (hu.shrink (by omega)))
      (shoreVisa h i (he.shrink (by omega)))
  rcases p with p|p|p|p
  · have hz : faceValue U p=faceValue U' p := facesight _ (parent_step S) U U' p (hu.shrink (by change separation o o+_≤_; rw [separation_self]; omega))
    cases v
    · change finest T R U _ V p=finest T R U' _ V' p; unfold finest; rw [ufront h _ (hu.shrink (by change separation o o+_≤_; rw [separation_self]; omega))]
      refine congrArg₂ (·+·) rfl (sum_congr rfl fun j _=> ?_)
      rw [show canopyF _ _ _ (p,j)=_ from shoreVisa h (.inl (p,j)) (he.shrink (by change separation o o+_≤_; rw [separation_self]; omega)),
        show T.Xf R U (p,j)=T.Xf R U' (p,j) from plotted_near _ (parent_step S) U U' T.high T.up R 1 (p,j) le_rfl (hu.shrink
          (by change separation o o+(R+4) ≤_; rw [separation_self]; unfold R; omega))]; rfl
    change flora T R U _ V p=flora T R U' _ V' p; unfold flora; rw [hz]; exact congrArg₂ (·+·) rfl
      (sum_congr rfl (fun j _=> congr_arg (fun F : G.Color=> ‖F‖^2/2) (hx (.inl (p,j)) rfl)))
  · change nora T R U _ V p=nora T R U' _ V' p; unfold nora; rw [hx (.inr p) rfl, hp p (by change separation o o≤_; simp), he p (by change separation o o≤_; simp)]
  · obtain ⟨h1,h2,h3⟩:= shoresT h p he hu hp; exact congr_arg₂ (· + ·) h1 (congr_arg₂ (· + ·) h2 h3)
  change ‖canopyN T R V p‖^2/2=_; exact congr_arg (fun v:G.Color=> ‖v‖^2/2) (clearsV (T.N R) Prod.fst
    (sameLevel _ _ S.patch.L.property T.R.o (Row.rights _ _ h.accepted.crosses.2.1 P.width.le) id mesh) h p
    (he.shrink (by change separation o o+_≤_; rw [separation_self]; omega)))
end YM.ConnectedActivityE6.Blaze.Frond
