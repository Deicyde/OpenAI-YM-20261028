import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Stigma

/-!
# One cost with actual drow supports including all Q

A cost in one oriented actual patch. Complement in kernel space uses
branches. Values. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.LocalRows
open Filter Function Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented  Sector SliceRows.DataKernel
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f n d : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {x : ℝ} {L : Side}
variable {V W Q Q' : Config G c} {U U' : Config G f}
variable (h : Room P S T x)

omit h in
private lemma landsZ {ι : Type} [Fintype ι] (D : Config G c→ι→Twin c→Pay G) (u v : ι→G.Color) (p : ι→Site c)
    (j : Twin c) {R : ℕ} (hr : Rule R D p (fun i=> i.1.1)) (hp : AgreeNear id j.1.1 (2*R) V W) (he :
      ∀ i, separation j.1.1 (p i)≤R → u i=v i) : unzip (D V) u j=unzip (D W) v j := by
  unfold unzip; refine sum_congr rfl fun i _=> ?_
  by_cases h : separation j.1.1 (p i) ≤ R
  · rw [he i h,hr.stencil i V W (hp.shrink (by omega)) j]
  have hf Z := not_imp_not.mpr (hr.reach Z i j) (show ¬ separation (p i) j.1.1 ≤ R by rwa [separation_comm])
  rw [not_ne_iff.mp (hf _), not_ne_iff.mp (hf _), map_zero,_root_.zero_apply, _root_.zero_apply]

include h in
private lemma coarse_works (p : Cell c)
    (he : AgreeNear id p.1 (radiusB x/2) V W) (hq : AgreeNear id p.1 (radiusB x/2) Q Q')
    (hf : AgreeNear S.ratio.parent p.1 (radiusB x/2) U U') :
    let u:=Pressure.temp x; let R:=till x
    T.workL R U Q V u p=T.workL R U' Q' W u p ∧ T.workC R V u p=T.workC R W u p ∧ T.workD R V u p=T.workD R W u p := by
  intro u R
  let D := radiusB x; let o (j : Twin c):= j.1.1; let a (q : Twin f):= S.ratio.parent q.1.1
  have hu : 100 ≤ D := h.sight.1
  have hr : 4*R+4 ≤ D/100 := by have he:= h.sight; unfold R D; omega
  have H := he.shrink (D':=2*R) (q':=p.1) (by rw [separation_self]; change 0+_ ≤ D/2; omega)
  have ⟨hh,hy⟩ := coastfront h p (he.shrink (by rw [separation_self]; omega))
  have hX i : T.Xn R V (p,i)=T.Xn R W (p,i) := plotted_near id (sep_step (c:=c)) V W T.low T.down R S.patch.L.val (p,i) S.patch.L.property
    (he.shrink (by change separation p.1 p.1+(R+4)≤ D/2; rw [separation_self]; omega))
  have ha : Rule R (T.Φ R) a o := crosses R T P h.accepted
  have hl : Rule R (T.Φ' R) Prod.fst o := sameLevel _ _ S.patch.L.property T.R.mn (Row.rights _ _ h.accepted.crosses.1 P.width.le) pole mesh
  have hv : Rule R (T.N R) Prod.fst o := sameLevel _ _ S.patch.L.property T.R.o (Row.rights _ _ h.accepted.crosses.2.1 P.width.le) id mesh
  have hk (i) (hi : separation p.1 (a i)≤R) : AgreeNear id (a i) (D/4) V W := he.shrink (by change _ ≤ D/2; omega)
  have hp y (hi : separation p.1 y ≤ R) : AgreeNear id y (D/4) V W := he.shrink (by change _≤ D/2; omega)
  have hF i (hi : separation p.1 (a i) ≤ R) : T.Xf R U i=T.Xf R U' i := plotted_near _ (parent_step S) U U' T.high T.up R 1 i le_rfl
    (hf.shrink (by change separation p.1 (a i)+_ ≤ D/2; omega))
  have hQ (i : Bond c) (hi : separation p.1 i.1 ≤ R) : Tube.Z S Q V i=Tube.Z S Q' W i := by
    have hs : separation p.1 i.1 ≤ radiusB x/2 := by change _≤ D/2; omega
    unfold Tube.Z; rw [he i hs,hq i hs]
  refine ⟨?_,?_,?_⟩
  · unfold Tube.workL; refine sum_congr rfl fun i _=> ?_
    rw [show T.vision R u V (p,i)=T.vision R u W (p,i) from hy i, hX i, landsZ _ _ _ _ (p,i) ha H hF, landsZ _ _ _ _ (p,i) hl H hQ]
  · unfold Tube.workC; simp_rw [show crown T.down T.low R _ u V p=_ from hh]; congr 1
    exact sum_congr rfl fun i _=> by rw [show T.vision R u V (p,i)=T.vision R u W (p,i) from hy i,hX i]
  unfold Tube.workD; refine sum_congr rfl fun i _=> ?_
  -- glossary
  rw [show T.vision R u V (p,i)=T.vision R u W (p,i) from hy i, landsZ (u:=T.Mv R u V) (v:=T.Mv R u W) _ _ (p,i) ha H (fun j hj => sharePay h _ _ ha _ (hk j hj)),
    landsZ (u:=T.Mw R u V) (v:=T.Mw R u W) _ _ (p,i) hl H (fun j hj=> sharePay h _ _ hl j (hp _ hj)),
    landsZ (u:=zip (T.N R V) (T.vision R u V)) (v:=zip (T.N R W) (T.vision R u W)) _ _ (p,i) hv H (fun j hj=> sharePay h _ _ hv j (hp _ hj))]

include h in
lemma broad (p : Spot c f)
    (he : AgreeNear id (lead S p) (radiusB x/2) V W) (hq : AgreeNear id (lead S p) (radiusB x/2) Q Q')
    (hf : AgreeNear S.ratio.parent (lead S p) (radiusB x/2) U U') :
    principal T x U V Q p=principal T x U' W Q' p := by
  let R:= till x; let B:= radiusB x/2; let t:= Pressure.temp x
  rcases p with p|p|p|p
  · let u:=Pressure.fiery G x S.patch.L; let o:=S.ratio.parent p.1
    change T.workF R U V u t p=T.workF R U' W u t p; unfold Tube.workF
    rw [ufront h p (hf.shrink (by change separation o o+_≤_; rw [separation_self]; omega))]
    refine congrArg₂ (·+·) (show crown _ _ _ _ _ _ _=crown T.up T.high R 1 u U' p from rfl) ?_
    refine sum_congr rfl fun i _=> ?_
    let p':= (p,i)
    have hx := costsX h (.inl p') (he.shrink (by change separation o o+_ ≤_; rw [separation_self]; omega))
    rw [show T.Mv R t V p'=T.Mv R t W p' from hx]; rw [show T.Xf R U p'=T.Xf R U' p' from ?_]
    exact plotted_near _ (parent_step S) U U' T.high T.up R 1 p' le_rfl (hf.shrink (by
      change separation o o+(R+4)≤_; rw [separation_self]; have hh := h.sight; unfold R; omega))
  · have hv : separation (lead S (.inr (.inl p))) (id p.1) = 0 := separation_self _
    change T.workI R Q V t p=T.workI R Q' W t p; unfold Tube.workI monetary wire Tube.Z
    rw [show T.Mw R t V p=T.Mw R t W p from costsX h (.inr p) (he.shrink (by change separation p.1 p.1+_ ≤ _; rw [separation_self]; omega)),
      he p (by rw [hv]; omega),hq p (by rw [hv]; omega)]
  · have ⟨hv,hx,hy⟩ := coarse_works h p he hq hf
    change T.workC R V t p+_=T.workC R W t p+_; rw [hx,hv,hy]
  change ‖zip (T.N R V) _ p‖^2/2=‖zip (T.N R W) _ p‖^2/2; rw [sharePay h (T.N R) Prod.fst
    (sameLevel _ _ S.patch.L.property T.R.o (Row.rights _ _ h.accepted.crosses.2.1 P.width.le) id mesh) p
    (he.shrink (by change separation p.1 p.1+_ ≤_; rw [separation_self]; omega))]

include h in
lemma cloudy (p : Spot c f) (k k' : S.Choices) (he : AgreeNear id (lead S p) (radiusB x/2) V W)
    (hp : AgreeNear id (lead S p) (radiusB x/2) (S.prediction U k) (S.prediction U' k'))
    (hq : AgreeNear S.ratio.parent (lead S p) (radiusB x/2) U U') :
    yielding T x U V k p=yielding T x U' W k' p := by
  rcases p with p|p
  · change soft T x U V k p=soft T x U' W k' p
    let q:= S.ratio.parent p.1; have hv : 100 ≤ radiusB x := h.sight.1
    unfold soft; rw [facesight _ (parent_step S) U U' p (hq.shrink (by change separation q q+_≤_; rw [separation_self]; omega))]
    refine congrArg₂ (·+·) rfl ?_; apply sum_congr rfl; intro i _
    let p' : Rod c f:= .inl (p,i); unfold SliceRows.bill entryCost
    have he' : ∀ n, n ≤ radiusB x/2 → separation (lead S (.inl p)) (focus S p')+n ≤ radiusB x/2 := by
      intro n hn; change separation q q+n≤_; rw [separation_self,zero_add]; exact hn
    rw [costsX h p' (he.shrink (he' _ (by omega))), costsy h p' (he.shrink (he' _ (Nat.zero_le _)))
      (hp.shrink (he' _ (Nat.zero_le _))) (hq.shrink (he' _ (by omega)))]
  exact broad h (.inr p) he hp hq
end YM.ConnectedActivityE6.LocalRows
