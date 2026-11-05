import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Rainbows
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Scroll


/-!
# Symmetries on analytic Polar formula (even off healthy test)

Use gauge **at anchor** for analytic comparison (flat extrapolation).
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Frond
open Filter Function Lattice RG Pressure Pressure.Tube Pressure.Stores Work.E03 Work.F03 Exterior Wilson Push Push.AbsoluteSums Finset
open Precision Shell Channel Next.Fluctuations Bloch Laurent SliceRows Mask Coat SliceRows.DataKernel Scroll   LocalRows
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical InnerProductSpace
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S}
variable (z : Site c→ G.El) (U : Config G f) (V : Config G c) {x : ℝ} {P : Teller G} (h : P.Funds S T)

private lemma cairn {ι : Type} [Fintype ι] {α : ι → Site c} (R : ℕ) (F : Config G c→ ι → Twin c → Pay G)
    (h : P.Funds S T) (he : Rule R F α (fun i=>i.1.1)) (j : ι) :
    zip (F (gauge z V)) (T.Xn R (gauge z V)) j=G.adjoint (z (α j)) (zip (F V) (T.Xn R V) j) := by
  obtain ⟨_,_,-,hb⟩:= h.feeds; rw [← h.low] at hb
  unfold zip; rw [map_sum]; apply sum_congr rfl; intro i _; rw [show T.Xn R _ i=G.adjoint _ (T.Xn R V i) from plots V z hb _ _ _]; exact he.move ..

private lemma chasm {ι : Type} [Fintype ι] {α : ι → Site c} {R : ℕ} (F : Config G c→ ι→ Twin c→ Pay G)
    (h : Rule R F α (fun i=>i.1.1)) {a b : ι→G.Color} (hp : ∀ i, G.adjoint (z (α i)) (a i)=b i)
    (j : Twin c) : unzip (F (gauge z V)) b j=G.adjoint (z j.1.1) (unzip (F V) a j) := by
  unfold unzip; rw [map_sum]; apply sum_congr rfl; intro i hi; rw [← hp]
  apply ext_inner_left ℝ; intro g; let Z:= z j.1.1; let p:= G.adjoint Z⁻¹ g
  suffices he : inner ℝ (G.adjoint Z p) _=inner ℝ (G.adjoint Z p) _ from by unfold p at he; rwa [← G.adjoint_mul,mul_inv_cancel,G.adjoint_one] at he
  rw [ContinuousLinearMap.adjoint_inner_right, h.move z V i j p]; unfold Z; rw [Hues.duet,Hues.duet,ContinuousLinearMap.adjoint_inner_right]

include h
lemma freshens (V : Config G c) (R i) : visual T R (gauge z V) i=G.adjoint (z (focus S i)) (visual T R V i) := by
  rcases i with i|i
  · exact cairn z V _ _ h (crosses R T P h) _
  exact cairn z V _ (T.Φ' R) h (sameLevel _ _ S.patch.L.property T.R.mn (Row.rights _ _ h.crosses.1 P.width.le) pole mesh) i
lemma peony (t : S.Choices) (V : Config G c) (i : Rod c f) : freely T x (gauge z V) t i=G.adjoint (z (focus S i)) (freely T x V t i) := by
  unfold freely; rw [reference_v _ h,freshens z h V,map_sub]
lemma winds (x : ℝ) (p : Spot c f) (t : S.Choices) (v : Bool) : loft T x (gauge (constantGauge z S.ratio) U) t (gauge z V) v p=loft T x U t V v p := by
  let A := constantGauge z S.ratio; let Y:= gauge A U; let Q := S.prediction U t; let K := gauge z V
  let R:=till x
  have he i : effective T R Y (S.prediction Y t) K i=G.adjoint (z (focus S i)) (effective T R U Q V i) := by
    unfold effective; rw [freshens z h V,map_sub]; exact congr_arg₂ (· - ·) (entry_turn h R U t V z i) rfl
  have hf i (x : Site _) := Hues.duet (z x) i
  have hz := h.crosses
  obtain ⟨_,_,ha,hb⟩:= h.feeds; rw [← h.low] at hb; rw [← h.high] at ha
  have hF (p : Twin f) : canopyF T R K p=G.adjoint (A p.1.1) (canopyF T R V p) := freshens z h V R (.inl p)
  have ht p : T.Xf R Y p=G.adjoint (A p.1.1) (T.Xf R U p) := plots U A ha _ _ _
  have hh p : T.Xn R K p=G.adjoint (z p.1.1) (T.Xn R V p) := plots V z hb _ _ _
  have hN := sameLevel (G:=G) (c:=c) R S.patch.L.val S.patch.L.property T.R.o (Row.rights _ _ h.crosses.2.1 P.width.le) id mesh
  rcases p with p|p|p|p
  · cases v
    · change finest T _ Y _ K _=_; unfold Scroll.loft; dsimp only [Sum.elim,Bool.false_eq_true,↓reduceIte]; change finest T R _ _ _ _=finest T R _ _ _ _
      unfold finest; rw [Hues.priceC ha f R _ _ U A p]; apply congr_arg₂ (·+·) rfl; refine sum_congr rfl fun i _=> ?_
      rw [hF,ht, Hues.duet,G.norm_adjoint]
    change flora T R Y (S.prediction Y t) K p=flora T R U Q V p
    unfold flora; simp_rw [he,G.norm_adjoint]; unfold flaw Y
    rw [face_gauge,G.chord_conj,G.curvature_conjugate,G.norm_adjoint]
  · have hv : K p*(S.prediction Y t p)⁻¹= z p.1*(V p*(Q p)⁻¹)*(z p.1)⁻¹ := by
      rw [Hues.feed z U t (SectorMeasure.funds_branch h)]; unfold K Q Lattice.gauge; group
    change nora T R Y _ K _=nora T R _ Q _ _; unfold nora flaw; rw [he,G.norm_adjoint,hv,G.chord_conj,G.curvature_conjugate,G.norm_adjoint]
  · have hc : Rule R (T.Φ R) (fun i=> S.ratio.parent i.1.1) (fun i=>i.1.1) := crosses R T P h
    have hu : Rule R (T.Φ' R) Prod.fst (fun i=>i.1.1) := sameLevel _ _ S.patch.L.property T.R.mn (Row.rights _ _ h.crosses.1 P.width.le) pole mesh
    change stormC T K p+ (stormL T R Y _ K p+stormD T R K p)=stormC T V p+ (stormL T R U Q V p+stormD T R V p)
    refine congr_arg₂ (·+·) ?_ (congr_arg₂ (·+·) ?_ ?_)
    · unfold stormC flaw K; rw [face_gauge,G.chord_conj,G.curvature_conjugate,G.norm_adjoint]
    · unfold stormL; apply sum_congr rfl; intro i _
      rw [hh,chasm z V (T.Φ R) hc (a:=T.Xf R U) (b:=T.Xf R Y) (fun i => (ht i).symm) (p,i),chasm z V
        (T.Φ' R) hu (a:=Tube.Z S Q V) (b:=Tube.Z S (S.prediction Y t) K) (fun i=> (entry_turn h R U t V z (.inr i)).symm) (p,i)]
      rw [← map_add,← map_sub,Hues.duet]
    unfold stormD; apply sum_congr rfl; intro i _
    rw [hh,chasm z V (T.Φ R) hc (a:=canopyF T R V) (b:=canopyF T R K) (fun i=> (hF i).symm) (p,i), chasm z V (T.Φ' R)
      hu (a:=canopyI T R V) (b:=canopyI T R K) (fun i=> (freshens z h V R (.inr i)).symm) (p,i), chasm z V (T.N R)
      hN (a:=canopyN T R V) (b:=canopyN T R K) (fun i=> (cairn z V _ _ h hN i).symm) (p,i)]
    rw [← map_add,← map_add,← map_sub,Hues.duet]
  change ‖canopyN T R K p‖^2/2=‖canopyN T R V p‖^2/2
  rw [show canopyN T R K p=_ from cairn z V R (T.N R) h hN p, G.norm_adjoint]; rfl
end YM.ConnectedActivityE6.Blaze.Frond
