import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE.Geometry
import YM.Next.MULTISOURCE.LevelD
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Turn.Pollen

/-! # Reindex work of the canonical cut. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Turn
open Function Filter Finset Lattice Wilson RG Pressure Pressure.Tube Precision Tree MeasureTheory
open AnalyticBridge.GaussianFieldAlignment Locations Channels
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask
open Next.Fluctuations Next.SectorChange Push.SectorMeasure Push.AbsoluteSums Oriented
open Exterior Bloch Laurent
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f}

section shifts
variable (b : Site c) (V Q : Config G c) (U : Config G f) (T : Tube G S) (R : ℕ) (t : ℝ)
lemma translated_kept (p : Clip) (x : Site c) : PathData.kept p t x (translate b V) ↔ PathData.kept p t (x+b) V := by
  unfold PathData.kept; conv_rhs=> rw [← (Channels.shift b PlaqAxes).forall_congr_right]
  simp_rw [translated_face]; simp only [Channels.shift,Equiv.prodCongr_apply,Prod.map,Equiv.coe_addRight,Equiv.refl_apply,separation_translate]
lemma translated_crown (q : PathData G) (p : Clip) (d : ℕ) (x : Cell c) : crown q p R d t (translate b V) x=crown q p R d t V (Channels.shift b _ x) := by
  unfold crown trunk; rw [translated_face, translated_shorten]; rw [if_congr (translated_kept b V t p x.1) rfl rfl]; rfl
lemma translated_F (v τ : ℝ) (x : Cell f) :
    T.workF R (translate (S.ratio.embed b) U) (translate b V) v τ x=T.workF R U V v τ (Channels.shift (S.ratio.embed b) _ x) := by
  unfold workF; rw [translated_crown]; simp_rw [translated_Mv,Xf, Channels.translated_plot]; rfl
lemma translated_I (x : Bond c) : T.workI R (translate b Q) (translate b V) t x=T.workI R Q V t (Channels.shift b _ x) := by
  unfold workI; rw [Channels.translated_Mw]; rfl
lemma translated_C (x : Cell c) : T.workC R (translate b V) t x=T.workC R V t (Channels.shift b _ x) := by unfold workC vision Xn; simp_rw [translated_crown, Channels.translated_plot,translated_thinned]; rfl
lemma zipped {ι κ : Type} [Fintype κ] (e : Equiv.Perm ι) (g : Equiv.Perm κ) (h h' : ι→κ→Pay G) (f f' : κ→G.Color)
    (he : ∀ i j,h' i j=h (e i) (g j)) (hx : ∀ i, f' i=f (g i)) (i : ι) : Pressure.zip h' f' i=Pressure.zip h f (e i) := by
  unfold Pressure.zip; simp_rw [he,hx]; exact Equiv.sum_comp g fun k=> h (e i) k (f k)
lemma unzipped {ι κ : Type} [Fintype ι] (e : Equiv.Perm ι) (g : Equiv.Perm κ) (h h' : ι→κ→Pay G) (f f' : ι→G.Color)
    (he : ∀ i j,h' i j=h (e i) (g j)) (hx : ∀ i,f' i=f (e i)) (i) : unzip h' f' i=unzip h f (g i) := by
  unfold unzip; simp_rw [he,hx]; exact Equiv.sum_comp e fun k=> (h k (g i)).adjoint (f k)
set_option maxHeartbeats 480000 in
lemma translated_L (x : Cell c) : T.workL R (translate (S.ratio.embed b) U) (translate b Q) (translate b V) t x=T.workL R U Q V t (Channels.shift b _ x) := by
  unfold workL; apply Finset.sum_congr rfl; intro i _
  let e := Channels.shift b PlaqAxes
  have hv y : T.vision R t (translate b V) y=T.vision R t V (Channels.twin b y) := translated_thinned ..
  have hx y : T.Xf R (translate (S.ratio.embed b) U) y=T.Xf R U (Channels.twin (S.ratio.embed b) y) := Channels.translated_plot ..
  have he (j) : unzip (T.Φ R (translate b V)) (T.Xf R (translate (S.ratio.embed b) U)) j=unzip (T.Φ R V) (T.Xf R U) (Channels.twin b j) := unzipped _ _ _ _ _ _ (fun i j=> Channels.translated_leap ..) hx j
  have hh (j) : unzip (T.Φ' R (translate b V)) (Z S (translate b Q) (translate b V)) j= unzip (T.Φ' R V) (Z S Q V) (Channels.twin b j) :=
    unzipped (Channels.shift b Axis) _ _ _ _ _ (fun i j=> Channels.translated_lane ..) (fun _=> Channels.translated_Z ..) j
  have hhT : Channels.twin b (x,i)=(e x,i) := rfl
  rw [he,hh,hv]; unfold Xn; rw [Channels.translated_plot,hhT]
lemma translated_R (j : Co c Gain) : Pressure.zip (T.N R (translate b V)) (T.vision R t (translate b V)) j=Pressure.zip (T.N R V) (T.vision R t V) (Channels.shift b _ j) :=
  zipped _ (Channels.twin b) _ _ _ _ (fun _ _=>Channels.translated_lane ..) (fun _=>Channels.translated_thinned ..) _
lemma translated_N (j : Co c Gain) : T.workN R (translate b V) t j=T.workN R V t (Channels.shift b _ j) := by unfold workN; rw [translated_R]
lemma translated_D (x : Cell c) : T.workD R (translate b V) t x=T.workD R V t (Channels.shift b _ x) := by
  let Y:=translate b V; let F i:=T.Mv R t Y i; let e:=Channels.twin b
  have hv y : T.vision R t (translate b V) y=T.vision R t V (Channels.twin b y) := Channels.translated_thinned ..
  have hx y : T.Mv R t (translate b V) y=T.Mv R t V (Channels.twin (S.ratio.embed b) y) := Channels.translated_Mv ..
  have he j : unzip (T.Φ R (translate b V)) (T.Mv R t Y) j=unzip (T.Φ R V) (T.Mv R t V) (e j) := unzipped _ _ _ _ _ _ (fun i j=> Channels.translated_leap ..) hx j
  have hh j : unzip (T.Φ' R (translate b V)) (T.Mw R t (translate b V)) j= unzip (T.Φ' R V) (T.Mw R t V) (Channels.twin b j) := unzipped (Channels.shift b Axis) _ _ _ _ _ (fun i j=>Channels.translated_lane ..) (fun i=> Channels.translated_Mw ..) j
  have hz j : unzip (T.N R Y) (Pressure.zip (T.N R Y) (T.vision R t Y)) j= unzip (T.N R V) (Pressure.zip (T.N R V) (T.vision R t V)) (e j) := unzipped (Channels.shift b Gain) _ _ _ _ _ (fun i j=> Channels.translated_lane ..) (translated_R b V T R t) j
  unfold workD; unfold Y at *; simp_rw [he,hv,hz, hh]; rfl
end shifts

section all
variable {F : Forest S.ratio} {P : Teller G} {T : Tube G S}
    {X : Coat T F} {s b} {Y : Coat T (Locations.forest s b F)}
namespace Tuned
variable (h : Tuned s b X Y) (hp : P.Funds S T) {W C : ℝ} (ht : ShellAccess S G X.x W X.width C)
include h hp
lemma predictor (u : Directions G f) (q : Signed) :
    S.prediction (pull q 0 (Y.input (wheels (S:=S) s b X.V u))) (choice q Y.k)=
      translate (Channels.offset s b q) (S.prediction (pull (s*q) 0 (X.input u)) (choice (s*q) X.k)) := by
  have ht:=funds_branch hp
  rw [(carry q ht ..).2,h.way,h.completed,S.prediction_channel ht,Channels.ticket,Equiv.apply_symm_apply,(carry (s*q) ht ..).2,channel_turn]
lemma compass (u : Directions G f) (q : Signed) (i : Spot c f) : Y.energy (wheels (S:=S) s b X.V u) q i=X.energy u (s*q) (wind s b S q i) := by
  unfold Coat.energy; dsimp only; rw [h.predictor hp,h.completed,h.v,h.x,Channels.channel_turn,Channels.channel_turn,Channels.offset_fine]
  rcases i with i|i|i|i
  · exact translated_F ..
  · exact translated_I ..
  · exact congr_arg₂ (·+·) (translated_C ..) (congr_arg₂ (·+·) (translated_L ..) (translated_D ..))
  exact translated_N ..
omit hp in
lemma near (u : Directions G f) (q : Signed) (i : Cell f) :
    soft T Y.x (pull q 0 (Y.input (wheels (S:=S) s b X.V u))) (pull q 0 Y.V) (choice q Y.k) i=
      soft T X.x (pull (s*q) 0 (X.input u)) (pull (s*q) 0 X.V) (choice (s*q) X.k) (Channels.shift (S.ratio.embed (Channels.offset s b q)) _ i) := by
  rw [h.completed,h.v,h.x,Channels.channel_turn,Channels.offset_fine,Channels.channel_turn]; unfold soft
  rw [translated_face]; apply congr_arg; apply Finset.sum_congr rfl; intro j _
  unfold SliceRows.bill SliceRows.entryCost SliceRows.guide Tube.Xf; simp_rw [Sum.elim_inl,Channels.translated_plot,Channels.translated_Mv]; rfl
include ht
lemma debit_eq (u : Directions G f) (q : Signed) (i : Spot c f) : Y.debit (wheels (S:=S) s b X.V u) q i=X.debit u (s*q) (wind s b S q i) := by unfold debit; rw [h.compass hp,h.ex hp ht]
lemma light_eq (u : Directions G f) (q : Signed) (i : Spot c f) : Y.light (wheels (S:=S) s b X.V u) q i=X.light u (s*q) (wind s b S q i) := by
  unfold Coat.light; rw [h.ex hp ht]; apply congr_arg₂ (·-·) _ rfl
  rcases i with i|i
  · exact h.near ..
  exact h.compass hp u q (.inr i)
end Tuned
end all
end YM.PhysicalNext.Repeat.Turn
