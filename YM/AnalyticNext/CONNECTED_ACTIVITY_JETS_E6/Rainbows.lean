import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Hood
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Hues
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Shower

/-! # Physical charge and masks natural. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Hues
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented  Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll  
open  Ursell Trees    Rotation
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {n c f : Side} {S : StepData c f} {T : Tube G S} {F : Tree.Forest S.ratio}
variable {a α W μ C η r Q Y : ℝ} {R : Rep G f} {L : Side} {B : ℕ}
variable (X : Coat T F) (z : Site c→ G.El) (p : P.Funds S T) (ht : ShellAccess S G X.x W X.width C)

lemma feed (U : Config G f) (k : S.Choices) (h : S.patch.Branches S.kernel G) :
    S.prediction (gauge (constantGauge z S.ratio) U) k=gauge z (S.prediction U k) := by
  rw [(SectorMeasure.choice_gauge h U k _).2]; rw [show constantGauge z S.ratio ∘ S.ratio.embed=z from
    funext fun x=> congr_arg z (S.ratio.embed_parent x)]
lemma priceC {Q : Clip} {R : PathData G} {σ D Λ : ℝ} (h : R.Bounds Q σ D Λ) (n : Side) (k d : ℕ) (t : ℝ)
    (U : Config G n) (z : Site n→G.El) (i : Cell n) : crown R Q k d t (gauge z U) i=crown R Q k d t U i := by
  simp only [crown, Pressure.trunk, DataKernel.kept U z, DataKernel.short_gauge U z h,G.norm_adjoint,
    face_gauge,G.chord_conj]
lemma duet (p : G.El) (i j : G.Color) : inner ℝ (G.adjoint p i) (G.adjoint p j)=inner ℝ i j :=
    (skew p).inner_map_map ..

include p in
lemma singing (x : ℝ) (i : Spot c f) (U : Config G f) (V : Config G c) (k : S.Choices) :
    let Y := gauge (constantGauge z S.ratio) U; let Q:= gauge z V
    Coat.principal T x Y Q (S.prediction Y k) i = Coat.principal T x U V (S.prediction U k) i ∧
    Coat.yielding T x Y Q k i=Coat.yielding T x U V k i := by
  intro Y Q; let u:=Pressure.temp x; let v:= Pressure.fiery G x S.patch.L; let R:= till x; let P':= S.prediction U k
  have he (p' : Rod c f) : SliceRows.bill T x Y k Q p'=G.adjoint (z (focus S p')) (SliceRows.bill T x U k V p') := by
    unfold SliceRows.bill; rw [map_sub,entry_turn p R U k V z, guide_gauge p x V z]
  obtain ⟨s,A,hb,ha⟩:=p.feeds
  rw [← p.high] at hb; rw [← p.low] at ha
  rcases i with i|i|i|i
  · constructor
    · change T.workF R Y Q v u i=T.workF R U V v u i; unfold Tube.workF
      rw [priceC hb f R 1 v U (constantGauge z S.ratio) i]; refine congrArg₂ (· + ·) rfl ?_
      refine sum_congr rfl fun j _=> ?_
      have hf := DataKernel.mvg p R u z V (i,j)
      rw [show T.Mv R u Q (i,j)=_ from hf, show T.Xf R Y (i,j)=_ from entry_turn p R U k V z (.inl (i,j))];
      change ‖G.adjoint _ _‖^2/2-inner ℝ _ (G.adjoint _ _) = _; rw [G.norm_adjoint]; dsimp only [focus,entryCost,Sum.elim]; rw [duet]
    change SliceRows.soft T x Y Q k i=SliceRows.soft T x U V k i
    unfold soft; simp_rw [he,G.norm_adjoint]; unfold flaw
    unfold Y; rw [face_gauge,G.chord_conj,G.curvature_conjugate,G.norm_adjoint]
  · have hv := feed z U k (funds_branch p)
    have hx : wire (S.prediction Y k) Q i=wire P' V i := by unfold Y; rw [hv]; exact wire_gauge ..
    have hz : T.workI R (S.prediction Y k) Q u i=T.workI R P' V u i := by
      unfold Tube.workI monetary; rw [hx, DataKernel.mwg p R u z V i,
        show Tube.Z S (S.prediction Y k) Q i= G.adjoint (z i.1) (Tube.Z S P' V i) from entry_turn p R U k V z (.inr i), duet,G.norm_adjoint]
    exact ⟨hz,hz⟩
  · have hf := gauge_gaps P T p R U V k z
    have hx i : T.vision R u Q i= G.adjoint (z i.1.1) (T.vision R u V i) := DataKernel.thins V z ha ..
    have hs (j:Bool) : inner ℝ (T.vision R u Q (i,j)) (dGap T R Q (T.vision R u Q) (i,j))=
        inner ℝ (T.vision R u V (i,j)) (dGap T R V (T.vision R u V) (i,j)) := by
      rw [hx,show T.vision R u Q=turnData z _ (T.vision R u V) from funext hx,(hf _).2,duet]
    have hl j : inner ℝ (T.vision R u Q (i,j)) (lGap T R Y (S.prediction Y k) Q (i,j))=
      inner ℝ (T.vision R u V (i,j)) (lGap T R U P' V (i,j)) := by
      rw [hx,show lGap T R Y (S.prediction Y k) Q (i,j)= _ from (hf (i,j)).1,duet]
    have hv : T.workC R Q u i=T.workC R V u i := by
      unfold Tube.workC
      apply congr_arg₂ <;> [skip; exact priceC ha c R _ u V z i]
      refine sum_congr rfl fun j _=> ?_; rw [hx,show T.Xn R Q (i,j)= _ from DataKernel.plots V z ha R _ _, duet,G.norm_adjoint]; rfl
    have hm : Coat.principal T x Y Q (S.prediction Y k) (.inr (.inr (.inl i)))= Coat.principal T x U V P' (.inr (.inr (.inl i))) :=
      congr_arg₂ (· + ·) hv (show T.workL R Y _ Q u i+_=T.workL R U P' V u i+_ from congr_arg₂ (·+·)
        (sum_congr rfl fun j _=> hl j) (show T.workD R Q u i=_ from sum_congr rfl fun j _=> congr_arg (· / 2) (hs j)))
    exact ⟨hm,hm⟩
  have hv : T.workN R Q u i=T.workN R V u i := by unfold Tube.workN; unfold Q; rw [DataKernel.ng p,G.norm_adjoint]
  exact ⟨hv,hv⟩

include p ht
lemma rainWorks (u : Directions G f) (s : Signed) (i : Spot c f) :
    let Y := sluice X z; let v:=spinRow S z u
    Y.debit v s i=X.debit u s i ∧ Y.light v s i=X.light u s i ∧ Y.extracted v s i=X.extracted u s i := by
  intro Y v; let k:= choice s X.k
  let U:= X.input u; let Q:=X.V
  have he : Y.extracted v s i=X.extracted u s i := by
    unfold Coat.extracted; refine sum_congr rfl fun j _ => ?_
    simp_rw [surcharge, show Y.selected s (spot S j)=X.selected s (spot S j) from rfl,show Y.realPath s j v=_ from springs X p ht z u s j, G.norm_adjoint]
  let t : Site c→G.El := z ∘ Lattice.affine s 0
  have hF : pull s 0 (Y.input v)=gauge (constantGauge t S.ratio) (pull s 0 U) := by
    rw [banks X z u,Work.F05.pull_gauge_zero];
    have hk : (fun x:Site f=>constantGauge z S.ratio (Lattice.affine s 0 x))=constantGauge t S.ratio := by
      funext j; simp only [constantGauge,t,affine0,Function.comp_apply]; rw [S.ratio.parent_signed S.patch.odd_side]
    rw [hk]
  have hx := singing t p X.x i (pull s 0 U) (pull s 0 Q) k
  unfold debit Coat.light Coat.energy
  have ht' : pull s 0 Y.V= gauge t (pull s 0 X.V) := Work.F05.pull_gauge_zero ..
  change Coat.principal T X.x _ _ (S.prediction _ k) _-_= _ ∧ Coat.yielding T X.x _ _ k _-_= _ ∧ _
  rw [he,hF,ht']; exact ⟨congr_arg (·-_) hx.1, congr_arg (·-_) hx.2, rfl⟩
end YM.ConnectedActivityE6.Hues
