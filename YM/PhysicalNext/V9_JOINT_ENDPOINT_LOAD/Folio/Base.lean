import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.LocalStation
import YM.AnalyticBridge.NONFLAT_COVARIANCE_LOCALITY.Either
import YM.AnalyticBridge.RESET_INCOME_PORT.LogQuote
import YM.AnalyticBridge.RESET_INCOME_PORT.Sheen
import YM.Extra.WEAK_SCALING_ACTLAW.Shared
import YM.Further.GAUSSIAN_SCALAR_LEDGER.Balance
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Calendar



/-!
# Dependencies actually charged for the linear ratio letter, I

Goal here: quantitative full-address hit bills compatible with `JointLoad`
on `LocalGaussian.spectacle` (endpoint windows). This file checks the inputs
of each affine-source call. x, T (path, horizons, fiscal maps etc.), q, d,
couplings, period *fixed*, but every function on argument fields evaluated
with the actual record & choices at physical positions, including the
extension at partially wrong flags. No replacing a full shared tag by a
random tag per letter use. Only λ/P/Haar dependence below through the stated
inputs; to move weights in an interacting expansion keep ALL the other
likelihoods, Y, k, ancestor & eligibility reads when used. This is NOT an
indexing/occurrence-decomposition producer. Hold mechanisms in the integrand
also have to ensure genuine evaluations use their required operands & agree
with the extension. No movement of a differentiated hard flag profile here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Folio
open Function Lattice RG Precision Pressure Wilson Tree Matrix
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Wisps Push.SectorMeasure
open AnalyticBridge.NonflatCovarianceLocality AnalyticBridge.NonflatCovarianceLocality.Matching
open AnalyticBridge.SectorAffine (Offset.fixedBase Offset.f0)
open AnalyticBridge.LocalGaussianLaws (Lift.vBand Lift.kickBand Lift.zipAt Lift.signedAgree Lift.copyAgree)
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical

variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {P : Teller G} {A B : Stores S} {F H : Forest S.ratio}
    {V W : Config G c} {k k' : S.Choices} {x : ℝ} {o : Site c} {r : ℕ}

abbrev leaf (A : Stores S) (F : Forest S.ratio) (x : ℝ) (Y : Config G f) : LinkArray G (Frozen A x F) := fun i => Y i.val.val

def enough (S : StepData c f) (x : ℝ) := 2*span S.patch x + 10*radiusB x+4

lemma fixed_agrees (hp : P.Funds S T) (h : ReadsWithin o r A B F H V W k k') (p : Rows.Receipt G S)
    (he : separation o (down S p)+2*span S.patch x ≤ r) :
    Offset.fixedBase T x V k p.1 = Offset.fixedBase T x W k' p.1 := by
  obtain ⟨⟨s,i⟩,b⟩ := p
  let R := Stores.till x; let L := span S.patch x; let y := roots S (i.elim (fun p => Sum.inl p.1) Sum.inr)
  change separation o (s.act y)+2*L ≤ r at he
  let v := pull s 0 V; let w := pull s 0 W
  have h₀ : AgreeNear id y (2*R + 4) v w := Lift.signedAgree _ _ _ _ _ <|
    h.sites.shrink (show separation o (s.act y)+(2*R+4+1)≤r by unfold L span R at *; omega)
  have hx (j : Twin c) (hh : separation y j.1.1 ≤ R) : T.Xn R v j=T.Xn R w j :=
    plotted_near id Work.E03.sep_step v w T.low T.down R S.patch.L.val j S.patch.L.property (h₀.shrink (by change separation y j.1.1+_ ≤ _; omega))
  have hz {I : Type} (i : I) (φ : Config G c→I→Twin c→Pay G) (h : ∀ j,
      (R < separation y j.1.1 → φ v i j = 0) ∧ (AgreeNear id y R v w → φ v i j=φ w i j)) :=
    Lift.zipAt R v w y i φ _ _ h (h₀.shrink (by simp only [separation_self]; omega)) hx
  cases i with
  | inl i =>
    change T.Xf R (facade S s V 0) i - _=T.Xf R (facade S s W 0) i - _
    rw [hz i (T.Φ R) (Lift.vBand T R v w i),fixed_facade, fixed_facade, ← AnalyticBridge.SectorAffine.Identity.top_copy,← AnalyticBridge.SectorAffine.Identity.top_copy]
    exact congr_arg (·-_) (plotted_near S.ratio.parent (Work.E03.parent_step S) (replica S.ratio v) (replica S.ratio w) T.high T.up R 1 i le_rfl
      (Lift.copyAgree _ _ _ _ <| h₀.shrink (show separation y y+(R+4) ≤ _ by rw [separation_self]; omega)))
  | inr i =>
    let j := sendEdge s 0 i
    have h₁ := spin_step i s; have h₂ := Work.E03.sep_step j.1 j.2
    have ht : separation o j.1 ≤ separation o (s.act y)+1 := (separation_triangle o (s.act y) _).trans (Nat.add_le_add_left h₁ _)
    have ht' := separation_triangle o j.1 (j.1+step j.2)
    have hL : L = Stores.till x+5+predReach S.patch := rfl
    have hy : predictGroup V k s i (0:Directions G f) = predictGroup W k' s i 0 := by
      unfold predictGroup facade; rw [(Push.SectorMeasure.Oriented.carry s (funds_branch hp) k _).2,(Push.SectorMeasure.Oriented.carry s (funds_branch hp) k' _).2, Motion.turn_read,Motion.turn_read]
      let u (V : Config G c) := increment (replica S.ratio V) (0:Directions G f)
      have hu : AgreeNear S.ratio.parent j.1 (predReach S.patch) (u V) (u W) := by
        have hh := Lift.copyAgree (S:=S) V W _ _ (h.sites.shrink (show separation o j.1+predReach S.patch ≤ r by omega))
        intro t ht; unfold u increment; rw [hh t ht]
      have h_eq : S.prediction (u V) k j=S.prediction (u W) k' j := by
        rw [prediction_near_eq (funds_branch hp) _ _ k _ hu]
        exact same_tags S j _ _ (h.choices _ (by omega)) (h.choices _ (by omega)) (h.bonds _ (by omega)) _
      rw [h_eq]
    change Tube.Z _ _ v i - _=Tube.Z _ _ w i - _
    rw [hz i (T.Φ' R) (Lift.kickBand T R v w i)]
    unfold Tube.Z; rw [show S.prediction (facade S s V 0) _ i = S.prediction (facade S s W 0) _ i from hy,h₀ i (show separation y y ≤ _ from by simp)]

lemma inputs_agree (h : ReadsWithin o r A B F H V W k k') (Y Y' : Config G f)
    (hY : AgreeNear S.ratio.parent o r Y Y') {e : Bond f} (he : separation o (S.ratio.parent e.1)+10*radiusB x+4 ≤ r)
    (q : Chi) (d : ℝ) : Rows.input x A F (autoShell q d V (leaf A F x Y)) e = Rows.input x B H (autoShell q d W (leaf B H x Y')) e := by
  have ht : e ∈ F.trunks ↔ e∈H.trunks := h.tree (by omega)
  have ha : engaged x A F e ↔ engaged x B H e := h.enabled x he
  have hb := Lift.copyAgree (S:=S) V W o r h.sites
  by_cases hv : e∈F.trunks
  · rw [Rows.input,dif_neg (not_not_intro hv),Rows.input,dif_neg (not_not_intro (ht.mp hv))]
  have hv' := mt ht.mpr hv
  have hh : chill A x F ⟨e,hv⟩ ↔ chill B x H ⟨e,hv'⟩ := by
    simpa only [engaged,hv,hv',not_false_eq_true,true_and,chill, ← not_or, not_iff_not] using ha
  unfold Rows.input
  rw [dif_pos hv,dif_pos hv']
  by_cases hX : chill A x F ⟨e,hv⟩
  · rw [dif_pos hX,dif_pos (hh.mp hX)]
    change patched q d (Y e*(replica S.ratio V e)⁻¹) = patched q d (Y' e*(replica S.ratio W e)⁻¹)
    rw [hY e (by omega), hb e (by omega)]
  rw [dif_neg hX, dif_neg (mt hh.mpr hX)]

/-- The good extension on F0 is local, including its test whether a row
is selected in the first place (through the full flags table and trees,
snaps and the predictor, not by V agreements alone). Uses a common full
representative just for the frozen `Y` inputs. -/
lemma f0_agrees (hp : P.Funds S T) (h : ReadsWithin o r A B F H V W k k') (Y Y' : Config G f)
    (hY : AgreeNear S.ratio.parent o r Y Y') (p : Receipt G S) (he : separation o (down S p)+enough S x ≤ r)
    (q : Chi) (d : ℝ) : Offset.f0 T x A F k V q d (leaf A F x Y) p = Offset.f0 T x B H k' W q d (leaf B H x Y') p := by
  unfold enough at he
  have hf := fixed_agrees hp h p (by omega : separation o (down S p)+2*span S.patch x ≤ r)
  have hk := h.correspond x p (by omega)
  let a := Rows.input x A F (autoShell q d V (leaf A F x Y)); let b := Rows.input x B H (autoShell q d W (leaf B H x Y'))
  have ht : bump T x V k a p.1=bump T x W k' b p.1 := by
    rw [h.bump_eq hp _ p (by omega)]
    apply bump_dep T x W k' p.1.1 p.1.2 a b (funds_branch hp)
    intro e he'
    have hp := (contains ..).mp he'; have hz := separation_triangle o (down S p) (S.ratio.parent e.1)
    have he' : separation (down S p) (S.ratio.parent e.1) ≤ span S.patch x := hp
    exact inputs_agree h Y Y' hY (by omega) q d
  unfold Offset.f0; rw [tape_read,tape_read]; unfold Rows.restrict
  simp only [hk,Pi.add_apply,hf]
  rw [ht]
end YM.PhysicalNext.JointLoad.Folio
