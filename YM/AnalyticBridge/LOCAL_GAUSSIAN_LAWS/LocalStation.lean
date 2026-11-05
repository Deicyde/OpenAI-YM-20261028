import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.ChipHeal
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Flux
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.TurnZero

/-!
# Local station reads (order-zero, hold choices and common gauges)

For use on actual means; even with different versions of horizon kernel
quotes. Preserve distances in native coarse sites including incidence
shifts. Key point: `vision` has actual masks on the evaluated V (so
clamped or not), but on a sufficiently cleared patch the *actual*
full read is equal to that `plotted` on a small log extension at all
sites addressed by the used rows. This does not read masks for the
continuation--no claims at that mask of differentiability.
We need RowNear lemmas for ZIP not lGap/dGap; f_near and lane_near
from Next.FLUCTUATIONS/Locality adapted (private).
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussianLaws.Lift
open Function Filter Lattice RG Wilson Finset Pressure Pressure.Stores Pressure.Tube Precision Exterior Tree Bloch Bid Matrix
open Next Next.Fluctuations SectorChange SectorChange.Rows SectorChange.Gaussian Push.SectorMeasure 
open scoped Topology InnerProductSpace BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f n : Side} {S : StepData c f} {x : ℝ}
open Work.E03

lemma vBand (T : Tube G S) (R : ℕ) (V V' : Config G c) (i : Twin f) (j : Twin c) :
    (R<separation (S.ratio.parent i.1.1) j.1.1 → T.Φ R V i j=0) ∧
    (AgreeNear id (S.ratio.parent i.1.1) R V V' → T.Φ R V i j=T.Φ R V' i j) := by
  constructor
  · intro h
    have hf (u : Cover) : casted S T.R R V (mesh i) (mesh j) u = 0 := by
      dsimp only [casted]; split
      next hv =>
        let w := route (lift (S.ratio.residue (mesh i).1)) (S.patch.L.val • u) 1
        have hp := sep_walk S.ratio.parent (parent_step S) (mesh i).1 w
        rw [show stop _ w = _ from casted_endpoint S (mesh i).1 u, S.ratio.embed_parent, ← hv.2] at hp
        exact (h.not_ge (hp.trans hv.1)).elim
      next hv => rfl
    simp only [Tube.Φ,leap,hf,tsum_zero]
  · intro h
    apply tsum_congr
    intro u
    dsimp only [casted]; split
    next ht =>
      have he : AgreeNear S.ratio.parent (S.ratio.parent (mesh i).1) R (replica S.ratio V) (replica S.ratio V') := by
        intro e he; unfold replica; split
        next hx => rfl
        next hx => exact h _ he
      rw [rated, rated, travel_near _ (parent_step S) _ _ _ _ R ht.1 he]
    next ht => rfl

lemma kickBand (T : Tube G S) (R : ℕ) (V V' : Config G c) (i : Bond c) (j : Twin c) :
    (R<separation i.1 j.1.1 → T.Φ' R V i j=0) ∧
    (AgreeNear id i.1 R V V' → T.Φ' R V i j=T.Φ' R V' i j) := by
  let L := S.patch.L.val
  have hl k (h : k*L ≤ R) : k≤R := le_trans (le_mul_of_one_le_right (Nat.zero_le _) S.patch.L.property) h
  let K := T.R.mn
  change (R<_ → lane R L V K (pole i) (mesh j)=_) ∧ (_ → lane R L V K (pole i) (mesh j)=_)
  constructor
  · intro h; have hf (u : Cover) : priced R L V K (pole i) (mesh j) u = 0 := by
      unfold priced; split
      next hv =>
        have hx : stop (pole i).1 (route 0 u 1) = (mesh j).1 := by
          rw [hv.2]; simpa only [map_zero, add_zero] using Work.E03.stop_route (pole i).1 0 u
        have he : separation (pole i).1 (mesh j).1 ≤ R := by
          rw [← hx]; exact (sep_walk (fun x : Site c => x) sep_step ..).trans (hl _ hv.1)
        exact (h.not_ge he).elim
      next hv => rfl
    simp [lane,hf]
  intro h; apply tsum_congr
  intro u; unfold priced; split
  next ht => rw [rated,rated, travel_near id (fun y i => sep_step y i) _ _ (pole i).1 _ R (hl _ ht.1) h]
  next ht => rfl

lemma zipAt {I : Type} (Z : ℕ) (R W : Config G c) (x : Site c) (i : I)
    (P : Config G c → I → Twin c → Pay G) (a b : Twin c → G.Color)
    (h : ∀ j, (Z<separation x j.1.1 → P R i j=0) ∧ (AgreeNear id x Z R W → P R i j=P W i j))
    (hh : AgreeNear id x Z R W) (he : ∀ j, separation x j.1.1≤Z → a j=b j) : zip (P R) a i=zip (P W) b i := by
  unfold zip; refine sum_congr rfl fun j _ => ?_
  by_cases ht : separation x j.1.1 ≤ Z
  · rw [(h j).2 hh,he j ht]
  have hv : P W i j=0 := ((h j).2 hh).symm.trans ((h j).1 (lt_of_not_ge ht))
  rw [hv,(h j).1 (lt_of_not_ge ht)]; rfl

lemma signedAgree (s : Signed) (i : Site c) (r : ℕ) (U V : Config G c)
    (h : AgreeNear id (s.act i) (r+1) U V) : AgreeNear id i r (pull s 0 U) (pull s 0 V) := by
  rintro ⟨y,e⟩ he
  rw [Motion.turn_read, Motion.turn_read]
  have hx : separation (s.act i) (sendEdge s (0:Site c) (y,e)).1 ≤ r+1 := by
    refine (separation_triangle (s.act i) (s.act y) _).trans (Nat.add_le_add ((separation_signed ..).le.trans he) ?_)
    unfold sendEdge Step.used affine; dsimp only; split
    · have hu (p) := sep_step (s.act y-step p) p; simp only [sub_add_cancel] at hu; rw [separation_comm]; simpa using hu ((posDir e).rotate s).dir
    simp
  rw [h _ hx]

lemma copyAgree (A B : Config G c) (o : Site c) (r : ℕ) : AgreeNear id o r A B → AgreeNear S.ratio.parent o r (replica S.ratio A) (replica S.ratio B) := by
  intro h i hi; unfold replica; split
  · rfl
  exact h _ hi

section hold
open Remote
lemma charged_at (A : Stores S) (o : Site c) (D : ℕ) (hz : Clears A x o D) (V : Config G c)
    (h : A.flags=RG.flags (temp x) V) (s : Signed) (p : Cell c) (hs : separation o (s.act p.1) ≤ D) :
    toll (pull s 0 V) p ≤ temp x := by
  by_contra! he
  apply hz
  have hh : p.1∈RG.flags (temp x) (pull s 0 V) := (flags_spec ..).2 ⟨p,YM.Work.E01.base_touched p,he⟩
  have ht : s.act p.1 ∈ A.flags := h.symm ▸ Work.H03.flags_send s 0 (temp x) V ▸ (by
    change _ ∈ Finset.image _ _; rw [← add_zero (s.act p.1)]; exact mem_image_of_mem (affine s 0) hh)
  apply halo_spec.mpr; rw [separation_comm] at hs
  exact ⟨s.act p.1, mem_union_right _ ht,hs.trans (by omega)⟩

lemma farView (p : Clip) : ∀ᶠ x in atTop, ∀ {c f : Side} (S : StepData c f) (A : Stores S) (o : Site c), Clears A x o (radiusB x) →
    ∀ (V : Config G c) (T : Tube G S), T.low=p → A.flags=RG.flags (temp x) V → ∀ (s : Signed) (j : Twin c),
    separation o (s.act j.1.1)≤3*radiusB x/4 → T.vision (till x) (temp x) (pull s 0 V) j=T.Xn (till x) (pull s 0 V) j := by
  have h := Work.E04.eventually_room 0 p.relaxation p.radius_pos
  filter_upwards [h] with x hx
  rw [add_zero] at hx
  intro c f S A o Hz V T hp hA s j hd
  let v := pull s (0:Site c) V
  have he (q : Cell c) (hh : separation j.1.1 q.1 + 1≤radiusB x/50) : toll v q ≤ temp x := by
    apply charged_at A o (radiusB x) Hz V hA s q
    have h := separation_triangle o (s.act j.1.1) (s.act q.1); rw [separation_signed] at h; omega
  have h0 : toll v j.1 ≤ temp x := charged_at A o (radiusB x) Hz V hA s j.1 (hd.trans (by omega))
  unfold vision Xn thinned plotted; split
  · rw [if_pos (show PathData.kept _ _ _ _ from ?_)]
    intro q
    change toll v q ≤ _
    by_cases ht : G.chord (faceValue v q) ≤ temp x * Real.exp (separation j.1.1 q.1 / T.low.relaxation)
    exact ht
    have hl : temp x*Real.exp (separation j.1.1 q.1 / p.relaxation)<2 := by rw [← hp]; exact (lt_of_not_ge ht).trans_le (G.chord_le_two _)
    exact (he q (hx.2 _ hl)).trans (le_mul_of_one_le_right (temp_nonneg _) (Real.one_le_exp (div_nonneg (Nat.cast_nonneg _) T.low.radius_pos.le)))
  rw [show (if toll (pull s 0 V) j.1=0 then (1:ℝ) else min 1 (temp x/toll (pull s 0 V) j.1))=1 from ?_,one_smul]; split
  · rfl
  exact min_eq_left ((one_le_div (lt_of_le_of_ne (G.chord_nonneg _) (by symm; assumption))).mpr h0)
lemma stamped (p : Clip) : ∀ᶠ x in atTop, ∀ {c f : Side} (S : StepData c f) (A : Stores S) (o : Site c), Clears A x o (radiusB x) →
    ∀ (V : Config G c) (T : Tube G S) (k : S.Choices), T.low=p → S.patch.Branches S.kernel G → A.flags=RG.flags (temp x) V →
    span S.patch x ≤ radiusB x/50 → ∀ (s : Signed) (v : Dir G c) (j : Twin f ⊕ Bond c), AgreeNear id o (radiusB x) V (represent v) →
    separation o (Remote.aim S (s,j))≤radiusB x/2 →
    let a:=pulled (blueprint S v) s; let b:=pulled v s; let R:=till x
    let U:= represent a; let W:=represent b; let X:=T.Xn R W
    Rows.base T x V k (s,j)=j.elim (fun p => T.Xf R U p-zip (T.Φ R W) X p) (fun p => Z S (S.prediction U (Oriented.choice s k)) W p-zip (T.Φ' R W) X p) := by
  filter_upwards [farView (G:=G) p, Work.E01.radiusB_tendsto.eventually_ge_atTop 100] with x hx hB
  intro c f S A o ho V T k hQ hS hA hr s v j hv he a b R U W X
  let B:=radiusB x; let v' := pull s (0:Site c) V; let u':=pull s (0:Site f) (replica S.ratio V)
  have h0 : 100≤B := hB; change R+5+predReach S.patch ≤ B/50 at hr
  have ht (y : Site c) (hy : separation o (s.act y)≤B/2) :
      AgreeNear S.ratio.parent y (3*R+4+predReach S.patch) u' U ∧ AgreeNear id y (3*R+4+predReach S.patch) v' W := by
    let L := 3*R+4+predReach S.patch
    constructor
    · rw [show U=pull s 0 (replica S.ratio (represent v)) from (turned_repr ..).trans (congr_arg _ (replica_rep (S:=S) _).symm)]
      exact pulled_near _ _ _ _ _ (copyAgree V (represent v) _ _ (hv.shrink (D':=L+1) (by unfold L; unfold B at *; omega)))
    rw [show W=pull s 0 (represent v) from turned_repr ..]; exact signedAgree _ _ _ _ _ (hv.shrink (D':=L+1) (by unfold L; omega))
  have hz {I : Type} (P : Config G c→I→Twin c→Pay G) (i : I) (z : Site c) (he : separation o (s.act z)≤B/2)
      (hl : ∀ j, (R<separation z j.1.1 → P v' i j=0) ∧ (AgreeNear id z R v' W → P v' i j=P W i j)) :
      zip (P v') (T.vision R (temp x) v') i=zip (P W) X i := zipAt R v' W z i _ _ _ hl ((ht z he).2.shrink (by simp; omega)) (fun j hj => by
        have hr' := separation_triangle o (s.act z) (s.act j.1.1); rw [separation_signed] at hr'
        rw [hx S A o ho V T hQ hA s j (by change _ ≤ 3*B/4; omega)]
        exact plotted_near id (fun y i => sep_step y i) v' W T.low T.down R S.patch.L.val j S.patch.L.property ((ht z he).2.shrink (by change separation z j.1.1 + _≤_; omega)))
  cases j
  next j =>
    change separation o (s.act (S.ratio.parent j.1.1))≤B/2 at he
    let P := S.ratio.parent j.1.1
    change T.Xf R (facade S s V 0) j-zip _ _ j=T.Xf R U j-_
    rw [fixed_facade, show T.Xf R (pull s 0 (replica S.ratio V)) j = _ from plotted_near S.ratio.parent (parent_step S) u' U T.high T.up R 1 j le_rfl ((ht P he).1.shrink (by change separation P P+_≤_; rw [separation_self]; omega)), hz (T.Φ R) j P he (vBand T R v' W j)]; rfl
  next j =>
    change separation o (s.act j.1)≤B/2 at he
    change Z _ _ _ _-zip _ _ j=Z _ _ _ _-_
    rw [hz (T.Φ' R) j j.1 he (kickBand T R v' W j)]
    apply congr_arg (·-zip _ X j)
    have hh := prediction_near_eq hS u' U (Oriented.choice s k) j ((ht _ he).1.shrink (by simp))
    unfold Z; rw [fixed_facade,hh]; change _ • G.curvature (v' j*_)=_; rw [(ht _ he).2 j (by simp [id])]
end hold
end YM.AnalyticBridge.LocalGaussianLaws.Lift
