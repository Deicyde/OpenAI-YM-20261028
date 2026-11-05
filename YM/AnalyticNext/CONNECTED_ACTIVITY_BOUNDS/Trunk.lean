import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Gauge2
import YM.Push.SECTOR_MEASURE.Gauges

/-!
# Gauge transport of *additional* operations needed here

Compare `YM.Next.FLUCTUATIONS.Covariance` which already exposes L/D
gap transport but not the lemmas needed on F/I/N separately. We adapt
its underlying `rated` argument here (no shared-file edits). Keep
choices and orientation on all arrays.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Aff
open Lattice RG Wilson Precision Pressure Pressure.Stores Exterior Bloch Turn
open Work.F03 Work.E03 Next.Fluctuations Push.SectorMeasure Push.SectorMeasure.Oriented
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f}

lemma read_shift {Y : Clip} {σ C Λ : ℝ} (T : PathData G) (hT : T.Bounds Y σ C Λ)
    (R d : ℕ) (V : Config G n) (u : Site n→G.El) (i : Twin n) :
    shorten T R d (gauge u V) i.1 = G.adjoint (u i.1.1) (shorten T R d V i.1) := by
  let F := (G.adjoint (u i.1.1)).toContinuousLinearMap
  change _ = F (∑' l, shortenTerm T _ _ _ _ l)
  rw [F.map_tsum (shorten_summable T V hT R d i.1)]
  apply tsum_congr; intro p
  unfold shortenTerm; split
  next h => rw [PathData.ellTerms, PathData.ellTerms, Work.F05.slot_gauge, F.map_smul]; rfl
  next h => rw [map_zero]

lemma viewed {Y : Clip} {σ C Λ : ℝ} (T : PathData G) (hT : T.Bounds Y σ C Λ)
    (R d : ℕ) (V : Config G n) (u : Site n→G.El) (i : Twin n) :
    plotted T Y R d (gauge u V) i = G.adjoint (u i.1.1) (plotted T Y R d V i) := by
  unfold plotted; split
  next => exact read_shift _ hT ..
  next => rw [shoot, shoot,face_gauge, G.curvature_conjugate,map_smul]

lemma viewed_clip {Y : Clip} {σ C Λ : ℝ} (T : PathData G) (hT : T.Bounds Y σ C Λ)
    (R d : ℕ) (x : ℝ) (V : Config G n) (u : Site n→G.El) (i : Twin n) :
    thinned T Y x d R (gauge u V) i = G.adjoint (u i.1.1) (thinned T Y x d R V i) := by
  unfold thinned; split
  next =>
    have he : PathData.kept Y x i.1.1 (gauge u V) ↔ PathData.kept Y x i.1.1 V := by simp [PathData.kept]
    simp only [he]; split
    next => exact read_shift _ hT ..
    next => rw [map_zero]
  next => simp only [shoot,face_gauge,G.curvature_conjugate,map_smul,toll_gauge]

private lemma turn_rated (z : Site n → G.El) (U : Config G n) (i : Site n) (w : Walk) (x : ℝ) (a : G.Color) :
    rated (gauge z U) i w x (G.adjoint (z (stop i w)) a) = G.adjoint (z i) (rated U i w x a) := by
  unfold rated; rw [travel_gauge]; change x • G.adjoint _ _ = G.adjoint _ (x • G.adjoint _ _)
  rw [map_smul, G.adjoint_mul,G.adjoint_mul,← G.adjoint_mul (z (stop i w))⁻¹ _,inv_mul_cancel,G.adjoint_one]

-- Generic arrays, pay product over column transforms by pointwise theorem,
-- with total read. This permits using the transported operator not just a norm.
section arrays
variable {ι κ : Type*}

def Correspond (F H : ι→κ→Pay G) (p : ι→G.El) (q : κ→G.El) : Prop :=
    ∀ i j (v : G.Color), H i j (G.adjoint (q j) v) = G.adjoint (p i) (F i j v)

lemma Correspond.positions [Fintype κ] {F H : ι→κ→Pay G} {p q} (he : Correspond F H p q) (v : κ→G.Color) (i) :
    zip H (fun j=> G.adjoint (q j) (v j)) i = G.adjoint (p i) (zip F v i) := by simp only [zip,he i,map_sum]

private lemma sum_shift (K H : Cover → Pay G) (hk : Summable K) (hh : Summable H)
    (u v : G.El) (A : G.Color) (he : ∀ x, K x (G.adjoint u A)=G.adjoint v (H x A)) :
    (∑' x,K x) (G.adjoint u A)=G.adjoint v ((∑' x,H x) A) := by
  let L := ContinuousLinearMap.apply ℝ G.Color (G.adjoint u A)
  let M := (G.adjoint v).toContinuousLinearMap.comp (ContinuousLinearMap.apply ℝ G.Color A)
  change L (∑' x,K x) = M (∑' x,H x); rw [L.map_tsum hk,M.map_tsum hh]; exact tsum_congr he

private lemma earth (V : Config G c) (d R : ℕ) (K : Row ι κ) (h : K.safe) (u : Site c → G.El) :
    Correspond (lane R d V K) (lane R d (gauge u V) K) (fun i=>u i.1) (fun i=>u i.1) := by
  intro i j x
  have hj (V : Config G c) : Summable (priced R d V K i j) := by
    apply Summable.of_norm_bounded (h i.2 j.2); intro p
    unfold priced; split
    · exact norm_rated_le ..
    simp
  refine sum_shift _ _ (hj _) (hj V) _ _ _ fun p => ?_
  unfold priced; split
  next h =>
    have hv : j.1 = stop i.1 (route 0 p 1) := h.2.trans (by simpa only [map_zero, add_zero]
      using (Work.E03.stop_route i.1 0 p).symm)
    have he := turn_rated u V i.1 (route 0 p 1) (K i.2 j.2 p) x
    rw [← hv] at he; exact he
  next h => simp

variable {P : Teller G} {T : Tube G S} (hT : P.Funds S T) (R : ℕ) (V : Config G c) (u : Site c → G.El)
include hT

lemma spin_Φ : Correspond (T.Φ R V) (T.Φ R (gauge u V)) (fun i=>u (S.ratio.parent i.1.1))
    (fun i=>u i.1.1) := by
  intro i j x
  have hp (V : Config G c) : Summable (casted S T.R R V (mesh i) (mesh j)) := by
    apply Summable.of_norm_bounded (Row.rights _ _ hT.crosses.2.2.1 P.width.le
      (S.ratio.residue (mesh i).1,(mesh i).2) (mesh j).2); intro v
    dsimp only [casted]; split
    · exact norm_rated_le ..
    simp
  refine sum_shift _ _ (hp _) (hp V) _ _ _ fun v => ?_
  dsimp only [casted]; split
  next h =>
    let i' := (mesh i).1
    let Y := route (lift (S.ratio.residue i')) (S.patch.L.val • v) 1
    have he : S.ratio.parent (stop i' Y)=(mesh j).1 := by
      rw [show stop i' Y = _ from casted_endpoint S i' v,S.ratio.embed_parent]; exact h.2.symm
    let s := replica S.ratio V
    rw [← copied S.ratio S.patch.odd_side]
    have ht := turn_rated (constantGauge u S.ratio) s i' Y (T.R.mf (S.ratio.residue (mesh i).1,(mesh i).2) (mesh j).2 v) x
    simp only [constantGauge,Function.comp_apply,he] at ht; exact ht
  next => simp

lemma spin_I : Correspond (T.Φ' R V) (T.Φ' R (gauge u V)) (u ∘ Prod.fst) (fun i=>u i.1.1) :=
    fun i j x => earth V _ _ T.R.mn (Row.rights _ _ hT.crosses.1 P.width.le) u (pole i) (mesh j) x
lemma spin_N : Correspond (T.N R V) (T.N R (gauge u V)) (u ∘ Prod.fst) (fun i=>u i.1.1) :=
    fun i j x => earth V _ _ T.R.o (Row.rights _ _ hT.crosses.2.1 P.width.le) u i (mesh j) x
end arrays
section spin
variable (P : Teller G) {T : Tube G S} (hT : P.Funds S T) (R : ℕ) (V : Config G c) (u : Site c → G.El)
include P hT

lemma movers (s : ℝ) : let U := gauge u V
    T.vision R s U = (fun i=> G.adjoint (u i.1.1) (T.vision R s V i)) ∧
    T.Mv R s U = (fun i=> G.adjoint (u (S.ratio.parent i.1.1)) (T.Mv R s V i)) ∧
    T.Mw R s U = (fun i=> G.adjoint (u i.1) (T.Mw R s V i)) ∧
    zip (T.N R U) (T.vision R s U) = (fun i=> G.adjoint (u i.1) (zip (T.N R V) (T.vision R s V) i)) := by
  intro U
  obtain ⟨C,W,h1,h2⟩ := hT.feeds; rw [← hT.low] at h2
  have he i : T.vision R s U i=G.adjoint (u i.1.1) (T.vision R s V i) := viewed_clip _ h2 ..
  refine ⟨funext he,?_,?_,?_⟩
  · unfold Tube.Mv; rw [funext he]; funext; exact (spin_Φ hT R V u).positions _ _
  · unfold Tube.Mw; rw [funext he]; funext; exact (spin_I hT R V u).positions _ _
  · rw [funext he]; funext; exact (spin_N hT R V u).positions _ _

lemma target_gauge (U : Config G f) (q : Pos S) (s : ℝ) (k : S.Choices) :
    target T R s q k (gauge u V) (gauge (u∘S.ratio.parent) U) = G.adjoint (u (base S q)) (target T R s q k V U) := by
  rcases q with ⟨a,i⟩; unfold target
  rw [gauge_pulled,gauge_pulled]
  let v := pull a 0 V; let y := u ∘ a.act (R := Per c); let t := pull a 0 U
  have hm : ((u ∘ S.ratio.parent) ∘ (a.act (R:=Per f))) = y ∘ S.ratio.parent := by
    funext j; simp only [y, Function.comp_apply,S.ratio.parent_signed S.patch.odd_side]
  rw [hm]; obtain ⟨C,L,h1,h2⟩ := hT.feeds; rw [← hT.high] at h1
  obtain ⟨-,hf,hc,-⟩ := movers P hT R v y s
  have ht : (y∘S.ratio.parent)∘S.ratio.embed=y := by funext; simp [Function.comp_def, Ratio.embed_parent]
  rcases i with i|i
  · dsimp only [Sum.elim_inl]
    have hx : T.Xf R (gauge (y ∘ S.ratio.parent) t) i=G.adjoint (y (S.ratio.parent i.1.1)) (T.Xf R t i) :=
      viewed T.up h1 .. -- args fix
    rw [map_sub]
    exact congr_arg₂ _ hx (congr_fun hf i)
  dsimp only [Sum.elim_inr]
  rw [(choice_gauge (funds_branch hT) t _ (y ∘ S.ratio.parent)).2, ht, map_sub]; apply congr_arg₂
  · let Q := S.prediction t (choice a k)
    change Tube.Z S (gauge y Q) (gauge y v) i = G.adjoint (y i.1) _
    unfold Tube.Z Lattice.gauge; rw [show y i.1*v i*_ * (y i.1*Q i*_)⁻¹ = y i.1*(v i*(Q i)⁻¹)*(y i.1)⁻¹ by group,G.curvature_conjugate,map_smul]
  exact congr_fun hc i
end spin
end YM.AnalyticNext.ConnectedActivity.Aff
