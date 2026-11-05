import YM.SharpGram.Weak.Reading
import YM.SharpGram.Weak.Compatible

/-!
# Smear estimates on choice-of-coverage, then passage to aligned fields

`Y` from trajectory visible basis chart & tune_grades. Require `Checks`
for this geometry to permit jointly smearing through ties. For **every**
x in free-label system and test t with this supp & norm we have estimates
for the calibrated U = `chart` through d, to the stipulated arity. Then
use known finite-cost apparatus for moving frames. Keep `SubLimits` in same
filter `u`, not the period/cutoff filter resulting from the smearing proof.
Uses adapt of `Stations.harvested`, `podium_seq`, `UVW.Focus.flowing`;
the latter for fixed finite horizons *before* diagonalizing.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SharpGram.Weak.Portfolio
open Function Set Filter MeasureTheory Analysis Next.Rank.Station Extraction Table Ward Climb RG Lattice
open PhysicalNext.RankCovariance Org Spec Next.UVStress Further.CorrectedLift MergeProof.East
open scoped Topology ContDiff BigOperators Classical
set_option quotPrecheck false
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
variable {H:C.Makes}{D:ℕ}{u:Filter (ℕ×ℕ)} [u.NeBot] (X:Portfolio C H D u)
variable (hG:G.Simple){W r T₀}(T:OPE.TableTickets C W r T₀)(hf:u≤f.fuse) (hX : CanSmear X)
variable {R : ℝ} {v k : ℕ} {ε : ℝ}
local notation "U"=> S.Hierarchy
local notation "S'"=> (Bel C.book)
local notation "θ"=> Maxwell.Free.spin_free C.labels
local notation "σ"=> F.room.kernel.spin

section
omit [u.NeBot]
variable (c : ℝ)
def wheel (k : ℕ) : Wheel C D := wok C D (X.atK k) X.aperture c (X.matrix k)
-- Maybe reorder c k. Use named.
include hG T H
lemma granularAfter (hc : Checks (X.p 0).arc (X.p 1).arc (X.p 2).arc c (trays D) D) (hr : 0<R)
    (he : ∀ i:ℕ, Poised X.p X.labelsC H X.omega X.j (trays D) X.z (X.atK (i+k)) (X.matrix (i+k))) :
    Granular (fun i=>wheel X c (i+k)) f θ (trays D) R := by
  have hx (i : ℕ) := w_right c f θ X.aperture (he i) -- explicit
  let w(i) :=wheel X c (i+k)
  change Granular w f _ _ _
  refine ⟨⟨Eventually.of_forall fun i=>(hx i).1,Eventually.of_forall fun i=>(hx i).2.mono fun j h=> h.mono fun k h=>h.1,
     Eventually.of_forall fun i=>(hx i).2.mono fun j h=> h.mono fun k h=> h.2.1,
     Eventually.of_forall fun i=>(hx i).2.mono fun j h=> h.mono fun k h=> h.2.2⟩,
     ((tendsto_add_atTop_iff_nat k).mpr (X.detonates hG)), ?_⟩
  intro n hn t ht x
  exact MergeProof.East.aspect X.p X.labelsC H hG T.system X.omega X.j X.z X.named
    f (Nat.le_add_left ..) R hr (Maxwell.table_smooth _) θ hc t ht (depthWord t x) hn
    ((tendsto_add_atTop_iff_nat k).mpr X.admits) (fun i=>X.matrix (i+k)) he

include F in
lemma admissible (hc : Checks (X.p 0).arc (X.p 1).arc (X.p 2).arc c (trays D) D) (hr : 0<R) (he : 0<ε) :
    ∀ᶠ k in atTop, (X.wheel c k).toStation.Admissible f θ (trays D) R ε := by
  obtain ⟨k,hk⟩:= eventually_atTop.mp X.onLevel
  have h' := supply_wheel _ (X.granularAfter (f:=f) hG T c hc hr (k:=k)
    (fun i =>(hk _ (Nat.le_add_left ..)).2.2.1)) F.room.ordered F.room.kernel.smooth H F.room.generic (Maxwell.table_smooth _) hr ε he
  obtain ⟨m,hm⟩:= eventually_atTop.mp h'
  filter_upwards [eventually_ge_atTop (m+k)] with j hj
  obtain ⟨i,rfl⟩:= Nat.exists_eq_add_of_le' (show k≤j by omega) -- order
  exact hm _ (show _ by omega)

end
variable (c : ℝ)
include F H hf hG T
lemma actual_smears (hc : Checks (X.p 0).arc (X.p 1).arc (X.p 2).arc c (trays D) D) (hr : 0<R) (he : 0<ε) :
    ∀ᶠ k in atTop, ∀ (n : ℕ), n ≤ trays D → ∀ v : Fin n → (Bel C.book).Tag, (∀ i,(v i).1 ≤ D) →
        ∀ t : Test n, tsupport t ⊆ Scaling.window R n →
        ∀ M : ℝ, 0 < M → (∀ x, ‖t x‖ ≤ M) →
        ‖t.applyTo (Next.UVStress.tested (X.radius k) (fun d=> (X.chart F k d).toLinearMap) v) - t.applyTo (disc v)‖ ≤ ε * Station.charge v * M := by
  filter_upwards [X.admissible F hG T c hc hr he,eventually_all.mpr (fun i:Fin (D+1)=> X.chartDraw F T hf hG i),X.onLevel] with k hk he h' n hN v hv t ht M hM hz
  -- not obligating all cutoff convergence uniformly in k
  let V (d) := (X.chart F k d).toLinearMap
  let g : Caps n := fun i=>(v i).1
  let w (j:Fin n) : Fin (D+1) := ⟨g j,Nat.lt_succ_of_le (hv j)⟩
  let T₁ := (X.wheel c k).toStation
  let Y (j:Fin (D+1)) i x := microscope C X.aperture (X.atK k) (X.matrix k) j i (ladder C j x)
  have hP (d:Fin (D+1))(i:ℕ×ℕ)(x:(S').Field d): Y d i x=T₁.atCut i d x:= rfl
  let y : (j:Fin n) → C.book.Ref (g j) := fun j=> X.field k (w j) (ladder C (w j) (v j).2)
  let μ (i:ℕ×ℕ)(j:Fin n) : C.book.Ref (g j) := Y (w j) i (v j).2
  have he (d:Fin (D+1)) (x:(S').Field d) : V d x=S.project d (X.field k d (ladder C d x)) := (he d).2 x
  have hh : S.integralOn g y (dilate T₁.rad t)=t.applyTo (Next.UVStress.tested T₁.r V v) := by
    unfold Table.integralOn; rw [zoom_integral]
    apply t.apply_eq; intro x hx
    change S.value g _ y = S.useAt S _ (panels V ∘ v)
    let l : Fin n → C.book.Token := fun i=>⟨g i,y i⟩
    rw [show panels V ∘ v = S.classTokens ∘ l from funext (fun i => by
      change Sigma.mk (g i) (V (g i) (v i).2)=Sigma.mk (g i) (S.project (g i) (X.field k (w i) (ladder C (w i) ((v i).2))))
      rw [← he (w i)])]
    exact (S.at_project S F.room.kernel.laws.toSymmetric (fun _=>le_rfl) ((Next.UVStress.enlarged T₁.rad _).1 hx) l).symm
  have ht' : Tendsto (fun j : ℕ×ℕ => T₁.paid v hv t j.1 j.2) u (𝓝 (t.applyTo (Next.UVStress.tested T₁.r V v))) := hh ▸
    calibrated_smear F.room.ordered u hf _ (v:=μ) (x:=y) fun i=>h'.2.2.2 (w i) _
  refine le_of_forall_pos_le_add fun η hη => le_of_tendsto ((ht'.sub_const _).norm)
    ((show ∀ᶠ i in f.fuse, ‖T₁.paid v hv t i.1 i.2 - t.applyTo (disc v)‖ ≤ ε * Station.charge v * M + η from
      hk.short hN v hv t ht M hM hz η hη).filter_mono hf)

end YM.SharpGram.Weak.Portfolio

namespace YM.SharpGram
open Function Set Filter MeasureTheory Analysis Extraction Table Ward Climb RG Lattice Org Spec Next.UVStress Further.CorrectedLift MergeProof.East
open scoped Topology ContDiff BigOperators Classical
set_option quotPrecheck false
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
variable {P:ℕ→ Next.UVStress.Panel S}{r:ℕ→ℝ}
local notation "S'"=> (Bel C.book)
variable {n : ℕ} {t : Caps n}

-- just the finite code tests for a given arity/degree schema needed, adapt flowing
include F
lemma fadeTuple
    (hp : ∀ i, 0 < r i)
    (ht : ∀ i : record C t, let x:= hang t (combination (fun j=>(Bel C.book).Field (t j)) i); Fades (fun k => Next.UVStress.tested (r k) (P k) x-disc x))
    (v : ℕ → Ribbon (Bel C.book) t) (x : Ribbon (Bel C.book) t) (hz : ∀ i, Tendsto (fun k => v k i) atTop (𝓝 (x i))) :
    Fades (fun k => tested (r k) (P k) (hang t (v k)) - disc (hang t x)) := by
  let A (i) := (Bel C.book).Field (t i)
  let R (b : Code A) (k : ℕ) := tested (r k) (P k) (hang t (combination A b))
  let H (b : Code A) := disc (hang t (combination A b))
  let U (b : Code A) k := coords A b (v k) • (R b k - H b)
  let D (b : Code A) k := (coords A b (v k)-coords A b x) • H b
  refine ((Fades.sum U Finset.univ ?_).plus (Fades.sum D Finset.univ ?_)).congr ?_ (Eventually.of_forall (fun k y _ => ?_))
  · intro b _; exact (ht b).times (tendsto_coords A b hz)
  · intro b _; apply Fades.small_scalar (smoothDisc (T:=Bel C.book) (Maxwell.table_smooth _) _)
    simpa only [sub_self] using (tendsto_coords A b hz).sub_const (coords A b x)
  · exact fun k => (smoothZoom F.room.kernel.smooth _ (hp k)).sub (smoothDisc (T:=Bel C.book) (Maxwell.table_smooth _) _)
  let M := (S.classMoment S t (r k • y)).compLinearMap fun i => P k (t i)
  let N := (Bel C.book).classMoment (Bel C.book) t y
  change ((∑ b : Code A, U b)+(∑ b, D b)) k y = M (v k)-N x
  have hu b : R b k y=M (combination A b) := rfl
  have hv b : H b y=N (combination A b) := rfl
  rw [basis_tuple A _ M,basis_tuple A _ N,← Finset.sum_sub_distrib]
  simp only [Pi.add_apply, Finset.sum_apply, U,D,Pi.smul_apply, Pi.sub_apply, hu,hv,smul_eq_mul]
  rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun b _=>by ring

namespace Weak.Portfolio
variable {H:C.Makes}{D:ℕ}{u:Filter (ℕ×ℕ)} [u.NeBot] (X:Portfolio C H D u)
variable (hG:G.Simple){W μ T₀}(T:OPE.TableTickets C W μ T₀)(hf:u≤f.fuse) (hX : CanSmear X)

include X hG T hf hX F
lemma coordinates (q : Fin n→ (Bel C.book).Tag) (he : ∀ i,(q i).1 ≤ D) (hv : n ≤ MergeProof.East.trays D) :
    Fades (fun k=> tested (X.radius k) (fun d=>(chart F X k d).toLinearMap) q-disc q) := by
  refine ⟨fun k =>(smoothZoom F.room.kernel.smooth _ (X.charged k)).sub (smoothDisc (T:=Bel C.book) (Maxwell.table_smooth _) _), fun s hK hC M hp ε hε=>?_⟩
  obtain ⟨c,hc⟩:= hX
  obtain ⟨R,hr,hR⟩:= ((Work.A05.compact_fits hK hC).and (eventually_gt_atTop (0:ℝ))).exists
  -- Station.charge could be 0
  let z:=Station.charge q * M
  have h:0≤z:=mul_nonneg (Finset.prod_nonneg (fun i _=>norm_nonneg _)) hp.le
  let η:=ε/(1+z)
  have hη : 0 < η:=div_pos hε (add_pos_of_pos_of_nonneg zero_lt_one h)
  filter_upwards [X.actual_smears F hG T hf c hc hR hη] with k hk t hx hm
  rw [test_sub]; rotate_left
  · exact (smoothZoom F.room.kernel.smooth (panels (fun d=>(X.chart F k d).toLinearMap) ∘ q) (X.charged k)).continuousOn
  · exact (smoothDisc (T:=Bel C.book) (Maxwell.table_smooth _) _).continuousOn
  have he' : z ≤ 1+z:= le_add_of_nonneg_left zero_le_one
  refine (hk n hv q he t (hx.trans hr) M hp hm).trans ?_
  rw [mul_assoc]; exact (mul_le_mul_of_nonneg_left he' hη.le).trans (le_of_eq (div_mul_cancel₀ _ (by linarith : 1+z ≠0)))

lemma progresses (q : ℕ → ∀ d, YM.Spin.change S d)
    (hp : ∀ d : Fin (D+1), ∀ v, Tendsto (fun k => (X.chart F k d).symm (q k d v)) atTop (𝓝 v))
    (hv : n ≤ MergeProof.East.trays D) (he : ∀ i, t i ≤ D) (x : Ribbon (Bel C.book) t) :
    Fades (fun k=> tested (X.radius k) (fun d => (q k d).toLinearMap) (hang t x) - disc (hang t x)) := by
  let p k (i : Fin n) := (X.chart F k (t i)).symm (q k (t i) (x i))
  apply Fades.congr (fadeTuple F X.charged (P:=fun k d=>(chart F X k d).toLinearMap) (fun i=> coordinates F X hG T hf hX _ he hv) p x
    (fun i=> hp (⟨t i,Nat.lt_succ_of_le (he i)⟩:Fin (D+1)) (x i))) (fun k=> (smoothZoom F.room.kernel.smooth _ (X.charged k)).sub (smoothDisc (T:=Bel C.book) (Maxwell.table_smooth _) _))
  filter_upwards with k y _
  change S.classMoment S t _ (fun i => X.chart F k (t i) (p k i)) - _ = S.classMoment S t _ (fun i => q k (t i) (x i))- _
  unfold p; simp
end Weak.Portfolio
end YM.SharpGram
