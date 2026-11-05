import YM.Bid.Town
import YM.Next.ROTATIONS.River

/-!
# ROuter. Discharge Miles exactly. The analytic estimates here precede (& use no part
of) the continuous-rotation bootstrap. Include all collinear spectators & tuples incl empty.
-/
noncomputable section
namespace YM.Outer
open Function Filter Set MeasureTheory Measure Complex Row OS Ward Table Climb Analysis Work.A01
open scoped Topology ContDiff BigOperators NNReal ENNReal InnerProductSpace Matrix.Norms.Frobenius Classical
variable {G : Gauge} {L : Register G} {S : Table L} {m : ℕ}

def vane (a b l : Axis) (n : ℕ) (d : Axis) := if d=b then petal a b l n else if d=a then -petal b a l n else 0
lemma vane_s (a b l n d) : ContDiff ℝ ∞ (vane a b l n d) := by
  unfold vane; split_ifs; exacts [petal_smooth ..,(petal_smooth ..).neg,contDiff_const]
lemma vane_k (a b l n d) : HasCompactSupport (vane a b l n d) := by
  unfold vane; split_ifs; exacts [petal_short a b l n,(petal_short b a l n).neg,HasCompactSupport.zero]
lemma roll_plane (a b d : Axis) (x : E4) : roll (Ortho.plane b a) x d=(if d=b then x a else 0)-(if d=a then x b else 0) := by
  simp [roll,M4.at_coord,Ortho.plane,Matrix.single_apply,ite_and, Finset.sum_sub_distrib,sub_mul,ite_mul, eq_comm]
lemma vane_home (x : E4) (a b l d : Axis) (h : a≠b) : ∀ᶠ n in atTop, vane a b l n d =ᶠ[𝓝 x] comps d (roll (Ortho.plane b a)) := by
  filter_upwards [petal_home a b l x,petal_home b a l x] with n ht hl
  filter_upwards [ht,hl] with p hp hv; by_cases hb:d=b
  · subst d; rw [vane,if_pos rfl,hp,comps,roll_plane]; simp [Ne.symm h]
  by_cases ha:d=a
  · subst d; rw [vane,if_neg hb,if_pos rfl,Pi.neg_apply,hv,comps,roll_plane];simp [hb]
  simp [comps,vane,hb,ha,roll_plane]

abbrev draught (x : Points (m+1)) (q : Fin (m+1)→ S.Tag) (J : Stress S) (a b l : Axis) (n : ℕ) (y : E4) :=
    ∑ d∈other a, breeze J q x a b l d n y
lemma draught_river (x : Points (m+1)) (q : Fin (m+1)→S.Tag) (J : Stress S) (hs : ∀ i j,J i j=J j i) (a b l : Axis) (h : a≠b) (n : ℕ) (y : E4) :
    river x q J (vane a b l n) y=draught x q J a b l n y-draught x q J b a l n y := by
  let F := vane a b l n; let X (d c : Axis) := creek x q J F d c y
  change ∑ d : Axis,∑ c : Axis, X d c=_
  have hv : F b=petal a b l n := if_pos rfl
  have ht : F a= -petal b a l n := by simp [F,vane,h]
  have he d : X d b= breeze J q x a b l d n y := by unfold X creek; rw [hv]; rfl
  have ha d : X d a= -breeze J q x b a l d n y := by
    unfold X creek; rw [ht,D,fderiv_neg,(show ∀ U : E4→L[ℝ]ℝ, (-U) (basis d) = -U (basis d) from fun _ => rfl),neg_smul]; rfl
  rw [Finset.sum_comm, ← Finset.add_sum_erase _ (f:=fun c => ∑ d, X d c) (Finset.mem_univ b),← Finset.add_sum_erase _ _ (apart h)]
  have hl : ∑ c∈(other b).erase a, ∑ d, X d c=0 := Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun d _ => by
    have h1 : i≠a := (Finset.mem_erase.mp hi).1; have h2 := (Finset.mem_erase.mp (show i∈other b from (Finset.mem_erase.mp hi).2)).1
    simp [X,creek,F,vane,h1,h2,D]
  rw [hl,add_zero]; simp_rw [he,ha, Finset.sum_neg_distrib]
  unfold draught other; rw [← Finset.add_sum_erase (f:=fun d => breeze J q x a b l d n y) _ (Finset.mem_univ a),← Finset.add_sum_erase (f:=fun d => breeze J q x b a l d n y) _ (Finset.mem_univ b)]
  have hz : breeze J q x a b l a n y=breeze J q x b a l b n y := by
    unfold breeze; rw [petal_self,petal_self,chart_symm a b]; unfold viewed; rw [hs a b]
  rw [hz]; abel
lemma drained (x : Points (m+1)) (hx : x∈conf _) (q : Fin (m+1)→ S.Tag) (J : Stress S) (P : DiffPlan S) (H : S.Hierarchy) (hp : P.Derivatives S) (hi : P.Orientation H.spin)
    (C : Conserved P H.spin J) (hr : RawTensor H.spin J) (a b l : Axis) (hh : a≠b) (ht : onLine l x) :
    (∀ᶠ n in atTop, Integrable (draught x q J a b l n)) ∧ Budget (-1) (fun n => ∫ y,draught x q J a b l n y) := by
  have he d (h : d∈other a) := blows a b l d (Finset.mem_erase.mp h).1 hh P hp H hi J hr C q x hx ht
  have hv : ∀ᶠ n in atTop, ∀ d∈other a, Integrable (breeze J q x a b l d n) := (eventually_all_finset _).mpr fun d hd => (he d hd).1
  refine ⟨hv.mono fun n h => integrable_finsetSum _ h,?_⟩
  exact (budget_sum (other a) (fun d n => integral volume (breeze J q x a b l d n)) _ (fun d h => (he d h).2)).same
    (hv.mono fun n hn => (integral_finsetSum _ hn).symm)
lemma axisTurn (x : Points (m+1)) (hx : x∈conf _) (q : Fin (m+1)→ S.Tag) (J : Stress S) (P : DiffPlan S) (H : S.Hierarchy) (hp : P.Derivatives S) (hi : P.Orientation H.spin)
    (p : Parts S) (Y : SpinRows S) (h : Pre H P J p Y) (a b l : Axis) (hh : a≠b) (ht : onLine l x) : localTurn p Y (Ortho.plane b a) q x=0 := by
  obtain ⟨hA,hB⟩ := drained x hx q J P H hp hi h.tensor h.symmetric a b l hh ht
  obtain ⟨hY,hZ⟩ := drained x hx q J P H hp hi h.tensor h.symmetric b a l (Ne.symm hh) ht
  let K := Ortho.plane b a
  have he : Budget (-1) (fun _ => localTurn p Y K q x) := by
    refine ((hB.sub hZ).neg).same ?_
    filter_upwards [hA,hY,eventually_all.mpr fun i => eventually_all.mpr fun j => vane_home (x j) a b l i hh] with n hon hin hs
    rw [flux_value P H hp J p Y h K x hx q (vane a b l n) (vane_s a b l n) (vane_k a b l n) hs]
    simp_rw [draught_river x q J h.tensor.symmetric a b l hh n]; rw [integral_sub hon hin]
  exact tendsto_nhds_unique tendsto_const_nhds (he.limits (by norm_num))

private def rl (v : E4) (a : Axis) : Ortho.Skew →ₗ[ℝ] ℝ := {
  toFun K := roll K v a
  map_add' A B := by simp [roll,M4.at_coord,add_mul,Finset.sum_add_distrib]
  map_smul' t A := by simp [roll,M4.at_coord,Finset.mul_sum,mul_assoc] }
lemma swirlLinear (p : Parts S) (Y : SpinRows S) (q : Fin m→ S.Tag) (x : Points m) : ∃ U : Ortho.Skew →ₗ[ℝ] ℂ, ∀ K, localTurn p Y K q x=U K := by
  let v (i : Fin m) : Ortho.Skew→ₗ[ℝ] S.Field (q i).1 := {
    toFun A := Y _ A (q i).2
    map_add' A B := by simp
    map_smul' t A := by simp }
  let T (i : Fin m) := ((here q x i _).restrictScalars ℝ).comp (v i)
  let W (i : Fin m) := ∑ b : Axis,(rl (x i) b).smulRight (disc (update q i (⟨_,p _ b (q i).2⟩:S.Tag)) x)
  refine ⟨∑ i,(T i + W i),fun K => ?_⟩
  unfold localTurn; simp only [LinearMap.sum_apply, LinearMap.add_apply]
  refine Finset.sum_congr rfl fun i _ => ?_; rw [turns,← takes]; unfold T W; rw [LinearMap.sum_apply]; rfl
lemma fullTurn (P : DiffPlan S) (H : S.Hierarchy) (hp : P.Derivatives S) (hi : P.Orientation H.spin) (J : Stress S)
    (p : Parts S) (Y : SpinRows S) (h : Pre H P J p Y) (x : Points m) (hx : x∈conf _) (q : Fin m → S.Tag) (l : Axis) (ht : onLine l x) (K : Ortho.Skew) :
    localTurn p Y K q x=0 := by
  cases m with
  | zero => simp [localTurn]
  | succ m =>
    obtain ⟨U,hU⟩ := swirlLinear p Y q x
    have he : U=0 := by
      refine Spin.extendsE _ _ fun i => ?_
      obtain ⟨b,a⟩ := i
      by_cases hf:a=b
      · subst b; rw [show Spin.K (a,a)=0 from Subtype.ext (by simp [Spin.K,Ortho.plane]),map_zero,LinearMap.zero_apply]
      rw [← hU]; exact axisTurn x hx q J P H hp hi p Y h a b l hf ht
    rw [hU,he,LinearMap.zero_apply]

lemma stagger (x : Points m) (hx : x∈conf _) (p : Parts S) (Y : SpinRows S) (q : Fin m→ S.Tag) (H : S.Hierarchy) (a b : Axis) (h : a≠b) :
    localTurn p Y (Ortho.plane b a) q (Points.across (basis a) x) = localTurn p Y (Ortho.plane b a) q x +
      ∑ i, disc (update q i (⟨_,p _ b (q i).2⟩:S.Tag)) x := by
  let K := Ortho.plane b a; let y := Points.across (basis a) x
  have he (r : Fin m→S.Tag) : disc r y=disc r x := H.translations m x hx _ (expose ∘ r)
  have hf (i : Fin m) (j : Axis) : M4.move K.val (y i) j = M4.move K.val (x i) j + basis b j := by
    have h : roll K (basis a) j=basis b j := by
      rw [show K= _ from rfl,roll_plane]; by_cases hv : j=b <;> simp [hv,Ne.symm h]
    rw [← h]; exact congr_arg (fun y : E4 => y j) (map_add (Matrix.toEuclideanLin K.val) (x i) (basis a))
  change localTurn p Y K q y=_; unfold localTurn; simp_rw [he,hf,add_smul,Finset.sum_add_distrib]
  simp [add_assoc,K]
lemma shiftedLine (x : Points m) (l : Axis) (h : onLine l x) : onLine l (Points.across (basis l) x) := by
  intro i; obtain ⟨t,ht⟩ := h i
  exact ⟨t+1,by rw [add_smul,one_smul,← ht]; rfl⟩

/-- Stronger than Miles, hence no rank/scale law used to obtain itself. -/
theorem outer (P : DiffPlan S) (H : S.Hierarchy) (hp : P.Derivatives S) (hi : P.Orientation H.spin) (J : Stress S)
    (p : Parts S) (Y : SpinRows S) (h : Pre H P J p Y) :
    Bid.LineSum p ∧ ∀ K a n (q : Fin n→ S.Tag) (x : Points n), x∈conf _ → onLine a x → localTurn p Y K q x=0 := by
  refine ⟨?_,fun K a _ q x hx ht => fullTurn P H hp hi J p Y h x hx q _ ht K⟩
  intro d n l b hb v x hx ht
  let q := column v
  have he := stagger x hx p Y q H l b (Ne.symm hb)
  rw [fullTurn P H hp hi J p Y h _ hx _ l ht, fullTurn P H hp hi J p Y h _ (Points.across_in _ hx) _ l (shiftedLine x l ht),zero_add] at he; exact he.symm

theorem miles : YM.Bid.Miles := fun V _ I H _ h => outer V H.basis.kernel h H.aligned I.J I.p I.Y H.planet
end YM.Outer
