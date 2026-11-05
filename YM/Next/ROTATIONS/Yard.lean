import YM.Next.ROTATIONS.Patch
import YM.Org.Twist
import YM.Work.A01.Support

/-!
# Decay at external distances applied to actual Ward integrand
-/
noncomputable section
namespace YM.Outer
open Function Filter Set MeasureTheory Measure Complex Boundary Probe Row OS Table Ward Word
open scoped Topology ContDiff NNReal ENNReal BigOperators InnerProductSpace Classical
variable {G : Gauge} {L : Register G} {S : Table L} {m : ℕ}

lemma fan_out (l : Axis) (D : Weight L→Prop) (h : ∀ A B : Weight L,D A → D B → D (A+B))
    (he : ∀ A : Weight L, (∀ i∈other l,Pressed i A) → ∀ e : Axis→Bool,(∀ i,Own A i (e i)) → D A) :
    ∀ A, (∀ i∈other l,Pressed i A) → D A := by
  have hm (R : Finset Axis) : ∀ A : Weight L,(∀ i∈other l,Pressed i A) → ∀ e : Axis→Bool,(∀ i∉R,Own A i (e i)) → D A := by
    induction R using Finset.induction_on with
    | empty => exact fun A hh e hp => he A hh e (fun i => hp _ (by simp))
    | insert i R hi ih =>
      intro A hh e hp
      have hu (b : Bool) : D (chooseSign i b A) := ih _ (fun j hj => pressed_choose _ _ _ (hh j hj) _) (update e i b) fun j hj => by
        by_cases hz:j=i
        · subst j; rw [update_self]; exact chosen ..
        rw [update_of_ne hz]; exact stable _ _ _ A (hp j (by simp [hj,hz]))
      rw [← joins i A]; exact h _ _ (hu _) (hu _)
  exact fun A hh => hm Finset.univ A hh (fun _ => true) (by simp)

lemma off_label (B A : Weight L) (H : S.Hierarchy) (a b l d : Axis) (h : d≠a)
    (k : Axis) (f : Bool) (hf : Own B k f) (hh : Own A k (spar d b k)) (hp : f≠spar a b k) (n : ℕ) :
    (∫ q, readsCluster S B A q * positionTest (tracks (chart a b l) d n (canvas (shiftPlot d (orchard a)))) q)=0 := by
  let z (q : E4) := readsCluster S B A q * positionTest (tracks (chart a b l) d n (canvas (shiftPlot d (orchard a)))) q
  let K := Ortho.motion (Signed.reflect k)
  have hm (q : E4) : z (K q)= -z q := by
    have hu : signValue f*signValue (spar d b k)*signValue (spar a d k)=-1 := by
      have he (x y z f : Bool) (hp : f≠ Bool.xor x y) : signValue f*signValue (Bool.xor z y)*signValue (Bool.xor x z)=-1 := by
        cases x <;> cases y <;> cases z <;> cases f <;> simp_all [signValue]
      exact he _ _ _ _ hp
    unfold z; rw [show K q=Ortho.move _ q from rfl,reads_mirror S H.spin k B A f _ hf hh,pose_sign a b l d k h]
    simp only [← mul_assoc] at *; rw [mul_right_comm _ (readsCluster _ _ _ q),hu]; simp
  have ht : (∫ q,z q)= -(∫ q, z q) := by
    conv_lhs => rw [← K.measurePreserving.integral_comp K.toHomeomorph.measurableEmbedding]
    simp_rw [hm,integral_neg]
  have hp : 2*(∫ q,z q)=0 := by
    rw [two_mul]; conv_lhs => lhs; rw [ht]
    exact neg_add_cancel _
  exact (mul_eq_zero.mp hp).resolve_left (by norm_num)

lemma pick_price (a b l d : Axis) (hd : d≠a) (hh : a≠b) (P : DiffPlan S) (hP : P.Derivatives S) (H : S.Hierarchy) (hi : P.Orientation H.spin) (J : Stress S) (hr : RawTensor H.spin J) (C : Conserved P H.spin J) (B : Weight L)
    (hu : ∀ i∈other l,Pressed i B) :
    let T n := fun q : E4 => readsCluster S B (pick (J d b)) q * Complex.ofReal (Analysis.D (basis d) (petal a b l n) q)
    (∀ᶠ n in atTop, Integrable (T n)) ∧ Budget (-1) (fun n => ∫ q, T n q) := by
  intro T
  let V i := Classical.choice (realization H i)
  obtain ⟨A,hA,hx,ht⟩ := enters_weights H _ _ (shines J H hr d b)
  let f := canvas (shiftPlot d (orchard a)); have hf : ∀ p : ℝ,hat (f d) p≠0 → 1≤|p| := pose_far a d hd
  let R (B : Weight L) n := fun q : E4 => readsCluster S B A q * positionTest (tracks (chart a b l) d n f) q
  let D (B : Weight L) := (∀ᶠ n in atTop, Integrable (R B n)) ∧ Budget (-101) (fun n => integral volume (R B n))
  have hp : D B := by
    refine fan_out l D (fun U C H h => ?_) (fun B h e H' => ?_) B hu
    · have he (n : ℕ) q : R (U+C) n q=R U n q+R C n q := by unfold R; rw [reads_add_l,add_mul]
      rcases H with ⟨hI,hU⟩; rcases h with ⟨hj,hj'⟩
      refine ⟨?_, (hU.add hj').same ?_⟩
      · filter_upwards [hI,hj] with n hv ht; rw [funext (he n)]; exact hv.add ht
      filter_upwards [hI,hj] with n hv ht; rw [funext (he n),integral_add hv ht]
    have hk : chart a b l d < 0 := (chart_bounds a b l d).2.trans_lt (by norm_num)
    refine ⟨(track_sale _ d (V d) H B A _ _ (H' _) (hx _) f hk hf).mono fun _ H => H.1,?_⟩
    by_cases hz : e=spar a b
    · subst e
      exact exterior_size a b l d hd hh P hP V H hi J hr C B A hA H' h hx ht f hf
    obtain ⟨k,hk⟩ := Function.ne_iff.mp hz
    exact (no_budget (X:=ℂ) (-101)).same (.of_forall fun n => (off_label B A H a b l d hd k _ (H' _) (hx _) hk n).symm)
  have he n : T n= fun q => (fuel 100 n:ℂ) * R B n q := by
    ext1 q; unfold T R; rw [hA.1,track_pose,mul_left_comm]
  rcases hp with ⟨h,h'⟩
  simp_rw [he]; exact ⟨h.mono fun n hn => hn.const_mul _, (((budget_fuel 100).of_r.prod h').rise (le_of_eq (by ring))).same
    (.of_forall fun n => (integral_const_mul ..).symm)⟩

abbrev viewed (J : Stress S) (q : Fin m→ S.Tag) (x : Points m) (d b : Axis) (y : E4) := S.useAt S
  (Points.cons y x) (Fin.cons ⟨4,J d b⟩ q)
abbrev breeze (J : Stress S) (q : Fin m→ S.Tag) (x : Points m) (a b l d : Axis) (n : ℕ) (y : E4) :=
    Complex.ofReal (Analysis.D (basis d) (petal a b l n) y) * viewed J q x d b y

lemma collimated (J : Stress S) (H : S.Hierarchy) (q : Fin m→S.Tag) (x : Points m) (hx : x∈conf m) (l : Axis) (ht : onLine l x) (d b : Axis) :
    ∃ B : Weight L,(∀ i ∈ other l,Pressed i B) ∧ ∀ y : E4,Points.cons y x∈conf _ → viewed J q x d b y=readsCluster S B (pick (J d b)) y := by
  let V : Fin m→ L.Token := fun i => L.conjugate (expose (q i))
  let W := realize V x
  have hW : distinct W := (Word.realized ..).mpr hx
  let U : Core L := ⟨W.reverse,locations.mpr (by rw [List.map_reverse]; exact List.nodup_reverse.mpr (locations.mp hW))⟩
  refine ⟨nice U,fun i hi A hA p hp => ?_,fun y hy => ?_⟩
  · unfold nice at hA; simp only [Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] at hA
    subst A; rw [show U.val=W.reverse from rfl,List.mem_reverse] at hp; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hp
    obtain ⟨v,hv⟩ := ht j; change x j i=0; rw [hv]; simp [(Finset.mem_erase.mp hi).1]
  let r := realize (expose ∘ q) x; let f := (y,expose (tag J d b)); let v : Fin (m+1)→S.Tag := Fin.cons (tag J d b) q
  have hh : carry (piece (S.representative _ (J d b))).val y=[f] := by simp [carry,f,tag,expose,piece]
  have he : conjugate U.val.reverse=r := by
    rw [show U.val=W.reverse from rfl,List.reverse_reverse]; unfold conjugate W r realize
    rw [List.map_ofFn]; congr 1; ext1 i; unfold V; dsimp only [Function.comp_apply]; congr 1; cases t : expose (q i) with | mk j v => simp [Register.conjugate]; exact star_star _
  have hq : f::r=realize (expose ∘ v) (Points.cons y x) := by rw [realize,List.ofFn_succ]; unfold r realize; simp [v,f, Points.cons]
  have hp : distinct (f::r) := hq ▸ ((Word.realized ..).mpr hy)
  have hF : List.Perm (f::r) (r ++ [f]) := @List.perm_append_comm _ [f] r
  rw [pick,reads_nice,bare]
  simp only [he,hh]; rw [if_pos (locations.mpr ((hF.map _).nodup (locations.mp hp))),Table.order S H.laws.toSymmetric hp hF,hq,S.readAt]; rfl

lemma blows (a b l d : Axis) (hd : d≠a) (hh : a≠b) (P : DiffPlan S) (hP : P.Derivatives S) (H : S.Hierarchy) (hi : P.Orientation H.spin)
    (J : Stress S) (hr : RawTensor H.spin J) (C : Conserved P H.spin J) (q : Fin m→S.Tag) (x : Points m) (hx : x∈conf m) (ht : onLine l x) :
    (∀ᶠ n in atTop, Integrable (breeze J q x a b l d n)) ∧ Budget (-1) (fun n => ∫ y,breeze J q x a b l d n y) := by
  obtain ⟨B,hB,h⟩ := collimated J H q x hx l ht d b
  obtain ⟨hA,hC⟩ := pick_price a b l d hd hh P hP H hi J hr C B hB
  have he n : (fun y : E4 => readsCluster S B (pick (J d b)) y * Complex.ofReal (Analysis.D (basis d) (petal a b l n) y)) =ᵐ[volume] breeze J q x a b l d n := by
    have hu : ∀ᵐ p : E4,p∉ Set.range x.ofLp := by rw [ae_iff]; simpa only [Classical.not_not, setOf_mem_eq] using (finite_range _).measure_zero _
    filter_upwards [hu] with p hp
    unfold breeze; rw [h p (Work.A01.conf_cons hx fun i he => hp ⟨i,he.symm⟩),mul_comm]
  exact ⟨hA.mono fun n hn => hn.congr (he n),hC.same (Eventually.of_forall fun n => integral_congr_ae (he n))⟩
end YM.Outer
