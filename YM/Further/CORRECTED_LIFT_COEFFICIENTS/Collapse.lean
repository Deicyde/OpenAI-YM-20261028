import YM.Extra.MULTISOURCE_TRAJECTORIES.Service
import YM.Extra.WILSON_STARTUP.Curvature
import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Deliver
import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Symbol
import YM.Further.CORRECTED_LIFT_COEFFICIENTS.TurnCorner

/-!
# Actually realize the chart. I: collapse the loops

Germs for eventual use at the
identity, no mask detection here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CorrectedLift.Collapse
open Filter Function Set Lattice Wilson Labels RG Cells Source Source.Drops WilsonStartup
open Work Push.Corrected Push.CutoffProjectors
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G : Gauge} {n : Side}

private lemma across (w z : Walk) (a b : Lattice.Step) (U : CoverConfig G) :
    let T := travel U 0 w
    travel U 0 (w++a::b::z) = (T*travel U (stop 0 w) (oriented a b)*T⁻¹) * travel U 0 (w++b::a::z) := by
  intro T; unfold T; rw [travel_append _ 0 w _, travel_append _ 0 w _]
  let i := stop (0:Cover) w
  have he : i+a.vec+b.vec=i+b.vec+a.vec := add_right_comm _ _ _
  have ht : i+a.vec+b.vec+a.rev.vec=i+b.vec := by rw [Step.vec_rev]; abel
  simp only [Lattice.oriented,travel,mul_one]
  change travel U 0 w * (a.read U i * (b.read U _ * travel U (i+a.vec+b.vec) z)) = (T *
    (a.read U i * (b.read U (i+a.vec) * (a.rev.read U (i+a.vec+b.vec)* b.rev.read U (i+a.vec+b.vec+a.rev.vec))))*T⁻¹) * (T*(b.read U i * (a.read U (i+b.vec)*_)))
  rw [ht,he,Step.read_rev,Step.read_rev]; unfold T; group
  rw [add_comm _ i]

-- Each time use one more positive slot with fixed-scale sign
abbrev Brick := Slot × { r : ℝ // r=1 ∨ r=-1 }
def lay (U : CoverConfig G) (b : Brick) := recover G (b.2.val • b.1.eval U)

private lemma swap (w z : Walk) (a b : Lattice.Step) (h : a.dir≠b.dir) : ∃ B : Brick, B.1.walk.length ≤ w.length+2 ∧
    ∀ᶠ U : CoverConfig G in 𝓝 1, travel U 0 (w++a::b::z) = lay U B * travel U 0 (w++b::a::z) := by
  obtain ⟨v,c,ha,hc,hv⟩ := Compass.worth (G:=G) w a b h
  let i := stop (0:Cover) w
  let T (U : CoverConfig G) := travel U 0 w
  let F (U : CoverConfig G) := T U * travel U i (oriented a b) * (T U)⁻¹
  have he : Continuous F := by dsimp only [T,F]; fun_prop
  have hz : F 1 = 1 := by dsimp only [T,F]; rw [Pressure.one,Pressure.one]; group
  refine ⟨(v,⟨c,hc⟩),ha,?_⟩
  filter_upwards [(show Tendsto F (𝓝 1) (𝓝 1) from hz ▸ he.tendsto 1).eventually (recover_left G)] with U hU
  change travel U 0 (w++a::b::z)=recover G (c • v.eval U)* _
  rw [← hv]; change _= recover G (G.adjoint (T U) (G.curvature (travel U i (oriented a b)))) * _
  rw [← G.curvature_conjugate,hU]; exact across w z a b U

private lemma share {a b : Lattice.Step} (h : a.dir=b.dir) (he : a.rev≠b) : a=b := by
  rcases a with ⟨i,_|_⟩ <;> rcases b with ⟨j,_|_⟩ <;> obtain rfl : i=j := h
  all_goals first | rfl | exact False.elim (he rfl)

private lemma next (A L : Walk) (a : Lattice.Step) (he : a.rev∈L) : ∃ Z : Walk, ∃ X : List Brick,
    Z.length+2=(A++a::L).length ∧ X.length≤L.length ∧ (∀ b∈X,b.1.walk.length ≤ (A++a::L).length) ∧
      stop (0:Cover) (A++a::L)=stop 0 Z ∧
        ∀ᶠ U : CoverConfig G in 𝓝 1, travel U 0 (A++a::L) = (X.map (lay U)).prod * travel U 0 Z := by
  induction L generalizing A with
  | nil => cases he
  | cons b w ih =>
    by_cases hh : a.rev=b
    · subst b; refine ⟨A++w,[],by simp; omega, by simp, by simp,?_,Eventually.of_forall fun U => ?_⟩
      · simp [stop_append,stop,Step.vec_rev]
      simp [travel_append,travel,Step.vec_rev]
    have hi := List.mem_of_ne_of_mem hh he
    obtain ⟨Z,X,hz,hX,ht,hv,hu⟩ := ih (A++[b]) hi
    rw [List.append_assoc] at hz ht hv hu
    have hp : (A++a::b::w).length=(A++[b]++(a::w)).length := by simp
    rw [List.append_assoc] at hp
    refine ⟨Z,?_⟩
    have hs : stop (0:Cover) (A++a::b::w)=stop 0 Z := Eq.trans (by
      simp only [List.singleton_append,stop_append, stop]; rw [add_right_comm]) hv
    by_cases he : a.dir=b.dir
    · obtain rfl := share he hh; exact ⟨X,hz,hX.trans (Nat.le_succ _),ht,hs,hu⟩
    obtain ⟨B,hB,H⟩ := swap (G:=G) A w a b he; refine ⟨B::X,hz.trans hp.symm,Nat.succ_le_succ hX, ?_,hs,?_⟩
    · intro i hi; rcases List.mem_cons.mp hi with rfl|hi
      · exact hB.trans (by simp)
      exact hp.symm ▸ ht i hi
    filter_upwards [hu,H] with U hx he
    change travel U 0 (A++b::a::w)=_ at hx
    rw [he,hx,List.map_cons,List.prod_cons,mul_assoc]

private lemma back (w : Walk) (a : Lattice.Step) (h : stop (0:Cover) (a::w)=0) : a.rev∈w := by
  by_contra ht
  rcases a with ⟨i,_|_⟩
  · have hs (z : Cover) (x : Walk) (h : negDir i ∉ x) : z i ≤ stop z x i := by
      induction x generalizing z with
      | nil => rfl
      | cons u x ih =>
        rw [List.mem_cons, not_or] at h; obtain ⟨h1,h2⟩ := h
        refine le_trans ?_ (ih (z+u.vec) h2)
        rcases u with ⟨j,_|_⟩
        · change _ ≤ z i+step j i; simp only [step_apply]; split <;> omega
        have he : j≠i := by rintro rfl; exact h1 rfl
        change _ ≤ z i+ -step j i; simp [he.symm]
    change stop (0+(posDir i).vec) w = _ at h
    have he := hs (0+(posDir i).vec) w ht; rw [h] at he; simp at he
  have hs (z : Cover) (x : Walk) (h : posDir i ∉ x) : stop z x i ≤ z i := by
    induction x generalizing z with
    | nil => rfl
    | cons u x ih =>
      rw [List.mem_cons, not_or] at h; obtain ⟨h1,h2⟩ := h; refine (ih (z+u.vec) h2).trans ?_
      rcases u with ⟨j,_|_⟩
      · have he : j≠i := by rintro rfl; exact h1 rfl
        change z i+step j i ≤ _; simp [he.symm]
      change z i+ -step j i ≤ _; simp only [step_apply]; split <;> omega
  change stop (0+(negDir i).vec) w=_ at h
  have he := hs (0+(negDir i).vec) w ht; rw [h] at he; simp at he

lemma compress (w : Walk) (he : stop (0:Cover) w=0) : ∃ X : List Brick,
    X.length ≤ w.length^2 ∧ (∀ b∈X,b.1.walk.length ≤ w.length) ∧
      ∀ᶠ U : CoverConfig G in 𝓝 1, travel U 0 w=(X.map (lay U)).prod := by
  generalize hp : w.length = n
  induction n using Nat.strong_induction_on generalizing w with | h n ih =>
  cases w with
  | nil => exact ⟨[],Nat.zero_le _,by simp,Eventually.of_forall fun _ => rfl⟩
  | cons a w =>
    obtain ⟨Z,X,hz,hl,hX,hw,hy⟩ := next (G:=G) [] w a (back w a he)
    rw [List.nil_append] at hz hw hX hy; rw [hp] at hz hX; rw [List.length_cons] at hp
    obtain ⟨L,hL,hm,h⟩ := ih Z.length (by omega) Z (hw.symm.trans he) rfl
    refine ⟨X++L, ?_,fun b hb => Or.elim (List.mem_append.mp hb) (hX b) (fun he => (hm b he).trans (by omega)),?_⟩
    · rw [List.length_append]; apply (add_le_add hl hL).trans; rw [← hz]; nlinarith only [hp,hz]
    filter_upwards [h,hy] with U hQ hr
    rw [hr,hQ,List.map_append,List.prod_append]
end YM.Further.CorrectedLift.Collapse
