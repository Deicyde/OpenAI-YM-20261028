import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.AffOrd
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Voyage
import YM.Progress.STATIONARY_SCENES.Response

/-!
# Spring in one unified F: response and turns

Copy straightens. At a negative link the Ad transported row derivative also
has Ad of barV (not in spring, flat oriented exactly before V changes). The
stencil stamp is available pre choice from StationaryScenes, no extra
witness per branch.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.SliceRows
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid Response Next.Free
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f n : Side} {P : Teller G} {S : StepData c f} {T : Tube G S}

lemma spring_smul (F : Forest S.ratio) (b : LogField G c) (s : ℝ) : spring T F (s • b)=s • spring T F b := by
  have he (i) : linearCopy S.ratio (collect G (s • b)) i = s • linearCopy S.ratio (collect G b) i := by
    unfold linearCopy; split
    next hh => rw [smul_zero]
    next hh => rfl
  have hp (i:G.ColorIndex) : parts G 1 (s • b) i=s • parts G 1 b i := rfl
  funext i; rw [Pi.smul_apply,spring_ticks,spring_ticks]; split
  next hv => rw [smul_zero]
  next hv =>
    ext j; unfold relative
    simp only [hp, he,Matrix.mulVec_smul, Pi.smul_apply,PiLp.smul_apply, smul_eq_mul]; ring

lemma spring_cap (P : Teller G) : ∃ C : ℝ, 0<C ∧ ∀ {c f : Side} (S : StepData c f) (T : Tube G S), P.Funds S T →
    ∀ (F : Forest S.ratio) (b : LogField G c), ‖spring T F b‖ ≤ C*‖b‖ := by
  let C := Response.total P.j P.η P.C + Real.exp P.η
  let h := max 1 (max 0 C * Fintype.card G.ColorIndex)
  have hC : C ≤ max 0 C := le_max_right ..
  have hh : 0 < h := zero_lt_one.trans_le (le_max_left ..)
  refine ⟨h, hh, fun {c f} S T hp F b => ?_⟩
  let A := ‖b‖
  have hv (b : LogField G c) (ht : ‖b‖ ≤ 1) : ‖spring T F b‖ ≤ h := by
    refine (pi_norm_le_iff_of_nonneg hh.le).mpr fun i => ?_
    rw [spring_ticks]; split
    next hn => rw [norm_zero]; exact hh.le
    next hn =>
      let x : F.Free := ⟨i,hn⟩
      have hO j : |relative F (installed S.ratio T.R.A0) b x j| ≤ C := by
        unfold C; rw [← hp.atStep]
        refine tangent_apply S P.width.le ?_ F x j b ?_
        · have he := (hp.crosses.2.2.2 [] (Nat.zero_le _)).1; simp only [advanceC,List.length_nil,add_zero,pow_one] at he; exact he
        intro e; apply ((stand_cap j (b e)).trans ((norm_le_pi_norm _ _).trans ht)).trans
        apply Real.one_le_exp; have := P.width; positivity
      exact (color_cover (le_max_left ..) _ (fun j => (hO j).trans hC)).trans
        ((mul_comm ..).le.trans (le_max_right (1:ℝ) _))
  by_cases he : b=0
  · have hs := spring_smul (T:=T) F (0:LogField G c) 0; rw [zero_smul,zero_smul] at hs; simp [he,hs]
  have hx : 0<A := norm_pos_iff.mpr he
  have hk : ‖A⁻¹ • b‖ ≤ 1 := by rw [norm_smul, Real.norm_of_nonneg (by positivity)]; exact (inv_mul_cancel₀ hx.ne').le
  have hi := hv _ hk; rw [spring_smul,norm_smul,Real.norm_of_nonneg (by positivity), inv_mul_eq_div] at hi
  exact (div_le_iff₀ hx).mp hi

lemma moves (x : LogField G n) (s : Signed) : collect G (pulled x s)=displacement s (collect G x) 1 := by
  funext i; unfold displacement pulled; dsimp only [collect]
  have he : axisEquiv.symm (coord i.2)=i.2 := axisEquiv.symm_apply_apply _
  unfold edge sendEdge; simp only [he,Step.rotate, posDir, Bool.false_xor]; split <;> simp
lemma light_pull (x : LogField G n) (s : Signed) : ‖pulled x s‖ ≤ ‖x‖ := by
  have hh (a : LogField G n) : ‖a‖=‖collect G a‖ := by rw [← counted,logged]
  rw [hh, hh x,moves]; exact displacement_bounded ..

lemma rotor_copy (b : LogField G c) (s : Signed) :
    displacement s (linearCopy S.ratio (collect G b)) 1 = linearCopy S.ratio (collect G (pulled b s)) := by
  let x := linearCopy S.ratio (collect G b)
  let y := linearCopy S.ratio (collect G (pulled b s))
  let z := pulled (toLog x) s
  rw [← show collect G z=displacement s x 1 from by unfold z; rw [moves,collects]]
  have he (k : ℝ) : represent (k • z) = represent (k • toLog y) := by
    let f' (b : LogField G c) := toLog (linearCopy S.ratio (collect G b))
    have hp (b : LogField G c) : represent (k • f' b) = replica S.ratio (represent (k • b)) := by
      have ht : k • f' b = f' (k • b) := by
        unfold f' linearCopy collect toLog; funext i; rw [Pi.smul_apply]; dsimp only; split
        next hn => rw [smul_zero]
        next hn => rfl
      rw [ht]; unfold f' represent; rw [collects]; exact exp_copy ..
    unfold z; rw [← represent_pulled,hp,pulls_replica, represent_pulled]; exact (hp _).symm
  have hb : z=toLog y := by
    funext i; obtain ⟨p,rfl⟩ := (poleEquiv f).surjective i
    apply G.colorMat_injective
    have hs := Work.F03.represent_rate z p; simp_rw [he] at hs
    exact hs.unique (Work.F03.represent_rate (toLog y) p)
  rw [hb,collects]

/-- The uncutChannel already annihilates around `spring`. Used near a remote
row of `priced` to price a real linear identity. -/
lemma rear (hp : P.Funds S T) (h : Stamp T) (F : Forest S.ratio) (a : LogField G c) (s : Signed) (p : Rod c f) :
    let v := spring T F a; let x := pulled a s; let C := linearCopy S.ratio (collect G x)
    (linearCost T (toLog C) x p-linearGuide T x p) + uncutField T (displacement s v 1) p = 0 := by
  intro v x C; let b := pulled (shifted T F a) s; let V := displacement s v 1
  have ht : V + C=collect G b := by
    unfold b; rw [moves,show C=linearCopy S.ratio (collect G x) from rfl,← rotor_copy]
    funext i; unfold V displacement v spring; rw [Pi.add_apply]; split
    next hh => simp only [Pi.sub_apply,map_sub]; abel
    next hh => simp only [Pi.sub_apply, sub_add_cancel]
  have he : uncutField T V p+linearCost T (toLog C) x p=linearGuide T x p := by
    rw [← SliceRows.linear_add T hp,ht,logged]
    exact congr_fun (accords hp h F a s) p
  rw [show displacement s v (1:Config G f)=V from rfl]
  rw [← he]; abel
end YM.ConnectedActivityE6.SliceRows
