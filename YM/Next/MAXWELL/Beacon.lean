import YM.Bid.Loan
import YM.Bid.Station
import YM.Next.MAXWELL.Scripts
import YM.Next.MAXWELL.Taxes
import YM.Work.A14



/-!
# K and J, on the real Shell and Polynomial Bel

Select inputs for Lighthouse on an arbitrary register. Preserve
negative gradient and both options for the choice of nonzero multiplier
(normalization in the IR argument must eventually be paid separately).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis MeasureTheory Wick
open scoped ContDiff Topology BigOperators InnerProductSpace ComplexOrder
variable {G : Gauge} (F : Labels.Frames G) {n d : ℕ}

lemma gear_cont (d : ℕ) (p : (Model F).Field d) : Continuous (fun s => (gear F).act d s p) := by
  let B := Module.finBasis ℂ ((Model F).Field d)
  let f s := (gear F).act d s p
  have he (s) : f s = ∑ i, B.coord i (f s) • B i := (B.sum_repr (f s)).symm
  change Continuous f
  have ht (i) : Continuous (fun s => B.coord i (f s)) := by
    obtain ⟨g,hg,H⟩ := writes_any F d (B.coord i) p
    rw [← show g ∘ paints = _ from funext H]; exact hg.continuous.comp reads_cont
  rw [show f = (fun s => ∑ i, B.coord i (f s) • B i) from funext he]
  exact continuous_finsetSum _ fun i _ => (ht i).smul continuous_const

lemma gear_has (d : ℕ) (p : (Model F).Field d) (s : Ortho.Skew) :
    HasDerivAt (fun t => (gear F).act d (Ortho.oneParameter s t) p) ((gear F).lie d s p) 0 := by
  let B := Module.finBasis ℂ ((Model F).Field d)
  let f t := (gear F).act d (Ortho.oneParameter s t) p
  have he (p : (Model F).Field d) : p=∑ i, B.coord i p • B i := (B.sum_repr p).symm
  let z := (gear F).lie d s p
  change HasDerivAt f z 0
  rw [show f = _ from funext (fun t => he (f t)), he z]
  exact HasDerivAt.fun_sum (u := Finset.univ) fun i _ => (actual_generator F d (B.coord i) p s).smul_const (B i)

lemma gear_port : Spin.Port (gear F) (spin_free F) where
  spin := gear_cont F
  fixes d p := address_inj F d (by rw [paints_gear,pol_one])
  sends d g k s := address_inj F d (by simp only [paints_gear, pol_mul])
  signed d k s := address_inj F d (by rw [paints_gear,address_motion])
  real d s x := address_inj F d (by
    rw [address_star,paints_gear,paints_gear,address_star]; apply equalPol; intro A
    rw [real_eval,reflects_eval,reflects_eval,real_eval])
  spinAt d g x := gear_has F d x g

lemma gear_motion : (gear F).Oriented (Model F) := by
  intro n p x hx s; rw [display,display]
  rw [show (supply F ∘ Table.Rotation.label (gear F) s ∘ p) = _ from
    funext (fun i => (show _=reflectPol s (supply F (p i)) from paints_gear F _ s ((p i).snd)))]
  exact moment_rotation x hx _ s

lemma gear_laws : (gear F).Laws (scheme F) (spin_free F) := Work.A14.laws_of_oriented
  (hierarchy F) _ (scheme_filters F) (scheme_derives F) _ (gear_port F) (gear_motion F)

section flux
variable {x : Points (n+1)}





lemma upper_charge (p : (Model F).Field 4) (u : ℝ) : address F 4 (u • p)=(u:ℂ) • address F 4 p := by
  rw [RCLike.real_smul_eq_coe_smul (K:=ℂ) u p, map_smul]; rfl

/-- Keep same sign in both identities. -/
lemma beacon_signal (c : ℝ) : Table.StressLaws (Model F) (c • original F)
    ((-c) • (scheme F).deriv) ((-c) • (gear F).lie) where
  translation := by
    intro n x hx q χ w b d p
    let B := Fin.cons (α:=fun _ => (Model F).Tag) ⟨d,p⟩ q
    let f := supply F ∘ B
    have he := moment_force hx w (straight_motion (G:=G) w.1 w.2.1 w.2.2.1 b) f
    have hp : Table.shellGrad (Model F) (c • original F) χ b x q p = (c : ℂ)*exportFlux (stressRead x (drift b) f) χ := by
      have ht (a y) : stressRead x (drift b) f a y=bookend x y f (polStress G a b) := by simp [stressRead,drift,kr_eq,ite_smul]
      have hs (a : Axis) (y : E4) : (Model F).useAt (Model F) (Points.cons y x)
          (Fin.cons ⟨4,(c • original F) a b⟩ B) = (c:ℂ)*stressRead x (drift b) f a y := by
        rw [ht, display]
        rw [← show bookend x y f ((c:ℂ) • polStress G a b) = (c:ℂ)*bookend x y f (polStress G a b) from (bookend x y f).map_smul (c:ℂ) (polStress G a b),book_eval]
        congr 1; ext1 i; refine Fin.cases ?_ (fun j => ?_) i
        · change address F _ (c • original F a b)= _; rw [upper_charge,inertia]; rfl
        rfl
      unfold Table.shellGrad; change -(∑ a : Axis, ∫ y : E4, _ * (Model F).useAt _ _ (Fin.cons _ B)) = _
      simp_rw [hs,mul_left_comm (a := ((↑(Analysis.D _ χ _):ℂ))) (↑c:ℂ), integral_const_mul, ← Finset.mul_sum]
      unfold exportFlux; simp [grad, Complex.real_smul,mul_neg]
    rw [hp,he,display]
    change _ = moment G x (supply F ∘ Fin.cons (α:=fun _ => (Model F).Tag) ⟨d+1,(-c) • (scheme F).deriv _ _ p⟩ q)
    let D := rewired (glide G (basis b)) (f 0)
    rw [show (supply F ∘ Fin.cons (α:=fun _ => (Model F).Tag) ⟨d+1,(-c) • (scheme F).deriv d b p⟩ q) =
      update f 0 ((-(c:ℂ)) • D) from ?_, MultilinearMap.map_update_smul]
    · simp only [smul_eq_mul,mul_neg,neg_mul,D]
    funext i; refine Fin.cases ?_ (fun j => ?_) i
    · rw [update_self]; change address F (d+1) ((-c) • _) = _
      rw [RCLike.real_smul_eq_coe_smul (K:=ℂ) (-c),map_smul,address_derive]
      change ((↑(-c) : ℂ)) • D = _; rw [Complex.ofReal_neg]
    rw [update_of_ne (Fin.succ_ne_zero _)]; rfl
  rotation := by
    intro n x hx q χ w g d p
    let B := Fin.cons (α:=fun _ => (Model F).Tag) ⟨d,p⟩ q
    let f := supply F ∘ B
    let v := fromCenter g.val (x 0)
    have he := moment_force hx w (rotational_motion (G:=G) w.1 w.2.1 w.2.2.1 g) f
    have hp : Table.shellSpin (Model F) (c • original F) χ g x q p = (c : ℂ)*exportFlux (stressRead x v f) χ := by
      have hs (a b : Axis) (y : E4) : (Model F).useAt (Model F) (Points.cons y x)
          (Fin.cons ⟨4,(c • original F) a b⟩ B) = (c:ℂ)*bookend x y f (polStress G a b) := by
        rw [display, ← show bookend x y f ((c:ℂ) • polStress G a b) = (c:ℂ)*bookend x y f (polStress G a b) from (bookend x y f).map_smul (c:ℂ) (polStress G a b),book_eval]
        congr 1; ext1 i; refine Fin.cases ?_ (fun j => ?_) i
        · change address F _ (c • original F a b)= _; rw [upper_charge,inertia]; rfl
        rfl
      unfold Table.shellSpin; change -(∑ a : Axis, ∑ b : Axis, ∫ y : E4, _ * (Model F).useAt _ _ (Fin.cons _ B)) = _
      unfold exportFlux stressRead; simp_rw [hs, Finset.smul_sum]
      have hh (a b) : Integrable (fun y => grad a χ y • (v b y • bookend x y f (polStress G a b))) :=
        petal_green hx w _ b f (skew_K g _)
      simp_rw [integral_finsetSum _ fun b _ => hh _ b]
      rw [mul_neg]; simp_rw [Finset.mul_sum]; congr 1; apply Finset.sum_congr rfl; intro a _;
      apply Finset.sum_congr rfl; intro b _
      rw [← integral_const_mul]; refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [grad,D,v,fromCenter,Complex.real_smul,Complex.ofReal_mul]; ring
    rw [hp]; unfold v; rw [he,display]
    change _ = moment G x (supply F ∘ Fin.cons (α:=fun _ => (Model F).Tag) ⟨d,(-c) • scopeRise F _ g p⟩ q)
    let D := rewired (wheel G g) (f 0)
    rw [show (supply F ∘ Fin.cons (α:=fun _ => (Model F).Tag) ⟨d,(-c) • scopeRise F _ g p⟩ q) =
      update f 0 ((-(c:ℂ)) • D) from ?_, MultilinearMap.map_update_smul]
    · simp only [smul_eq_mul,mul_neg,neg_mul,D]
    funext i; refine Fin.cases ?_ (fun j => ?_) i
    · rw [update_self]; change address F d ((-c) • _) = _
      rw [RCLike.real_smul_eq_coe_smul (K:=ℂ) (-c),map_smul,scopeRewrite]
      change ((↑(-c) : ℂ)) • D = _; rw [Complex.ofReal_neg]
    rw [update_of_ne (Fin.succ_ne_zero _)]; rfl


end flux
end YM.Maxwell.Free
