import YM.Analysis.Polydisc
import YM.Bid.Corners

/-!
# From Ward boosts on strict time heights to real motion on W

Keep the same distributions and labels throughout. Two kinds of propagation:
* translations & spatial rotations compare scalar holomorphic functions
  with fixed labels, then take the corner values;
* boosts as given in `Boosty` first give infinitesimal equations of
  **distributions**, then we integrate (on the real-rapidity group,
  after testing). Labels here will only have to move within fixed caps,
  and the Poincare push is on joint Schwartz tests.

Conditional; not supplying Ward identities, any analytic input from
Euclidean reconstruction, or the input label action here.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Work.C09
open Bid Boundary Mink Mink.Poincare Table Analysis Filter Function MeasureTheory Set Complex
open scoped Topology InnerProductSpace BigOperators NNReal ContDiff

variable {G : Gauge} {L : Register G} {S T : Table L} {n : ℕ}

/-- Holomorphic uniqueness on strict times from the purely imaginary
slice. The version with a common time translation: take `k=0`
for simple equality; for `k≠0` we suppose we can translate commonly on
that slice and obtain the equality for real Minkowski time translation by k.
The entire argument can use one complex parameter, continuing the extra
translation also in that parameter. -/
theorem time_compare (p q : Times n → ℂ)
    (hp : DifferentiableOn ℂ p (strict n)) (hq : DifferentiableOn ℂ q (strict n))
    (k : ℝ) (h : ∀ y : Heights n, y ∈ east n → ∀ b : ℝ,
      p (fun i => (↑(y i + b * k):ℂ) * I) = q (fun i => (↑(y i):ℂ)*I))
    (z : Times n) (hz : z ∈ strict n) : p (fun i => z i + (k:ℂ)) = q z := by
  let w (k : ℝ) (c : ℂ) : Times n := fun i => (↑(z i).im:ℂ)*I + c * ↑((z i).re + k)
  let D := w 0 ⁻¹' strict n
  have hi (a : ℝ) (c : ℂ) (i : Fin n) : (w a c i).im = (z i).im + c.im * ((z i).re+a) := by
    simp [w]
  have hD (c : ℂ) (hc : c ∈ D) (a : ℝ) : w a c ∈ strict n := by
    change w 0 c ∈ strict n at hc
    intro i j hij
    have he := hc hij
    change (w 0 c i).im < (w 0 c j).im at he
    change (w a c i).im < (w a c j).im
    simp only [hi, add_zero] at he ⊢
    linarith
  have hw (a : ℝ) : Differentiable ℂ (w a) := by
    unfold w; fun_prop
  have ho : IsOpen D := (open_strict n).preimage (hw 0).continuous
  have hc : Convex ℝ D := by
    intro a ha b hb x y hx hy heq
    change w 0 a ∈ strict n at ha
    change w 0 b ∈ strict n at hb
    change w 0 _ ∈ strict n
    intro i j hij
    have he (l : Fin n) : (w 0 (x • a + y • b) l).im = x * (w 0 a l).im + y * (w 0 b l).im := by
      simp only [hi, add_zero, add_im, real_smul]
      simp only [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
      linear_combination -(z l).im * heq
    change (w 0 _ i).im < (w 0 _ j).im
    rw [he, he]
    rcases hx.eq_or_lt with h0|hpos
    · exact add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left (le_of_lt (ha hij)) hx)
        (mul_lt_mul_of_pos_left (hb hij) (by linarith))
    exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left (ha hij) hpos)
      (mul_le_mul_of_nonneg_left (le_of_lt (hb hij)) hy)
  have h0 : (0:ℂ) ∈ D := by
    change w 0 0 ∈ strict n
    intro i j hij
    change (w 0 0 i).im < (w 0 0 j).im
    simpa [hi] using hz hij
  have h1 : (1:ℂ) ∈ D := by
    change w 0 1 ∈ strict n
    intro i j hij
    change (w 0 1 i).im < (w 0 1 j).im
    simpa [hi] using hz hij
  let E : ℝ → ℂ := fun b => (b:ℂ)*I
  have hn : Tendsto E (𝓝[>] (0:ℝ)) (𝓝[≠] (0:ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have he : Continuous E := by unfold E; fun_prop
      simpa [E] using (he.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    filter_upwards [self_mem_nhdsWithin] with x hx
    change E x ≠ 0
    simp [E,(mem_Ioi.mp hx).ne']
  have hp' : AnalyticOnNhd ℂ (p ∘ w k) D := by
    apply DifferentiableOn.analyticOnNhd _ ho
    exact hp.comp (hw k).differentiableOn (fun c hc => hD _ hc _)
  have hq' : AnalyticOnNhd ℂ (q ∘ w 0) D := by
    apply DifferentiableOn.analyticOnNhd _ ho
    exact hq.comp (hw 0).differentiableOn (fun _ hc => hc)
  have he : EqOn (p ∘ w k) (q ∘ w 0) D := by
    apply hp'.eqOn_of_preconnected_of_frequently_eq hq' hc.isPreconnected h0
    intro hneg
    have ht := (hn.mono_right nhdsWithin_le_nhds).eventually (ho.mem_nhds h0)
    obtain ⟨b,hne,hmem⟩ := ((hn.eventually hneg).and ht).exists
    apply hne
    let y : Heights n := fun i => (z i).im + b*(z i).re
    have he (a : ℝ) : w a (E b) = fun i => (↑(y i + b * a):ℂ)*I := by
      funext i
      simp only [w,E,y,ofReal_add, ofReal_mul]; ring
    have hy : y∈east n := by
      change w 0 (E b)∈strict n at hmem
      intro i j hij
      have hj := hmem hij
      change (w 0 (E b) i).im < (w 0 (E b) j).im at hj
      simpa only [he, mul_zero, add_zero,mul_im,ofReal_re,I_im,mul_one,ofReal_im,zero_mul] using hj
    change p (w k _) = q (w 0 _)
    simpa only [he, mul_zero, add_zero] using h y hy b
  have hj (a : ℝ) : w a 1 = fun i => z i + (a:ℂ) := by
    funext i
    apply Complex.ext <;> simp [w]
  simpa only [Function.comp_apply, hj, ofReal_zero, add_zero] using he h1

variable {R : Rotation S} {K : Spins S} {Y : Waves S} {W : Surface S}

/-- The common translation in `Points n` on a strict height gives
pointwise equality. Note both the real time and the spatial translation;
the Euclidean hypothesis is used at the intermediate, purely imaginary
times only. -/
theorem restricted_translation (hT : T.Homogeneous) (he : Y.Region T)
    (v : Fin n → S.Tag) (x : Points n) (a : E4) {y : Heights n} (hy : y∈east n) :
    Y.restricted (ink v) y ((translation a).zusammen n x) = Y.restricted (ink v) y x := by
  let z := shift x y
  have hz : z ∈ strict n := by
    simpa [z] using on_profile x y 1 (by norm_num) hy
  let p : SpacePoints n := trace x
  let p' : SpacePoints n := fun i => spatial (x i)+spatial a
  have hs : trace ((translation a).zusammen n x) = p' := by
    funext i; simp [trace,zusammen,p']
  have ht : shift ((translation a).zusammen n x) y = fun i => z i + (↑(YM.time a):ℂ) := by
    funext i
    simp [z,zusammen,shift,add_left_comm,add_comm]
  unfold Waves.restricted; rw [hs, ht]
  refine time_compare (fun u => Y.F n u p' (ink v)) (fun u => Y.F n u p (ink v))
    (he.hol n (ink v) p') (he.hol n (ink v) p) (YM.time a) ?_ z hz
  intro u hu b
  let u' : Heights n := fun i => u i + b*YM.time a
  have hu' : u'∈east n := fun _ _ hij => add_lt_add_left (hu hij) _
  have hpp : place p' u' = Points.across (position (spatial a) (b*YM.time a)) (place p u) := by
    ext1 i
    apply Mink.ext_by <;> simp [place,p',p,u',trace]
  change Y.F n _ p' (fun i => S.pin (v i).1 (v i).2) = Y.F n _ p (fun i => S.pin (v i).1 (v i).2)
  rw [he.roots n v p' u' hu',he.roots n v p u hu,hpp]
  exact hT n (place p u) (clear hu _) (position (spatial a) (b*YM.time a))
    (fun i => ⟨(v i).1,S.representative _ (v i).2⟩)

def spatialMap (U : Ortho) (x : Space3) : Space3 := spatial (U.move (position x 0))

/-- `spatialTurn` ensures this really moves purely spatially. -/
theorem move_position (U : Ortho) (hs : Lorentz.spatialTurn U) (x : Space3) (t : ℝ) :
    U.move (position x t) = position (spatialMap U x) t := by
  apply Mink.ext_by
  · let q := position 0 t
    have hh : spatial (U.move q)=0 := by
      apply norm_eq_zero.mp
      have he := squares (U.move q)
      rw [U.move_norm, hs.2, squares q] at he
      have ht : spatial q=0 := by simp [q]
      rw [ht,norm_zero] at he; nlinarith
    have hg : position x t = position x 0 + q := Mink.ext_by (by simp [q]) (by simp [q])
    rw [hg,show U.move (_ + _) = U.move (position x 0)+ U.move q from U.motion.map_add _ q]
    simp only [rest_add,hh,add_zero,spatial_position]; rfl
  rw [hs.2,time_position,time_position]

theorem restricted_spatial (hori : R.Oriented T) (he : Y.Region T) (v : Fin n → S.Tag)
    (x : Points n) (r : Ortho) (hr : Lorentz.spatialTurn r) {y : Heights n} (hy : y∈east n) :
    Y.restricted (ink (R.label r ∘ v)) y ((motion (Lorentz.room r hr)).zusammen n x) =
      Y.restricted (ink v) y x := by
  let z := shift x y
  have hz : z ∈ strict n := by
    simpa [z] using on_profile x y 1 (by norm_num) hy
  let p := trace x
  let p' : SpacePoints n := spatialMap r ∘ p
  let t := (motion (Lorentz.room r hr)).zusammen n x
  have heq i : t i = r.move (x i) := by
    simp only [t,zusammen,points,WithLp.ofLp_toLp,as_active]; rfl
  have hpp (i) : t i = position (p' i) (YM.time (x i)) := by
    change t i = position (spatialMap r (p i)) _
    rw [heq, ← move_position r hr (p i)]; simp [p,trace]
  have hs : trace t = p' := by funext i; simp [trace,hpp]
  have ht : shift t y = z := by
    funext i; simp only [z,shift]; rw [show YM.time (t i)=YM.time (x i) by rw [hpp,time_position]]
  let v' := R.label r ∘ v
  have hg (u : Heights n) : place p' u = Points.move r (place p u) := by
    ext1 i; exact (move_position r hr _ _).symm
  change Y.F n (shift t y) (trace t) (ink v') = Y.F n z p (ink v)
  rw [ht,hs]
  have hj (u : Heights n) (hu : u∈east n) (b : ℝ) :
      Y.F n (fun i => (↑(u i+b*0):ℂ)*I) p' (ink v') = Y.F n (fun i => (↑(u i):ℂ)*I) p (ink v) := by
    unfold ink
    rw [he.roots n v p u hu]
    simp only [mul_zero,add_zero]
    rw [he.roots n v' p' u hu,hg]
    exact hori _ v _ (clear hu _) r
  simpa using time_compare (fun u => Y.F n u p' (ink v')) (fun u => Y.F n u p (ink v))
    (he.hol _ _ _) (he.hol _ _ _) 0 hj z hz

/-- Transfer point covariance with unchanged strict heights to W. Here used
for spatial rotations and all real translations; not assuming such a
strict-height covariance for boosts. -/
theorem corner_maps (hw : Y.NonTangentialFree W) (p : Poincare) (v u : Fin n → S.Union)
    (h : ∀ x y, y∈east n → Y.restricted u y (p.zusammen n x) = Y.restricted v y x)
    (f : Joint n) : W.W n u (Joint.gpush n p f) = W.W n v f := by
  have he (p : Poincare) : LeftInverse (p⁻¹.zusammen n) (p.zusammen n) := by
    intro x; ext1 i; exact p.unmade (x i)
  let e : Points n ≃ᵐ Points n := {
    toFun := p.zusammen n
    invFun := p⁻¹.zusammen n
    left_inv := he p
    right_inv := by simpa only [Function.RightInverse,inv_inv] using he p⁻¹
    measurable_toFun := (p.together n).measurable
    measurable_invFun := (p⁻¹.together n).measurable }
  let f' := Joint.gpush n p f
  have hp (y : Heights n) (hy : y∈east n) : Y.psi u y f' = Y.psi v y f := by
    unfold Waves.psi
    rw [← (p.together n).integral_comp e.measurableEmbedding]
    simp_rw [h _ _ hy, f', Joint.gpush_at, he p _]
  haveI := awaits (light n)
  have hf : Tendsto (fun y => Y.psi u y f') (𝓝[east n] 0) (𝓝 (W.W n u f')) := hw.corner ..
  refine tendsto_nhds_unique hf ?_
  have hg : Tendsto (fun y => Y.psi v y f) (𝓝[east n] 0) (𝓝 (W.W n v f)) := hw.corner ..
  exact hg.congr' <| Eventually.mono self_mem_nhdsWithin fun x hx => (hp x hx).symm

theorem motion_push (p : Lorentz) (f : Joint n) :
    Joint.gpush n (motion p) f = Probe.along (togetherL p n).symm f := by
  ext1 x; simp only [Joint.gpush_at,Probe.along_at]
  apply congr_arg f; ext1 i; simp [zusammen, motion]

theorem push_one (f : Joint n) : Joint.gpush n 1 f = f := by
  ext1 x; simp [zusammen]

theorem push_mul (p q : Poincare) (f : Joint n) :
    Joint.gpush n (p*q) f = Joint.gpush n p (Joint.gpush n q f) := by
  ext1 x; simp [zusammen]

/-- Boost identity passes to the boundary. We only need corner convergence
on fixed tests, including the extra tests appearing with a coefficient that
vanishes with the ordered height. -/
theorem boost_corner (hb : Boosty R Y) (hw : Y.NonTangentialFree W)
    (v : Fin n → S.Tag) (a : SpaceAxis) (f : Joint n) :
    (∑ i, W.W n (update (ink v) i (kick R a (v i))) f) = W.W n (ink v) (inclined a 0 f) := by
  let F := 𝓝[east n] (0:Heights n)
  haveI : F.NeBot := awaits (light n)
  let u := ink v
  have he (w : Fin n → S.Union) (g : Joint n) : Tendsto (fun y => Y.psi w y g) F (𝓝 (W.W n w g)) := hw.corner ..
  let l := fun (i : Fin n) => realTerm i a.castSucc f
  let c := fun (i : Fin n) (y : Heights n) => (y i : ℂ)*I
  have hc (y : Heights n) : inclined a y f = inclined a 0 f + ∑ i, c i y • l i := by
    simp [inclined,c,l,Finset.sum_add_distrib]
  let P (y : Heights n) (hy : y∈east n) : Joint n →ₗ[ℂ] ℂ := {
    toFun := Y.psi u y
    map_add' g j := by
      unfold Waves.psi
      rw [← integral_add (hw.int n u y hy g) (hw.int n u y hy j)]
      apply integral_congr_ae; filter_upwards with x; simp [mul_add]
    map_smul' z g := by
      change Y.psi u y (z • g) = z * Y.psi u y g
      unfold Waves.psi; rw [← integral_const_mul]; congr! 1; ext x; simp; ring }
  have hh (y) (hy : y∈east n) : Y.psi u y (inclined a y f) = Y.psi u y (inclined a 0 f) +
      ∑ i, c i y * Y.psi u y (l i) := by
    rw [hc y]
    change P y hy _ = P y hy _ + ∑ i, c i y • (P y hy) (l i)
    simp only [map_add,map_sum,map_smul]
  have hz (i : Fin n) : Tendsto (fun y => c i y * Y.psi u y (l i)) F (𝓝 0) := by
    have hp : Continuous (c i) := by unfold c; fun_prop
    have ht := ((hp.tendsto 0).mono_left (nhdsWithin_le_nhds (s:= east n))).mul (he u (l i))
    simpa only [c,Pi.zero_apply,ofReal_zero,zero_mul] using ht
  have hs : Tendsto (fun y => ∑ i, c i y * Y.psi u y (l i)) F (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun i _ => hz i)
  let w := fun i => update u i (kick R a (v i))
  refine tendsto_nhds_unique (tendsto_finsetSum Finset.univ (fun i _ => he (w i) f)) ?_
  have ht := (he u (inclined a 0 f)).add hs
  rw [add_zero] at ht
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin (s:=east n)] with y hy
  exact (hh y hy).symm.trans (hb n v a f y hy).symm

/-- Differentiate a joint expectation with labels and tests both moving.
This uses only derivatives of pairings at *fixed* labels together with
label derivatives within finite-dimensional spaces (here a common cap).
In particular no continuity assumption on joint distributions as functions
on the whole Union, nor any norm-differentiability in a dual space. -/
theorem moving_eval {d : ℕ}
    (M : MultilinearMap ℂ (fun _ : Fin n => S.Field d) (Distn (Points n)))
    (v : ℝ → Fin n → S.Field d) (v' : Fin n → S.Field d)
    (f : ℝ → Joint n) (f' : Joint n)
    (hv : ∀ i, HasDerivAt (fun t => v t i) (v' i) 0)
    (hf : ∀ u, HasDerivAt (fun t => M u (f t)) (M u f') (0:ℝ)) :
    HasDerivAt (fun t => M (v t) (f t))
      ((∑ i, M (update (v 0) i (v' i)) (f 0)) + M (v 0) f') (0:ℝ) := by
  classical
  let B := Module.finBasis ℂ (S.Field d)
  let c (i) : S.Field d →L[ℝ] ℂ := (LinearMap.toContinuousLinearMap (B.coord i)).restrictScalars ℝ
  let p (j : Fin n → Fin (Module.finrank ℂ (S.Field d))) (u : Fin n → S.Field d) :=
    ∏ i, c (j i) (u i)
  let A (j : Fin n → Fin (Module.finrank ℂ (S.Field d))) := M (fun i => B (j i))
  have he (u : Fin n → S.Field d) : M u = ∑ j, p j u • A j := by
    have hh i : ∑ j, c j (u i) • B j = u i := B.sum_repr _
    conv_lhs => rw [← funext hh]
    rw [MultilinearMap.map_sum]
    exact Finset.sum_congr rfl fun j _ => M.map_smul_univ _ _
  have hh (u : Fin n → S.Field d) (g : Joint n) : M u g = ∑ j, p j u * A j g := by
    rw [he, sum_apply]; rfl
  have hl (i j) : HasDerivAt (fun t => c j (v t i)) (c j (v' i)) (0:ℝ) :=
    (c j).hasFDerivAt.comp_hasDerivAt 0 (hv i)
  have ht (j : Fin n → Fin (Module.finrank ℂ (S.Field d))) :
      HasDerivAt (fun t => p j (v t)) (∑ i, p j (update (v 0) i (v' i))) (0:ℝ) := by
    have hg (i : Fin n) : p j (update (v 0) i (v' i)) =
        (∏ k ∈ Finset.univ.erase i, c (j k) (v 0 k)) • c (j i) (v' i) := by
      unfold p
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
      simp only [update_self,smul_eq_mul]
      congr 1
      exact Finset.prod_congr rfl fun k hk => by rw [update_of_ne (Finset.mem_erase.mp hk).1]
    simp_rw [hg]
    exact HasDerivAt.fun_finsetProd (u:=Finset.univ) (fun i _ => hl i (j i))
  simp_rw [hh]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  apply HasDerivAt.fun_sum; intro j _
  simpa [Finset.sum_mul,A] using! (ht j).mul (hf (fun i => B (j i)))

def ride (W : Surface S) (K : Spins S) (a : SpaceAxis)
    (v : Fin n → S.Union) (f : Joint n) (t : ℝ) :=
  W.W n (fun i => K.rail ((Ray.fromAxis a).boost t) (v i))
    (Joint.gpush n (motion ((Ray.fromAxis a).boost t)) f)

variable {V : DiffPlan S} {H : S.Hierarchy}

theorem boost_origin (hpush : C08)
    (hinc : V.Inclusions S) (hk : K.Descends R H.spin)
    (hb : Boosty R Y) (hw : Y.NonTangentialFree W)
    (v : Fin n → S.Union) (f : Joint n) (a : SpaceAxis) :
    HasDerivAt (ride W K a v f) 0 (0:ℝ) := by
  classical
  obtain ⟨d,u,rfl⟩ := V.joint H.laws.toSymmetric hinc v
  let M : MultilinearMap ℂ (fun _ : Fin n => S.Field d) (Distn (Points n)) :=
    (W.W n).compLinearMap (fun _ => S.pin d)
  let b := Ray.fromAxis a
  let l (t : ℝ) := fun i => K.shell d (b.boost t) (u i)
  let l' : Fin n → S.Field d := fun i => (-I) • R.lie d (Ortho.plane timeAxis a.castSucc) (u i)
  let g (t) := Joint.gpush n (motion (b.boost t)) f
  have hg : g 0=f := by rw [show g 0 = Joint.gpush n 1 f by simp [g],push_one]
  let g' := -inclined a 0 f
  have hg' (w) : HasDerivAt (fun t => M w (g t)) (M w g') (0:ℝ) := by
    let D := (M w).restrictScalars ℝ
    change HasDerivAt (fun t => D (g t)) (D g') 0
    apply hasDerivAt_iff_tendsto_slope_zero.mpr
    have ht : Tendsto (fun t : ℝ => t⁻¹ • (g t - f)) (𝓝[≠] 0) (𝓝 g') := hpush.2 n f a
    have hs := (D.continuous.tendsto _).comp ht
    simpa only [Function.comp_def,map_smul,map_sub,zero_add,hg] using hs
  have he : HasDerivAt (fun t => M (l t) (g t))
      ((∑ i, M (update (l 0) i (l' i)) (g 0)) + M (l 0) g') (0:ℝ) :=
    moving_eval M l l' g g' (fun i => hk.boosts d a (u i)) hg'
  have hl : l 0 = u := by
    funext i; apply S.pin_inj d
    unfold l; rw [← hk.ties, b.boost_start,hk.identity]
  let w : Fin n → S.Tag := fun i => ⟨d,u i⟩
  have hu (i) : M (update u i (l' i)) = W.W n (update (ink w) i (kick R a (w i))) := by
    unfold M; rw [MultilinearMap.compLinearMap_apply]; apply congr_arg (W.W n)
    funext j; by_cases h : j=i <;> simp [h,w,l',ink,kick]
  rw [hg,hl] at he
  simp_rw [hu] at he
  rw [boost_corner hb hw w a f] at he
  change HasDerivAt (fun t => M (l t) (g t)) (_ + W.W n (ink w) (-inclined a 0 f)) (0:ℝ) at he
  rw [map_neg,add_neg_cancel] at he
  have hid : ride W K a (S.pin d ∘ u) f = fun t => M (l t) (g t) := by
    funext t
    unfold ride; simp_rw [Function.comp_apply,hk.ties]; rfl
  rw [hid]; exact he

theorem boost_invariant (hpush : C08)
    (hinc : V.Inclusions S) (hk : K.Descends R H.spin)
    (hb : Boosty R Y) (hw : Y.NonTangentialFree W)
    (v : Fin n → S.Union) (f : Joint n) (a : SpaceAxis) :
    ∀ r : ℝ, ride W K a v f r = W.W n v f := by
  let p := ride W K a v f
  have hp (t : ℝ) : HasDerivAt p 0 t := by
    let b := Ray.fromAxis a
    let v' : Fin n → S.Union := fun i => K.rail (b.boost t) (v i)
    let g := Joint.gpush n (motion (b.boost t)) f
    let q := ride W K a v' g
    have he (s : ℝ) : p (t+s) = q s := by
      unfold p q ride
      rw [add_comm t s,b.boost_add,overL,push_mul]
      simp_rw [hk.representation]; rfl
    have ht : p t=q 0 := by simpa using he 0
    have hq : HasDerivAt q 0 0 := boost_origin (H:=H) hpush hinc hk hb hw v' g a
    apply hasDerivAt_iff_tendsto_slope_zero.mpr
    simp_rw [he, ht]
    simpa only [zero_add] using hq.tendsto_slope_zero
  have h0 : p 0 = W.W n v f := by simp [p,ride,hk.identity,push_one]
  suffices h : p = fun _ => W.W n v f from congr_fun h
  apply eq_of_fderiv_eq (𝕜:=ℝ) (fun t => (hp t).differentiableAt) (differentiable_const _) _ 0 h0
  intro x
  rw [fderiv_fun_const, (hp x).hasFDerivAt.fderiv]
  ext; simp

/-- Conditional passage from strict tests & Lie identities to the Urs
socket. This uses no spectrum assumption on W. -/
theorem answer : YM.Bid.C09 := by
  intro sphere pushes G L S T R K H V hinc hT _hres hori _hlaws hk Y W he _hbr hb hw
  constructor
  · intro n v f a
    obtain ⟨d,u,rfl⟩ := V.joint H.laws.toSymmetric hinc v
    exact corner_maps hw (translation a) _ _
      (fun x _ hy => restricted_translation hT.translations he (fun i => ⟨d,u i⟩) x a hy) f
  let holds (p : Lorentz) := ∀ n (v : Fin n → S.Union) (f : Joint n),
      W.W n (fun i => K.rail p (v i)) (Joint.gpush n (motion p) f) = W.W n v f
  let U : Subgroup Lorentz := {
    carrier := {p | holds p}
    one_mem' := by intro n v f; simp [push_one,hk.identity]
    mul_mem' := by
      intro a b ha hh
      change holds a at ha
      change holds b at hh
      intro n v f; rw [overL,push_mul]; simp_rw [hk.representation]; rw [ha,hh]
    inv_mem' := by
      intro a ha
      change holds a at ha
      intro n v f
      let v' : Fin n → S.Union := fun i => K.rail a⁻¹ (v i)
      have heq (i : Fin n) : K.rail a (v' i)=v i := by unfold v'; rw [← hk.representation]; simp [hk.identity]
      have hh := ha _ v' (Joint.gpush n (motion a⁻¹) f)
      rw [← push_mul, ← overL,mul_inv_cancel,inactive,push_one] at hh
      simp_rw [heq] at hh; exact hh.symm }
  have hg : beamGens ≤ U := by
    apply (Subgroup.closure_le _).mpr
    rintro p (hp|hp)
    · rcases hp with ⟨r,hr,rfl⟩
      intro n v f
      obtain ⟨d,u,rfl⟩ := V.joint H.laws.toSymmetric hinc v
      simp_rw [Function.comp_apply,hk.ties,hk.spatial r hr]
      exact corner_maps hw _ _ _ (fun x _ hy => restricted_spatial hori he (fun i => ⟨d,u i⟩) x r hr hy) f
    rcases hp with ⟨i,t,rfl⟩
    intro n v f
    exact boost_invariant (H:=H) pushes hinc hk hb hw v f i t
  intro n v f r
  have hj : holds r := hg (show r ∈ beamGens by rw [show beamGens=⊤ from sphere]; trivial)
  rw [← motion_push r f]; exact hj _ v f
end YM.Work.C09
