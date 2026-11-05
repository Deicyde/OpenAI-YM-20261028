import YM.EveryPhase.Seeds

/-! # The jump at Euclidean external arguments. Keep compact supports disjoint. -/
set_option autoImplicit false
noncomputable section
namespace YM.EveryPhase.Stress
open Function Set Filter MeasureTheory Metric Boundary Next.BOUNDARY Mink Complex Probe Table
open Work.C20
open scoped Topology BigOperators Interval ContDiff
variable {G : Gauge} {L : Register G} {S U : Table L} {W : Surface S}
  {D : ∀ n, Blanket n} {Z : W.Aurora D} {P : DiffPlan S} {H : S.RealSpin} {F : Waves S} {n : ℕ}

lemma fibers (K : Killing) (T : S.Stress) (v : Fin n → S.Tag) (x : Points (n+1)) (k : Fin (n+1))
    (B : S.Tag) (g : Probe Space3) (hg : HasCompactSupport ⇑g) (hr : ∀ r, ((g r).re:ℂ)=g r) (c : ContDiffBump (0:ℝ))
    (w : Prospect F Z U P H T) (s : ℝ) (j : Fin (n+2)) :
    let u := YM.time (x k)
    let f := grounds U K T v x k B (hatChi c g u)
    let Y := Bid.ink (hole k v B)
    let z := ((((YM.time (x k)+s):ℝ):ℂ)*I)
    hole j (pureU x) z∈strict (n+2) →
      (∫ r, f (position r (u+s))) = ((deriv c s:ℝ):ℂ)*harbors Z K Y T g j (Boundary.trace x) (pureU x) z +
        (c s:ℂ)*docks Z K Y T g j (Boundary.trace x) (pureU x) z := by
  intro u f Y z h
  let w₁ (a) := waveT Z K Y T j a (Boundary.trace x) (pureU x) z
  have hw (r a) : curtain U K T v x k B a (position r (u+s))=w₁ a r := by
    rw [← waveT_pure w.hu w.hF w.hZ K T v x k j B a _]; simp only [spatial_position,time_position]; rfl
    simp only [time_position]; exact h
  have he r : f (position r (u+s))=(c s:ℂ)* (∑ i : SpaceAxis, drift g i r* w₁ i.castSucc r)+
      ((deriv c s:ℝ):ℂ)*(g r* w₁ timeAxis r) := by
    unfold f grounds; rw [Fin.sum_univ_castSucc]
    simp_rw [hw]
    change (∑ i : SpaceAxis, _)+( ((Analysis.D (basis timeAxis) _ _ : ℝ):ℂ) * w₁ timeAxis r)=_
    rw [(hat_jets c g hr u s r).1,mul_assoc]; simp_rw [(hat_jets c g hr u s r).2,mul_assoc,Finset.mul_sum]
  have hc a : Continuous (w₁ a) := (waveT_smooth K Y T j _ _ _ h a w.hZ).continuous
  have hi i : Integrable (fun r => drift g i r*w₁ i.castSucc r) :=
    ((drift g i).continuous.mul (hc i.castSucc)).integrable_of_hasCompactSupport (drift_compact g hg i).mul_right
  have hf : Integrable (fun r => g r*w₁ timeAxis r) := (g.continuous.mul (hc timeAxis)).integrable_of_hasCompactSupport hg.mul_right
  simp_rw [he]
  rw [integral_add ((integrable_finsetSum _ (fun i _ => hi i)).const_mul _) (hf.const_mul _),integral_const_mul,
    integral_const_mul,integral_finsetSum _ (fun i _ => hi i),add_comm]; rfl

-- `x` is the external Euclidean positions (B at x k).
theorem pure_clock (K : Killing) (T : S.Stress) (v : Fin n → S.Tag) (x : Points (n+1)) (k : Fin (n+1))
    (hx : x∈ordered (n+1)) (B : S.Tag) (R : S.Rotation) (w : Prospect F Z U P H T) (h : StressLaws U T P.deriv R.lie)
    (g : Probe Space3) (hg : HasCompactSupport ⇑g) (hr : ∀ r, ((g r).re:ℂ)=g r) (hs : g =ᶠ[𝓝 (spatial (x k))] fun _ => (1:ℂ)) :
    Tendsto (fun s => currentJump Z K T (Bid.ink (hole k v B)) g k (pureDock x,s)) (𝓝[>] 0) (𝓝 (taskE U K R P v x k B)) := by
  obtain ⟨d,hd⟩ := preparation x hx k
  let c : ContDiffBump (0:ℝ) := ⟨d/4,d/2,by have := hd.1; linarith,by have := hd.1; linarith⟩
  have hc : c.rOut<d := by have h := hd.1; change d/2<d; linarith
  let t := YM.time (x k)
  let χ := hatChi c g t
  have he := euclidean_shell U K P T R v x (ordered_conf hx) k B w.hu h χ (hat_window x k hd c hc g hg hs)
  let F := fun s : ℝ => ∫ y, grounds U K T v x k B χ (position y (t+s))
  obtain ⟨hF, hw⟩ := split_space t he.1
  let Y := Bid.ink (hole k v B)
  let p := pureDock x
  let A := fun s => crest Z K T Y g k (p,s)
  let a := fun s => docks Z K Y T g k.succ (Boundary.trace x) (pureU x) (morn p k s)
  let C := fun s => trough Z K T Y g k (p,s)
  let b := fun s => docks Z K Y T g k.castSucc (Boundary.trace x) (pureU x) (eve p k s)
  let f := fun s => (c s:ℂ)*A s-(c (-s):ℂ)*C s
  rw [← he.2,hw]
  refine curtainsFTC d hd.1 F f _ hF ?_ ?_ ?_ ?_
  · intro s he
    by_contra hK
    apply he
    have hb : |s| > c.rOut := lt_of_lt_of_le hc (le_of_not_gt (fun h => hK (abs_lt.mp h)))
    have hh (y : Space3) : (position y (t+s)) ∉ tsupport χ := fun hx =>
      not_le.mpr hb (by
        have hz : |YM.time (position y (t+s))-t| ≤ c.rOut := (hat_size c g hg t).2 hx
        simpa using hz)
    have ht (y : Space3) : grounds U K T v x k B χ (position y (t+s))=0 := by
      simp [grounds,Analysis.D,fderiv_of_notMem_tsupport ℝ (hh y)]
    simp [F,ht]
  · have he : c d=0 := c.zero_of_le_dist (by simp [abs_of_pos hd.1,hc.le])
    have hz : c (-d)=0 := c.zero_of_le_dist (by simpa [abs_of_pos hd.1] using hc.le)
    simp [f,he,hz]
  · intro s hs'
    have hh (s : ℝ) : morn p k s=((t+s:ℝ):ℂ)*I := by
      dsimp only [p,morn,town,pureDock,pureU,t]; push_cast; ring
    have hq (s : ℝ) : eve p k s=((t-s:ℝ):ℂ)*I := by
      dsimp only [p,eve,town,pureDock,pureU,t]; push_cast; ring
    have h₁ : hole k.succ (pureU x) (morn p k s)∈strict (n+2) := by rw [hh]; exact (hd.2 _ hs').1
    have h₂ : hole k.castSucc (pureU x) (eve p k s)∈strict (n+2) := by rw [hq]; exact (hd.2 _ hs').2
    have ha : HasDerivAt A (a s) s := by
      have ht : HasDerivAt (morn p k) I s := by
        unfold morn; simpa using ((ofRealCLM.hasDerivAt (x:=s)).mul_const I).const_add (town p k)
      refine (real_path (harbors_speed K k.succ Y T g hg w.hT w.hu w.hs w.hi w.hd w.hF w.hZ
        (Boundary.trace x) (pureU x) (morn p k s) h₁) ht).congr_deriv ?_
      simp [a, ←mul_assoc]
    have hb : HasDerivAt C (-b s) s := by
      have ht : HasDerivAt (eve p k) (-I) s := by
        unfold eve; simpa using (hasDerivAt_const s (town p k)).fun_sub ((ofRealCLM.hasDerivAt (x:=s)).mul_const I)
      refine (real_path (harbors_speed K k.castSucc Y T g hg w.hT w.hu w.hs w.hi w.hd w.hF w.hZ (Boundary.trace x)
        (pureU x) (eve p k s) h₂) ht).congr_deriv ?_; simp [b,←mul_assoc]
    have hu : F s=((deriv c s:ℝ):ℂ)*A s+(c s:ℂ)*a s := by
      change F _=_ *harbors Z K Y T g k.succ p.1.1 p.1.2 _ + _
      dsimp only [a]
      rw [hh]; exact fibers K T v x k B g hg hr c w s _ (hd.2 _ hs').1
    have hv : F (-s)=((deriv c (-s):ℝ):ℂ)*C s+(c (-s):ℂ)*b s := by
      change F _=_ *harbors Z K Y T g k.castSucc p.1.1 p.1.2 _ + _
      dsimp only [b]; rw [hq]
      have ht := fibers K T v x k B g hg hr c w (-s) k.castSucc
      dsimp only at ht
      simp only [← sub_eq_add_neg] at ht
      unfold F; rw [← sub_eq_add_neg]; exact ht (hd.2 _ hs').2
    have hw (s : ℝ) : HasDerivAt (fun s => (c s:ℂ)) ((deriv c s:ℝ):ℂ) s :=
      ofRealCLM.hasFDerivAt.comp_hasDerivAt s ((c.contDiff.differentiable (n:=∞) (by simp)) s).hasDerivAt
    refine (((hw s).mul ha).sub (((hw (-s)).scomp s (hasDerivAt_neg _)).mul hb)).congr_deriv ?_
    rw [hu,hv]; simp; ring
  change f =ᶠ[_] fun s => A s-C s
  have hy : Tendsto (fun s : ℝ => -s) (𝓝 0) (𝓝 0) := by simpa using ((continuous_neg.tendsto (0:ℝ)))
  apply Eventually.filter_mono nhdsWithin_le_nhds
  filter_upwards [c.eventuallyEq_one,hy.eventually c.eventuallyEq_one] with s he hh
  change c s=1 at he; change c (-s)=1 at hh; simp [f,he,hh]
end YM.EveryPhase.Stress
