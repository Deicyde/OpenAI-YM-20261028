import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.FrameCosts
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Station
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Veil

/-!
# Forecast the REAL affine remainder on the local unmasked arguments

Each piece estimated before regrouping. Polynomial costs all here post-L,
paid at fixed stencil and order. Don't estimate actual output on a forest using
only one period norm for analytic germs; these all-period invoices involve each
actual `T` and its path/alignment costs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Aff
open Function Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Bloch Turn
open Matrix Work.F03 Progress.StationaryScenes Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.AbsoluteSums Tree Next.Fluctuations Finset Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f}

def forecast (T : Tube G S) (p : Pos S) (a : LogField G f) (b : LogField G c) :=
  let x := orient p.1 a
  let y := orient p.1 b
  p.2.elim (fun i => xLin T.high T.up x i-Fout T y i) (fun i => zLin S x y i-Qout T y i)

-- This will give a forecast even for N (affine complement, needed on V)
def Guess (u v : G.Color) (A h w : ℝ) := ‖v‖ ≤ A*h ∧ ‖u-v‖ ≤ A*h*w

lemma Guess.loosen {u v : G.Color} {A h w B e : ℝ} (he : Guess u v A h w) (hh : 0≤h) (hv : 0≤w)
    (hB : 0≤B) (hy : A ≤ B) (hw : w≤e) : Guess u v B h e :=
  ⟨he.1.trans (by gcongr),he.2.trans (by gcongr)⟩

lemma Guess.subtract {u v a b : G.Color} {A B h w : ℝ} (he : Guess u v A h w) (hh : Guess a b B h w) :
    Guess (u-a) (v-b) (A+B) h w := by
  constructor
  · exact (norm_sub_le ..).trans ((add_le_add he.1 hh.1).trans_eq (add_mul A B h).symm)
  rw [show u-a-(v-b)=(u-v)-(a-b) by abel]; exact (norm_sub_le ..).trans ((add_le_add he.2 hh.2).trans_eq (by ring))

-- Analogous to EBare's interior L. zip first rather than maxtnorm of covariance.
private lemma ghost {X Y : Type} [Fintype X] [Fintype Y] (F W : X → Y → Pay G) (f v : Y → G.Color)
    {A D h w : ℝ} (hA : 0≤A) (hD : 0≤D) (hh : 0≤h) (hw : 0≤w) (hf : NearFlat F W A w)
    (he : ∀ i, Guess (f i) (v i) D h w) : ∀ x, Guess (zip F f x) (zip W v x) (2*A*D) h w := by
  intro i; constructor
  · apply (Work.E07.zip_uniform W v i (hf.full.rows i) (show 0≤D*h by positivity) (fun j => (he j).1)).trans
    nlinarith [mul_nonneg (mul_nonneg hA hD) hh]
  rw [show zip F f i-zip W v i=zip F (f-v) i+zip (F-W) v i by
    unfold zip; simp only [Pi.sub_apply,map_sub,_root_.sub_apply,sum_sub_distrib]; abel]
  exact (norm_add_le ..).trans ((add_le_add (Work.E07.zip_uniform F (f-v) i (hf.cut.rows i)
    (show 0≤D*h*w by positivity) (fun j => (he j).2)) (Work.E07.zip_uniform (F-W) v i
      (hf.close.rows i) (show 0≤D*h by positivity) (fun j => (he j).1))).trans_eq (by ring))

lemma orient_norm (s : Signed) (x : LogField G n) : ‖orient s x‖ ≤ ‖x‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun i => ?_)
  unfold orient Aff.form; rw [maps_cost]; exact norm_le_pi_norm x _

lemma ordered_cost (P : Teller G) (D : Patch) (hb : D.Branches P.bind G) : ∃ C τ r : ℝ,
    0<C ∧ 0<τ ∧ 0<r ∧ ∀ (c f : Side) (S : StepData c f) (T : Tube G S), P.Funds S T → S.patch=D →
      ∀ (x : LogField G f) (b : LogField G c) (h : ℝ), h≤r → ‖x‖≤h → ‖b‖≤h →
      ∀ (R : ℕ) (k : S.Choices), let U := represent x; let V := represent b; let w := widen R h τ
      (∀ i, Guess (primalN T R V i) (zip (flatN T) (Limage T b) i) C h w) ∧
      ∀ p, Guess (primal T R p k V U) (forecast T p x b) C h w := by
  obtain ⟨A,r,hA,hr,H⟩ := x_chart_cost G P.top 1 (by decide)
  obtain ⟨B,v,hB,hv,K⟩ := x_chart_cost G P.below D.L.val D.L.property
  obtain ⟨E,s,w,hE,hs,hw,hp⟩ := kernel_chart_cost G D.L P.η P.C P.width
  obtain ⟨F,u,hF,hu,hq⟩ := z_chart_cost D P.bind G hb
  let C := (A+F)+2*E*B
  let τ := min P.top.width (min (P.below.width/D.L.val) s)
  let l := min (min r v) (min w u)
  have hh : 0 < P.below.width / D.L.val := div_pos P.below.width_pos (side_pos D.L)
  refine ⟨C,τ,l, by unfold C; positivity, lt_min P.top.width_pos (lt_min hh hs),lt_min (lt_min hr hv) (lt_min hw hu),?_⟩
  intro c f S T ht hD x b h hf hx hy R k U V t
  obtain ⟨a,a',ha,hb'⟩ := ht.feeds
  have hnn : 0 ≤ h := (norm_nonneg _).trans hx
  have hT : 0 ≤ t := widen_nonneg R hnn
  have hf' (x : LogField G f) (he : ‖x‖ ≤ h) (j : Twin f) :
      Guess (T.Xf R (represent x) j) (xLin T.high T.up x j) A h t := by
    dsimp only [Tube.Xf]; rw [ht.high]; apply Guess.loosen (w:=widen R h P.top.width) _ hnn (widen_nonneg _ hnn)
      hA.le (le_rfl) (widen_anti R h (min_le_left ..))
    simpa [Guess] using! H f T.up a ha R x h he (hf.trans ((min_le_left ..).trans (min_le_left ..))) j
  have hc (b : LogField G c) (he : ‖b‖ ≤ h) (j : Twin c) :
      Guess (T.Xn R (represent b) j) (Limage T b j) B h t := by
    dsimp only [Tube.Xn,Limage]; rw [ht.low,hD]; apply Guess.loosen (w:=widen R h (P.below.width/D.L.val)) _ hnn
      (widen_nonneg _ hnn) hB.le (le_rfl) (widen_anti R h ((min_le_right ..).trans (min_le_left ..)))
    exact K c T.down a' hb' R b h he (hf.trans ((min_le_left ..).trans (min_le_right ..))) j
  have hy' (b : LogField G c) (he : ‖b‖ ≤ h) : let V := represent b
      NearFlat (T.Φ R V) (flatF T) E t ∧ NearFlat (T.Φ' R V) (flatI T) E t ∧ NearFlat (T.N R V) (flatN T) E t := by
    intro V; obtain ⟨h1,h2,h3⟩ := hp S T (congr_arg _ hD) ⟨_,ht.crosses⟩ R b h he (hf.trans
      ((min_le_right ..).trans (min_le_left ..)))
    have hv : widen R h s ≤ t := widen_anti R h ((min_le_right ..).trans (min_le_right ..))
    exact ⟨h1.mono hE.le (widen_nonneg R hnn) le_rfl hv, h2.mono hE.le (widen_nonneg R hnn) le_rfl hv,
      h3.mono hE.le (widen_nonneg R hnn) le_rfl hv⟩
  constructor
  · intro j
    have he := ghost _ _ _ _ hE.le hB.le hnn hT (hy' b hy).2.2 (hc b hy) j
    exact he.loosen (B:=C) hnn hT (by unfold C; positivity) (by unfold C; linarith) le_rfl
  rintro ⟨s,p|p⟩
  · let y := orient s x; let z := orient s b
    have hr := (orient_norm s x).trans hx
    have hz := (orient_norm s b).trans hy
    unfold primal forecast; unfold V U; simp only [← orient_represents,Sum.elim_inl]
    have hv := hf' y hr p
    have ht := hv.subtract (ghost _ _ _ _ hE.le hB.le hnn hT (hy' _ hz).1 (hc z hz) p)
    exact ht.loosen (B:=C) hnn hT (by unfold C; positivity) (by unfold C; linarith) le_rfl
  let z := orient s b; let y := orient s x
  have hz := (orient_norm s b).trans hy
  have hy := (orient_norm s x).trans hx
  unfold primal forecast; unfold V U; simp only [← orient_represents, Sum.elim_inr]
  have hi : Guess (zTest S (choice s k) p (y,z)) (zLin S y z p) F h t := by
    have he : ‖(y,z)‖ ≤ h := max_le hy hz
    obtain ⟨hz,hy⟩ := hq c f S hD ht.knobs (choice s k) p (y,z)
    refine ⟨hz.trans (mul_le_mul_of_nonneg_left he hF.le),
      (hy (he.trans (hf.trans ((min_le_right ..).trans (min_le_right ..))))).trans ?_⟩
    calc
      _ ≤ F*h^2 := by gcongr
      _ = F*h*h := by ring
      _ ≤ F*h*t := by gcongr; exact le_widen R hnn
  have hb := hi.subtract (ghost _ _ _ _ hE.le hB.le hnn hT (hy' _ hz).2.1 (hc z hz) p)
  exact hb.loosen (B:=C) hnn hT (by unfold C; positivity) (by unfold C; linarith) le_rfl

-- retain the uncut row identities AND the cost of every path after cut

lemma orient_plus (s : Signed) (x y : LogField G n) : orient s (x+y)=orient s x+ orient s y := by
  unfold orient; rw [show collect G (x+y)=collect G x+collect G y from rfl,map_add]; rfl
lemma orient_zero (s : Signed) : orient s (0:LogField G n)=0 := by
  unfold orient; rw [show collect G (0:LogField G n)=0 from rfl,map_zero]; rfl

lemma form_collect (x : LogField G n) : form (collect G x)=x := by
  funext i; unfold Aff.form collect; dsimp only
  rw [show coord _ = axisEquiv _ from rfl, Equiv.apply_symm_apply]

lemma x_zero (q : Clip) (T : PathData G) (b : Twin n) : xLin q T (0:LogField G n) b=0 := by
  have hh (c : Cell n) : faceCurl c (0:LogField G n) = 0 := by
    ext k; unfold faceCurl dColor; simp only [show parts G 1 (0:LogField G n) k=0 from rfl,
      mulVec_zero,Pi.zero_apply]
    rfl
  unfold xLin ellLine; split <;> simp [hh]

lemma forecast_step {P : Teller G} {T : Tube G S} (hp : P.Funds S T) (p : Pos S) (x y : LogField G f) (b : LogField G c) :
    forecast T p (x+y) b=forecast T p x b + forecast T p y 0 := by
  let h := hp.feeds; obtain ⟨C,L,h1,h2⟩ := h
  rw [← hp.high] at h1
  have hv (a : LogField G f) (b : LogField G f) (i : Twin f) : xLin T.high T.up (a+b) i=xLin T.high T.up a i+xLin T.high T.up b i := by
    have he (p : Cell f) : faceCurl p (a+b)=faceCurl p a+faceCurl p b := by
      conv_lhs => rw [← form_collect (a+b),show collect G (a+b) = collect G a+collect G b from rfl]
      rw [← form_collect a, ← form_collect b]; simp only [collect_form]; apply curl_add -- loops check
    unfold xLin ellLine; split
    next =>
      simp only [he,smul_add]; exact (ellLine_summable _ h1 ..).tsum_add (ellLine_summable _ h1 ..)
    next => rw [he,smul_add]
  have hZ : Limage T (0:LogField G c)=0 := funext (x_zero T.low T.down)
  have he i (x y : LogField G f) (b : LogField G c) : zLin S (x+y) b i=zLin S x b i + zLin S y 0 i := by
    ext k; simp only [zLin,PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply, Pi.zero_apply,PiLp.zero_apply]
    rw [show parts G 1 (x+y) k=parts G 1 x k+parts G 1 y k from rfl, Matrix.mulVec_add,Pi.add_apply]; module
  rcases p with ⟨s,i|i⟩
  · simp only [forecast,orient_plus,hv,orient_zero,Fout,hZ,Sum.elim_inl]; unfold zip; simp only [Pi.zero_apply,
      map_zero,Finset.sum_const_zero,sub_zero]; abel
  simp only [forecast, orient_plus, he,orient_zero,Qout,hZ,Sum.elim_inr]; unfold zip; simp only [Pi.zero_apply,
    map_zero,Finset.sum_const_zero,sub_zero]; abel

lemma leave (P : Teller G) (x : ℝ) (T : Tube G S) (hp : P.Funds S T) (p : Pos S) (w : Directions G f)
    (a : ℝ) (ha : 0 ≤ a) (hx : ∀ i, ‖w i‖ ≤ a) :
    ‖forecast T p (form w) 0- derivative T (till x) p 1 w‖ ≤
      Real.exp (-P.top.width*till x)*P.top.paths*4*a := by
  obtain ⟨L,C,hA,hV⟩ := hp.feeds
  have hH : Limage T 0=0 := funext (x_zero T.low T.down)
  have he : untwine S p 1 w=maps p.1 1 w := by
    unfold untwine; rw [replica_one,show pull p.1 0 (1:Config G c)=1 from funext fun i => by simp [pull,Step.read]]
    funext; simp [rotateG,corner_flat]
  have hu : orient p.1 (form w)=form (untwine S p 1 w) := by rw [he,orient,collect_form]
  have hv v : ‖untwine S p 1 w v‖ ≤ a := by rw [pull_cost]; exact hx _
  let R := till x
  let B := Real.exp (-P.top.width*R)
  have hb : 0≤B := (Real.exp_pos _).le
  have hy : 0 < P.top.paths := P.top.paths_pos
  rcases p with ⟨s,⟨i,y⟩|i⟩
  · unfold forecast derivative; dsimp only [Sum.elim_inl]
    rw [hu,orient_zero,Fout,hH,show zip (flatF T) 0 (i,y)=0 from by simp [zip],sub_zero,level,xLin]; split
    next hy =>
      let z := untwine S (s,Sum.inl (i,y)) (1:Config G c) w
      let u (l : ℕ) := (T.up.row i.2 l).1 • curl (slotFace (T.up.row i.2 l).2 i.1) z
      let v l := bandTerm T R i l z
      have hu : Summable u := ellLine_summable _ hA ..
      have h2 : Summable v := band_summable hp ..
      change ‖(∑' l,u l)- ∑' l, v l‖ ≤ B*P.top.paths*4*a
      rw [← hu.tsum_sub h2]
      let A l := |(T.up.row i.2 l).1| * Real.exp (P.top.width*(T.up.row i.2 l).2.length)
      have H : SumBudget A P.top.paths := hA.rows _
      have hf l : ‖u l-v l‖ ≤ A l * (4*a*B) := by
        unfold v bandTerm; split
        next ht => unfold u; rw [sub_self,norm_zero]; unfold A; positivity
        next ht =>
          rw [sub_zero]; unfold u; rw [norm_smul]; unfold A
          let X := (T.up.row i.2 l).1
          let L := (T.up.row i.2 l).2.length
          have hp := P.top.width_pos
          have hh : 1 ≤ Real.exp (P.top.width*L)*B := by
            unfold B; rw [← Real.exp_add]; apply Real.one_le_exp
            have he : (R:ℝ) ≤ L := Nat.cast_le.mpr ((Nat.lt_of_not_ge ht).le)
            linarith only [mul_le_mul_of_nonneg_left he hp.le]
          apply le_trans (mul_le_mul_of_nonneg_left (curl_cost _ _ _ hv) (norm_nonneg _))
          calc
            ‖X‖*(4*a) ≤ ‖X‖*(4*a)*(Real.exp (P.top.width*L)*B) := le_mul_of_one_le_right (by positivity) hh
            _ = _ := by rw [Real.norm_eq_abs]; unfold L X; ring
      have hs := (H.2.1.mul_right (4*a*B)).of_nonneg_of_le (fun l => norm_nonneg _) hf
      calc
        _ ≤ ∑' l,A l *(4*a*B) := (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum hf (H.2.1.mul_right _))
        _ ≤ P.top.paths*(4*a*B) := by rw [tsum_mul_right]; gcongr; exact H.2.2
        _ = _ := by ring
    next => rw [sub_self,norm_zero]; positivity
  unfold forecast derivative; dsimp only [Sum.elim_inr]
  rw [hu,orient_zero,Qout,hH, show zip (flatI T) 0 i=0 from by simp [zip], sub_zero,sub_self,norm_zero]; positivity
end YM.AnalyticNext.ConnectedActivity.Aff
