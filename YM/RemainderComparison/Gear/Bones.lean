import YM.RemainderComparison.Gear.Quill
import YM.RemainderComparison.Gear.Pennon
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Splay
/-!
 # Authorizations. FULL stem without β losses.

 Coupling g^{a}; here asks v of actual threshold order J. Can ask
 auxiliary purchases independently. No forests transferred here.
 Inquiry fixed prior post-small.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Flux
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider RemainderComparison
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}

def Disk (G : Gauge) (L : Side) (f : ℝ→ℝ→ℝ) : Prop:= ∃ (k:ℕ) (p:ℝ→ℝ), Reserve G L p∧ ∀ s:ℝ, ∀ x:ℝ, 1 ≤ x → |f s x| ≤ |p s| * x^k
namespace Disk
variable {f g:ℝ→ℝ→ℝ}
lemma fixP {p : ℝ→ℝ} (h : Reserve G L p) : Disk G L (fun s _=> p s):= ⟨0,p,h,by simp⟩
lemma still (a:ℝ): Disk G L (fun _ _=> a):= fixP (Reserve.const _)
lemma datum : Disk G L (fun _ x=>x):= ⟨1,fun _=>1,Reserve.const _,by intro x y hy; rw [pow_one,abs_one,one_mul,abs_of_nonneg (zero_le_one.trans hy)]⟩
lemma add (hp : Disk G L f) (hh : Disk G L g) : Disk G L (fun x y=> f x y+g x y):= by
  obtain ⟨i,v,hv,H⟩:= hp; obtain ⟨j,u,hQ,hx⟩:= hh
  refine ⟨i+j,_,hv.absolute.add hQ.absolute,fun s p hr=>?_⟩
  rw [abs_of_nonneg (show 0 ≤ |v s|+|u s| from by positivity),add_mul]
  exact ((abs_add_le ..).trans (add_le_add (H s p hr) (hx s p hr))).trans (by gcongr <;> omega)
lemma mul (hp : Disk G L f) (hh : Disk G L g) : Disk G L (fun x y=> f x y*g x y) := by
  obtain ⟨i,v,hv,H⟩:= hp; obtain ⟨j,u,hQ,hx⟩:= hh
  refine ⟨i+j,_,hv.mul hQ,fun s p hr=>?_⟩; rw [pow_add,abs_mul,abs_mul]
  exact (mul_le_mul (H s p hr) (hx s p hr) (abs_nonneg _) (by positivity)).trans_eq (by ring)
lemma pow (h : Disk G L f) (i:ℕ) : Disk G L (fun x y=> (f x y)^i):=by
  induction i with
  | zero=>simp only [pow_zero]; exact still _
  | succ i ih =>simp only [pow_succ]; exact ih.mul h
end Disk
lemma stepsS {W B C : ℝ→ℝ} {Z : ℝ→ℝ→ℝ} (j : ℕ) (h : Reserve G L W) (hp : Reserve G L B) (hv : Reserve G L C) (he : Disk G L Z)
    (u h' g : ℝ) : Disk G L (fun x y=> y* |B x| +seismic j u h' (W x) g (C x) (Z x y) y) := by
  have hh (x):= Disk.still (G:=G) (L:=L) x
  let p:=Disk.datum (G:=G) (L:=L)
  have hT : Disk G L (fun x y=> cenote j y g (W x) (C x)):=by
    refine (((hh (↑(j+1:ℕ))).mul (((hh 1).add p).pow j)).mul ((hh j.factorial).mul ?_))
    exact ((hh 1).add ((((Disk.fixP h).mul (hh g)).add (hh 1)).mul (((hh 1).add (Disk.fixP hv)).pow j))).pow j
  have ht : Reserve G L (fun x=> token j (W x) g):=
    Reserve.sum (j+1) _ (fun i _=> by exact ((((h.mul (Reserve.const g)).add (Reserve.const 1)).pow i).mul (Reserve.const g))) -- metavar
  have hF : Disk G L (fun x y=> (y*(Z x y*(token j (W x) g*Z x y)))*(1+(1+(driftP j (C x)+1)))^j):=by
    apply (p.mul (he.mul ((Disk.fixP ht).mul he))).mul
    exact ((hh 1).add ((hh 1).add ((Disk.fixP ((Reserve.const _).mul hv)).add (hh 1)))).pow j
  apply (p.mul (Disk.fixP hp.absolute)).add
  refine (hh (1+j.factorial*h')).mul ((hh 1).add ?_)
  exact ((hh (j.factorial*u)).mul (((hh 1).add (((hh 1).add hT).mul (hh j))).pow j)).add (hF.add hF)
lemma scoreP (P : Teller G) (L : Side) (D : Patch) (hD : D.Branches P.bind G) (K γ W a : ℝ) (χ : Chi) (j : ℕ)
    {V u e : ℝ→ℝ} (h : Gear G L (-(1/2)) V) (hp : Gear G L (-(1/2)) u) (he : Reserve G L e)
    {η r S' : ℝ} (Y : ℝ) (p:Torch η r S') (d : ℝ) : ∃ (k:ℕ) (B:ℝ→ℝ), Reserve G L B ∧ ∀ᶠ x in atTop,
    ∀ (c f:Side) (S:StepData c f) (T:Tube G S), Works P L x S T→ S.patch=D → ShellAccess S G x W K γ →
      ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (y:E) (U:E → Config G c) (F:Forest S.ratio) (X:Coat T F) (z:Air f G)
      (R:Rep G f), X.x=x → X.width=K → X.χ=χ → Port P L η r S' Y X → Intake P T x R → Mode U y j (V x) →
        Clutch X z a R.beta (|u x|) y j U (fun i=> steer X d (worldZ X R.beta z) (U i)) (fun i=>course X d R.beta z (U i)) →
        (∀ i, Brush j 1 (e x) (fun v=> steerJ X d (worldZ X R.beta z) (U v) i) y) →
          ∀ I, Brush j 1 (|B x| * facescale I z^k) (fun y=> scalp I X (U y) R.beta d z) y := by
  obtain ⟨Q,hQ,hX⟩:= Brush.neighborhood (k:=j) 0 Real.contDiff_exp.contDiffAt
  obtain ⟨M,hM,hY⟩:= Brush.neighborhood (k:=j) 1 (Real.contDiffAt_log.mpr (by norm_num))
  obtain ⟨A,hA,hT⟩:= quartz P L D hD K γ W χ j p h
  obtain ⟨H,hH,hP⟩:= bounded_stencils P D hD
  let m:= carat D P L 0 H; let f:= m*m+1; let t:= tubularPrice G L; let g:=payE η r S' t
  let v x:= kernelGrowth (radiusB x) G (V x); let W' x:=driftP j (v x+v x)
  let B:=payE (retain η r S') (S'⁻¹/2) (1+g) t; let C x:= burst G L x * (|u x| + (|A x| +|A x|))
  have hu :Reserve G L v:= Gear.zero.mp (Gear.ascend (jet_growth G L h.rate) (by norm_num))
  have hω :Gear G L (1/2) (burst G L) := by
    apply (Gear.power.mul_left (Real.sqrt 2)).congr
    filter_upwards with x; rw [burst,Real.sqrt_mul (by norm_num : (0:ℝ)≤2),Real.sqrt_eq_rpow (betaF G x L)]
  have hc:Reserve G L C:= Gear.zero.mp (by convert hω.mul (hp.absG.add (hA.absG.add hA.absG)) using 1; ring)
  obtain ⟨k,T,ht,hF⟩:= stepsS j (polyP G L j t f g) he (show Reserve G L W' from (Reserve.const _).mul (hu.add hu)) ((Disk.fixP hc).add Disk.datum) M Q B
  refine ⟨k,T,ht,hT.mono ?_⟩
  intro x hx c f' S T hh hv hS E _ _ y U F X z A' he hK hχ h hv hM' hB' hK' I
  have hΓ:= h.sails; have hX': X.manifest:= h.placed; have hL:(vary X (U y)).manifest := hB'.tipped.symm ▸ hX'
  subst x
  have hc:Rotator P L η r S' Y (vary X (U y)) := by rw [hB'.tipped]; exact hΓ
  have hp := Gate.plates X D (by assumption) hh.length_eq hΓ.room hM' H hH (hP _ _ S T (by assumption) hh.funds) (le_refl 0) P.top.width_pos
  have hx' := hx c _ S T (by assumption) hh hS F X E U y rfl hK hχ hM' hL hc.scale
  let w := facescale I z; have he := (hK' (0,0)).pos; have hy:= hF X.x w (expenses I z).1; dsimp only at hy; rw [abs_of_nonneg he] at hy
  refine (elevates I hY.self_of_nhds hX.self_of_nhds hc hp hx' (abs_nonneg _) hB' hK' he (b:=C X.x+w) ?_).climb le_rfl ((le_abs_self _).trans hy)
  apply add_le_add_left
  unfold C
  exact mul_le_mul_of_nonneg_right (burst_h (L:=L) (hh.length_eq ▸ hv.window.2)) (add_nonneg (abs_nonneg _) (add_nonneg (abs_nonneg _) (abs_nonneg _)))
lemma walkersP (G : Gauge) (L : Side) (p : ℝ) (j : ℕ) : ∃ (A : ℝ→ℝ) (n : ℕ), Reserve G L A ∧ ∀ S : ℝ, ∀ (ι κ e:ℝ),
    1≤e → 0≤ι → ι≤e*ballCost (radiusB S)*(Itinerary.density L:ℝ) → κ=ι*Fintype.card G.ColorIndex →
    (1+ι+κ+κ)^j*(1+κ*(2*Real.exp (p*(j:ℝ)^2/2))) ≤ |A S| * e^n := by
  let v (x:ℝ) (e:ℝ):= e*ballCost (radiusB x)*(Itinerary.density L:ℝ); let k (x e:ℝ):= v x e*Fintype.card G.ColorIndex
  have hc (v):= Disk.still (G:=G) (L:=L) v
  have hv : Disk G L v:= (Disk.datum.mul (Disk.fixP (Reserve.ball _ Reserve.field))).mul (hc _)
  have hp : Disk G L k:=hv.mul (hc _)
  obtain ⟨l,A,h,F⟩:= (((((hc 1).add hv).add hp).add hp).pow j|>.mul ((hc 1).add (hp.mul (hc (2*Real.exp (p*(j:ℝ)^2/2))))))
  refine ⟨A,l,h,?_⟩; intro S i K e hr hi hK hV
  apply ((le_abs_self _).trans (F S e hr)) |> le_trans ?_
  change _ ≤ (1+v S e+k S e+k S e)^j*(1+k S e* _)
  rw [hV]; unfold k; replace hK: i ≤ v S e:= hK; gcongr
end YM.ConnectedActivityE6.Blaze.Flux
