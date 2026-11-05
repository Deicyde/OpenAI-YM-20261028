import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Intrados
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Moraine
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Periscope
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.StreamsCost

/-!
# Capacity of σ ledger at real matrices/measure

 Buys each occurrence, optional horizon supplied at TAGGED data. No
 odd/negative sign estimates except exact when necessary. Jacobian later.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Silica.Clutch
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge}

set_option maxHeartbeats 500000 in
lemma waits (P : Teller G) (L : Side) (D : Patch) (hD : D.Branches P.bind G) (K γ W a : ℝ) (χ : Chi) (j : ℕ)
    {p q : ℝ→ℝ} (h : Rate G L (-(1/2)) p) (he : ∀ᶠ x in atTop, 0≤p x) (hp : Rate G L (-(1/2)) q) {η r S' : ℝ} (Y : ℝ)
    (ho : Torch η r S') (t δ ε : ℝ) (ht : t<0) (hδ : 0 ≤ δ) (l:ℕ) (hl:4≤l) :
    ∃ V, Rate G L t V ∧ ∀ᶠ x in atTop, ∀ (c f: Side) (S: StepData c f) (T : Tube G S), S.patch=D → Works P L x S T →
      ShellAccess S G x W K γ → Tent P L x K η r S' Y T → ∃ R,
      Sales (radiusB x) δ ε (basisFoot S (radiusB x) l) R (basisCharge f) (V x) ∧
        ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (F : Forest S.ratio) (X : Coat T F) (A : Rep G f)
        (Z : E→ Config G c) (u:E→ Directions G f) (z : E → Air f G) (y:E) (w:Air f G), X.x=x → X.χ=χ → X.width=K → X.manifest →
        Mode Z y j (p x) → Clutch X w a A.beta (q x) y j Z u z → Intake P T x A → ∀ i : ChainIndex f,
        Brush j (R i) 1 (fun t=> spins (vary X (Z t)) a A (u t) (z t) i) y := by
  obtain ⟨C,hC,hX⟩:= bounded_stencils P D hD
  obtain ⟨b,hB,hz⟩:= Vine.enlighten P L D hD l j hl ho t δ ε ht hδ h
  obtain ⟨s,J,hS,hj,hY⟩:= Blaze.vines P L D hD K γ W χ j ho h he t
  obtain ⟨B,hB',hx⟩:= kernels G L χ hp j (2*a)
  let R:= min (P.top.width/2) (retain η r S')
  have hR : 0<R := lt_min (half_pos P.top.width_pos) ho.prices; have hh : R<P.top.width := (min_le_left ..).trans_lt
    (by linarith [P.top.width_pos]); have hk:R ≤ retain η r S' := min_le_right ..
  let u:= carat D P L R C; let G' := u*u+1; let d:=tubularPrice G L; let T:= payE η r S' d; let n := (Fintype.card G.ColorIndex:ℝ)
  let α x := q x+2*(2*a)*Pressure.fiery G x L; let w x:= |burst G L x| * (|α x|+|s x|)
  let v x:= kernelGrowth (radiusB x) G (p x); let g x:=v x+v x; let hP x:=driftP j (g x); let z x:=g x+(hP x+(g x+hP x))
  let f x:=z x+(|B x|+1)
  let X x:= facePrice j (radiusB x) d G' T; let F x:= G'*(token j G' T * tidal R G' (X x) (radiusB x)); let A x:= (w x)^2*n^4*(G'*F x); let N x:= n*F x
  have hG {p : ℝ→ℝ} {u : ℝ} (hp : Rate G L u p) : Rate G L u (fun x => |p x|) := hp.compare (Eventually.of_forall fun x=> (abs_abs _).le)
  have hc:= Rate.const (G:=G) (L:=L) (1:ℝ); have hr (V : ℝ→ℝ) (h : Rate G L 0 V) : Rate G L 0 (fun x=> (1+V x)^j) := by
    simpa only [zero_mul] using! (hc.add h).pow j
  have hw : Rate G L 0 w := by convert (hG (Coat.burst_rate G L)).mul ((hG (hp.add (Rate.flame.mul_left (2*(2*a))))).add (hG hS)) using 1; ring
  have hg := ((jet_growth G L h).add (jet_growth G L h)).weaken (b:=0) (by norm_num)
  have hp':Rate G L 0 hP := hg.mul_left _
  have hf:Rate G L 0 f := (hg.add (hp'.add (hg.add hp'))).add ((hG hB').add hc)
  have hF : Rate G L t F := ((swims G L t (polynomial G L j d G' T) hR G').mul_left _).mul_left _
  have hA : Rate G L t A := by simpa only [zero_mul,zero_add] using! (((hw.pow 2).mul_right (n^4)).mul (hF.mul_left G'))
  obtain ⟨V,hV,hT⟩:= out P L l 2 δ ε hδ hl ht _ _ (show Rate G L t (fun x=> blurs (f x) (A x) 2 j) from by
    simpa only [add_zero] using! hA.mul (hr _ (hf.mul_left (1+(2:ℝ))))) ((hF.mul_left n).mul_right (2^j))
  let D' x := n*(w x*|J x|)*(1+(|B x|+(1+1)))^j
  have hΨ : Rate G L t D' := by
    convert (((hw.mul (hG hj)).mul_left n).mul (hr _ ((hG hB').add (Rate.const (1+1))))) using 1; ring
  let E x:= ((Animals.ballCost ((l+1)*radiusB x):ℝ)*Itinerary.density L)*(D' x*Real.exp (δ*Animals.ballCost (l+1)))
  have hE:Rate G L t E := by
    have hs:= width_rate G L (l+1) 0; simp only [add_zero] at hs
    convert (hs.mul_right (Itinerary.density L)).mul (hΨ.mul_right _) using 1; ring
  refine ⟨_, hB.add (hB.add (hB.add (hE.add hV))),?_⟩
  filter_upwards [hz,he,hY,hT,hx,room G P L] with x hB hv hT H h hh' c f' S S_T hS hS' hP hΨ
  have hr:=hh' c f' S S_T hS'; let d':=radiusB x; have ho':= hr.sight
  obtain ⟨z',w',hz,hW,hO⟩:=hB _ _ S S_T hS hS'
  have hy:0≤w x:= by unfold w; positivity
  have he : 0≤ G' := add_nonneg (mul_self_nonneg _) zero_le_one
  have hH : 0≤f x:= by
    unfold f z
    have hs:0≤g x:=by unfold g v kernelGrowth; have hh:= royalty_ge G; positivity
    change 0≤g x+(driftP j (g x)+(g x+driftP j (g x)))+_; unfold driftP; positivity
  have hn : 0≤ n := by unfold n; positivity
  have hs : 0≤ T := mul_nonneg (mul_nonneg (tsum_nonneg fun j=> by unfold rates0; positivity) (Nat.cast_nonneg _))
    (inv_nonneg.mpr ((lt_min zero_lt_one (half_pos ho.spans)).le))
  have hG : 0≤F x := by
    dsimp only [F]; unfold tidal
    have hh : 0≤ token j G' T:= by unfold token; positivity
    have hx : 0≤ X x := mul_nonneg (Nat.cast_nonneg _) hh
    positivity
  have hu : 0≤D' x := by unfold D'; positivity
  let R' := Vine.alert S (radiusB x) j 2 (f x) (A x) (N x)
  have hP' : Sales (radiusB x) δ ε _ R' Sigma.fst (V x) := H _ _ S S_T hS'.length_eq hr
    (by
     dsimp only [blurs]
     have hx:0≤A x:=by unfold A; positivity
     positivity) (by positivity)
  have hκ : Sales d' δ ε (town S d' l) (fun _=>D' x) (fun _=>0) (E x) := by
    refine YM.ConnectedActivityE6.fixed (d:=l+1) (o:=atEdge S) (m:=Itinerary.density L) (hS'.length_eq ▸ perch S) (by unfold d'; omega) _ ?_ hδ hu
    intro i y hy; exact (Animals.neighbors_mem ..).mpr ((Itinerary.checking _ _ _ _ _ hy).trans (by rw [add_mul,one_mul]; unfold d'; omega))
  refine ⟨_,hz.together (hz.together (hW.together (hκ.together hP'))),?_⟩
  intro E _ _ _ F X R_A Z y z' wHat t hs' hχ hK hM hp HC hI i
  have hhV := hΨ F X hs' hK hM
  have hp':= hhV.sails.scale
  have ha := show Allow (vary X (Z wHat)).plate (along S) d η r S' from HC.tipped.symm ▸ hp'
  have hL:=hO E F X Z wHat hs' hp ha
  rcases i with i|i|i|i
  · exact semi (hL.1 i).opposite
  · let V': E→Config G c := fun _=>1
    have h : Mode V' wHat j (p x) := ⟨hv,fun i=> a_oneB G 1 hv⟩
    exact semi ((hO E F X.blank V' wHat hs' h (show Allow (vary X.blank (V' wHat)).plate _ _ _ _ _ from hhV.empty.scale)).1 i)
  · exact semi (hL.2 i)
  have hhZ : (vary X (Z wHat)).manifest := by rw [HC.tipped]; exact hM
  have hM':= hT _ _ S S_T hS hS' hP F X E Z wHat hs' hK hχ hp
  have hZ := hM' hhZ ha
  have hθ := (hS'.length_eq ▸ hI.window.2 : R_A.beta ≤ 2*betaF G x L)
  have hB := hZ.2 R_A.beta hI.positive hθ
  have hF := h c f' S S_T F X hs' hS'.length_eq hχ (show 0<2*a*X.t by rw [mul_assoc]; exact mul_pos (by norm_num) HC.pulse) E t a R_A.beta wHat Z y z' HC
  have hg:= Gate.plates X D hS hS'.length_eq (hs'.symm ▸ hr) hp C hC (hX c f' S S_T hS hS'.funds) hR.le hh
  have hG i: (X.Hot i → (¬ (fun k=>Polar.patch X a (y k) i)=ᶠ[𝓝 wHat] fun _=>0) → Brush j (w x) 1
      (fun u=> X.atmos (z' u) i) wHat) ∧ Brush j 1 (|B x|) (fun u=>Polar.patch X a (y u) i) wHat := by
    have he := abs_nonneg (B x)
    refine ⟨fun h hi=> (occupancy HC i (hZ.1 i) h hi).climb ?_ le_rfl,?_⟩
    · have hp' : 0≤ q x+2*(2*a)*X.t := by have ht:= HC.price; have hz := HC.pulse; nlinarith only [ht,hz]
      refine mul_le_mul ((burst_h hθ).trans (le_abs_self _)) ?_ (add_nonneg hp' (abs_nonneg _)) (abs_nonneg _)
      refine add_le_add_left ?_ _; unfold Coat.t; rw [hS'.length_eq, hs']; exact le_abs_self _
    unfold Polar.patch; split_ifs
    next hi=> exact hF i
    exact (Brush.certified he _).climb (by rw [norm_one]) le_rfl
  rcases i with i|i
  · have hP := X.crystals (V:=Z) (fun i j=> (hg.singular i j).smooth.of_le (by simp)) ha
    exact spindle (R:=R_A) HC hy (abs_nonneg _) (abs_nonneg _) hP (hs'.symm ▸ hr) hG i hB
  have hx:= slopeLedger X hg ha hk (hs'.symm ▸ hr) hy (abs_nonneg (B x)) i hG
  dsimp only [Coat.B] at hx; rw [hs'] at hx
  exact Vine.fluid _ i hH hx
end YM.ConnectedActivityE6.Blaze.Silica.Clutch
