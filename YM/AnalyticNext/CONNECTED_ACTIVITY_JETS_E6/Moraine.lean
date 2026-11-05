import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Duster
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Inc
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Pedi


/-!
# At protected endpoints of actual ratio letters

 At x Manifest even if angular cold elsewhere. Avoid *any* density powers from
 external Gaussian amplitude. Telescope on full block persistence, not
 assuming sign of matrix powers or eliminating Shared psi in a partner.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Silica.Clutch
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Tablet
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen 
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {k : Finset ℕ} {R : Rep G f} {X : Coat T F} {z : Air f G} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}
variable {a A α β γ d η σ W s b μ r Q p q v : ℝ} {j n : ℕ}
variable {V : E→ Config G c} {w : E → Directions G f} {u : E→ Air f G}

lemma occupancy (H : Clutch X z a β s x j V w u) (p : Bond f) (hμ : Brush j d 1 (fun x=>voltage (vary X (V x)) p) x) (hp : X.Hot p)
    (he : ¬ (fun y=> Polar.patch X a (w y) p)=ᶠ[𝓝 x] fun _=>0) :
    Brush j ((gStep β)⁻¹*((s+2*(2*a)*X.t)+d)) 1 (fun x' => X.atmos (u x') p) x := by
  have hv : 0<2*a*X.t := by rw [mul_assoc]; exact mul_pos (by norm_num) H.pulse
  simp_rw [Polar.patch,if_pos hp] at he
  have hh:= (H.fostered p hv he).2
  have hg : 0<gStep β:=inv_pos.mpr (Real.sqrt_pos.mpr H.beta)
  have he x : X.atmos (u x) p=(gStep β)⁻¹ • (w x p-voltage (vary X (V x)) p) := by
    rw [← H.moving x, worldZ,Pi.add_apply, Pi.smul_apply, add_sub_cancel_left, inv_smul_smul₀ hg.ne']; rfl
  have hz:= (hh.separating hμ).smul ((gStep β)⁻¹); rw [Real.norm_of_nonneg (inv_nonneg.mpr hg.le)] at hz
  exact hz.shimmy (Eventually.of_forall he)

private lemma spindlePay (H : Clutch X z a β s x j V w u) (he : 0≤p) (hz : 0≤q) (hv : 0≤d)
    (hp : ∀ᶠ y in 𝓝 x,(vary X (V y)).Noncrystal) (hy : Room P S T X.x)
    (hU : ∀ i, (X.Hot i → (¬ (fun y=>Polar.patch X a (w y) i)=ᶠ[𝓝 x] fun _=>0) → Brush j p 1 (fun y=> X.atmos (u y) i) x) ∧
      Brush j 1 d (fun y=> Polar.patch X a (w y) i) x) (i : Bond f)
    (hF : ∀ i, Brush j q 1 (fun y=> shimmer (vary X (V y)) β i) x) (hr : R.beta=β) :
    Brush j ((Fintype.card G.ColorIndex:ℝ)*(p*q)) (d+(1+1)) (fun y=> major (vary X (V y)) a R (w y) (u y) i) x := by
  subst β
  have hx : 0≤ (Fintype.card G.ColorIndex:ℝ)*(p*q) := by positivity
  have hq : 0 ≤ d+(1+1) := by linarith
  by_cases hi:X.Hot i
  swap; · apply Brush.zi _ hx hq
          filter_upwards [hp] with y hh; let Y:= vary X (V y); unfold major
          rw [show (∑ k:G.ColorIndex,u y (i,k)*shimmer Y R.beta (i,k))=0 from sum_eq_zero fun j _=> by rw [Y.calm_crys hh hy.accepted R.beta (i,j) hi, mul_zero], mul_zero]
  let f t:= Polar.patch X a (w t) i
  by_cases h:f=ᶠ[𝓝 x] fun _=>0
  · apply Brush.zi _ hx hq; filter_upwards [h] with y hy; change f y*_ = (0:ℝ); rw [show f y=0 from hy,zero_mul]
  apply ((hU i).2.paints (Brush.spree univ _ _ (show (0:ℝ)≤1+1 by norm_num) (fun k (_:k∈ (univ:Finset G.ColorIndex))=> (colorEvaluated k ((hU i).1 hi h)).paints (hF (i,k))))).climb _ le_rfl
  rw [sum_const,nsmul_eq_mul,card_univ,one_mul]

lemma spindle (H : Clutch X z a R.beta s x j V w u) (he : 0≤p) (hz : 0≤q) (hv : 0≤d)
    (hp : ∀ᶠ y in 𝓝 x,(vary X (V y)).Noncrystal) (hy : Room P S T X.x)
    (hU : ∀ i, (X.Hot i → (¬ (fun y=>Polar.patch X a (w y) i)=ᶠ[𝓝 x] fun _=>0) → Brush j p 1 (fun y=> X.atmos (u y) i) x) ∧
      Brush j 1 d (fun y=> Polar.patch X a (w y) i) x) (i : Bond f)
    (hF : ∀ i, Brush j q 1 (fun y=> shimmer (vary X (V y)) R.beta i) x) :
    Brush j ((Fintype.card G.ColorIndex:ℝ)*(p*q)*(1+(d+(1+1)))^j) 1 (fun y=> major (vary X (V y)) a R (w y) (u y) i) x :=
    (spindlePay H he hz hv hp hy hU i hF rfl).trim

lemma slopeLedger (X : Coat T F) (hP : Tablet j γ q v (fun y=> (vary X (V y)).plate) (along S) (along S) x) {m : ℕ}
    (ho : Allow (vary X (V x)).plate (along S) m η r Q) (hg : γ≤ retain η r Q) (hp : Room P S T X.x)
    (_he : 0≤p) (hv : 0≤d) (l : Ledger f 2)
    (hU : ∀ i, (X.Hot i → (¬ (fun y=>Polar.patch X a (w y) i)=ᶠ[𝓝 x] fun _=>0) → Brush j p 1 (fun y=> X.atmos (u y) i) x) ∧
      Brush j 1 d (fun y=> Polar.patch X a (w y) i) x) :
    let s:= payE η r Q m; let f:=facePrice j X.B m q s; let t:= tidal γ q f X.B; let z:= q*(token j q s*t)
    let c:=(Fintype.card G.ColorIndex:ℝ); let d':=v+(driftP j v+(v+driftP j v)); let H:=d'+(d+1)
    Brush j (cap S X.B 2 l (p^2 * c^4 * (q*z)) (c*z)) ((↑(l.1+2:ℕ):ℝ)*H)
      (fun y=> entangled (vary X (V y)) a (w y) (u y) l) x := by
  intro s f' t z c' d' H; rcases l with ⟨n,e,l⟩
  let Y k:= vary X (V k); let i:= arrive e l; have hx:= debris X.shutter hP ho hg (fun k=> (Y k).balanced)
  have hb : 0≤q:=hP.basis; have hz :0≤z:=hx.basis; have hc:0≤c':=Nat.cast_nonneg _
  have hd:0≤d':=hx.pos; have hk : 0≤ (↑(n+2:ℕ):ℝ)*H := by unfold H; positivity
  let T x:=combo e l ((Y x).finale n)
  let v (j t : ℕ):= if t ≤ j then z else q
  have hh x : (Y x).qunique (u x) ⟨n,e,l⟩=(1/2:ℝ)*(∑ k:G.ColorIndex,u x (e,k)*∑ j:G.ColorIndex, T x k j*u x (i,j)) := rfl
  by_cases h:Armed S (3*X.B) e l
  swap
  · unfold Pulse.Itinerary.cap; refine Brush.zi ?_ (by rw [if_neg (by exact h)]) hk
    refine Eventually.of_forall fun x=>?_
    have hf : T x=0 := filtered S (3*X.B) _ _ h _ (fun j _=> by
      unfold finale; split
      next he=> exact Itinerary.opposite _ (effects _ _ ((Y x).span hp) (le_trans (by norm_num) hp.sight.1))
      next => exact fun i l ht=> (Y x).span hp i l (by change separation _ _ > (Y x).B/2; change X.B/2 < _; omega))
    change _*(Y x).qunique (u x) ⟨n,e,l⟩=0; rw [hh x,hf]; simp
  unfold cap; rw [if_pos (by exact h)]
  have hnn : 0 ≤ p^2*c'^4*(q*z)*(c'*z)^n := by positivity
  by_cases hi : X.Hot e ∧ X.Hot i
  swap
  · have hv : ∀ᶠ x' in 𝓝 x,(Y x').Noncrystal := X.crystals (V:=V) (fun i k=> (hP.singular i k).smooth.of_le (by simp)) ho
    refine Brush.zi (hv.mono (fun x hx=> ?_)) hnn hk
    have he : (Y x).qunique (u x) ⟨n,e,l⟩=0 := by by_contra hn; exact hi ((Y x).emitting_crys hx hp.accepted _ ⟨n,e,l⟩ hn)
    exact show _ * (Y x).qunique (u x) ⟨n,e,l⟩ = _ from by rw [he,mul_zero]
  by_cases he' : ((fun y=>Polar.patch X a (w y) e)=ᶠ[𝓝 x] fun _=>0) ∨ ((fun y=>Polar.patch X a (w y) i)=ᶠ[𝓝 x] fun _=>0)
  · apply Brush.zi _ hnn hk
    rcases he' with h|h
    · filter_upwards [h] with y hy; change Polar.patch X a (w y) e*_*_=_; rw [show Polar.patch X a (w y) _=0 from hy]; simp
    filter_upwards [h] with y hy; change _ * Polar.patch X a (w y) i * _=_; rw [show Polar.patch X a (w y) _=0 from hy]; simp
  obtain ⟨hu,hU'⟩:= not_or.mp he'
  let V':= c'^(n+2)*(q*z^(n+1)); let W:= ((↑(n+2:ℕ):ℝ)*d')
  have hW:0≤W:= mul_nonneg (Nat.cast_nonneg _) hd
  have hf k j' : Brush j V' W (fun x=> T x k j') x := by
    refine (canon (n:=n+2) (fun y=> (Y y).finale n) (v n) (fun k hk i j'=> ?_) hd l e k j').climb ?_ le_rfl
    · unfold v; split
      next ht=> simp_rw [finale,if_pos ht]; exact hx.mirror.singular ..
      next ht=> simp_rw [finale,if_neg ht]; exact (hP.singular ..).climb le_rfl (le_add_of_nonneg_right (by
        unfold driftP; have :=hP.pos; positivity))
    have hg (n : ℕ) : Itinerary.tally (n:=n+2) (v n)=q*z^(n+1) := by
      induction n with
      | zero=> rw [count_mul 1,count_mul 0]; change v 0 0*(v 0 1*1)=_; simp [v,mul_comm]
      | succ n ih=> rw [count_mul (n+2),show (fun i=>v (n+1) (i+1))=v n from funext fun i=>by simp [v], ih]
                    unfold v; rw [if_pos (Nat.zero_le _),pow_succ]; ring
    rw [hg]
  have hT k : Brush j (c'*(V'*p)) (W+1) (fun x=> ∑ j', T x k j'*u x (i,j')) x := by
    apply (Brush.spree _ _ _ (by positivity :0≤W+1) (fun j' (_:j'∈univ)=> (hf k j').paints (colorEvaluated j' ((hU _).1 hi.2 hU')))).climb _ le_rfl
    rw [sum_const,nsmul_eq_mul,card_univ]
  have hQ : Brush j (c'*(p*(c'*(V'*p)))) (1+(W+1)) (fun x=> ∑ j',u x (e,j')*∑ k,T x j' k*u x (i,k)) x := by
    apply (Brush.spree _ _ _ (by positivity : 0≤1+(W+1)) (fun j' (_:j'∈univ)=> (colorEvaluated j' ((hU _).1 hi.1 hu)).paints (hT j'))).climb _ le_rfl
    rw [sum_const,nsmul_eq_mul,card_univ]
  have hA := hQ.smul (1/2)
  apply (((hU e).2.paints (hU i).2).paints hA).climb
  · rw [Real.norm_of_nonneg (by norm_num : 0≤ (1/2:ℝ)), one_mul,one_mul]; apply (mul_le_of_le_one_left hQ.nonneg (by norm_num)).trans
    unfold V'; exact le_of_eq (by dsimp only; ring)
  dsimp only; unfold W H; push_cast; nlinarith [Nat.cast_nonneg (α:=ℝ) n]
end YM.ConnectedActivityE6.Blaze.Silica.Clutch
