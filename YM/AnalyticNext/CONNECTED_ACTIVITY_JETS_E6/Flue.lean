import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Hogs
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.TowerPower
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Veined

/-!
# All-purpose stock bill spends. Compulsory per whole packet including
 fore readings. Large constants are NOT amplitude estimates on every field;
 only nourish the exponential marker. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Silica.Clutch
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {k : Finset ℕ} {R : Rep G f} {X : Coat T F} {z : Air f G} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}
variable {a A α β γ d η σ W s b μ r Q p q v y' : ℝ} {j n l : ℕ}
variable {V : E→ Config G c} {w : E → Directions G f} {u : E→ Air f G}

private lemma conical {B : ℝ→ℝ} (hB : Rate G L 1 B) (j : ℕ) : ∃ C : ℝ, 0≤C ∧ ∀ᶠ x : ℝ in atTop,
    ∀ m : ℕ,1 ≤ m → ((|B x| *m:ℝ))^j ≤ Real.exp ((C*Delay.bill G L x^5) * m) := by
  refine ⟨3*(j:ℝ),by positivity,?_⟩
  filter_upwards [hB 2 (by norm_num), (Work.E09.betaF_growth G L).eventually_ge_atTop 2] with x hx ht m hm
  let M : ℝ:=m; have hM:1≤ M := by unfold M; exact_mod_cast hm
  let g:=Delay.bill G L x; let t:= betaF G x L; have ht : 2≤ t := ht
  have he : 1≤ g:= Delay.bill_ge ..; have ht':0 < t:= by linarith
  have hh : Real.log t ≤ g := by unfold g Delay.bill t; nlinarith [Nat.cast_nonneg (α:=ℝ) (radiusB x)]
  have hp : |B x| ≤ Real.exp (2*g^5*M) := by
    apply hx.trans; rw [Real.rpow_two,show betaF G x L=t from rfl,← Real.exp_log ht', ← Real.exp_nat_mul]
    apply Real.exp_monotone; push_cast; nlinarith [le_self_pow₀ (n:=5) he (by decide)]
  apply (pow_le_pow_left₀ (show 0≤ |B x| *M from by positivity) (mul_le_mul hp (show M ≤ Real.exp (g^5*M) by
    have he := one_le_pow₀ (n:=5) he; linarith [Real.add_one_le_exp (g^5*M), le_mul_of_one_le_left (zero_le_one.trans hM) he]) (zero_le_one.trans hM) (Real.exp_pos _).le) j).trans_eq
  rw [← Real.exp_add,← Real.exp_nat_mul]; congr 1; unfold g M; ring

lemma chimney (P : Teller G) (D : Patch) (L : Side) (hd : D.Branches P.bind G) (K γ W a : ℝ) (χ : Chi) (j : ℕ)
    {Ñ : ChartRatio G} (hÑ : LocalRatio Ñ) {p q : ℝ→ℝ} (h : Rate G L (-(1/2)) p) (he : ∀ᶠ x in atTop,0≤p x) (hp : Rate G L (-(1/2)) q)
    {η r Q : ℝ} (μ : ℝ) (Y : ℝ) (ht : Torch η r Q) (ha : 0<a) (hW : 0<W) (hm : γ*K ≤ a) : ∃ C, 0≤ C ∧ ∀ᶠ x in atTop,
    ∀ (c f:Side) (S:StepData c f) (T: Tube G S), S.patch=D → Works P L x S T → ShellAccess S G x W K γ → PointCharge T x W μ →
      ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (y:E) (U : E→ Config G c) (F : Forest S.ratio)
      (X : Coat T F) (A : Rep G f) (u:E → Directions G f) (w : Air f G) (z : E→ Air f G), X.x=x → X.χ=χ → X.width=K →
      Port P L η r Q Y X → Mode U y j (p x) → Intake P T x A → Clutch X w a A.beta (q x) y j U u z →
        ∀ (Z:Stores S) (l:ℕ) (k: Finset ℕ),500≤l → 1≤Z.shares → Healthy (Pressure.temp X.x) (Z.dome (l*X.B)) X.V →
        Brush j (Packets.income 1 (C*Delay.bill G L x^5) (A.beta*(μ*X.t^2)) Z.shares) 1
          (fun v=> Polar.stock (vary X (U v)) a A W Ñ (u v) (X.input (worldZ X A.beta w)) k Z) y := by
  obtain ⟨A,hA,hX⟩:= dinner P D L hd hÑ ha hW η r Q Y γ K μ hm
  obtain ⟨B,hB,hY⟩:= stilly P L D hd K γ W a χ j hÑ h he hp Y ht
  obtain ⟨E,hE,hT⟩:= dynam G L χ j hp h a W
  obtain ⟨R,hR,H⟩:= Brush.neighborhood (k:=j) 0 Real.contDiff_exp.contDiffAt
  let C := 1+(j.factorial:ℝ)*R; let a' x:= 1+(C*(1+|B x|)+ |E x|)
  have hh {V : ℝ→ℝ} (h : Rate G L 1 V):= h.compare (v:=fun x=>|V x|) (Eventually.of_forall fun x=> (abs_abs _).le)
  have hI := (Rate.const (L:=L) (G:=G) (1:ℝ)).weaken (b:=1) (by norm_num)
  have hQ:Rate G L 1 a':= hI.add (((hI.add (hh hB)).mul_left C).add (hh (hE.weaken (by norm_num))))
  obtain ⟨U,hU,hF⟩:= conical hQ j
  refine ⟨A+U,add_nonneg hA hU,?_⟩
  filter_upwards [hX,hY,hT,hF] with x hX hY hT hF c f S T hS hP hZ hk E' _ _ _ y V F X R_ u w z he hχ hK Γ hv hR' h Z l k hl hm h'
  let P := X.input (worldZ X R_.beta w); let Y:= X.plaza (Z.dome (304*X.B))
  let A' j:=X.enforce a (u j) Y; let C' j:= Mask.profiles Z X.χ (300*X.B) X.x W P X.k (V j)
  let Y':= Mask.tickets Z (300*X.B) P X.k
  let B' := Contract.order R_ k (vias S Z (300*X.B)) P
  let b := (A+U)*Delay.bill G L x ^ 5; let θ := R_.beta*(μ*X.t^2)
  let L' i:= vary X (V i); let f i := plumeLog (L' i) a R_ Ñ (u i) P Z
  have hs : 0 ≤ Packets.income 1 b θ Z.shares := by unfold Packets.income; positivity
  unfold Polar.stock; change Brush j (Packets.income 1 b θ Z.shares) 1 (fun i=> if Z.place ⊆ X.seeds.place ∧ Z.flags=∅ then
    Real.exp (f i)*B'*Y'*C' i*A' i else 0) _
  split_ifs with hg
  swap; · exact Brush.zi EventuallyEq.rfl hs zero_le_one
  by_cases hh : (A'=ᶠ[𝓝 y] fun _=>0) ∨ Y'=0 ∨ (C'=ᶠ[𝓝 y] fun _=>0)
  · refine Brush.zi ?_ hs zero_le_one
    rcases hh with h|h|h
    · filter_upwards [h] with y hy; dsimp only at *
      rw [hy,mul_zero]
    · exact Eventually.of_forall fun x=> by dsimp only; rw [h]; ring
    filter_upwards [h] with y hy; dsimp only at *; rw [hy,mul_zero,zero_mul]
  obtain ⟨hψ,hh⟩ := not_or.mp hh; obtain ⟨hz,hw⟩:=not_or.mp hh; let x' : ℝ:=Z.shares; have hx:1 ≤ x' := by unfold x'; exact_mod_cast hm
  let d := Delay.bill G L x
  have hφ : Real.exp (f y+tollFee S.patch (300*X.B)*x') ≤ Packets.income 1 (A*d^5) θ Z.shares := hX c _ S T hP hS hk F X he Γ hK
    (he.symm ▸ hZ) E' y V R_ (he.symm ▸ hR') u z w j _ _ hv h Z hg.1 hg.2 l hl h' hψ hz hw
  have hp := hT _ _ S T F X he hP.length_eq hχ (show 0<W*X.t from mul_pos hW Γ.sails.room.fiery) _ y V u w z R_ hv h Z P k
  have ht := fever f (hY c _ S T hS hP hZ _ y V F X R_ u w z he hχ hK Γ hv hR' h Z P hψ) H.self_of_nhds
  have hq: Brush j (Packets.income 1 (A*d^5) θ Z.shares) (C*(1+|B x| * x')+ |E x| *x') _ y := (ht.paints hp).climb (by rw [← Real.exp_add]; exact hφ) le_rfl
  refine (hq.trim.climb ?_ le_rfl).shimmy ?_;
  · have hb : 0 < C := by unfold C; positivity
    have hA := hF Z.shares hm
    have hxo : 1+(C*(1+|B x| * x')+|E x| *x') ≤ |a' x| *x' := by
      apply le_trans _ (mul_le_mul_of_nonneg_right (le_abs_self _) (zero_le_one.trans hx)); unfold a'; nlinarith only [hx,hb]
    apply (mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ (by positivity) hxo j).trans hA) hq.nonneg).trans_eq
    unfold Packets.income; rw [mul_assoc,← Real.exp_add]; unfold b d; congr 2; ring
  exact Eventually.of_forall fun i=> by change _=Real.exp (f i)*(B'*Y'*C' i*A' i); ring
end YM.ConnectedActivityE6.Blaze.Silica.Clutch
