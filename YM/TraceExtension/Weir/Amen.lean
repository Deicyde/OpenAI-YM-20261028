import YM.TraceExtension.Weir.Vang
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Weir
open Function Filter Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Push.Uniform Det Lamp Analysis Finset
open Metric Filch Turret Shepherd AnalyticBridge VerifiedReset Extra.Iteration SectorAffine Offset Fen Kits Pills Loft Xo Zn StressFlux MeasureTheory Push.SectorMeasure
open PhysicalNext.JointLoad.Heir Next.Foundations Push.Local Swift WardBin WardBin.Lies WardBin.Wheels Next.Fluctuations Planned.AtomRegular.Foliage Next.SectorChange
open Wicket Outer.Nodes
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{n:Side} {k P:ℕ} {x:ℝ}
structure Snow (R:Rep G n)(F:Peat G n)(x c:ℝ):Prop where
   regular:R.p.Regular (tempQ x) F
   fare : R.p.supBounds (0:Site n) (tempQ x) F c
structure ClimateJ (R:Rep G n)(F:Peat G n)(x c C:ℝ):Prop where
   silk : F∈ loom G n
   puff: Snow R F x c
   price(U : Config G n): |F U| ≤ C
abbrev crumb(x:ℝ):ℝ:= thetaP x ^ (2:ℕ)*Wave (-2) x
abbrev trayF(x:ℝ):ℝ:= thetaP x ^(2:ℕ)*Wave (1/8) x
lemma wnt(S:Stage)(B:ℝ)(he:1≤B)(k:ℕ) : ∀ᶠ x:ℝ in atTop,
    let T (X s:ℝ):=composeCost k (X * evenR 2 B * s^ (2:ℕ)) B
    (∀ c:ℝ,c ≤ wideM x→ T c (sash S x)≤ trayF x) ∧ T (2*thinM x) (sash S x)≤ trayF x ∧ T (calorie x) (sash S x) ≤ crumb x ∧ composeCost k (swole x) B ≤ crumb x:=by
   let p(x:ℝ):=(1+(high x:ℝ))^S.power; let A:= (k.factorial:ℝ)*evenR 2 B*(1+B)^k; have hp:ConstMass 0 p:= ((mass zero_le_one).gather expansion).crop _; have hA:0 ≤ A:=by unfold A evenR; positivity
   let f(U:ℝ→ℝ)(x):= U x*(A*(p x)^2); have h(U:ℝ→ℝ)(a:ℝ)(h:ConstMass a U): ConstMass a (f U):=by
       simpa only [add_zero] using! h.prod ((hp.crop 2).times A hA)
   have hz:= h wideM (1/50) (waveM _) (1/8) (by norm_num); have he':= h (fun x=>2*thinM x) (1/200) ((waveM _).times 2 zero_le_two) (1/8) (by norm_num);
   have hu:Tigh (fun x=>Wave 2 x*f calorie x) 28:= Tigh.mult ((Zn.stays 30).fly ((hp.crop 2).times A hA)) (waveM _)
   let g(x:ℝ):=swole x; let F(x:ℝ):=(k.factorial:ℝ)*(1+B)^k*x^(-(1/100:ℝ))
   have hg:Lim (0+ -(1/100:ℝ)) F := (board (show 0 ≤(k.factorial:ℝ)*(1+B)^k by positivity)).prod (sands _)
   have H:=(hg.prod (ferry (waveM 2))).tiny (by norm_num)
   filter_upwards [H,hz,he',hu.tight (show 0≤28 by omega), eventually_gt_atTop (1:ℝ)] with x hm hv hZ hB hx
   have hw:0 < Wave 2 x:=Zn.wake ..; have hw' : Wave 2 x* Wave (-2) x=1:=by rw[Zn.walt]; simp [Wave];
   have hF(X:ℝ→ℝ)(z:ℝ)(hz:f X x ≤ z):composeCost k (X x*evenR 2 B*(sash S x)^(2:ℕ)) B ≤ thetaP x^(2:ℕ) * z :=by
       rw[show composeCost _ _ _=thetaP x^(2:ℕ)*f X x from ?_]; swap; · unfold f A p composeCost sash; ring
       exact mul_le_mul_of_nonneg_left hz (by positivity)
   refine ⟨fun c hC=> le_trans ?_ (hF wideM (Wave (1/8) x) hv.2), hF (fun x=>2*thinM x) _ hZ.2, hF calorie _ (le_of_mul_le_mul_left ?_ hw),?_⟩
   · unfold composeCost; have hs: 0≤ evenR 2 B:=by unfold evenR; positivity
     dsimp only; gcongr
   · rw[hw']; simpa only [pow_zero,_root_.inv_one] using hB.2
   rw[show composeCost k (swole x) B= thetaP x^(2:ℕ)*F x from (by unfold F composeCost swole; ring)]; apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ thetaP x^ (2:ℕ)); exact le_of_mul_le_mul_right (le_trans hm (by rw [mul_comm,hw'])) hw
-- Convert order across clocks. Compatible Sector and stress.Muted prices
variable {R:RG.Rep G n}{F:Peat G n}{S:Stage} {x:ℝ} {U:Config G n}
private lemma spiny (k:ℕ)(T:Collar G S.order)(r' ℓ:ℕ)(A x' Λ:ℝ)(h:Age S x Λ R)(hr:Cube.Wire R.p (high x) (h.rank.symm ▸ T))(he:F∈loom G n)(hσ:∀ U:Config G n, ContDiffAt ℝ ω (F ∘ increment U) 0)(hC:GaugeInvariant F)(he':LocalOn (ExtS n x) F)(hZ:2*(high x+10)< n.val)(hq:∀ (U:Config G n)(v:Directions G n), ‖v‖ ≤ Cube.fee T→ Allows k (F ∘ increment U) v A)(hp:S.order≤ k) : ClimateJ R F x (composeCost S.order (A*evenR 2 (Cube.fee T)*(sash S x)^2) (Cube.fee T)) A:=by
    let Q:= tempQ (n:=n) x; let T':Collar G R.p.order:=h.rank.symm ▸ T; have ht:Cube.fee T'=Cube.fee T:= fees_eq ..; have hB: R.p.Regular Q F:= regularAi hC (fun U W hv=> he' U W (agrees_mono hv (coe_subset.mpr (dec_b ..|>.2)))) (fun U=> (hσ U).of_le le_top); have he(i:Directions G n)(hx:‖i‖≤ Cube.fee T'):= ((hq 1 i (ht ▸ hx)).order (k:=R.p.order) (h.rank.le.trans hp))
    have hy: 1 ≤ Cube.fee T':= Cube.fee_one T'; have hq': (0:ℝ)≤A:=(he _ (show ‖(0:Directions G n)‖ ≤ _ from by rw[norm_zero]; positivity)).nonneg
    have hU := Turret.boundsP (r:=high x) T' A hq' hr (by omega) ‹F∈loom G n› he he' hB
    change R.p.supBounds _ _ _ (composeCost R.p.order (A*evenR 2 (Cube.fee T')*(Cube.moduleBill R.p (high x))^2) (Cube.fee T')) at hU
    rw [← shifts x S Λ R h,ht,h.rank] at hU
    refine ⟨‹_›,⟨hB,hU⟩,fun x=>?_⟩; have hx := hq x 0 (by rw[← ht,norm_zero]; positivity); simpa [Work.G07.at_zero_increment] using! hx.value
-- universal bill interface. Note hearth only analytic finite. pre multiplier K large.
lemma shimmer(G:Gauge)(S:Stage)(k:ℕ)(hp:S.order ≤ k)(T:Collar G S.order) : ∃ D:ℝ,0 ≤ D ∧ ∀ (x Λ:ℝ)(n:Side)(R:Rep G n)(h:Age S x Λ R), Cube.Wire R.p (high x) (h.rank.symm ▸ T)→2*(high x+10)<n.val→∀ (A:ℝ)(F:Peat G n),
    Splendor F (ExtS n x) k A D ∨ HearthV F (ExtS n x) k A D → ClimateJ R F x (composeCost S.order (A*evenR 2 (Cube.fee T)*(sash S x)^2) (Cube.fee T)) A:=by
   obtain ⟨C,hC,H⟩:= atp G (k+1) (Cube.fee T) (zero_le_one.trans (Cube.fee_one T))
   refine ⟨C,hC,fun x Λ n R h hz h' A F H'=>?_⟩
   rcases H' with hP|hP
   · exact spiny k T 0 0 A 0 Λ h hz hP.cloth hP.lit hP.symm hP.locale h' (fun U v he=> hP.tickets _ _ _ (fun i=>(H n U v he i).order (by omega))) hp
   exact spiny k T 0 0 A 0 Λ h hz hP.silk (fun U=> hP.choir _ _ _ (incrementA U 0)) hP.symU hP.pillar h' (fun U v he=> hP.price _ _ _ (H n U v he)) hp
end YM.Trace.Weir
