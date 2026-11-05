import YM.TraceExtension.Weir.Broad
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Weir
open Function Filter Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Push.Uniform Det Lamp Analysis Finset
open Metric Filch Turret Shepherd AnalyticBridge VerifiedReset Extra.Iteration SectorAffine Offset Fen Kits Pills Loft Xo Zn StressFlux MeasureTheory Push.SectorMeasure
open PhysicalNext.JointLoad.Heir Next.Foundations Push.Local Swift WardBin WardBin.Lies WardBin.Wheels Next.Fluctuations Planned.AtomRegular.Foliage Next.SectorChange
open Wicket Outer.Nodes
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{n:Side} {j:ℕ}
-- bound site footprint at Ext+.
def TileNo := ((2000000:ℕ)+2000000+1)^4
lemma tote (S:Stage)(x Λ:ℝ) (R:Rep G n)(H:Age S x Λ R): coverNumber R.p.B (tempQ x (n:=n)) ≤ TileNo:=by
   have hB:=R.p.B_pos
   have ht: high x+1 ≤ 2000000*R.p.B:=by unfold high puff rim;rw [← H.hM.2.1]; omega
   exact le_trans (Corona.cover_mono (sprout_mono _ ht) R.p.B) (Corona.tile (0:Site n) 2000000 R.p.B hB)
def dreamZ(x:ℝ):= x^(-(109/100:ℝ))
lemma zealH(S:Stage)(G:Gauge)(A Y:ℝ)(p q:ℕ)(hA:0≤ A)(hY:0≤ Y):∀ᶠ x:ℝ in atTop,∀ (Λ:ℝ) (h:ℕ)(hw: h≤ towerH x p)(n:Side)(R:Rep G n)(H:Age S x Λ R),
   let r:= Cleft x h; let K:=beamAmt R S.paths S.width Λ Y (rim x) q + vat R.p r A*((((r+r+1)^4:ℕ):ℝ)*hue x); K≤ dreamZ x∧ dreamZ x ≤1∧ polar R.p (dreamZ x) ≤1:=by
   let f(x:ℝ):= Cleft x (towerH x p); let g(x:ℝ):= ((1+(f x:ℝ))^S.power)^S.order; have hg:ConstMass 0 g:=((((mass zero_le_one).gather (campC p)).crop S.power).crop S.order)
   let Z:= momentPrice (q+4) (S.width/4); let T:=Geo.lowerSize S.clip S.paths; have hT:0 ≤ T:=by unfold T Geo.lowerSize; positivity [S.paths_pos,S.clip.quadratic_pos];
   have hζ:0 ≤ Z:=by unfold Z; exact (momentPrice_pos _ (by positivity[S.width_pos])).le
   let u(x):=(((2:ℝ)^S.order*(g x*A)*(2*g x))*(((f x+f x+1)^ (4:ℕ):ℕ):ℝ))*hue x
   have hu:Lim (-(11:ℝ)/10) u:=by
       let p(x:ℝ):= ((2:ℝ)^S.order*(g x*A)*(2*g x)); have hP:ConstMass 0 p:=((mass (show 0≤ (2:ℝ)^S.order by positivity)).cop (hg.cop (mass hA))).cop ((mass (show 0 ≤ (2:ℝ) by norm_num)).cop hg);
       have hD: ConstMass 0 (fun x=>p x*(((f x+ f x+1)^4:ℕ):ℝ)):=by push_cast; exact hP.cop ((((campC _).gather (campC _)|>.gather (mass zero_le_one)).crop 4))
       simpa only [zero_add] using! (ferry hD).prod chime
   let t(x:ℝ):= humble x; let A'(x):= Z*(T+(S.paths+S.paths+t x)); have hA':Lim 0 A':=by
      let V:= S.paths+S.paths; have hx:Lim 0 (fun x=>T+(V+t x)):= (board hT).plus ((board (show 0 ≤ V by unfold V; positivity [S.paths_pos])).plus (ferry h_mass)); simpa only [add_zero] using! (board hζ).prod hx
   let V(x:ℝ):= bankCost (radiusB x)*(Shepherd.wide G S.supportExponent*2*(1+4*x)*Y*Real.exp (-(S.width/4)*rim x))*A' x
   have hV : Lim (-(11:ℝ)/10) V:=by
      have h:S.width/4>0:= by positivity [S.width_pos]
      have ht: Lim 1 (fun x=>1+4*x):=by
         have he:Lim 1 (fun x=>4*x):=by simpa only [Real.rpow_one, zero_add] using! ((board (show (0:ℝ)≤4 by norm_num)).prod (sands 1))
         exact ((board zero_le_one).spot zero_le_one).plus he
      exact (( ((ferry bnk).prod ((( (board (show 0≤Shepherd.wide G S.supportExponent*2 by unfold Shepherd.wide; positivity)).prod ht).prod (board hY)).prod (oil 4 (stern 4 h)) )).prod hA')).spot (by norm_num)
   have hh:= (Lim.plus hV hu) (-(109/100:ℝ)) (by norm_num)
   have he := (Lim.prod (board (by positivity : 0≤ (2:ℝ)^S.order)) ((board (zenV S.order)).prod (sands (-(109/100:ℝ))))).tiny (by norm_num)
   filter_upwards [hh,eventually_ge_atTop (1:ℝ),he] with x hx hv hq Λ m hm n R H; intro r K
   refine ⟨le_trans ?_ hx.2,Real.rpow_le_one_of_one_le_of_nonpos hv (by norm_num),?_⟩; swap
   · unfold polar; rw[H.rank]; exact hq
   apply add_le_add
   · unfold V beamAmt; rw [H.hM.2.1,H.depth,H.hM.1]; unfold A' T; have h : 0 ≤ Λ:= Cost.nonneg H.good.paths.two; have hp:=S.paths_pos; dsimp only[Z]; gcongr <;> first | exact H.bnd|exact H.beta| (unfold bankCost; try unfold Shepherd.wide; positivity)
     positivity
   have hD:hue x ≥0:=by unfold hue; positivity
   have hr:r≤ f x:= Cleft_mon _ hm; unfold u vat g; rw[mul_assoc _ _ (hue x),H.rank,hikeFee,H.rank,H.paid]; gcongr
lemma orb_charge(S:Stage) (m:ℕ)(A K C:ℝ)(ha:1≤ A)(hc:0≤ C)(hK:0 ≤ K)(hm:1 ≤ m) : Lim (-1/2) (fun x=> composeCost S.order (orbAmt K (thinM x) (shear x) A (sash S x) C (S.order+m+1)) A):=by
   obtain ⟨a,h,hD⟩:=bears m S.order A C S ha hc hm; let p:= S.order; let u:=p+m+1; unfold orbAmt; have hx:= ( ((board (show 0≤(2:ℝ)^u by positivity)).prod (((board hK).prod (ferry (waveM (1/200:ℝ)))).prod (hStep S))).prod (ferry hD)); unfold composeCost; simpa only[zero_add,add_zero] using! ((board (show 0 ≤ (p.factorial:ℝ) by positivity)).prod hx).prod (board (show 0 ≤ (1+A)^p by positivity))
def baubleZ (m:ℕ)(S:Stage)(K C D:ℝ)(G:Gauge)(x:ℝ) := let d:=composeCost S.order (orbAmt K (thinM x) (shear x) C (sash S x) D (S.order+m+1)) C;
   2*(2^S.order*(budC S.order*dreamZ x))* (Real.exp (S.supportExponent *TileNo)* d)
def wheat (m:ℕ):ℝ:=∑ i∈range m,|wage m i|
abbrev cardB (G:Gauge)(x:ℝ):ℝ:= (((puff x+puff x+1)^4:ℕ)* Fintype.card (Loc G 1):ℕ)
lemma minister(G:Gauge)(S:Stage)(m:ℕ)(K C D:ℝ)(hm:1≤ m)(hK:0≤ K)(hC:1≤ C)(hD:0≤ D): ∀ᶠ x:ℝ in atTop, cardB G x*(wheat m*baubleZ m S K C D G x)/peace x ≤ swole x:=by
   let f(x:ℝ):= cardB G x; have h: ConstMass 0 f:= by unfold f cardB; push_cast; exact ((((balloon.gather balloon).gather (mass zero_le_one)).crop 4).cop (mass (Nat.cast_nonneg _)))
   let v(x:ℝ):=baubleZ m S K C D G x; have hv: Lim (-(109/100:ℝ)+(-1/2)) v:=by
      have hz:= ((board zero_le_two).prod ((board (show 0 ≤ (2:ℝ)^S.order by positivity)).prod ((board (zenV S.order)).prod (sands (-(109/100:ℝ)))))).prod ((board (Real.exp_pos (S.supportExponent*TileNo)|>.le)).prod (orb_charge S m C K D hC hD hK hm))
      simpa only [zero_add] using! hz
   have hz:=(((ferry h).prod ((board (show 0≤ wheat m from sum_nonneg fun i _=>abs_nonneg _)).prod hv)).prod fieryG) (-(101/100:ℝ)) (by norm_num)
   filter_upwards [hz,swole_b] with x hx he; rw [div_eq_mul_inv]; exact hx.2.trans he
end YM.Trace.Weir
